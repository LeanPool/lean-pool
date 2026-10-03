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

@[expose]
noncomputable def nb090_split_alpha_0096 (v : Var) (u : Var) (A : Class) (h : Var)
    (dv_h_u : h ≠ u) (dv_h_v : h ≠ v) (dv_u_v : u ≠ v) :
    TAlphaWff
      [((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (syn_wbr (Class.cv (nb090_alpha_dummy_041 A))
          (syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A)))
          (Class.cv (nb090_alpha_dummy_042 A))) (syn_wbr
          (syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_041 A)))
          (syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A)))
          (syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_042 A)))))
      (Wff.imp (syn_wbr (Class.cv (nb090_alpha_dummy_043 v u h))
          (syn_cfv (syn_c1st) (Class.cv u)) (Class.cv (nb090_alpha_dummy_044 v u h)))
        (syn_wbr (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))
          (syn_cfv (syn_c1st) (Class.cv v))
          (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0084 v u A h)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.neg (nb090_split_alpha_0085 v u A h)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.neg (nb090_split_alpha_0085 v u A h))))))))))))
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                (freshVar_injective (((Class.cab (nb090_alpha_dummy_655 A) (Wff.classEq
                        (Class.cab (nb090_alpha_dummy_653 A)
                          (syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c1st)
                            (Class.cv (nb090_alpha_dummy_653 A))))
                        (syn_csn (Class.cv (nb090_alpha_dummy_655 A)))))).fv) (by decide))
                (freshVar_injective (((Class.cab (nb090_alpha_dummy_656 u) (Wff.classEq
                        (Class.cab (nb090_alpha_dummy_654 u) (syn_wbr (Class.cv u) (syn_c1st)
                            (Class.cv (nb090_alpha_dummy_654 u))))
                        (syn_csn (Class.cv (nb090_alpha_dummy_656 u)))))).fv) (by decide))
                (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.classMem (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                    (nb090_split_alpha_0086 v u A h dv_h_u dv_u_v)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_653 A) ≠ (nb090_alpha_dummy_662 A) from (by
          unfold nb090_alpha_dummy_662;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0716 A)
                  1)))) (show (nb090_alpha_dummy_654 u) ≠ (nb090_alpha_dummy_664 u) from (by
          unfold nb090_alpha_dummy_664;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0718 u)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_653 A) ≠
        (nb090_alpha_dummy_661 A) from (by
          unfold nb090_alpha_dummy_661;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0716 A)
                  0)))) (show (nb090_alpha_dummy_654 u) ≠ (nb090_alpha_dummy_663 u) from (by
          unfold nb090_alpha_dummy_663;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0718 u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_653 A) ≠
        (nb090_alpha_dummy_691 A) from (by
          unfold nb090_alpha_dummy_691;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0720
                    A)
                  0)))) (show (nb090_alpha_dummy_654 u) ≠ (nb090_alpha_dummy_692 u) from (by
          unfold nb090_alpha_dummy_692;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0721
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_653 A) ≠
        (nb090_alpha_dummy_665 A) from (by
          unfold nb090_alpha_dummy_665;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0717
                    A)
                  0)))) (show (nb090_alpha_dummy_654 u) ≠ (nb090_alpha_dummy_666 u) from (by
          unfold nb090_alpha_dummy_666;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0719
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_653 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_654 u))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0087 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_693 A), (nb090_alpha_dummy_694 u)), ((nb090_alpha_dummy_662 A),
        (nb090_alpha_dummy_664 u)), ((nb090_alpha_dummy_661 A), (nb090_alpha_dummy_663 u)),
        ((nb090_alpha_dummy_691 A), (nb090_alpha_dummy_692 u)), ((nb090_alpha_dummy_665 A),
        (nb090_alpha_dummy_666 u)), ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)),
        ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)), ((nb090_alpha_dummy_658 A),
        (nb090_alpha_dummy_660 u)), ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)),
        ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_653 A) ≠ (nb090_alpha_dummy_662 A) from (by
          unfold nb090_alpha_dummy_662;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0716 A)
                  1)))) (show (nb090_alpha_dummy_654 u) ≠ (nb090_alpha_dummy_664 u) from (by
          unfold nb090_alpha_dummy_664;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0718 u)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_653 A) ≠
        (nb090_alpha_dummy_661 A) from (by
          unfold nb090_alpha_dummy_661;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0716 A)
                  0)))) (show (nb090_alpha_dummy_654 u) ≠ (nb090_alpha_dummy_663 u) from (by
          unfold nb090_alpha_dummy_663;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0718 u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_653 A) ≠
        (nb090_alpha_dummy_691 A) from (by
          unfold nb090_alpha_dummy_691;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0720
                    A)
                  0)))) (show (nb090_alpha_dummy_654 u) ≠ (nb090_alpha_dummy_692 u) from (by
          unfold nb090_alpha_dummy_692;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0721
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_653 A) ≠
        (nb090_alpha_dummy_665 A) from (by
          unfold nb090_alpha_dummy_665;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0717
                    A)
                  0)))) (show (nb090_alpha_dummy_654 u) ≠ (nb090_alpha_dummy_666 u) from (by
          unfold nb090_alpha_dummy_666;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0719
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_653 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_654 u))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0087 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_693 A), (nb090_alpha_dummy_694 u)), ((nb090_alpha_dummy_662 A),
        (nb090_alpha_dummy_664 u)), ((nb090_alpha_dummy_661 A), (nb090_alpha_dummy_663 u)),
        ((nb090_alpha_dummy_691 A), (nb090_alpha_dummy_692 u)), ((nb090_alpha_dummy_665 A),
        (nb090_alpha_dummy_666 u)), ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)),
        ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)), ((nb090_alpha_dummy_658 A),
        (nb090_alpha_dummy_660 u)), ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)),
        ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.refl_of_reflOn
                        [((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)),
                          ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)),
                          ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)),
                          ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)),
                          ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
                          ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                          ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                          ((nb090_alpha_dummy_001 A), u),
                          ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                        (syn_c1st) (nb090_wpp_refl_0298 v u A h)))) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_655 A) ≠ (nb090_alpha_dummy_697 A) from (by
                              unfold nb090_alpha_dummy_697;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0726 A) 0))))
                          (show (nb090_alpha_dummy_656 u) ≠ (nb090_alpha_dummy_698 u) from (by
                              unfold nb090_alpha_dummy_698;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0727 u) 0))))
                          (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classMem (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0090 v u A h)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem
                                      (TAlphaVar.there (freshVar_injective
        (((Class.cab (nb090_alpha_dummy_779 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_777 A)
        (syn_wbr (Class.cv (nb090_alpha_dummy_042 A)) (Class.cv (nb090_alpha_dummy_000 A))
        (Class.cv (nb090_alpha_dummy_777 A)))) (syn_csn (Class.cv
        (nb090_alpha_dummy_779 A)))))).fv) (by decide)) (freshVar_injective
        (((Class.cab (nb090_alpha_dummy_780 v u h) (Wff.classEq
        (Class.cab (nb090_alpha_dummy_778 v u h) (syn_wbr (Class.cv
        (nb090_alpha_dummy_044 v u h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_778 v u h))))
        (syn_csn (Class.cv (nb090_alpha_dummy_780 v u h)))))).fv) (by decide))
                                        (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb090_split_alpha_0091 v u A h))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_777 A) ≠
        (nb090_alpha_dummy_786 A) from (by
          unfold
            nb090_alpha_dummy_786;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0856
                    A)
                  1)))) (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_788 v u h) from
        (by
          unfold
            nb090_alpha_dummy_788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0858
                    v
                    u
                    h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_777 A) ≠
        (nb090_alpha_dummy_785 A) from (by
          unfold
            nb090_alpha_dummy_785;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0856
                    A)
                  0)))) (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_787 v u h) from
        (by
          unfold
            nb090_alpha_dummy_787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0858
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_777 A) ≠
        (nb090_alpha_dummy_815 A) from (by
          unfold
            nb090_alpha_dummy_815;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0860
                    A)
                  0)))) (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_816 v u h) from
        (by
          unfold
            nb090_alpha_dummy_816;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0861
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_777 A) ≠
        (nb090_alpha_dummy_789 A) from (by
          unfold
            nb090_alpha_dummy_789;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0857
                    A)
                  0)))) (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_790 v u h) from
        (by
          unfold
            nb090_alpha_dummy_790;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0859
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_042 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_777 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_044 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_778 v u h))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0092 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_817 A), (nb090_alpha_dummy_818 v u h)), ((nb090_alpha_dummy_786 A),
        (nb090_alpha_dummy_788 v u h)), ((nb090_alpha_dummy_785 A), (nb090_alpha_dummy_787 v u
        h)), ((nb090_alpha_dummy_815 A), (nb090_alpha_dummy_816 v u h)), ((nb090_alpha_dummy_789
        A), (nb090_alpha_dummy_790 v u h)), ((nb090_alpha_dummy_777 A), (nb090_alpha_dummy_778
        v u h)), ((nb090_alpha_dummy_779 A), (nb090_alpha_dummy_780 v u h)),
        ((nb090_alpha_dummy_782 A), (nb090_alpha_dummy_784 v u h)), ((nb090_alpha_dummy_781 A),
        (nb090_alpha_dummy_783 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u
        h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775
        A), (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704
        v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A),
        h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_ccompl (syn_csn
        (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_777
        A) ≠ (nb090_alpha_dummy_786 A) from (by
          unfold
            nb090_alpha_dummy_786;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0856
                    A)
                  1)))) (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_788 v u h) from
        (by
          unfold
            nb090_alpha_dummy_788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0858
                    v
                    u
                    h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_777 A) ≠
        (nb090_alpha_dummy_785 A) from (by
          unfold
            nb090_alpha_dummy_785;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0856
                    A)
                  0)))) (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_787 v u h) from
        (by
          unfold
            nb090_alpha_dummy_787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0858
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_777 A) ≠
        (nb090_alpha_dummy_815 A) from (by
          unfold
            nb090_alpha_dummy_815;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0860
                    A)
                  0)))) (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_816 v u h) from
        (by
          unfold
            nb090_alpha_dummy_816;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0861
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_777 A) ≠
        (nb090_alpha_dummy_789 A) from (by
          unfold
            nb090_alpha_dummy_789;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0857
                    A)
                  0)))) (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_790 v u h) from
        (by
          unfold
            nb090_alpha_dummy_790;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0859
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_042 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_777 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_044 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_778 v u h))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0092 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_817 A), (nb090_alpha_dummy_818 v u h)), ((nb090_alpha_dummy_786 A),
        (nb090_alpha_dummy_788 v u h)), ((nb090_alpha_dummy_785 A), (nb090_alpha_dummy_787 v u
        h)), ((nb090_alpha_dummy_815 A), (nb090_alpha_dummy_816 v u h)), ((nb090_alpha_dummy_789
        A), (nb090_alpha_dummy_790 v u h)), ((nb090_alpha_dummy_777 A), (nb090_alpha_dummy_778
        v u h)), ((nb090_alpha_dummy_779 A), (nb090_alpha_dummy_780 v u h)),
        ((nb090_alpha_dummy_782 A), (nb090_alpha_dummy_784 v u h)), ((nb090_alpha_dummy_781 A),
        (nb090_alpha_dummy_783 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u
        h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775
        A), (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704
        v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A),
        h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_ccompl (syn_csn
        (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_777 A) from (by
          unfold nb090_alpha_dummy_777;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0868 A)
                  0)))) (show h ≠ (nb090_alpha_dummy_778 v u h) from (by
          unfold nb090_alpha_dummy_778;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0871 v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_779 A) from (by
          unfold nb090_alpha_dummy_779;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0869 A)
                  0)))) (show h ≠ (nb090_alpha_dummy_780 v u h) from (by
          unfold nb090_alpha_dummy_780;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0872 v
                    u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_782 A) from (by
          unfold nb090_alpha_dummy_782;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0870
                    A)
                  1)))) (show h ≠ (nb090_alpha_dummy_784 v u h) from (by
          unfold nb090_alpha_dummy_784;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0873
                    v u h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_781 A) from (by
          unfold nb090_alpha_dummy_781;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0870
                    A)
                  0)))) (show h ≠ (nb090_alpha_dummy_783 v u h) from (by
          unfold nb090_alpha_dummy_783;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0873
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_700 A) from (by
          unfold
            nb090_alpha_dummy_700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0780
                    A)
                  1)))) (show h ≠ (nb090_alpha_dummy_702 v u h) from (by
          unfold
            nb090_alpha_dummy_702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0782
                    v u h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_699 A) from (by
          unfold
            nb090_alpha_dummy_699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0780
                    A)
                  0)))) (show h ≠ (nb090_alpha_dummy_701 v u h) from (by
          unfold
            nb090_alpha_dummy_701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0782
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_775 A) from (by
          unfold
            nb090_alpha_dummy_775;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0866
                    A)
                  0)))) (show h ≠ (nb090_alpha_dummy_776 v u h) from (by
          unfold
            nb090_alpha_dummy_776;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0867
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_703 A) from (by
          unfold
            nb090_alpha_dummy_703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0781
                    A)
                  0)))) (show h ≠ (nb090_alpha_dummy_704 v u h) from (by
          unfold
            nb090_alpha_dummy_704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0783
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_042 A) from (by
          unfold
            nb090_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0778
                    A)
                  1)))) (show h ≠ (nb090_alpha_dummy_044 v u h) from (by
          unfold
            nb090_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0779
                    v u h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_041 A) from (by
          unfold
            nb090_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0778
                    A)
                  0)))) (show h ≠ (nb090_alpha_dummy_043 v u h) from (by
          unfold
            nb090_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0779
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_779 A) ≠ (nb090_alpha_dummy_821 A) from (by
          unfold nb090_alpha_dummy_821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0874 A)
                  0)))) (show (nb090_alpha_dummy_780 v u h) ≠ (nb090_alpha_dummy_822 v u h) from
        (by
          unfold nb090_alpha_dummy_822;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0875 v u
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (nb090_split_alpha_0093 v u A h)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem
                                      (TAlphaVar.there (freshVar_injective
        (((Class.cab (nb090_alpha_dummy_779 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_777 A)
        (syn_wbr (Class.cv (nb090_alpha_dummy_042 A)) (Class.cv (nb090_alpha_dummy_000 A))
        (Class.cv (nb090_alpha_dummy_777 A)))) (syn_csn (Class.cv
        (nb090_alpha_dummy_779 A)))))).fv) (by decide)) (freshVar_injective
        (((Class.cab (nb090_alpha_dummy_780 v u h) (Wff.classEq
        (Class.cab (nb090_alpha_dummy_778 v u h) (syn_wbr (Class.cv
        (nb090_alpha_dummy_044 v u h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_778 v u h))))
        (syn_csn (Class.cv (nb090_alpha_dummy_780 v u h)))))).fv) (by decide))
                                        (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb090_split_alpha_0091 v u A h))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_777 A) ≠
        (nb090_alpha_dummy_786 A) from (by
          unfold
            nb090_alpha_dummy_786;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0856
                    A)
                  1)))) (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_788 v u h) from
        (by
          unfold
            nb090_alpha_dummy_788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0858
                    v
                    u
                    h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_777 A) ≠
        (nb090_alpha_dummy_785 A) from (by
          unfold
            nb090_alpha_dummy_785;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0856
                    A)
                  0)))) (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_787 v u h) from
        (by
          unfold
            nb090_alpha_dummy_787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0858
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_777 A) ≠
        (nb090_alpha_dummy_815 A) from (by
          unfold
            nb090_alpha_dummy_815;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0860
                    A)
                  0)))) (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_816 v u h) from
        (by
          unfold
            nb090_alpha_dummy_816;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0861
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_777 A) ≠
        (nb090_alpha_dummy_789 A) from (by
          unfold
            nb090_alpha_dummy_789;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0857
                    A)
                  0)))) (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_790 v u h) from
        (by
          unfold
            nb090_alpha_dummy_790;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0859
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_042 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_777 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_044 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_778 v u h))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0092 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_817 A), (nb090_alpha_dummy_818 v u h)), ((nb090_alpha_dummy_786 A),
        (nb090_alpha_dummy_788 v u h)), ((nb090_alpha_dummy_785 A), (nb090_alpha_dummy_787 v u
        h)), ((nb090_alpha_dummy_815 A), (nb090_alpha_dummy_816 v u h)), ((nb090_alpha_dummy_789
        A), (nb090_alpha_dummy_790 v u h)), ((nb090_alpha_dummy_777 A), (nb090_alpha_dummy_778
        v u h)), ((nb090_alpha_dummy_779 A), (nb090_alpha_dummy_780 v u h)),
        ((nb090_alpha_dummy_782 A), (nb090_alpha_dummy_784 v u h)), ((nb090_alpha_dummy_781 A),
        (nb090_alpha_dummy_783 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u
        h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775
        A), (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704
        v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A),
        h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_ccompl (syn_csn
        (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_777
        A) ≠ (nb090_alpha_dummy_786 A) from (by
          unfold
            nb090_alpha_dummy_786;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0856
                    A)
                  1)))) (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_788 v u h) from
        (by
          unfold
            nb090_alpha_dummy_788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0858
                    v
                    u
                    h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_777 A) ≠
        (nb090_alpha_dummy_785 A) from (by
          unfold
            nb090_alpha_dummy_785;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0856
                    A)
                  0)))) (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_787 v u h) from
        (by
          unfold
            nb090_alpha_dummy_787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0858
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_777 A) ≠
        (nb090_alpha_dummy_815 A) from (by
          unfold
            nb090_alpha_dummy_815;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0860
                    A)
                  0)))) (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_816 v u h) from
        (by
          unfold
            nb090_alpha_dummy_816;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0861
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_777 A) ≠
        (nb090_alpha_dummy_789 A) from (by
          unfold
            nb090_alpha_dummy_789;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0857
                    A)
                  0)))) (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_790 v u h) from
        (by
          unfold
            nb090_alpha_dummy_790;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0859
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_042 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_777 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_044 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_778 v u h))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0092 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_817 A), (nb090_alpha_dummy_818 v u h)), ((nb090_alpha_dummy_786 A),
        (nb090_alpha_dummy_788 v u h)), ((nb090_alpha_dummy_785 A), (nb090_alpha_dummy_787 v u
        h)), ((nb090_alpha_dummy_815 A), (nb090_alpha_dummy_816 v u h)), ((nb090_alpha_dummy_789
        A), (nb090_alpha_dummy_790 v u h)), ((nb090_alpha_dummy_777 A), (nb090_alpha_dummy_778
        v u h)), ((nb090_alpha_dummy_779 A), (nb090_alpha_dummy_780 v u h)),
        ((nb090_alpha_dummy_782 A), (nb090_alpha_dummy_784 v u h)), ((nb090_alpha_dummy_781 A),
        (nb090_alpha_dummy_783 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u
        h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775
        A), (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704
        v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A),
        h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_ccompl (syn_csn
        (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_777 A) from (by
          unfold nb090_alpha_dummy_777;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0868 A)
                  0)))) (show h ≠ (nb090_alpha_dummy_778 v u h) from (by
          unfold nb090_alpha_dummy_778;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0871 v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_779 A) from (by
          unfold nb090_alpha_dummy_779;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0869 A)
                  0)))) (show h ≠ (nb090_alpha_dummy_780 v u h) from (by
          unfold nb090_alpha_dummy_780;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0872 v
                    u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_782 A) from (by
          unfold nb090_alpha_dummy_782;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0870
                    A)
                  1)))) (show h ≠ (nb090_alpha_dummy_784 v u h) from (by
          unfold nb090_alpha_dummy_784;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0873
                    v u h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_781 A) from (by
          unfold nb090_alpha_dummy_781;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0870
                    A)
                  0)))) (show h ≠ (nb090_alpha_dummy_783 v u h) from (by
          unfold nb090_alpha_dummy_783;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0873
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_700 A) from (by
          unfold
            nb090_alpha_dummy_700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0780
                    A)
                  1)))) (show h ≠ (nb090_alpha_dummy_702 v u h) from (by
          unfold
            nb090_alpha_dummy_702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0782
                    v u h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_699 A) from (by
          unfold
            nb090_alpha_dummy_699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0780
                    A)
                  0)))) (show h ≠ (nb090_alpha_dummy_701 v u h) from (by
          unfold
            nb090_alpha_dummy_701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0782
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_775 A) from (by
          unfold
            nb090_alpha_dummy_775;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0866
                    A)
                  0)))) (show h ≠ (nb090_alpha_dummy_776 v u h) from (by
          unfold
            nb090_alpha_dummy_776;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0867
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_703 A) from (by
          unfold
            nb090_alpha_dummy_703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0781
                    A)
                  0)))) (show h ≠ (nb090_alpha_dummy_704 v u h) from (by
          unfold
            nb090_alpha_dummy_704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0783
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_042 A) from (by
          unfold
            nb090_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0778
                    A)
                  1)))) (show h ≠ (nb090_alpha_dummy_044 v u h) from (by
          unfold
            nb090_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0779
                    v u h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_041 A) from (by
          unfold
            nb090_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0778
                    A)
                  0)))) (show h ≠ (nb090_alpha_dummy_043 v u h) from (by
          unfold
            nb090_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0779
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_779 A) ≠ (nb090_alpha_dummy_821 A) from (by
          unfold nb090_alpha_dummy_821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0874 A)
                  0)))) (show (nb090_alpha_dummy_780 v u h) ≠ (nb090_alpha_dummy_822 v u h) from
        (by
          unfold nb090_alpha_dummy_822;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0875 v u
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))))))
                            (nb090_split_alpha_0093 v u A h)))))))))))) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there (freshVar_injective
                  (((Class.cab (nb090_alpha_dummy_829 A) (Wff.classEq
                        (Class.cab (nb090_alpha_dummy_827 A)
                          (syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c1st)
                            (Class.cv (nb090_alpha_dummy_827 A))))
                        (syn_csn (Class.cv (nb090_alpha_dummy_829 A)))))).fv) (by decide))
                (freshVar_injective (((Class.cab (nb090_alpha_dummy_830 v) (Wff.classEq
                        (Class.cab (nb090_alpha_dummy_828 v) (syn_wbr (Class.cv v) (syn_c1st)
                            (Class.cv (nb090_alpha_dummy_828 v))))
                        (syn_csn (Class.cv (nb090_alpha_dummy_830 v)))))).fv) (by decide))
                (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.classMem (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                    (nb090_split_alpha_0094 v u A h dv_h_v)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_827 A) ≠ (nb090_alpha_dummy_836 A) from (by
          unfold nb090_alpha_dummy_836;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0916 A)
                  1)))) (show (nb090_alpha_dummy_828 v) ≠ (nb090_alpha_dummy_838 v) from (by
          unfold nb090_alpha_dummy_838;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0918 v)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_827 A) ≠
        (nb090_alpha_dummy_835 A) from (by
          unfold nb090_alpha_dummy_835;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0916 A)
                  0)))) (show (nb090_alpha_dummy_828 v) ≠ (nb090_alpha_dummy_837 v) from (by
          unfold nb090_alpha_dummy_837;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0918 v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_827 A) ≠
        (nb090_alpha_dummy_865 A) from (by
          unfold nb090_alpha_dummy_865;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0920
                    A)
                  0)))) (show (nb090_alpha_dummy_828 v) ≠ (nb090_alpha_dummy_866 v) from (by
          unfold nb090_alpha_dummy_866;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0921
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_827 A) ≠
        (nb090_alpha_dummy_839 A) from (by
          unfold nb090_alpha_dummy_839;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0917
                    A)
                  0)))) (show (nb090_alpha_dummy_828 v) ≠ (nb090_alpha_dummy_840 v) from (by
          unfold nb090_alpha_dummy_840;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0919
                    v)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_827 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_828 v))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0095 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_867 A), (nb090_alpha_dummy_868 v)), ((nb090_alpha_dummy_836 A),
        (nb090_alpha_dummy_838 v)), ((nb090_alpha_dummy_835 A), (nb090_alpha_dummy_837 v)),
        ((nb090_alpha_dummy_865 A), (nb090_alpha_dummy_866 v)), ((nb090_alpha_dummy_839 A),
        (nb090_alpha_dummy_840 v)), ((nb090_alpha_dummy_827 A), (nb090_alpha_dummy_828 v)),
        ((nb090_alpha_dummy_829 A), (nb090_alpha_dummy_830 v)), ((nb090_alpha_dummy_832 A),
        (nb090_alpha_dummy_834 v)), ((nb090_alpha_dummy_831 A), (nb090_alpha_dummy_833 v)),
        ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_827 A) ≠ (nb090_alpha_dummy_836 A) from (by
          unfold nb090_alpha_dummy_836;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0916 A)
                  1)))) (show (nb090_alpha_dummy_828 v) ≠ (nb090_alpha_dummy_838 v) from (by
          unfold nb090_alpha_dummy_838;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0918 v)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_827 A) ≠
        (nb090_alpha_dummy_835 A) from (by
          unfold nb090_alpha_dummy_835;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0916 A)
                  0)))) (show (nb090_alpha_dummy_828 v) ≠ (nb090_alpha_dummy_837 v) from (by
          unfold nb090_alpha_dummy_837;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0918 v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_827 A) ≠
        (nb090_alpha_dummy_865 A) from (by
          unfold nb090_alpha_dummy_865;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0920
                    A)
                  0)))) (show (nb090_alpha_dummy_828 v) ≠ (nb090_alpha_dummy_866 v) from (by
          unfold nb090_alpha_dummy_866;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0921
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_827 A) ≠
        (nb090_alpha_dummy_839 A) from (by
          unfold nb090_alpha_dummy_839;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0917
                    A)
                  0)))) (show (nb090_alpha_dummy_828 v) ≠ (nb090_alpha_dummy_840 v) from (by
          unfold nb090_alpha_dummy_840;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0919
                    v)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_827 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_828 v))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0095 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_867 A), (nb090_alpha_dummy_868 v)), ((nb090_alpha_dummy_836 A),
        (nb090_alpha_dummy_838 v)), ((nb090_alpha_dummy_835 A), (nb090_alpha_dummy_837 v)),
        ((nb090_alpha_dummy_865 A), (nb090_alpha_dummy_866 v)), ((nb090_alpha_dummy_839 A),
        (nb090_alpha_dummy_840 v)), ((nb090_alpha_dummy_827 A), (nb090_alpha_dummy_828 v)),
        ((nb090_alpha_dummy_829 A), (nb090_alpha_dummy_830 v)), ((nb090_alpha_dummy_832 A),
        (nb090_alpha_dummy_834 v)), ((nb090_alpha_dummy_831 A), (nb090_alpha_dummy_833 v)),
        ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.refl_of_reflOn
                        [((nb090_alpha_dummy_827 A), (nb090_alpha_dummy_828 v)),
                          ((nb090_alpha_dummy_829 A), (nb090_alpha_dummy_830 v)),
                          ((nb090_alpha_dummy_832 A), (nb090_alpha_dummy_834 v)),
                          ((nb090_alpha_dummy_831 A), (nb090_alpha_dummy_833 v)),
                          ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
                          ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                          ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                          ((nb090_alpha_dummy_001 A), u),
                          ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                        (syn_c1st) (nb090_wpp_refl_0327 v u A h)))) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_829 A) ≠ (nb090_alpha_dummy_871 A) from (by
                              unfold nb090_alpha_dummy_871;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0926 A) 0))))
                          (show (nb090_alpha_dummy_830 v) ≠ (nb090_alpha_dummy_872 v) from (by
                              unfold nb090_alpha_dummy_872;
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

@[expose]
noncomputable def nb090_split_alpha_0097 (v : Var) (u : Var) (A : Class) (h : Var)
    (dv_h_u : h ≠ u) (dv_h_v : h ≠ v) (dv_u_v : u ≠ v) :
    TAlphaWff
      [((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (syn_wbr (syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
            (Class.cv (nb090_alpha_dummy_041 A)))
          (syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A)))
          (syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_042 A))))
        (syn_wbr (Class.cv (nb090_alpha_dummy_041 A))
          (syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A)))
          (Class.cv (nb090_alpha_dummy_042 A))))
      (Wff.imp (syn_wbr (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))
          (syn_cfv (syn_c1st) (Class.cv v))
          (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h))))
        (syn_wbr (Class.cv (nb090_alpha_dummy_043 v u h))
          (syn_cfv (syn_c1st) (Class.cv u)) (Class.cv (nb090_alpha_dummy_044 v u h)))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0090 v u A h)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem
                                      (TAlphaVar.there (freshVar_injective
        (((Class.cab (nb090_alpha_dummy_779 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_777 A)
        (syn_wbr (Class.cv (nb090_alpha_dummy_042 A)) (Class.cv (nb090_alpha_dummy_000 A))
        (Class.cv (nb090_alpha_dummy_777 A)))) (syn_csn (Class.cv
        (nb090_alpha_dummy_779 A)))))).fv) (by decide)) (freshVar_injective
        (((Class.cab (nb090_alpha_dummy_780 v u h) (Wff.classEq
        (Class.cab (nb090_alpha_dummy_778 v u h) (syn_wbr (Class.cv
        (nb090_alpha_dummy_044 v u h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_778 v u h))))
        (syn_csn (Class.cv (nb090_alpha_dummy_780 v u h)))))).fv) (by decide))
                                        (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb090_split_alpha_0091 v u A h))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_777 A) ≠
        (nb090_alpha_dummy_786 A) from (by
          unfold
            nb090_alpha_dummy_786;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0856
                    A)
                  1)))) (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_788 v u h) from
        (by
          unfold
            nb090_alpha_dummy_788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0858
                    v
                    u
                    h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_777 A) ≠
        (nb090_alpha_dummy_785 A) from (by
          unfold
            nb090_alpha_dummy_785;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0856
                    A)
                  0)))) (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_787 v u h) from
        (by
          unfold
            nb090_alpha_dummy_787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0858
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_777 A) ≠
        (nb090_alpha_dummy_815 A) from (by
          unfold
            nb090_alpha_dummy_815;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0860
                    A)
                  0)))) (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_816 v u h) from
        (by
          unfold
            nb090_alpha_dummy_816;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0861
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_777 A) ≠
        (nb090_alpha_dummy_789 A) from (by
          unfold
            nb090_alpha_dummy_789;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0857
                    A)
                  0)))) (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_790 v u h) from
        (by
          unfold
            nb090_alpha_dummy_790;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0859
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_042 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_777 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_044 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_778 v u h))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0092 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_817 A), (nb090_alpha_dummy_818 v u h)), ((nb090_alpha_dummy_786 A),
        (nb090_alpha_dummy_788 v u h)), ((nb090_alpha_dummy_785 A), (nb090_alpha_dummy_787 v u
        h)), ((nb090_alpha_dummy_815 A), (nb090_alpha_dummy_816 v u h)), ((nb090_alpha_dummy_789
        A), (nb090_alpha_dummy_790 v u h)), ((nb090_alpha_dummy_777 A), (nb090_alpha_dummy_778
        v u h)), ((nb090_alpha_dummy_779 A), (nb090_alpha_dummy_780 v u h)),
        ((nb090_alpha_dummy_782 A), (nb090_alpha_dummy_784 v u h)), ((nb090_alpha_dummy_781 A),
        (nb090_alpha_dummy_783 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u
        h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775
        A), (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704
        v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A),
        h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_ccompl (syn_csn
        (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_777
        A) ≠ (nb090_alpha_dummy_786 A) from (by
          unfold
            nb090_alpha_dummy_786;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0856
                    A)
                  1)))) (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_788 v u h) from
        (by
          unfold
            nb090_alpha_dummy_788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0858
                    v
                    u
                    h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_777 A) ≠
        (nb090_alpha_dummy_785 A) from (by
          unfold
            nb090_alpha_dummy_785;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0856
                    A)
                  0)))) (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_787 v u h) from
        (by
          unfold
            nb090_alpha_dummy_787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0858
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_777 A) ≠
        (nb090_alpha_dummy_815 A) from (by
          unfold
            nb090_alpha_dummy_815;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0860
                    A)
                  0)))) (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_816 v u h) from
        (by
          unfold
            nb090_alpha_dummy_816;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0861
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_777 A) ≠
        (nb090_alpha_dummy_789 A) from (by
          unfold
            nb090_alpha_dummy_789;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0857
                    A)
                  0)))) (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_790 v u h) from
        (by
          unfold
            nb090_alpha_dummy_790;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0859
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_042 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_777 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_044 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_778 v u h))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0092 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_817 A), (nb090_alpha_dummy_818 v u h)), ((nb090_alpha_dummy_786 A),
        (nb090_alpha_dummy_788 v u h)), ((nb090_alpha_dummy_785 A), (nb090_alpha_dummy_787 v u
        h)), ((nb090_alpha_dummy_815 A), (nb090_alpha_dummy_816 v u h)), ((nb090_alpha_dummy_789
        A), (nb090_alpha_dummy_790 v u h)), ((nb090_alpha_dummy_777 A), (nb090_alpha_dummy_778
        v u h)), ((nb090_alpha_dummy_779 A), (nb090_alpha_dummy_780 v u h)),
        ((nb090_alpha_dummy_782 A), (nb090_alpha_dummy_784 v u h)), ((nb090_alpha_dummy_781 A),
        (nb090_alpha_dummy_783 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u
        h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775
        A), (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704
        v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A),
        h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_ccompl (syn_csn
        (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_777 A) from (by
          unfold nb090_alpha_dummy_777;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0868 A)
                  0)))) (show h ≠ (nb090_alpha_dummy_778 v u h) from (by
          unfold nb090_alpha_dummy_778;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0871 v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_779 A) from (by
          unfold nb090_alpha_dummy_779;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0869 A)
                  0)))) (show h ≠ (nb090_alpha_dummy_780 v u h) from (by
          unfold nb090_alpha_dummy_780;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0872 v
                    u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_782 A) from (by
          unfold nb090_alpha_dummy_782;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0870
                    A)
                  1)))) (show h ≠ (nb090_alpha_dummy_784 v u h) from (by
          unfold nb090_alpha_dummy_784;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0873
                    v u h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_781 A) from (by
          unfold nb090_alpha_dummy_781;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0870
                    A)
                  0)))) (show h ≠ (nb090_alpha_dummy_783 v u h) from (by
          unfold nb090_alpha_dummy_783;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0873
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_700 A) from (by
          unfold
            nb090_alpha_dummy_700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0780
                    A)
                  1)))) (show h ≠ (nb090_alpha_dummy_702 v u h) from (by
          unfold
            nb090_alpha_dummy_702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0782
                    v u h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_699 A) from (by
          unfold
            nb090_alpha_dummy_699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0780
                    A)
                  0)))) (show h ≠ (nb090_alpha_dummy_701 v u h) from (by
          unfold
            nb090_alpha_dummy_701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0782
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_775 A) from (by
          unfold
            nb090_alpha_dummy_775;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0866
                    A)
                  0)))) (show h ≠ (nb090_alpha_dummy_776 v u h) from (by
          unfold
            nb090_alpha_dummy_776;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0867
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_703 A) from (by
          unfold
            nb090_alpha_dummy_703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0781
                    A)
                  0)))) (show h ≠ (nb090_alpha_dummy_704 v u h) from (by
          unfold
            nb090_alpha_dummy_704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0783
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_042 A) from (by
          unfold
            nb090_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0778
                    A)
                  1)))) (show h ≠ (nb090_alpha_dummy_044 v u h) from (by
          unfold
            nb090_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0779
                    v u h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_041 A) from (by
          unfold
            nb090_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0778
                    A)
                  0)))) (show h ≠ (nb090_alpha_dummy_043 v u h) from (by
          unfold
            nb090_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0779
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_779 A) ≠ (nb090_alpha_dummy_821 A) from (by
          unfold nb090_alpha_dummy_821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0874 A)
                  0)))) (show (nb090_alpha_dummy_780 v u h) ≠ (nb090_alpha_dummy_822 v u h) from
        (by
          unfold nb090_alpha_dummy_822;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0875 v u
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (nb090_split_alpha_0093 v u A h)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem
                                      (TAlphaVar.there (freshVar_injective
        (((Class.cab (nb090_alpha_dummy_779 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_777 A)
        (syn_wbr (Class.cv (nb090_alpha_dummy_042 A)) (Class.cv (nb090_alpha_dummy_000 A))
        (Class.cv (nb090_alpha_dummy_777 A)))) (syn_csn (Class.cv
        (nb090_alpha_dummy_779 A)))))).fv) (by decide)) (freshVar_injective
        (((Class.cab (nb090_alpha_dummy_780 v u h) (Wff.classEq
        (Class.cab (nb090_alpha_dummy_778 v u h) (syn_wbr (Class.cv
        (nb090_alpha_dummy_044 v u h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_778 v u h))))
        (syn_csn (Class.cv (nb090_alpha_dummy_780 v u h)))))).fv) (by decide))
                                        (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb090_split_alpha_0091 v u A h))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_777 A) ≠
        (nb090_alpha_dummy_786 A) from (by
          unfold
            nb090_alpha_dummy_786;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0856
                    A)
                  1)))) (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_788 v u h) from
        (by
          unfold
            nb090_alpha_dummy_788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0858
                    v
                    u
                    h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_777 A) ≠
        (nb090_alpha_dummy_785 A) from (by
          unfold
            nb090_alpha_dummy_785;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0856
                    A)
                  0)))) (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_787 v u h) from
        (by
          unfold
            nb090_alpha_dummy_787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0858
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_777 A) ≠
        (nb090_alpha_dummy_815 A) from (by
          unfold
            nb090_alpha_dummy_815;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0860
                    A)
                  0)))) (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_816 v u h) from
        (by
          unfold
            nb090_alpha_dummy_816;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0861
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_777 A) ≠
        (nb090_alpha_dummy_789 A) from (by
          unfold
            nb090_alpha_dummy_789;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0857
                    A)
                  0)))) (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_790 v u h) from
        (by
          unfold
            nb090_alpha_dummy_790;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0859
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_042 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_777 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_044 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_778 v u h))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0092 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_817 A), (nb090_alpha_dummy_818 v u h)), ((nb090_alpha_dummy_786 A),
        (nb090_alpha_dummy_788 v u h)), ((nb090_alpha_dummy_785 A), (nb090_alpha_dummy_787 v u
        h)), ((nb090_alpha_dummy_815 A), (nb090_alpha_dummy_816 v u h)), ((nb090_alpha_dummy_789
        A), (nb090_alpha_dummy_790 v u h)), ((nb090_alpha_dummy_777 A), (nb090_alpha_dummy_778
        v u h)), ((nb090_alpha_dummy_779 A), (nb090_alpha_dummy_780 v u h)),
        ((nb090_alpha_dummy_782 A), (nb090_alpha_dummy_784 v u h)), ((nb090_alpha_dummy_781 A),
        (nb090_alpha_dummy_783 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u
        h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775
        A), (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704
        v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A),
        h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_ccompl (syn_csn
        (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_777
        A) ≠ (nb090_alpha_dummy_786 A) from (by
          unfold
            nb090_alpha_dummy_786;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0856
                    A)
                  1)))) (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_788 v u h) from
        (by
          unfold
            nb090_alpha_dummy_788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0858
                    v
                    u
                    h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_777 A) ≠
        (nb090_alpha_dummy_785 A) from (by
          unfold
            nb090_alpha_dummy_785;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0856
                    A)
                  0)))) (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_787 v u h) from
        (by
          unfold
            nb090_alpha_dummy_787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0858
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_777 A) ≠
        (nb090_alpha_dummy_815 A) from (by
          unfold
            nb090_alpha_dummy_815;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0860
                    A)
                  0)))) (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_816 v u h) from
        (by
          unfold
            nb090_alpha_dummy_816;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0861
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_777 A) ≠
        (nb090_alpha_dummy_789 A) from (by
          unfold
            nb090_alpha_dummy_789;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0857
                    A)
                  0)))) (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_790 v u h) from
        (by
          unfold
            nb090_alpha_dummy_790;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0859
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_042 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_777 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_044 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_778 v u h))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0092 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_817 A), (nb090_alpha_dummy_818 v u h)), ((nb090_alpha_dummy_786 A),
        (nb090_alpha_dummy_788 v u h)), ((nb090_alpha_dummy_785 A), (nb090_alpha_dummy_787 v u
        h)), ((nb090_alpha_dummy_815 A), (nb090_alpha_dummy_816 v u h)), ((nb090_alpha_dummy_789
        A), (nb090_alpha_dummy_790 v u h)), ((nb090_alpha_dummy_777 A), (nb090_alpha_dummy_778
        v u h)), ((nb090_alpha_dummy_779 A), (nb090_alpha_dummy_780 v u h)),
        ((nb090_alpha_dummy_782 A), (nb090_alpha_dummy_784 v u h)), ((nb090_alpha_dummy_781 A),
        (nb090_alpha_dummy_783 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u
        h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775
        A), (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704
        v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A),
        h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_ccompl (syn_csn
        (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_777 A) from (by
          unfold nb090_alpha_dummy_777;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0868 A)
                  0)))) (show h ≠ (nb090_alpha_dummy_778 v u h) from (by
          unfold nb090_alpha_dummy_778;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0871 v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_779 A) from (by
          unfold nb090_alpha_dummy_779;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0869 A)
                  0)))) (show h ≠ (nb090_alpha_dummy_780 v u h) from (by
          unfold nb090_alpha_dummy_780;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0872 v
                    u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_782 A) from (by
          unfold nb090_alpha_dummy_782;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0870
                    A)
                  1)))) (show h ≠ (nb090_alpha_dummy_784 v u h) from (by
          unfold nb090_alpha_dummy_784;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0873
                    v u h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_781 A) from (by
          unfold nb090_alpha_dummy_781;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0870
                    A)
                  0)))) (show h ≠ (nb090_alpha_dummy_783 v u h) from (by
          unfold nb090_alpha_dummy_783;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0873
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_700 A) from (by
          unfold
            nb090_alpha_dummy_700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0780
                    A)
                  1)))) (show h ≠ (nb090_alpha_dummy_702 v u h) from (by
          unfold
            nb090_alpha_dummy_702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0782
                    v u h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_699 A) from (by
          unfold
            nb090_alpha_dummy_699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0780
                    A)
                  0)))) (show h ≠ (nb090_alpha_dummy_701 v u h) from (by
          unfold
            nb090_alpha_dummy_701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0782
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_775 A) from (by
          unfold
            nb090_alpha_dummy_775;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0866
                    A)
                  0)))) (show h ≠ (nb090_alpha_dummy_776 v u h) from (by
          unfold
            nb090_alpha_dummy_776;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0867
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_703 A) from (by
          unfold
            nb090_alpha_dummy_703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0781
                    A)
                  0)))) (show h ≠ (nb090_alpha_dummy_704 v u h) from (by
          unfold
            nb090_alpha_dummy_704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0783
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_042 A) from (by
          unfold
            nb090_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0778
                    A)
                  1)))) (show h ≠ (nb090_alpha_dummy_044 v u h) from (by
          unfold
            nb090_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0779
                    v u h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_041 A) from (by
          unfold
            nb090_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0778
                    A)
                  0)))) (show h ≠ (nb090_alpha_dummy_043 v u h) from (by
          unfold
            nb090_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0779
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_779 A) ≠ (nb090_alpha_dummy_821 A) from (by
          unfold nb090_alpha_dummy_821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0874 A)
                  0)))) (show (nb090_alpha_dummy_780 v u h) ≠ (nb090_alpha_dummy_822 v u h) from
        (by
          unfold nb090_alpha_dummy_822;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0875 v u
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))))))
                            (nb090_split_alpha_0093 v u A h)))))))))))) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there (freshVar_injective
                  (((Class.cab (nb090_alpha_dummy_829 A) (Wff.classEq
                        (Class.cab (nb090_alpha_dummy_827 A)
                          (syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c1st)
                            (Class.cv (nb090_alpha_dummy_827 A))))
                        (syn_csn (Class.cv (nb090_alpha_dummy_829 A)))))).fv) (by decide))
                (freshVar_injective (((Class.cab (nb090_alpha_dummy_830 v) (Wff.classEq
                        (Class.cab (nb090_alpha_dummy_828 v) (syn_wbr (Class.cv v) (syn_c1st)
                            (Class.cv (nb090_alpha_dummy_828 v))))
                        (syn_csn (Class.cv (nb090_alpha_dummy_830 v)))))).fv) (by decide))
                (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.classMem (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                    (nb090_split_alpha_0094 v u A h dv_h_v)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_827 A) ≠ (nb090_alpha_dummy_836 A) from (by
          unfold nb090_alpha_dummy_836;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0916 A)
                  1)))) (show (nb090_alpha_dummy_828 v) ≠ (nb090_alpha_dummy_838 v) from (by
          unfold nb090_alpha_dummy_838;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0918 v)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_827 A) ≠
        (nb090_alpha_dummy_835 A) from (by
          unfold nb090_alpha_dummy_835;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0916 A)
                  0)))) (show (nb090_alpha_dummy_828 v) ≠ (nb090_alpha_dummy_837 v) from (by
          unfold nb090_alpha_dummy_837;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0918 v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_827 A) ≠
        (nb090_alpha_dummy_865 A) from (by
          unfold nb090_alpha_dummy_865;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0920
                    A)
                  0)))) (show (nb090_alpha_dummy_828 v) ≠ (nb090_alpha_dummy_866 v) from (by
          unfold nb090_alpha_dummy_866;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0921
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_827 A) ≠
        (nb090_alpha_dummy_839 A) from (by
          unfold nb090_alpha_dummy_839;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0917
                    A)
                  0)))) (show (nb090_alpha_dummy_828 v) ≠ (nb090_alpha_dummy_840 v) from (by
          unfold nb090_alpha_dummy_840;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0919
                    v)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_827 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_828 v))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0095 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_867 A), (nb090_alpha_dummy_868 v)), ((nb090_alpha_dummy_836 A),
        (nb090_alpha_dummy_838 v)), ((nb090_alpha_dummy_835 A), (nb090_alpha_dummy_837 v)),
        ((nb090_alpha_dummy_865 A), (nb090_alpha_dummy_866 v)), ((nb090_alpha_dummy_839 A),
        (nb090_alpha_dummy_840 v)), ((nb090_alpha_dummy_827 A), (nb090_alpha_dummy_828 v)),
        ((nb090_alpha_dummy_829 A), (nb090_alpha_dummy_830 v)), ((nb090_alpha_dummy_832 A),
        (nb090_alpha_dummy_834 v)), ((nb090_alpha_dummy_831 A), (nb090_alpha_dummy_833 v)),
        ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_827 A) ≠ (nb090_alpha_dummy_836 A) from (by
          unfold nb090_alpha_dummy_836;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0916 A)
                  1)))) (show (nb090_alpha_dummy_828 v) ≠ (nb090_alpha_dummy_838 v) from (by
          unfold nb090_alpha_dummy_838;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0918 v)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_827 A) ≠
        (nb090_alpha_dummy_835 A) from (by
          unfold nb090_alpha_dummy_835;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0916 A)
                  0)))) (show (nb090_alpha_dummy_828 v) ≠ (nb090_alpha_dummy_837 v) from (by
          unfold nb090_alpha_dummy_837;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0918 v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_827 A) ≠
        (nb090_alpha_dummy_865 A) from (by
          unfold nb090_alpha_dummy_865;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0920
                    A)
                  0)))) (show (nb090_alpha_dummy_828 v) ≠ (nb090_alpha_dummy_866 v) from (by
          unfold nb090_alpha_dummy_866;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0921
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_827 A) ≠
        (nb090_alpha_dummy_839 A) from (by
          unfold nb090_alpha_dummy_839;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0917
                    A)
                  0)))) (show (nb090_alpha_dummy_828 v) ≠ (nb090_alpha_dummy_840 v) from (by
          unfold nb090_alpha_dummy_840;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0919
                    v)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_827 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_828 v))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0095 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_867 A), (nb090_alpha_dummy_868 v)), ((nb090_alpha_dummy_836 A),
        (nb090_alpha_dummy_838 v)), ((nb090_alpha_dummy_835 A), (nb090_alpha_dummy_837 v)),
        ((nb090_alpha_dummy_865 A), (nb090_alpha_dummy_866 v)), ((nb090_alpha_dummy_839 A),
        (nb090_alpha_dummy_840 v)), ((nb090_alpha_dummy_827 A), (nb090_alpha_dummy_828 v)),
        ((nb090_alpha_dummy_829 A), (nb090_alpha_dummy_830 v)), ((nb090_alpha_dummy_832 A),
        (nb090_alpha_dummy_834 v)), ((nb090_alpha_dummy_831 A), (nb090_alpha_dummy_833 v)),
        ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.refl_of_reflOn
                        [((nb090_alpha_dummy_827 A), (nb090_alpha_dummy_828 v)),
                          ((nb090_alpha_dummy_829 A), (nb090_alpha_dummy_830 v)),
                          ((nb090_alpha_dummy_832 A), (nb090_alpha_dummy_834 v)),
                          ((nb090_alpha_dummy_831 A), (nb090_alpha_dummy_833 v)),
                          ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
                          ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                          ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                          ((nb090_alpha_dummy_001 A), u),
                          ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                        (syn_c1st) (nb090_wpp_refl_0327 v u A h)))) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_829 A) ≠ (nb090_alpha_dummy_871 A) from (by
                              unfold nb090_alpha_dummy_871;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0926 A) 0))))
                          (show (nb090_alpha_dummy_830 v) ≠ (nb090_alpha_dummy_872 v) from (by
                              unfold nb090_alpha_dummy_872;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0927 v) 0))))
                          (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classMem (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0084 v u A h)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.neg (nb090_split_alpha_0085 v u A h)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.neg (nb090_split_alpha_0085 v u A h))))))))))))
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                (freshVar_injective (((Class.cab (nb090_alpha_dummy_655 A) (Wff.classEq
                        (Class.cab (nb090_alpha_dummy_653 A)
                          (syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c1st)
                            (Class.cv (nb090_alpha_dummy_653 A))))
                        (syn_csn (Class.cv (nb090_alpha_dummy_655 A)))))).fv) (by decide))
                (freshVar_injective (((Class.cab (nb090_alpha_dummy_656 u) (Wff.classEq
                        (Class.cab (nb090_alpha_dummy_654 u) (syn_wbr (Class.cv u) (syn_c1st)
                            (Class.cv (nb090_alpha_dummy_654 u))))
                        (syn_csn (Class.cv (nb090_alpha_dummy_656 u)))))).fv) (by decide))
                (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.classMem (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                    (nb090_split_alpha_0086 v u A h dv_h_u dv_u_v)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_653 A) ≠ (nb090_alpha_dummy_662 A) from (by
          unfold nb090_alpha_dummy_662;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0716 A)
                  1)))) (show (nb090_alpha_dummy_654 u) ≠ (nb090_alpha_dummy_664 u) from (by
          unfold nb090_alpha_dummy_664;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0718 u)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_653 A) ≠
        (nb090_alpha_dummy_661 A) from (by
          unfold nb090_alpha_dummy_661;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0716 A)
                  0)))) (show (nb090_alpha_dummy_654 u) ≠ (nb090_alpha_dummy_663 u) from (by
          unfold nb090_alpha_dummy_663;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0718 u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_653 A) ≠
        (nb090_alpha_dummy_691 A) from (by
          unfold nb090_alpha_dummy_691;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0720
                    A)
                  0)))) (show (nb090_alpha_dummy_654 u) ≠ (nb090_alpha_dummy_692 u) from (by
          unfold nb090_alpha_dummy_692;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0721
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_653 A) ≠
        (nb090_alpha_dummy_665 A) from (by
          unfold nb090_alpha_dummy_665;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0717
                    A)
                  0)))) (show (nb090_alpha_dummy_654 u) ≠ (nb090_alpha_dummy_666 u) from (by
          unfold nb090_alpha_dummy_666;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0719
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_653 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_654 u))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0087 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_693 A), (nb090_alpha_dummy_694 u)), ((nb090_alpha_dummy_662 A),
        (nb090_alpha_dummy_664 u)), ((nb090_alpha_dummy_661 A), (nb090_alpha_dummy_663 u)),
        ((nb090_alpha_dummy_691 A), (nb090_alpha_dummy_692 u)), ((nb090_alpha_dummy_665 A),
        (nb090_alpha_dummy_666 u)), ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)),
        ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)), ((nb090_alpha_dummy_658 A),
        (nb090_alpha_dummy_660 u)), ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)),
        ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_653 A) ≠ (nb090_alpha_dummy_662 A) from (by
          unfold nb090_alpha_dummy_662;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0716 A)
                  1)))) (show (nb090_alpha_dummy_654 u) ≠ (nb090_alpha_dummy_664 u) from (by
          unfold nb090_alpha_dummy_664;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0718 u)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_653 A) ≠
        (nb090_alpha_dummy_661 A) from (by
          unfold nb090_alpha_dummy_661;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0716 A)
                  0)))) (show (nb090_alpha_dummy_654 u) ≠ (nb090_alpha_dummy_663 u) from (by
          unfold nb090_alpha_dummy_663;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0718 u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_653 A) ≠
        (nb090_alpha_dummy_691 A) from (by
          unfold nb090_alpha_dummy_691;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0720
                    A)
                  0)))) (show (nb090_alpha_dummy_654 u) ≠ (nb090_alpha_dummy_692 u) from (by
          unfold nb090_alpha_dummy_692;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0721
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_653 A) ≠
        (nb090_alpha_dummy_665 A) from (by
          unfold nb090_alpha_dummy_665;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0717
                    A)
                  0)))) (show (nb090_alpha_dummy_654 u) ≠ (nb090_alpha_dummy_666 u) from (by
          unfold nb090_alpha_dummy_666;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0719
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_653 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_654 u))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0087 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_693 A), (nb090_alpha_dummy_694 u)), ((nb090_alpha_dummy_662 A),
        (nb090_alpha_dummy_664 u)), ((nb090_alpha_dummy_661 A), (nb090_alpha_dummy_663 u)),
        ((nb090_alpha_dummy_691 A), (nb090_alpha_dummy_692 u)), ((nb090_alpha_dummy_665 A),
        (nb090_alpha_dummy_666 u)), ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)),
        ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)), ((nb090_alpha_dummy_658 A),
        (nb090_alpha_dummy_660 u)), ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)),
        ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.refl_of_reflOn
                        [((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)),
                          ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)),
                          ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)),
                          ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)),
                          ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
                          ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                          ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                          ((nb090_alpha_dummy_001 A), u),
                          ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                        (syn_c1st) (nb090_wpp_refl_0298 v u A h)))) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_655 A) ≠ (nb090_alpha_dummy_697 A) from (by
                              unfold nb090_alpha_dummy_697;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0726 A) 0))))
                          (show (nb090_alpha_dummy_656 u) ≠ (nb090_alpha_dummy_698 u) from (by
                              unfold nb090_alpha_dummy_698;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0727 u) 0))))
                          (TAlphaVar.here _ _ _)))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
