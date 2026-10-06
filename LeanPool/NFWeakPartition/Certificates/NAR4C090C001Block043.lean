/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block042

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part117`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0094`. -/
@[expose]
noncomputable def nb090SplitAlpha0094 (v : Var) (u : Var) (A : Class) (h : Var)
    (dv_h_v : h ≠ v) :
    TAlphaWff
      [((nb090AlphaDummy841 A), (nb090AlphaDummy842 v)),
        ((nb090AlphaDummy839 A), (nb090AlphaDummy840 v)),
        ((nb090AlphaDummy827 A), (nb090AlphaDummy828 v)),
        ((nb090AlphaDummy829 A), (nb090AlphaDummy830 v)),
        ((nb090AlphaDummy832 A), (nb090AlphaDummy834 v)),
        ((nb090AlphaDummy831 A), (nb090AlphaDummy833 v)),
        ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy841 A))
          (Class.cab (nb090AlphaDummy835 A)
            (synWrex (nb090AlphaDummy836 A) (Class.cv (nb090AlphaDummy002 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy835 A))
                (synCphi (Class.cv (nb090AlphaDummy836 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy841 A))
            (Class.cab (nb090AlphaDummy835 A)
              (synWrex (nb090AlphaDummy836 A) (Class.cv (nb090AlphaDummy002 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy835 A))
                  (synCphi (Class.cv (nb090AlphaDummy836 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy842 v))
          (Class.cab (nb090AlphaDummy837 v) (synWrex (nb090AlphaDummy838 v) (Class.cv v)
              (Wff.classEq (Class.cv (nb090AlphaDummy837 v))
                (synCphi (Class.cv (nb090AlphaDummy838 v))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy842 v))
            (Class.cab (nb090AlphaDummy837 v)
              (synWrex (nb090AlphaDummy838 v) (Class.cv v)
                (Wff.classEq (Class.cv (nb090AlphaDummy837 v))
                  (synCphi (Class.cv (nb090AlphaDummy838 v))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy836 A) from (by
                      unfold nb090AlphaDummy836;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0888 A) 1))))
                  (show v ≠ (nb090AlphaDummy838 v) from (by
                      unfold nb090AlphaDummy838;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0890 v) 1))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy835 A) from (by
                        unfold nb090AlphaDummy835;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0888 A) 0))))
                    (show v ≠ (nb090AlphaDummy837 v) from (by
                        unfold nb090AlphaDummy837;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0890 v) 0)))) (TAlphaVar.there
                      (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy841 A) from (by
                          unfold nb090AlphaDummy841;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0892 A) 0))))
                      (show v ≠ (nb090AlphaDummy842 v) from (by
                          unfold nb090AlphaDummy842;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0893 v) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy839 A) from (by
                            unfold nb090AlphaDummy839;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0889 A) 0))))
                        (show v ≠ (nb090AlphaDummy840 v) from (by
                            unfold nb090AlphaDummy840;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0891 v) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy827 A) from (by
                              unfold nb090AlphaDummy827;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0882 A) 0))))
                          (show v ≠ (nb090AlphaDummy828 v) from (by
                              unfold nb090AlphaDummy828;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0885 v) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy829 A) from (by
                                unfold nb090AlphaDummy829;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0883 A) 0))))
                            (show v ≠ (nb090AlphaDummy830 v) from (by
                                unfold nb090AlphaDummy830;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0886 v) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy832 A) from
                                (by
                                  unfold nb090AlphaDummy832;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0884 A) 1))))
                              (show v ≠ (nb090AlphaDummy834 v) from (by
                                  unfold nb090AlphaDummy834;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0887 v) 1))))
                              (TAlphaVar.there (show
                                  (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy831 A) from (by
                                    unfold nb090AlphaDummy831;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0884 A)
                                            0)))) (show v ≠ (nb090AlphaDummy833 v) from (by
                                    unfold nb090AlphaDummy833;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0887 v)
                                            0)))) (TAlphaVar.there (show
                                    (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy042 A) from
                                    (by
                                      unfold nb090AlphaDummy042;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0880 A)
                                              1)))) (show v ≠ (nb090AlphaDummy044 v u h) from
                                    (by
                                      unfold nb090AlphaDummy044;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb090_support_mem_0881 v u h) 1))))
                                  (TAlphaVar.there (show (nb090AlphaDummy002 A) ≠
                                        (nb090AlphaDummy041 A) from (by
                                        unfold nb090AlphaDummy041;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0880 A)
                                                0))))
                                    (show v ≠ (nb090AlphaDummy043 v u h) from (by
                                        unfold nb090AlphaDummy043;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0881 v u h) 0))))
                                    (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                                      (Ne.symm dv_h_v) (TAlphaVar.here _ _ _))))))))))))))
            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090AlphaDummy002 A))).fv ∪
                      ((Class.cv (nb090AlphaDummy827 A))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv v)).fv ∪ ((Class.cv (nb090AlphaDummy828 v))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy836 A) ≠ (nb090AlphaDummy843 A) from (by
                              unfold nb090AlphaDummy843;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0894 A) 0))))
                          (show (nb090AlphaDummy838 v) ≠ (nb090AlphaDummy845 v) from (by
                              unfold nb090AlphaDummy845;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0895 v) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy836 A) ≠ (nb090AlphaDummy844 A) from (by
                                unfold nb090AlphaDummy844;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0894 A) 1))))
                            (show (nb090AlphaDummy838 v) ≠ (nb090AlphaDummy846 v) from (by
                                unfold nb090AlphaDummy846;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0895 v) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090AlphaDummy836 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090AlphaDummy838 v))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy843 A) ≠ (nb090AlphaDummy850 A) from (by
          unfold nb090AlphaDummy850;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0898 A) 1)))) (show (nb090AlphaDummy845 v) ≠
        (nb090AlphaDummy853 v) from (by
          unfold nb090AlphaDummy853;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0899 v) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy843 A) ≠ (nb090AlphaDummy849 A) from (by
          unfold nb090AlphaDummy849;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0898 A) 0)))) (show (nb090AlphaDummy845 v) ≠
        (nb090AlphaDummy852 v) from (by
          unfold nb090AlphaDummy852;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0899 v) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy843 A) ≠ (nb090AlphaDummy847 A) from (by
          unfold nb090AlphaDummy847;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0896 A)
                  0)))) (show (nb090AlphaDummy845 v) ≠ (nb090AlphaDummy848 v) from (by
          unfold nb090AlphaDummy848;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0897 v)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy851 A), (nb090AlphaDummy854 v)), ((nb090AlphaDummy850 A),
        (nb090AlphaDummy853 v)), ((nb090AlphaDummy849 A), (nb090AlphaDummy852 v)),
        ((nb090AlphaDummy847 A), (nb090AlphaDummy848 v)), ((nb090AlphaDummy843 A),
        (nb090AlphaDummy845 v)), ((nb090AlphaDummy844 A), (nb090AlphaDummy846 v)),
        ((nb090AlphaDummy836 A), (nb090AlphaDummy838 v)), ((nb090AlphaDummy835 A),
        (nb090AlphaDummy837 v)), ((nb090AlphaDummy841 A), (nb090AlphaDummy842 v)),
        ((nb090AlphaDummy839 A), (nb090AlphaDummy840 v)), ((nb090AlphaDummy827 A),
        (nb090AlphaDummy828 v)), ((nb090AlphaDummy829 A), (nb090AlphaDummy830 v)),
        ((nb090AlphaDummy832 A), (nb090AlphaDummy834 v)), ((nb090AlphaDummy831 A),
        (nb090AlphaDummy833 v)), ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy850
        A) ≠ (nb090AlphaDummy857 A) from (by
          unfold
            nb090AlphaDummy857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0902
                    A)
                  0)))) (show (nb090AlphaDummy853 v) ≠ (nb090AlphaDummy858 v) from (by
          unfold
            nb090AlphaDummy858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0903
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy850 A) ≠
        (nb090AlphaDummy855 A) from (by
          unfold
            nb090AlphaDummy855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0900
                    A)
                  0)))) (show (nb090AlphaDummy853 v) ≠ (nb090AlphaDummy856 v) from (by
          unfold
            nb090AlphaDummy856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0901
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy843
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy851 A) ≠ (nb090AlphaDummy857 A) from (by
          unfold
            nb090AlphaDummy857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0906
                    A)
                  0)))) (show (nb090AlphaDummy854 v) ≠ (nb090AlphaDummy858 v) from (by
          unfold
            nb090AlphaDummy858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0907
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy851 A) ≠
        (nb090AlphaDummy855 A) from (by
          unfold
            nb090AlphaDummy855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0904
                    A)
                  0)))) (show (nb090AlphaDummy854 v) ≠ (nb090AlphaDummy856 v) from (by
          unfold
            nb090AlphaDummy856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0905
                    v)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy850 A) ≠ (nb090AlphaDummy857 A) from (by
          unfold
            nb090AlphaDummy857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0902
                    A)
                  0)))) (show (nb090AlphaDummy853 v) ≠ (nb090AlphaDummy858 v) from (by
          unfold
            nb090AlphaDummy858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0903
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy850 A) ≠
        (nb090AlphaDummy855 A) from (by
          unfold
            nb090AlphaDummy855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0900
                    A)
                  0)))) (show (nb090AlphaDummy853 v) ≠ (nb090AlphaDummy856 v) from (by
          unfold
            nb090AlphaDummy856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0901
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy843
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy851 A) ≠ (nb090AlphaDummy857 A) from (by
          unfold
            nb090AlphaDummy857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0906
                    A)
                  0)))) (show (nb090AlphaDummy854 v) ≠ (nb090AlphaDummy858 v) from (by
          unfold
            nb090AlphaDummy858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0907
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy851 A) ≠
        (nb090AlphaDummy855 A) from (by
          unfold
            nb090AlphaDummy855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0904
                    A)
                  0)))) (show (nb090AlphaDummy854 v) ≠ (nb090AlphaDummy856 v) from (by
          unfold
            nb090AlphaDummy856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0905
                    v)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy851 A), (nb090AlphaDummy854 v)), ((nb090AlphaDummy850 A),
        (nb090AlphaDummy853 v)), ((nb090AlphaDummy849 A), (nb090AlphaDummy852 v)),
        ((nb090AlphaDummy847 A), (nb090AlphaDummy848 v)), ((nb090AlphaDummy843 A),
        (nb090AlphaDummy845 v)), ((nb090AlphaDummy844 A), (nb090AlphaDummy846 v)),
        ((nb090AlphaDummy836 A), (nb090AlphaDummy838 v)), ((nb090AlphaDummy835 A),
        (nb090AlphaDummy837 v)), ((nb090AlphaDummy841 A), (nb090AlphaDummy842 v)),
        ((nb090AlphaDummy839 A), (nb090AlphaDummy840 v)), ((nb090AlphaDummy827 A),
        (nb090AlphaDummy828 v)), ((nb090AlphaDummy829 A), (nb090AlphaDummy830 v)),
        ((nb090AlphaDummy832 A), (nb090AlphaDummy834 v)), ((nb090AlphaDummy831 A),
        (nb090AlphaDummy833 v)), ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy843 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy843 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy845
        v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy850 A) ≠ (nb090AlphaDummy861 A) from (by
          unfold
            nb090AlphaDummy861;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0910
                    A)
                  0)))) (show (nb090AlphaDummy853 v) ≠ (nb090AlphaDummy862 v) from (by
          unfold
            nb090AlphaDummy862;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0911
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy850 A) ≠
        (nb090AlphaDummy859 A) from (by
          unfold
            nb090AlphaDummy859;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0908
                    A)
                  0)))) (show (nb090AlphaDummy853 v) ≠ (nb090AlphaDummy860 v) from (by
          unfold
            nb090AlphaDummy860;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0909
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy843
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy850 A) ≠ (nb090AlphaDummy861 A) from (by
          unfold
            nb090AlphaDummy861;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0910
                    A)
                  0)))) (show (nb090AlphaDummy853 v) ≠ (nb090AlphaDummy862 v) from (by
          unfold
            nb090AlphaDummy862;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0911
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy850 A) ≠
        (nb090AlphaDummy859 A) from (by
          unfold
            nb090AlphaDummy859;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0908
                    A)
                  0)))) (show (nb090AlphaDummy853 v) ≠ (nb090AlphaDummy860 v) from (by
          unfold
            nb090AlphaDummy860;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0909
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy843
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy851
        A) ≠ (nb090AlphaDummy863 A) from (by
          unfold
            nb090AlphaDummy863;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0914
                    A)
                  0)))) (show (nb090AlphaDummy854 v) ≠ (nb090AlphaDummy864 v) from (by
          unfold
            nb090AlphaDummy864;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0915
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy851 A) ≠
        (nb090AlphaDummy859 A) from (by
          unfold
            nb090AlphaDummy859;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0912
                    A)
                  0)))) (show (nb090AlphaDummy854 v) ≠ (nb090AlphaDummy860 v) from (by
          unfold
            nb090AlphaDummy860;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0913
                    v)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy851
        A) ≠ (nb090AlphaDummy863 A) from (by
          unfold
            nb090AlphaDummy863;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0914
                    A)
                  0)))) (show (nb090AlphaDummy854 v) ≠ (nb090AlphaDummy864 v) from (by
          unfold
            nb090AlphaDummy864;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0915
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy851 A) ≠
        (nb090AlphaDummy859 A) from (by
          unfold
            nb090AlphaDummy859;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0912
                    A)
                  0)))) (show (nb090AlphaDummy854 v) ≠ (nb090AlphaDummy860 v) from (by
          unfold
            nb090AlphaDummy860;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0913
                    v)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy843 A) ≠ (nb090AlphaDummy847 A) from
                                      (by
                                        unfold nb090AlphaDummy847;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0896 A)
                                                0)))) (show (nb090AlphaDummy845 v) ≠
                                        (nb090AlphaDummy848 v) from (by
                                        unfold nb090AlphaDummy848;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0897 v)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy847 A), (nb090AlphaDummy848 v)),
                                    ((nb090AlphaDummy843 A), (nb090AlphaDummy845 v)),
                                    ((nb090AlphaDummy844 A), (nb090AlphaDummy846 v)),
                                    ((nb090AlphaDummy836 A), (nb090AlphaDummy838 v)),
                                    ((nb090AlphaDummy835 A), (nb090AlphaDummy837 v)),
                                    ((nb090AlphaDummy841 A), (nb090AlphaDummy842 v)),
                                    ((nb090AlphaDummy839 A), (nb090AlphaDummy840 v)),
                                    ((nb090AlphaDummy827 A), (nb090AlphaDummy828 v)),
                                    ((nb090AlphaDummy829 A), (nb090AlphaDummy830 v)),
                                    ((nb090AlphaDummy832 A), (nb090AlphaDummy834 v)),
                                    ((nb090AlphaDummy831 A), (nb090AlphaDummy833 v)),
                                    ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
                                    ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy843 A) ≠ (nb090AlphaDummy847 A) from
                                    (by
                                      unfold nb090AlphaDummy847;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0896 A)
                                              0)))) (show
                                    (nb090AlphaDummy845 v) ≠ (nb090AlphaDummy848 v) from
                                    (by
                                      unfold nb090AlphaDummy848;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0897 v)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy843 A) ≠ (nb090AlphaDummy847 A) from
                                      (by
                                        unfold nb090AlphaDummy847;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0896 A)
                                                0)))) (show (nb090AlphaDummy845 v) ≠
                                        (nb090AlphaDummy848 v) from (by
                                        unfold nb090AlphaDummy848;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0897 v)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy847 A), (nb090AlphaDummy848 v)),
                                    ((nb090AlphaDummy843 A), (nb090AlphaDummy845 v)),
                                    ((nb090AlphaDummy844 A), (nb090AlphaDummy846 v)),
                                    ((nb090AlphaDummy836 A), (nb090AlphaDummy838 v)),
                                    ((nb090AlphaDummy835 A), (nb090AlphaDummy837 v)),
                                    ((nb090AlphaDummy841 A), (nb090AlphaDummy842 v)),
                                    ((nb090AlphaDummy839 A), (nb090AlphaDummy840 v)),
                                    ((nb090AlphaDummy827 A), (nb090AlphaDummy828 v)),
                                    ((nb090AlphaDummy829 A), (nb090AlphaDummy830 v)),
                                    ((nb090AlphaDummy832 A), (nb090AlphaDummy834 v)),
                                    ((nb090AlphaDummy831 A), (nb090AlphaDummy833 v)),
                                    ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
                                    ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy836 A) from (by
                        unfold nb090AlphaDummy836;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0888 A) 1))))
                    (show v ≠ (nb090AlphaDummy838 v) from (by
                        unfold nb090AlphaDummy838;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0890 v) 1)))) (TAlphaVar.there
                      (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy835 A) from (by
                          unfold nb090AlphaDummy835;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0888 A) 0))))
                      (show v ≠ (nb090AlphaDummy837 v) from (by
                          unfold nb090AlphaDummy837;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0890 v) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy841 A) from (by
                            unfold nb090AlphaDummy841;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0892 A) 0))))
                        (show v ≠ (nb090AlphaDummy842 v) from (by
                            unfold nb090AlphaDummy842;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0893 v) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy839 A) from (by
                              unfold nb090AlphaDummy839;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0889 A) 0))))
                          (show v ≠ (nb090AlphaDummy840 v) from (by
                              unfold nb090AlphaDummy840;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0891 v) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy827 A) from (by
                                unfold nb090AlphaDummy827;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0882 A) 0))))
                            (show v ≠ (nb090AlphaDummy828 v) from (by
                                unfold nb090AlphaDummy828;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0885 v) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy829 A) from
                                (by
                                  unfold nb090AlphaDummy829;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0883 A) 0))))
                              (show v ≠ (nb090AlphaDummy830 v) from (by
                                  unfold nb090AlphaDummy830;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0886 v) 0))))
                              (TAlphaVar.there (show
                                  (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy832 A) from (by
                                    unfold nb090AlphaDummy832;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0884 A)
                                            1)))) (show v ≠ (nb090AlphaDummy834 v) from (by
                                    unfold nb090AlphaDummy834;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0887 v)
                                            1)))) (TAlphaVar.there (show
                                    (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy831 A) from
                                    (by
                                      unfold nb090AlphaDummy831;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0884 A)
                                              0)))) (show v ≠ (nb090AlphaDummy833 v) from (by
                                      unfold nb090AlphaDummy833;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0887 v)
                                              0)))) (TAlphaVar.there (show
                                      (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy042 A) from
                                      (by
                                        unfold nb090AlphaDummy042;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0880 A)
                                                1))))
                                    (show v ≠ (nb090AlphaDummy044 v u h) from (by
                                        unfold nb090AlphaDummy044;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0881 v u h) 1))))
                                    (TAlphaVar.there (show (nb090AlphaDummy002 A) ≠
        (nb090AlphaDummy041 A) from (by
                                          unfold nb090AlphaDummy041;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0880 A) 0))))
                                      (show v ≠ (nb090AlphaDummy043 v u h) from (by
                                          unfold nb090AlphaDummy043;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0881 v u h) 0))))
                                      (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                                        (Ne.symm dv_h_v) (TAlphaVar.here _ _ _))))))))))))))
              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090AlphaDummy002 A))).fv ∪
                        ((Class.cv (nb090AlphaDummy827 A))).fv) (by decide))
                    (freshVar_injective
                      (((Class.cv v)).fv ∪ ((Class.cv (nb090AlphaDummy828 v))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy836 A) ≠ (nb090AlphaDummy843 A) from (by
                                unfold nb090AlphaDummy843;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0894 A) 0))))
                            (show (nb090AlphaDummy838 v) ≠ (nb090AlphaDummy845 v) from (by
                                unfold nb090AlphaDummy845;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0895 v) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy836 A) ≠ (nb090AlphaDummy844 A) from
                                (by
                                  unfold nb090AlphaDummy844;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0894 A) 1))))
                              (show (nb090AlphaDummy838 v) ≠ (nb090AlphaDummy846 v) from
                                (by
                                  unfold nb090AlphaDummy846;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0895 v) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090AlphaDummy836 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090AlphaDummy838 v))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy843 A) ≠ (nb090AlphaDummy850 A) from (by
          unfold nb090AlphaDummy850;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0898 A) 1)))) (show (nb090AlphaDummy845 v) ≠
        (nb090AlphaDummy853 v) from (by
          unfold nb090AlphaDummy853;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0899 v) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy843 A) ≠ (nb090AlphaDummy849 A) from (by
          unfold nb090AlphaDummy849;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0898 A)
                  0)))) (show (nb090AlphaDummy845 v) ≠ (nb090AlphaDummy852 v) from (by
          unfold nb090AlphaDummy852;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0899 v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy843 A) ≠
        (nb090AlphaDummy847 A) from (by
          unfold nb090AlphaDummy847;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0896 A)
                  0)))) (show (nb090AlphaDummy845 v) ≠ (nb090AlphaDummy848 v) from (by
          unfold nb090AlphaDummy848;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0897 v)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy851 A), (nb090AlphaDummy854 v)), ((nb090AlphaDummy850 A),
        (nb090AlphaDummy853 v)), ((nb090AlphaDummy849 A), (nb090AlphaDummy852 v)),
        ((nb090AlphaDummy847 A), (nb090AlphaDummy848 v)), ((nb090AlphaDummy843 A),
        (nb090AlphaDummy845 v)), ((nb090AlphaDummy844 A), (nb090AlphaDummy846 v)),
        ((nb090AlphaDummy836 A), (nb090AlphaDummy838 v)), ((nb090AlphaDummy835 A),
        (nb090AlphaDummy837 v)), ((nb090AlphaDummy841 A), (nb090AlphaDummy842 v)),
        ((nb090AlphaDummy839 A), (nb090AlphaDummy840 v)), ((nb090AlphaDummy827 A),
        (nb090AlphaDummy828 v)), ((nb090AlphaDummy829 A), (nb090AlphaDummy830 v)),
        ((nb090AlphaDummy832 A), (nb090AlphaDummy834 v)), ((nb090AlphaDummy831 A),
        (nb090AlphaDummy833 v)), ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy850
        A) ≠ (nb090AlphaDummy857 A) from (by
          unfold
            nb090AlphaDummy857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0902
                    A)
                  0)))) (show (nb090AlphaDummy853 v) ≠ (nb090AlphaDummy858 v) from (by
          unfold
            nb090AlphaDummy858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0903
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy850 A) ≠
        (nb090AlphaDummy855 A) from (by
          unfold
            nb090AlphaDummy855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0900
                    A)
                  0)))) (show (nb090AlphaDummy853 v) ≠ (nb090AlphaDummy856 v) from (by
          unfold
            nb090AlphaDummy856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0901
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy843
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy851 A) ≠ (nb090AlphaDummy857 A) from (by
          unfold
            nb090AlphaDummy857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0906
                    A)
                  0)))) (show (nb090AlphaDummy854 v) ≠ (nb090AlphaDummy858 v) from (by
          unfold
            nb090AlphaDummy858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0907
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy851 A) ≠
        (nb090AlphaDummy855 A) from (by
          unfold
            nb090AlphaDummy855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0904
                    A)
                  0)))) (show (nb090AlphaDummy854 v) ≠ (nb090AlphaDummy856 v) from (by
          unfold
            nb090AlphaDummy856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0905
                    v)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy850 A) ≠ (nb090AlphaDummy857 A) from (by
          unfold
            nb090AlphaDummy857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0902
                    A)
                  0)))) (show (nb090AlphaDummy853 v) ≠ (nb090AlphaDummy858 v) from (by
          unfold
            nb090AlphaDummy858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0903
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy850 A) ≠
        (nb090AlphaDummy855 A) from (by
          unfold
            nb090AlphaDummy855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0900
                    A)
                  0)))) (show (nb090AlphaDummy853 v) ≠ (nb090AlphaDummy856 v) from (by
          unfold
            nb090AlphaDummy856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0901
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy843
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy851 A) ≠ (nb090AlphaDummy857 A) from (by
          unfold
            nb090AlphaDummy857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0906
                    A)
                  0)))) (show (nb090AlphaDummy854 v) ≠ (nb090AlphaDummy858 v) from (by
          unfold
            nb090AlphaDummy858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0907
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy851 A) ≠
        (nb090AlphaDummy855 A) from (by
          unfold
            nb090AlphaDummy855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0904
                    A)
                  0)))) (show (nb090AlphaDummy854 v) ≠ (nb090AlphaDummy856 v) from (by
          unfold
            nb090AlphaDummy856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0905
                    v)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy851 A), (nb090AlphaDummy854 v)), ((nb090AlphaDummy850 A),
        (nb090AlphaDummy853 v)), ((nb090AlphaDummy849 A), (nb090AlphaDummy852 v)),
        ((nb090AlphaDummy847 A), (nb090AlphaDummy848 v)), ((nb090AlphaDummy843 A),
        (nb090AlphaDummy845 v)), ((nb090AlphaDummy844 A), (nb090AlphaDummy846 v)),
        ((nb090AlphaDummy836 A), (nb090AlphaDummy838 v)), ((nb090AlphaDummy835 A),
        (nb090AlphaDummy837 v)), ((nb090AlphaDummy841 A), (nb090AlphaDummy842 v)),
        ((nb090AlphaDummy839 A), (nb090AlphaDummy840 v)), ((nb090AlphaDummy827 A),
        (nb090AlphaDummy828 v)), ((nb090AlphaDummy829 A), (nb090AlphaDummy830 v)),
        ((nb090AlphaDummy832 A), (nb090AlphaDummy834 v)), ((nb090AlphaDummy831 A),
        (nb090AlphaDummy833 v)), ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy843 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy843 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy845
        v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy850 A) ≠ (nb090AlphaDummy861 A) from (by
          unfold
            nb090AlphaDummy861;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0910
                    A)
                  0)))) (show (nb090AlphaDummy853 v) ≠ (nb090AlphaDummy862 v) from (by
          unfold
            nb090AlphaDummy862;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0911
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy850 A) ≠
        (nb090AlphaDummy859 A) from (by
          unfold
            nb090AlphaDummy859;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0908
                    A)
                  0)))) (show (nb090AlphaDummy853 v) ≠ (nb090AlphaDummy860 v) from (by
          unfold
            nb090AlphaDummy860;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0909
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy843
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy850 A) ≠ (nb090AlphaDummy861 A) from (by
          unfold
            nb090AlphaDummy861;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0910
                    A)
                  0)))) (show (nb090AlphaDummy853 v) ≠ (nb090AlphaDummy862 v) from (by
          unfold
            nb090AlphaDummy862;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0911
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy850 A) ≠
        (nb090AlphaDummy859 A) from (by
          unfold
            nb090AlphaDummy859;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0908
                    A)
                  0)))) (show (nb090AlphaDummy853 v) ≠ (nb090AlphaDummy860 v) from (by
          unfold
            nb090AlphaDummy860;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0909
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy843
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy851
        A) ≠ (nb090AlphaDummy863 A) from (by
          unfold
            nb090AlphaDummy863;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0914
                    A)
                  0)))) (show (nb090AlphaDummy854 v) ≠ (nb090AlphaDummy864 v) from (by
          unfold
            nb090AlphaDummy864;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0915
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy851 A) ≠
        (nb090AlphaDummy859 A) from (by
          unfold
            nb090AlphaDummy859;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0912
                    A)
                  0)))) (show (nb090AlphaDummy854 v) ≠ (nb090AlphaDummy860 v) from (by
          unfold
            nb090AlphaDummy860;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0913
                    v)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy851
        A) ≠ (nb090AlphaDummy863 A) from (by
          unfold
            nb090AlphaDummy863;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0914
                    A)
                  0)))) (show (nb090AlphaDummy854 v) ≠ (nb090AlphaDummy864 v) from (by
          unfold
            nb090AlphaDummy864;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0915
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy851 A) ≠
        (nb090AlphaDummy859 A) from (by
          unfold
            nb090AlphaDummy859;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0912
                    A)
                  0)))) (show (nb090AlphaDummy854 v) ≠ (nb090AlphaDummy860 v) from (by
          unfold
            nb090AlphaDummy860;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0913
                    v)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy843 A) ≠ (nb090AlphaDummy847 A)
                                        from (by
                                          unfold nb090AlphaDummy847;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0896 A) 0)))) (show
                                        (nb090AlphaDummy845 v) ≠ (nb090AlphaDummy848 v)
                                        from (by
                                          unfold nb090AlphaDummy848;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0897 v) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy847 A), (nb090AlphaDummy848 v)),
                                      ((nb090AlphaDummy843 A), (nb090AlphaDummy845 v)),
                                      ((nb090AlphaDummy844 A), (nb090AlphaDummy846 v)),
                                      ((nb090AlphaDummy836 A), (nb090AlphaDummy838 v)),
                                      ((nb090AlphaDummy835 A), (nb090AlphaDummy837 v)),
                                      ((nb090AlphaDummy841 A), (nb090AlphaDummy842 v)),
                                      ((nb090AlphaDummy839 A), (nb090AlphaDummy840 v)),
                                      ((nb090AlphaDummy827 A), (nb090AlphaDummy828 v)),
                                      ((nb090AlphaDummy829 A), (nb090AlphaDummy830 v)),
                                      ((nb090AlphaDummy832 A), (nb090AlphaDummy834 v)),
                                      ((nb090AlphaDummy831 A), (nb090AlphaDummy833 v)),
                                      ((nb090AlphaDummy042 A),
                                        (nb090AlphaDummy044 v u h)),
                                      ((nb090AlphaDummy041 A),
                                        (nb090AlphaDummy043 v u h)),
                                      ((nb090AlphaDummy000 A), h),
                                      ((nb090AlphaDummy002 A), v),
                                      ((nb090AlphaDummy001 A), u),
                                      ((nb090AlphaDummy003 A),
                                        (nb090AlphaDummy004 v u A h))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy843 A) ≠ (nb090AlphaDummy847 A) from
                                      (by
                                        unfold nb090AlphaDummy847;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0896 A)
                                                0)))) (show (nb090AlphaDummy845 v) ≠
                                        (nb090AlphaDummy848 v) from (by
                                        unfold nb090AlphaDummy848;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0897 v)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy843 A) ≠ (nb090AlphaDummy847 A)
                                        from (by
                                          unfold nb090AlphaDummy847;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0896 A) 0)))) (show
                                        (nb090AlphaDummy845 v) ≠ (nb090AlphaDummy848 v)
                                        from (by
                                          unfold nb090AlphaDummy848;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0897 v) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy847 A), (nb090AlphaDummy848 v)),
                                      ((nb090AlphaDummy843 A), (nb090AlphaDummy845 v)),
                                      ((nb090AlphaDummy844 A), (nb090AlphaDummy846 v)),
                                      ((nb090AlphaDummy836 A), (nb090AlphaDummy838 v)),
                                      ((nb090AlphaDummy835 A), (nb090AlphaDummy837 v)),
                                      ((nb090AlphaDummy841 A), (nb090AlphaDummy842 v)),
                                      ((nb090AlphaDummy839 A), (nb090AlphaDummy840 v)),
                                      ((nb090AlphaDummy827 A), (nb090AlphaDummy828 v)),
                                      ((nb090AlphaDummy829 A), (nb090AlphaDummy830 v)),
                                      ((nb090AlphaDummy832 A), (nb090AlphaDummy834 v)),
                                      ((nb090AlphaDummy831 A), (nb090AlphaDummy833 v)),
                                      ((nb090AlphaDummy042 A),
                                        (nb090AlphaDummy044 v u h)),
                                      ((nb090AlphaDummy041 A),
                                        (nb090AlphaDummy043 v u h)),
                                      ((nb090AlphaDummy000 A), h),
                                      ((nb090AlphaDummy002 A), v),
                                      ((nb090AlphaDummy001 A), u),
                                      ((nb090AlphaDummy003 A),
                                        (nb090AlphaDummy004 v u A h))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part118`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0095`. -/
@[expose]
noncomputable def nb090SplitAlpha0095 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy869 A), (nb090AlphaDummy870 v)),
        ((nb090AlphaDummy867 A), (nb090AlphaDummy868 v)),
        ((nb090AlphaDummy836 A), (nb090AlphaDummy838 v)),
        ((nb090AlphaDummy835 A), (nb090AlphaDummy837 v)),
        ((nb090AlphaDummy865 A), (nb090AlphaDummy866 v)),
        ((nb090AlphaDummy839 A), (nb090AlphaDummy840 v)),
        ((nb090AlphaDummy827 A), (nb090AlphaDummy828 v)),
        ((nb090AlphaDummy829 A), (nb090AlphaDummy830 v)),
        ((nb090AlphaDummy832 A), (nb090AlphaDummy834 v)),
        ((nb090AlphaDummy831 A), (nb090AlphaDummy833 v)),
        ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy869 A))
          (synCphi (Class.cv (nb090AlphaDummy836 A)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy869 A))
            (synCphi (Class.cv (nb090AlphaDummy836 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy870 v))
          (synCphi (Class.cv (nb090AlphaDummy838 v)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy870 v))
            (synCphi (Class.cv (nb090AlphaDummy838 v)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy836 A) ≠ (nb090AlphaDummy843 A) from (by
                      unfold nb090AlphaDummy843;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0894 A) 0))))
                  (show (nb090AlphaDummy838 v) ≠ (nb090AlphaDummy845 v) from (by
                      unfold nb090AlphaDummy845;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0895 v) 0))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy836 A) ≠ (nb090AlphaDummy844 A) from (by
                        unfold nb090AlphaDummy844;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0894 A) 1))))
                    (show (nb090AlphaDummy838 v) ≠ (nb090AlphaDummy846 v) from (by
                        unfold nb090AlphaDummy846;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0895 v) 1)))) (TAlphaVar.there
                      (show (nb090AlphaDummy836 A) ≠ (nb090AlphaDummy869 A) from (by
                          unfold nb090AlphaDummy869;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0924 A) 0))))
                      (show (nb090AlphaDummy838 v) ≠ (nb090AlphaDummy870 v) from (by
                          unfold nb090AlphaDummy870;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0925 v) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy836 A) ≠ (nb090AlphaDummy867 A) from (by
                            unfold nb090AlphaDummy867;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0922 A) 0))))
                        (show (nb090AlphaDummy838 v) ≠ (nb090AlphaDummy868 v) from (by
                            unfold nb090AlphaDummy868;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0923 v) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy836 A))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy838 v))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy843 A) ≠ (nb090AlphaDummy850 A) from
                                      (by
                                        unfold nb090AlphaDummy850;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0898 A)
                                                1)))) (show (nb090AlphaDummy845 v) ≠
                                        (nb090AlphaDummy853 v) from (by
                                        unfold nb090AlphaDummy853;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0899 v)
                                                1)))) (TAlphaVar.there (show
                                        (nb090AlphaDummy843 A) ≠ (nb090AlphaDummy849 A)
                                        from (by
                                          unfold nb090AlphaDummy849;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0898 A) 0)))) (show
                                        (nb090AlphaDummy845 v) ≠ (nb090AlphaDummy852 v)
                                        from (by
                                          unfold nb090AlphaDummy852;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0899 v) 0))))
                                      (TAlphaVar.there (show (nb090AlphaDummy843 A) ≠
        (nb090AlphaDummy847 A) from (by
          unfold nb090AlphaDummy847;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0896 A) 0)))) (show (nb090AlphaDummy845 v) ≠
        (nb090AlphaDummy848 v) from (by
          unfold nb090AlphaDummy848;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0897 v) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb090AlphaDummy851 A),
        (nb090AlphaDummy854 v)), ((nb090AlphaDummy850 A), (nb090AlphaDummy853 v)),
                                        ((nb090AlphaDummy849 A), (nb090AlphaDummy852 v)),
                                        ((nb090AlphaDummy847 A), (nb090AlphaDummy848 v)),
                                        ((nb090AlphaDummy843 A), (nb090AlphaDummy845 v)),
                                        ((nb090AlphaDummy844 A), (nb090AlphaDummy846 v)),
                                        ((nb090AlphaDummy869 A), (nb090AlphaDummy870 v)),
                                        ((nb090AlphaDummy867 A), (nb090AlphaDummy868 v)),
                                        ((nb090AlphaDummy836 A), (nb090AlphaDummy838 v)),
                                        ((nb090AlphaDummy835 A), (nb090AlphaDummy837 v)),
                                        ((nb090AlphaDummy865 A), (nb090AlphaDummy866 v)),
                                        ((nb090AlphaDummy839 A), (nb090AlphaDummy840 v)),
                                        ((nb090AlphaDummy827 A), (nb090AlphaDummy828 v)),
                                        ((nb090AlphaDummy829 A), (nb090AlphaDummy830 v)),
                                        ((nb090AlphaDummy832 A), (nb090AlphaDummy834 v)),
                                        ((nb090AlphaDummy831 A), (nb090AlphaDummy833 v)),
                                        ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
                                        ((nb090AlphaDummy002 A), v),
                                        ((nb090AlphaDummy001 A), u),
                                        ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy850 A) ≠ (nb090AlphaDummy857 A) from (by
          unfold
            nb090AlphaDummy857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0902
                    A)
                  0)))) (show (nb090AlphaDummy853 v) ≠ (nb090AlphaDummy858 v) from (by
          unfold
            nb090AlphaDummy858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0903
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy850 A) ≠
        (nb090AlphaDummy855 A) from (by
          unfold
            nb090AlphaDummy855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0900
                    A)
                  0)))) (show (nb090AlphaDummy853 v) ≠ (nb090AlphaDummy856 v) from (by
          unfold
            nb090AlphaDummy856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0901
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy843
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy851 A) ≠
        (nb090AlphaDummy857 A) from (by
          unfold
            nb090AlphaDummy857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0906
                    A)
                  0)))) (show (nb090AlphaDummy854 v) ≠ (nb090AlphaDummy858 v) from (by
          unfold
            nb090AlphaDummy858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0907
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy851 A) ≠
        (nb090AlphaDummy855 A) from (by
          unfold
            nb090AlphaDummy855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0904
                    A)
                  0)))) (show (nb090AlphaDummy854 v) ≠ (nb090AlphaDummy856 v) from (by
          unfold
            nb090AlphaDummy856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0905
                    v)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy850 A) ≠ (nb090AlphaDummy857 A) from (by
          unfold
            nb090AlphaDummy857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0902
                    A)
                  0)))) (show (nb090AlphaDummy853 v) ≠ (nb090AlphaDummy858 v) from (by
          unfold
            nb090AlphaDummy858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0903
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy850 A) ≠
        (nb090AlphaDummy855 A) from (by
          unfold
            nb090AlphaDummy855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0900
                    A)
                  0)))) (show (nb090AlphaDummy853 v) ≠ (nb090AlphaDummy856 v) from (by
          unfold
            nb090AlphaDummy856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0901
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy843
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy851 A) ≠
        (nb090AlphaDummy857 A) from (by
          unfold
            nb090AlphaDummy857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0906
                    A)
                  0)))) (show (nb090AlphaDummy854 v) ≠ (nb090AlphaDummy858 v) from (by
          unfold
            nb090AlphaDummy858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0907
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy851 A) ≠
        (nb090AlphaDummy855 A) from (by
          unfold
            nb090AlphaDummy855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0904
                    A)
                  0)))) (show (nb090AlphaDummy854 v) ≠ (nb090AlphaDummy856 v) from (by
          unfold
            nb090AlphaDummy856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0905
                    v)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb090AlphaDummy851 A), (nb090AlphaDummy854 v)),
        ((nb090AlphaDummy850 A), (nb090AlphaDummy853 v)), ((nb090AlphaDummy849 A),
        (nb090AlphaDummy852 v)), ((nb090AlphaDummy847 A), (nb090AlphaDummy848 v)),
        ((nb090AlphaDummy843 A), (nb090AlphaDummy845 v)), ((nb090AlphaDummy844 A),
        (nb090AlphaDummy846 v)), ((nb090AlphaDummy869 A), (nb090AlphaDummy870 v)),
        ((nb090AlphaDummy867 A), (nb090AlphaDummy868 v)), ((nb090AlphaDummy836 A),
        (nb090AlphaDummy838 v)), ((nb090AlphaDummy835 A), (nb090AlphaDummy837 v)),
        ((nb090AlphaDummy865 A), (nb090AlphaDummy866 v)), ((nb090AlphaDummy839 A),
        (nb090AlphaDummy840 v)), ((nb090AlphaDummy827 A), (nb090AlphaDummy828 v)),
        ((nb090AlphaDummy829 A), (nb090AlphaDummy830 v)), ((nb090AlphaDummy832 A),
        (nb090AlphaDummy834 v)), ((nb090AlphaDummy831 A), (nb090AlphaDummy833 v)),
        ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                                        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy843 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy843 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy850 A) ≠ (nb090AlphaDummy861 A) from (by
          unfold
            nb090AlphaDummy861;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0910
                    A)
                  0)))) (show (nb090AlphaDummy853 v) ≠ (nb090AlphaDummy862 v) from (by
          unfold
            nb090AlphaDummy862;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0911
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy850 A) ≠
        (nb090AlphaDummy859 A) from (by
          unfold
            nb090AlphaDummy859;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0908
                    A)
                  0)))) (show (nb090AlphaDummy853 v) ≠ (nb090AlphaDummy860 v) from (by
          unfold
            nb090AlphaDummy860;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0909
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy843
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy850 A) ≠
        (nb090AlphaDummy861 A) from (by
          unfold
            nb090AlphaDummy861;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0910
                    A)
                  0)))) (show (nb090AlphaDummy853 v) ≠ (nb090AlphaDummy862 v) from (by
          unfold
            nb090AlphaDummy862;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0911
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy850 A) ≠
        (nb090AlphaDummy859 A) from (by
          unfold
            nb090AlphaDummy859;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0908
                    A)
                  0)))) (show (nb090AlphaDummy853 v) ≠ (nb090AlphaDummy860 v) from (by
          unfold
            nb090AlphaDummy860;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0909
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy843
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy851 A) ≠ (nb090AlphaDummy863 A) from (by
          unfold
            nb090AlphaDummy863;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0914
                    A)
                  0)))) (show (nb090AlphaDummy854 v) ≠ (nb090AlphaDummy864 v) from (by
          unfold
            nb090AlphaDummy864;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0915
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy851 A) ≠
        (nb090AlphaDummy859 A) from (by
          unfold
            nb090AlphaDummy859;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0912
                    A)
                  0)))) (show (nb090AlphaDummy854 v) ≠ (nb090AlphaDummy860 v) from (by
          unfold
            nb090AlphaDummy860;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0913
                    v)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy851 A) ≠ (nb090AlphaDummy863 A) from (by
          unfold
            nb090AlphaDummy863;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0914
                    A)
                  0)))) (show (nb090AlphaDummy854 v) ≠ (nb090AlphaDummy864 v) from (by
          unfold
            nb090AlphaDummy864;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0915
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy851 A) ≠
        (nb090AlphaDummy859 A) from (by
          unfold
            nb090AlphaDummy859;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0912
                    A)
                  0)))) (show (nb090AlphaDummy854 v) ≠ (nb090AlphaDummy860 v) from (by
          unfold
            nb090AlphaDummy860;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0913
                    v)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy843 A) ≠ (nb090AlphaDummy847 A) from (by
                                unfold nb090AlphaDummy847;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0896 A) 0))))
                            (show (nb090AlphaDummy845 v) ≠ (nb090AlphaDummy848 v) from (by
                                unfold nb090AlphaDummy848;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0897 v) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb090AlphaDummy847 A), (nb090AlphaDummy848 v)),
                            ((nb090AlphaDummy843 A), (nb090AlphaDummy845 v)),
                            ((nb090AlphaDummy844 A), (nb090AlphaDummy846 v)),
                            ((nb090AlphaDummy869 A), (nb090AlphaDummy870 v)),
                            ((nb090AlphaDummy867 A), (nb090AlphaDummy868 v)),
                            ((nb090AlphaDummy836 A), (nb090AlphaDummy838 v)),
                            ((nb090AlphaDummy835 A), (nb090AlphaDummy837 v)),
                            ((nb090AlphaDummy865 A), (nb090AlphaDummy866 v)),
                            ((nb090AlphaDummy839 A), (nb090AlphaDummy840 v)),
                            ((nb090AlphaDummy827 A), (nb090AlphaDummy828 v)),
                            ((nb090AlphaDummy829 A), (nb090AlphaDummy830 v)),
                            ((nb090AlphaDummy832 A), (nb090AlphaDummy834 v)),
                            ((nb090AlphaDummy831 A), (nb090AlphaDummy833 v)),
                            ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
                            ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                            ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                            ((nb090AlphaDummy001 A), u),
                            ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy843 A) ≠ (nb090AlphaDummy847 A) from (by
                              unfold nb090AlphaDummy847;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0896 A) 0))))
                          (show (nb090AlphaDummy845 v) ≠ (nb090AlphaDummy848 v) from (by
                              unfold nb090AlphaDummy848;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0897 v) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy843 A) ≠ (nb090AlphaDummy847 A) from (by
                                unfold nb090AlphaDummy847;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0896 A) 0))))
                            (show (nb090AlphaDummy845 v) ≠ (nb090AlphaDummy848 v) from (by
                                unfold nb090AlphaDummy848;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0897 v) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb090AlphaDummy847 A), (nb090AlphaDummy848 v)),
                            ((nb090AlphaDummy843 A), (nb090AlphaDummy845 v)),
                            ((nb090AlphaDummy844 A), (nb090AlphaDummy846 v)),
                            ((nb090AlphaDummy869 A), (nb090AlphaDummy870 v)),
                            ((nb090AlphaDummy867 A), (nb090AlphaDummy868 v)),
                            ((nb090AlphaDummy836 A), (nb090AlphaDummy838 v)),
                            ((nb090AlphaDummy835 A), (nb090AlphaDummy837 v)),
                            ((nb090AlphaDummy865 A), (nb090AlphaDummy866 v)),
                            ((nb090AlphaDummy839 A), (nb090AlphaDummy840 v)),
                            ((nb090AlphaDummy827 A), (nb090AlphaDummy828 v)),
                            ((nb090AlphaDummy829 A), (nb090AlphaDummy830 v)),
                            ((nb090AlphaDummy832 A), (nb090AlphaDummy834 v)),
                            ((nb090AlphaDummy831 A), (nb090AlphaDummy833 v)),
                            ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
                            ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                            ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                            ((nb090AlphaDummy001 A), u),
                            ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb090AlphaDummy836 A) ≠ (nb090AlphaDummy843 A) from (by
                        unfold nb090AlphaDummy843;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0894 A) 0))))
                    (show (nb090AlphaDummy838 v) ≠ (nb090AlphaDummy845 v) from (by
                        unfold nb090AlphaDummy845;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0895 v) 0)))) (TAlphaVar.there
                      (show (nb090AlphaDummy836 A) ≠ (nb090AlphaDummy844 A) from (by
                          unfold nb090AlphaDummy844;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0894 A) 1))))
                      (show (nb090AlphaDummy838 v) ≠ (nb090AlphaDummy846 v) from (by
                          unfold nb090AlphaDummy846;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0895 v) 1))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy836 A) ≠ (nb090AlphaDummy869 A) from (by
                            unfold nb090AlphaDummy869;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0924 A) 0))))
                        (show (nb090AlphaDummy838 v) ≠ (nb090AlphaDummy870 v) from (by
                            unfold nb090AlphaDummy870;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0925 v) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy836 A) ≠ (nb090AlphaDummy867 A) from (by
                              unfold nb090AlphaDummy867;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0922 A) 0))))
                          (show (nb090AlphaDummy838 v) ≠ (nb090AlphaDummy868 v) from (by
                              unfold nb090AlphaDummy868;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0923 v) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb090AlphaDummy836 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090AlphaDummy838 v))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb090AlphaDummy843 A) ≠
        (nb090AlphaDummy850 A) from (by
                                          unfold nb090AlphaDummy850;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0898 A) 1)))) (show
                                        (nb090AlphaDummy845 v) ≠ (nb090AlphaDummy853 v)
                                        from (by
                                          unfold nb090AlphaDummy853;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0899 v) 1))))
                                      (TAlphaVar.there (show (nb090AlphaDummy843 A) ≠
        (nb090AlphaDummy849 A) from (by
          unfold nb090AlphaDummy849;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0898 A) 0)))) (show (nb090AlphaDummy845 v) ≠
        (nb090AlphaDummy852 v) from (by
          unfold nb090AlphaDummy852;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0899 v) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy843 A) ≠ (nb090AlphaDummy847 A) from (by
          unfold nb090AlphaDummy847;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0896 A) 0)))) (show (nb090AlphaDummy845 v) ≠
        (nb090AlphaDummy848 v) from (by
          unfold nb090AlphaDummy848;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0897 v) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb090AlphaDummy851 A),
        (nb090AlphaDummy854 v)), ((nb090AlphaDummy850 A), (nb090AlphaDummy853 v)),
        ((nb090AlphaDummy849 A), (nb090AlphaDummy852 v)), ((nb090AlphaDummy847 A),
        (nb090AlphaDummy848 v)), ((nb090AlphaDummy843 A), (nb090AlphaDummy845 v)),
        ((nb090AlphaDummy844 A), (nb090AlphaDummy846 v)), ((nb090AlphaDummy869 A),
        (nb090AlphaDummy870 v)), ((nb090AlphaDummy867 A), (nb090AlphaDummy868 v)),
        ((nb090AlphaDummy836 A), (nb090AlphaDummy838 v)), ((nb090AlphaDummy835 A),
        (nb090AlphaDummy837 v)), ((nb090AlphaDummy865 A), (nb090AlphaDummy866 v)),
        ((nb090AlphaDummy839 A), (nb090AlphaDummy840 v)), ((nb090AlphaDummy827 A),
        (nb090AlphaDummy828 v)), ((nb090AlphaDummy829 A), (nb090AlphaDummy830 v)),
        ((nb090AlphaDummy832 A), (nb090AlphaDummy834 v)), ((nb090AlphaDummy831 A),
        (nb090AlphaDummy833 v)), ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy850 A) ≠ (nb090AlphaDummy857 A) from (by
          unfold
            nb090AlphaDummy857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0902
                    A)
                  0)))) (show (nb090AlphaDummy853 v) ≠ (nb090AlphaDummy858 v) from (by
          unfold
            nb090AlphaDummy858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0903
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy850 A) ≠
        (nb090AlphaDummy855 A) from (by
          unfold
            nb090AlphaDummy855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0900
                    A)
                  0)))) (show (nb090AlphaDummy853 v) ≠ (nb090AlphaDummy856 v) from (by
          unfold
            nb090AlphaDummy856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0901
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy843
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy851 A) ≠ (nb090AlphaDummy857 A) from (by
          unfold
            nb090AlphaDummy857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0906
                    A)
                  0)))) (show (nb090AlphaDummy854 v) ≠ (nb090AlphaDummy858 v) from (by
          unfold
            nb090AlphaDummy858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0907
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy851 A) ≠
        (nb090AlphaDummy855 A) from (by
          unfold
            nb090AlphaDummy855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0904
                    A)
                  0)))) (show (nb090AlphaDummy854 v) ≠ (nb090AlphaDummy856 v) from (by
          unfold
            nb090AlphaDummy856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0905
                    v)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy850 A) ≠ (nb090AlphaDummy857 A) from (by
          unfold
            nb090AlphaDummy857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0902
                    A)
                  0)))) (show (nb090AlphaDummy853 v) ≠ (nb090AlphaDummy858 v) from (by
          unfold
            nb090AlphaDummy858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0903
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy850 A) ≠
        (nb090AlphaDummy855 A) from (by
          unfold
            nb090AlphaDummy855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0900
                    A)
                  0)))) (show (nb090AlphaDummy853 v) ≠ (nb090AlphaDummy856 v) from (by
          unfold
            nb090AlphaDummy856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0901
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy843
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy851 A) ≠ (nb090AlphaDummy857 A) from (by
          unfold
            nb090AlphaDummy857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0906
                    A)
                  0)))) (show (nb090AlphaDummy854 v) ≠ (nb090AlphaDummy858 v) from (by
          unfold
            nb090AlphaDummy858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0907
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy851 A) ≠
        (nb090AlphaDummy855 A) from (by
          unfold
            nb090AlphaDummy855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0904
                    A)
                  0)))) (show (nb090AlphaDummy854 v) ≠ (nb090AlphaDummy856 v) from (by
          unfold
            nb090AlphaDummy856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0905
                    v)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy851 A), (nb090AlphaDummy854 v)), ((nb090AlphaDummy850 A),
        (nb090AlphaDummy853 v)), ((nb090AlphaDummy849 A), (nb090AlphaDummy852 v)),
        ((nb090AlphaDummy847 A), (nb090AlphaDummy848 v)), ((nb090AlphaDummy843 A),
        (nb090AlphaDummy845 v)), ((nb090AlphaDummy844 A), (nb090AlphaDummy846 v)),
        ((nb090AlphaDummy869 A), (nb090AlphaDummy870 v)), ((nb090AlphaDummy867 A),
        (nb090AlphaDummy868 v)), ((nb090AlphaDummy836 A), (nb090AlphaDummy838 v)),
        ((nb090AlphaDummy835 A), (nb090AlphaDummy837 v)), ((nb090AlphaDummy865 A),
        (nb090AlphaDummy866 v)), ((nb090AlphaDummy839 A), (nb090AlphaDummy840 v)),
        ((nb090AlphaDummy827 A), (nb090AlphaDummy828 v)), ((nb090AlphaDummy829 A),
        (nb090AlphaDummy830 v)), ((nb090AlphaDummy832 A), (nb090AlphaDummy834 v)),
        ((nb090AlphaDummy831 A), (nb090AlphaDummy833 v)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy843 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy843 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy850 A) ≠ (nb090AlphaDummy861 A) from (by
          unfold
            nb090AlphaDummy861;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0910
                    A)
                  0)))) (show (nb090AlphaDummy853 v) ≠ (nb090AlphaDummy862 v) from (by
          unfold
            nb090AlphaDummy862;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0911
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy850 A) ≠
        (nb090AlphaDummy859 A) from (by
          unfold
            nb090AlphaDummy859;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0908
                    A)
                  0)))) (show (nb090AlphaDummy853 v) ≠ (nb090AlphaDummy860 v) from (by
          unfold
            nb090AlphaDummy860;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0909
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy843
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy850 A) ≠ (nb090AlphaDummy861 A) from (by
          unfold
            nb090AlphaDummy861;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0910
                    A)
                  0)))) (show (nb090AlphaDummy853 v) ≠ (nb090AlphaDummy862 v) from (by
          unfold
            nb090AlphaDummy862;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0911
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy850 A) ≠
        (nb090AlphaDummy859 A) from (by
          unfold
            nb090AlphaDummy859;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0908
                    A)
                  0)))) (show (nb090AlphaDummy853 v) ≠ (nb090AlphaDummy860 v) from (by
          unfold
            nb090AlphaDummy860;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0909
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy843
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy851 A) ≠ (nb090AlphaDummy863 A) from (by
          unfold
            nb090AlphaDummy863;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0914
                    A)
                  0)))) (show (nb090AlphaDummy854 v) ≠ (nb090AlphaDummy864 v) from (by
          unfold
            nb090AlphaDummy864;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0915
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy851 A) ≠
        (nb090AlphaDummy859 A) from (by
          unfold
            nb090AlphaDummy859;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0912
                    A)
                  0)))) (show (nb090AlphaDummy854 v) ≠ (nb090AlphaDummy860 v) from (by
          unfold
            nb090AlphaDummy860;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0913
                    v)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy851 A) ≠ (nb090AlphaDummy863 A) from (by
          unfold
            nb090AlphaDummy863;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0914
                    A)
                  0)))) (show (nb090AlphaDummy854 v) ≠ (nb090AlphaDummy864 v) from (by
          unfold
            nb090AlphaDummy864;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0915
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy851 A) ≠
        (nb090AlphaDummy859 A) from (by
          unfold
            nb090AlphaDummy859;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0912
                    A)
                  0)))) (show (nb090AlphaDummy854 v) ≠ (nb090AlphaDummy860 v) from (by
          unfold
            nb090AlphaDummy860;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0913
                    v)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090AlphaDummy843 A) ≠ (nb090AlphaDummy847 A) from
                                (by
                                  unfold nb090AlphaDummy847;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0896 A) 0))))
                              (show (nb090AlphaDummy845 v) ≠ (nb090AlphaDummy848 v) from
                                (by
                                  unfold nb090AlphaDummy848;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0897 v) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb090AlphaDummy847 A), (nb090AlphaDummy848 v)),
                              ((nb090AlphaDummy843 A), (nb090AlphaDummy845 v)),
                              ((nb090AlphaDummy844 A), (nb090AlphaDummy846 v)),
                              ((nb090AlphaDummy869 A), (nb090AlphaDummy870 v)),
                              ((nb090AlphaDummy867 A), (nb090AlphaDummy868 v)),
                              ((nb090AlphaDummy836 A), (nb090AlphaDummy838 v)),
                              ((nb090AlphaDummy835 A), (nb090AlphaDummy837 v)),
                              ((nb090AlphaDummy865 A), (nb090AlphaDummy866 v)),
                              ((nb090AlphaDummy839 A), (nb090AlphaDummy840 v)),
                              ((nb090AlphaDummy827 A), (nb090AlphaDummy828 v)),
                              ((nb090AlphaDummy829 A), (nb090AlphaDummy830 v)),
                              ((nb090AlphaDummy832 A), (nb090AlphaDummy834 v)),
                              ((nb090AlphaDummy831 A), (nb090AlphaDummy833 v)),
                              ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
                              ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                              ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                              ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                (nb090AlphaDummy004 v u A h))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy843 A) ≠ (nb090AlphaDummy847 A) from (by
                                unfold nb090AlphaDummy847;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0896 A) 0))))
                            (show (nb090AlphaDummy845 v) ≠ (nb090AlphaDummy848 v) from (by
                                unfold nb090AlphaDummy848;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0897 v) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090AlphaDummy843 A) ≠ (nb090AlphaDummy847 A) from
                                (by
                                  unfold nb090AlphaDummy847;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0896 A) 0))))
                              (show (nb090AlphaDummy845 v) ≠ (nb090AlphaDummy848 v) from
                                (by
                                  unfold nb090AlphaDummy848;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0897 v) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb090AlphaDummy847 A), (nb090AlphaDummy848 v)),
                              ((nb090AlphaDummy843 A), (nb090AlphaDummy845 v)),
                              ((nb090AlphaDummy844 A), (nb090AlphaDummy846 v)),
                              ((nb090AlphaDummy869 A), (nb090AlphaDummy870 v)),
                              ((nb090AlphaDummy867 A), (nb090AlphaDummy868 v)),
                              ((nb090AlphaDummy836 A), (nb090AlphaDummy838 v)),
                              ((nb090AlphaDummy835 A), (nb090AlphaDummy837 v)),
                              ((nb090AlphaDummy865 A), (nb090AlphaDummy866 v)),
                              ((nb090AlphaDummy839 A), (nb090AlphaDummy840 v)),
                              ((nb090AlphaDummy827 A), (nb090AlphaDummy828 v)),
                              ((nb090AlphaDummy829 A), (nb090AlphaDummy830 v)),
                              ((nb090AlphaDummy832 A), (nb090AlphaDummy834 v)),
                              ((nb090AlphaDummy831 A), (nb090AlphaDummy833 v)),
                              ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
                              ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                              ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                              ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                (nb090AlphaDummy004 v u A h))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

theorem nb090_wpp_notmem_2250 (A : Class) : (nb090AlphaDummy827 A) ∉ ((synC1st)).fv :=
  by simpa only [nb090AlphaDummy827, fv_syn_c1st] using (nb090_compact_fv_empty_0640 A)

theorem nb090_wpp_notmem_2251 (v : Var) : (nb090AlphaDummy828 v) ∉ ((synC1st)).fv :=
  by simpa only [nb090AlphaDummy828, fv_syn_c1st] using (nb090_compact_fv_empty_0641 v)

theorem nb090_wpp_notmem_2252 (A : Class) : (nb090AlphaDummy829 A) ∉ ((synC1st)).fv :=
  by simpa only [nb090AlphaDummy829, fv_syn_c1st] using (nb090_compact_fv_empty_0642 A)

theorem nb090_wpp_notmem_2253 (v : Var) : (nb090AlphaDummy830 v) ∉ ((synC1st)).fv :=
  by simpa only [nb090AlphaDummy830, fv_syn_c1st] using (nb090_compact_fv_empty_0643 v)

theorem nb090_wpp_notmem_2254 (A : Class) : (nb090AlphaDummy832 A) ∉ ((synC1st)).fv :=
  by simpa only [nb090AlphaDummy832, fv_syn_c1st] using (nb090_compact_fv_empty_0644 A)

theorem nb090_wpp_notmem_2255 (v : Var) : (nb090AlphaDummy834 v) ∉ ((synC1st)).fv :=
  by simpa only [nb090AlphaDummy834, fv_syn_c1st] using (nb090_compact_fv_empty_0645 v)

theorem nb090_wpp_notmem_2256 (A : Class) : (nb090AlphaDummy831 A) ∉ ((synC1st)).fv :=
  by simpa only [nb090AlphaDummy831, fv_syn_c1st] using (nb090_compact_fv_empty_0646 A)

theorem nb090_wpp_notmem_2257 (v : Var) : (nb090AlphaDummy833 v) ∉ ((synC1st)).fv :=
  by simpa only [nb090AlphaDummy833, fv_syn_c1st] using (nb090_compact_fv_empty_0647 v)

theorem nb090_compact_envfresh_0327 (v : Var) (u : Var) (A : Class) (h : Var) :
    TEnvFresh
      [((nb090AlphaDummy827 A), (nb090AlphaDummy828 v)),
        ((nb090AlphaDummy829 A), (nb090AlphaDummy830 v)),
        ((nb090AlphaDummy832 A), (nb090AlphaDummy834 v)),
        ((nb090AlphaDummy831 A), (nb090AlphaDummy833 v)),
        ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      ((synC1st)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb090AlphaDummy827 A) (nb090AlphaDummy828 v)
      (nb090_wpp_notmem_2250 A) (nb090_wpp_notmem_2251 v)
      (TEnvFresh.consFresh (nb090AlphaDummy829 A) (nb090AlphaDummy830 v)
        (nb090_wpp_notmem_2252 A) (nb090_wpp_notmem_2253 v)
        (TEnvFresh.consFresh (nb090AlphaDummy832 A) (nb090AlphaDummy834 v)
          (nb090_wpp_notmem_2254 A) (nb090_wpp_notmem_2255 v)
          (TEnvFresh.consFresh (nb090AlphaDummy831 A) (nb090AlphaDummy833 v)
            (nb090_wpp_notmem_2256 A) (nb090_wpp_notmem_2257 v)
            (TEnvFresh.consFresh (nb090AlphaDummy042 A) (nb090AlphaDummy044 v u h)
              (nb090_wpp_notmem_1812 A) (nb090_wpp_notmem_1813 v u h)
              (TEnvFresh.consFresh (nb090AlphaDummy041 A) (nb090AlphaDummy043 v u h)
                (nb090_wpp_notmem_1814 A) (nb090_wpp_notmem_1815 v u h)
                (TEnvFresh.consFresh (nb090AlphaDummy000 A) h (nb090_wpp_notmem_1816 A)
                  (nb090_wpp_notmem_1817 h) (TEnvFresh.consFresh (nb090AlphaDummy002 A) v
                    (nb090_wpp_notmem_1818 A) (nb090_wpp_notmem_1819 v)
                    (TEnvFresh.consFresh (nb090AlphaDummy001 A) u
                      (nb090_wpp_notmem_1820 A) (nb090_wpp_notmem_1821 u)
                      (TEnvFresh.consFresh (nb090AlphaDummy003 A)
                        (nb090AlphaDummy004 v u A h) (nb090_wpp_notmem_1822 A)
                        (nb090_wpp_notmem_1823 v u A h)
                        (TEnvFresh.nil ((synC1st)).fv)))))))))))

/-- Checked nominal proof certificate identified upstream as `nb090_wpp_refl_0327`. -/
@[expose]
noncomputable def nb090WppRefl0327 (v : Var) (u : Var) (A : Class) (h : Var) :
    TReflOn
      [((nb090AlphaDummy827 A), (nb090AlphaDummy828 v)),
        ((nb090AlphaDummy829 A), (nb090AlphaDummy830 v)),
        ((nb090AlphaDummy832 A), (nb090AlphaDummy834 v)),
        ((nb090AlphaDummy831 A), (nb090AlphaDummy833 v)),
        ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      ((synC1st)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0327 v u A h)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
