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

@[expose]
noncomputable def nb090_split_alpha_0094 (v : Var) (u : Var) (A : Class) (h : Var)
    (dv_h_v : h ≠ v) :
    TAlphaWff
      [((nb090_alpha_dummy_841 A), (nb090_alpha_dummy_842 v)),
        ((nb090_alpha_dummy_839 A), (nb090_alpha_dummy_840 v)),
        ((nb090_alpha_dummy_827 A), (nb090_alpha_dummy_828 v)),
        ((nb090_alpha_dummy_829 A), (nb090_alpha_dummy_830 v)),
        ((nb090_alpha_dummy_832 A), (nb090_alpha_dummy_834 v)),
        ((nb090_alpha_dummy_831 A), (nb090_alpha_dummy_833 v)),
        ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_841 A))
          (Class.cab (nb090_alpha_dummy_835 A)
            (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_002 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_841 A))
            (Class.cab (nb090_alpha_dummy_835 A)
              (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_002 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_842 v))
          (Class.cab (nb090_alpha_dummy_837 v) (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv v)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v))
                (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_842 v))
            (Class.cab (nb090_alpha_dummy_837 v)
              (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv v)
                (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_836 A) from (by
                      unfold nb090_alpha_dummy_836;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0888 A) 1))))
                  (show v ≠ (nb090_alpha_dummy_838 v) from (by
                      unfold nb090_alpha_dummy_838;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0890 v) 1))))
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_835 A) from (by
                        unfold nb090_alpha_dummy_835;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0888 A) 0))))
                    (show v ≠ (nb090_alpha_dummy_837 v) from (by
                        unfold nb090_alpha_dummy_837;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0890 v) 0)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_841 A) from (by
                          unfold nb090_alpha_dummy_841;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0892 A) 0))))
                      (show v ≠ (nb090_alpha_dummy_842 v) from (by
                          unfold nb090_alpha_dummy_842;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0893 v) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_839 A) from (by
                            unfold nb090_alpha_dummy_839;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0889 A) 0))))
                        (show v ≠ (nb090_alpha_dummy_840 v) from (by
                            unfold nb090_alpha_dummy_840;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0891 v) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_827 A) from (by
                              unfold nb090_alpha_dummy_827;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0882 A) 0))))
                          (show v ≠ (nb090_alpha_dummy_828 v) from (by
                              unfold nb090_alpha_dummy_828;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0885 v) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_829 A) from (by
                                unfold nb090_alpha_dummy_829;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0883 A) 0))))
                            (show v ≠ (nb090_alpha_dummy_830 v) from (by
                                unfold nb090_alpha_dummy_830;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0886 v) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_832 A) from
                                (by
                                  unfold nb090_alpha_dummy_832;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0884 A) 1))))
                              (show v ≠ (nb090_alpha_dummy_834 v) from (by
                                  unfold nb090_alpha_dummy_834;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0887 v) 1))))
                              (TAlphaVar.there (show
                                  (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_831 A) from (by
                                    unfold nb090_alpha_dummy_831;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0884 A)
                                            0)))) (show v ≠ (nb090_alpha_dummy_833 v) from (by
                                    unfold nb090_alpha_dummy_833;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0887 v)
                                            0)))) (TAlphaVar.there (show
                                    (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_042 A) from
                                    (by
                                      unfold nb090_alpha_dummy_042;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0880 A)
                                              1)))) (show v ≠ (nb090_alpha_dummy_044 v u h) from
                                    (by
                                      unfold nb090_alpha_dummy_044;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb090_support_mem_0881 v u h) 1))))
                                  (TAlphaVar.there (show (nb090_alpha_dummy_002 A) ≠
                                        (nb090_alpha_dummy_041 A) from (by
                                        unfold nb090_alpha_dummy_041;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0880 A)
                                                0))))
                                    (show v ≠ (nb090_alpha_dummy_043 v u h) from (by
                                        unfold nb090_alpha_dummy_043;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0881 v u h) 0))))
                                    (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                                      (Ne.symm dv_h_v) (TAlphaVar.here _ _ _))))))))))))))
            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_827 A))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_828 v))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_836 A) ≠ (nb090_alpha_dummy_843 A) from (by
                              unfold nb090_alpha_dummy_843;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0894 A) 0))))
                          (show (nb090_alpha_dummy_838 v) ≠ (nb090_alpha_dummy_845 v) from (by
                              unfold nb090_alpha_dummy_845;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0895 v) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_836 A) ≠ (nb090_alpha_dummy_844 A) from (by
                                unfold nb090_alpha_dummy_844;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0894 A) 1))))
                            (show (nb090_alpha_dummy_838 v) ≠ (nb090_alpha_dummy_846 v) from (by
                                unfold nb090_alpha_dummy_846;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0895 v) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_836 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_838 v))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_843 A) ≠ (nb090_alpha_dummy_850 A) from (by
          unfold nb090_alpha_dummy_850;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0898 A) 1)))) (show (nb090_alpha_dummy_845 v) ≠
        (nb090_alpha_dummy_853 v) from (by
          unfold nb090_alpha_dummy_853;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0899 v) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_843 A) ≠ (nb090_alpha_dummy_849 A) from (by
          unfold nb090_alpha_dummy_849;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0898 A) 0)))) (show (nb090_alpha_dummy_845 v) ≠
        (nb090_alpha_dummy_852 v) from (by
          unfold nb090_alpha_dummy_852;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0899 v) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_843 A) ≠ (nb090_alpha_dummy_847 A) from (by
          unfold nb090_alpha_dummy_847;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0896 A)
                  0)))) (show (nb090_alpha_dummy_845 v) ≠ (nb090_alpha_dummy_848 v) from (by
          unfold nb090_alpha_dummy_848;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0897 v)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_851 A), (nb090_alpha_dummy_854 v)), ((nb090_alpha_dummy_850 A),
        (nb090_alpha_dummy_853 v)), ((nb090_alpha_dummy_849 A), (nb090_alpha_dummy_852 v)),
        ((nb090_alpha_dummy_847 A), (nb090_alpha_dummy_848 v)), ((nb090_alpha_dummy_843 A),
        (nb090_alpha_dummy_845 v)), ((nb090_alpha_dummy_844 A), (nb090_alpha_dummy_846 v)),
        ((nb090_alpha_dummy_836 A), (nb090_alpha_dummy_838 v)), ((nb090_alpha_dummy_835 A),
        (nb090_alpha_dummy_837 v)), ((nb090_alpha_dummy_841 A), (nb090_alpha_dummy_842 v)),
        ((nb090_alpha_dummy_839 A), (nb090_alpha_dummy_840 v)), ((nb090_alpha_dummy_827 A),
        (nb090_alpha_dummy_828 v)), ((nb090_alpha_dummy_829 A), (nb090_alpha_dummy_830 v)),
        ((nb090_alpha_dummy_832 A), (nb090_alpha_dummy_834 v)), ((nb090_alpha_dummy_831 A),
        (nb090_alpha_dummy_833 v)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_850
        A) ≠ (nb090_alpha_dummy_857 A) from (by
          unfold
            nb090_alpha_dummy_857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0902
                    A)
                  0)))) (show (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_858 v) from (by
          unfold
            nb090_alpha_dummy_858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0903
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_850 A) ≠
        (nb090_alpha_dummy_855 A) from (by
          unfold
            nb090_alpha_dummy_855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0900
                    A)
                  0)))) (show (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_856 v) from (by
          unfold
            nb090_alpha_dummy_856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0901
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_843
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_851 A) ≠ (nb090_alpha_dummy_857 A) from (by
          unfold
            nb090_alpha_dummy_857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0906
                    A)
                  0)))) (show (nb090_alpha_dummy_854 v) ≠ (nb090_alpha_dummy_858 v) from (by
          unfold
            nb090_alpha_dummy_858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0907
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_851 A) ≠
        (nb090_alpha_dummy_855 A) from (by
          unfold
            nb090_alpha_dummy_855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0904
                    A)
                  0)))) (show (nb090_alpha_dummy_854 v) ≠ (nb090_alpha_dummy_856 v) from (by
          unfold
            nb090_alpha_dummy_856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0905
                    v)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_850 A) ≠ (nb090_alpha_dummy_857 A) from (by
          unfold
            nb090_alpha_dummy_857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0902
                    A)
                  0)))) (show (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_858 v) from (by
          unfold
            nb090_alpha_dummy_858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0903
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_850 A) ≠
        (nb090_alpha_dummy_855 A) from (by
          unfold
            nb090_alpha_dummy_855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0900
                    A)
                  0)))) (show (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_856 v) from (by
          unfold
            nb090_alpha_dummy_856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0901
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_843
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_851 A) ≠ (nb090_alpha_dummy_857 A) from (by
          unfold
            nb090_alpha_dummy_857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0906
                    A)
                  0)))) (show (nb090_alpha_dummy_854 v) ≠ (nb090_alpha_dummy_858 v) from (by
          unfold
            nb090_alpha_dummy_858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0907
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_851 A) ≠
        (nb090_alpha_dummy_855 A) from (by
          unfold
            nb090_alpha_dummy_855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0904
                    A)
                  0)))) (show (nb090_alpha_dummy_854 v) ≠ (nb090_alpha_dummy_856 v) from (by
          unfold
            nb090_alpha_dummy_856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0905
                    v)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_851 A), (nb090_alpha_dummy_854 v)), ((nb090_alpha_dummy_850 A),
        (nb090_alpha_dummy_853 v)), ((nb090_alpha_dummy_849 A), (nb090_alpha_dummy_852 v)),
        ((nb090_alpha_dummy_847 A), (nb090_alpha_dummy_848 v)), ((nb090_alpha_dummy_843 A),
        (nb090_alpha_dummy_845 v)), ((nb090_alpha_dummy_844 A), (nb090_alpha_dummy_846 v)),
        ((nb090_alpha_dummy_836 A), (nb090_alpha_dummy_838 v)), ((nb090_alpha_dummy_835 A),
        (nb090_alpha_dummy_837 v)), ((nb090_alpha_dummy_841 A), (nb090_alpha_dummy_842 v)),
        ((nb090_alpha_dummy_839 A), (nb090_alpha_dummy_840 v)), ((nb090_alpha_dummy_827 A),
        (nb090_alpha_dummy_828 v)), ((nb090_alpha_dummy_829 A), (nb090_alpha_dummy_830 v)),
        ((nb090_alpha_dummy_832 A), (nb090_alpha_dummy_834 v)), ((nb090_alpha_dummy_831 A),
        (nb090_alpha_dummy_833 v)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_843 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_843 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_845
        v))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_850 A) ≠ (nb090_alpha_dummy_861 A) from (by
          unfold
            nb090_alpha_dummy_861;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0910
                    A)
                  0)))) (show (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_862 v) from (by
          unfold
            nb090_alpha_dummy_862;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0911
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_850 A) ≠
        (nb090_alpha_dummy_859 A) from (by
          unfold
            nb090_alpha_dummy_859;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0908
                    A)
                  0)))) (show (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_860 v) from (by
          unfold
            nb090_alpha_dummy_860;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0909
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_843
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_850 A) ≠ (nb090_alpha_dummy_861 A) from (by
          unfold
            nb090_alpha_dummy_861;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0910
                    A)
                  0)))) (show (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_862 v) from (by
          unfold
            nb090_alpha_dummy_862;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0911
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_850 A) ≠
        (nb090_alpha_dummy_859 A) from (by
          unfold
            nb090_alpha_dummy_859;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0908
                    A)
                  0)))) (show (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_860 v) from (by
          unfold
            nb090_alpha_dummy_860;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0909
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_843
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_851
        A) ≠ (nb090_alpha_dummy_863 A) from (by
          unfold
            nb090_alpha_dummy_863;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0914
                    A)
                  0)))) (show (nb090_alpha_dummy_854 v) ≠ (nb090_alpha_dummy_864 v) from (by
          unfold
            nb090_alpha_dummy_864;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0915
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_851 A) ≠
        (nb090_alpha_dummy_859 A) from (by
          unfold
            nb090_alpha_dummy_859;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0912
                    A)
                  0)))) (show (nb090_alpha_dummy_854 v) ≠ (nb090_alpha_dummy_860 v) from (by
          unfold
            nb090_alpha_dummy_860;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0913
                    v)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_851
        A) ≠ (nb090_alpha_dummy_863 A) from (by
          unfold
            nb090_alpha_dummy_863;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0914
                    A)
                  0)))) (show (nb090_alpha_dummy_854 v) ≠ (nb090_alpha_dummy_864 v) from (by
          unfold
            nb090_alpha_dummy_864;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0915
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_851 A) ≠
        (nb090_alpha_dummy_859 A) from (by
          unfold
            nb090_alpha_dummy_859;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0912
                    A)
                  0)))) (show (nb090_alpha_dummy_854 v) ≠ (nb090_alpha_dummy_860 v) from (by
          unfold
            nb090_alpha_dummy_860;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0913
                    v)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_843 A) ≠ (nb090_alpha_dummy_847 A) from
                                      (by
                                        unfold nb090_alpha_dummy_847;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0896 A)
                                                0)))) (show (nb090_alpha_dummy_845 v) ≠
                                        (nb090_alpha_dummy_848 v) from (by
                                        unfold nb090_alpha_dummy_848;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0897 v)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_847 A), (nb090_alpha_dummy_848 v)),
                                    ((nb090_alpha_dummy_843 A), (nb090_alpha_dummy_845 v)),
                                    ((nb090_alpha_dummy_844 A), (nb090_alpha_dummy_846 v)),
                                    ((nb090_alpha_dummy_836 A), (nb090_alpha_dummy_838 v)),
                                    ((nb090_alpha_dummy_835 A), (nb090_alpha_dummy_837 v)),
                                    ((nb090_alpha_dummy_841 A), (nb090_alpha_dummy_842 v)),
                                    ((nb090_alpha_dummy_839 A), (nb090_alpha_dummy_840 v)),
                                    ((nb090_alpha_dummy_827 A), (nb090_alpha_dummy_828 v)),
                                    ((nb090_alpha_dummy_829 A), (nb090_alpha_dummy_830 v)),
                                    ((nb090_alpha_dummy_832 A), (nb090_alpha_dummy_834 v)),
                                    ((nb090_alpha_dummy_831 A), (nb090_alpha_dummy_833 v)),
                                    ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
                                    ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_843 A) ≠ (nb090_alpha_dummy_847 A) from
                                    (by
                                      unfold nb090_alpha_dummy_847;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0896 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_845 v) ≠ (nb090_alpha_dummy_848 v) from
                                    (by
                                      unfold nb090_alpha_dummy_848;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0897 v)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_843 A) ≠ (nb090_alpha_dummy_847 A) from
                                      (by
                                        unfold nb090_alpha_dummy_847;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0896 A)
                                                0)))) (show (nb090_alpha_dummy_845 v) ≠
                                        (nb090_alpha_dummy_848 v) from (by
                                        unfold nb090_alpha_dummy_848;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0897 v)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_847 A), (nb090_alpha_dummy_848 v)),
                                    ((nb090_alpha_dummy_843 A), (nb090_alpha_dummy_845 v)),
                                    ((nb090_alpha_dummy_844 A), (nb090_alpha_dummy_846 v)),
                                    ((nb090_alpha_dummy_836 A), (nb090_alpha_dummy_838 v)),
                                    ((nb090_alpha_dummy_835 A), (nb090_alpha_dummy_837 v)),
                                    ((nb090_alpha_dummy_841 A), (nb090_alpha_dummy_842 v)),
                                    ((nb090_alpha_dummy_839 A), (nb090_alpha_dummy_840 v)),
                                    ((nb090_alpha_dummy_827 A), (nb090_alpha_dummy_828 v)),
                                    ((nb090_alpha_dummy_829 A), (nb090_alpha_dummy_830 v)),
                                    ((nb090_alpha_dummy_832 A), (nb090_alpha_dummy_834 v)),
                                    ((nb090_alpha_dummy_831 A), (nb090_alpha_dummy_833 v)),
                                    ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
                                    ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_836 A) from (by
                        unfold nb090_alpha_dummy_836;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0888 A) 1))))
                    (show v ≠ (nb090_alpha_dummy_838 v) from (by
                        unfold nb090_alpha_dummy_838;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0890 v) 1)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_835 A) from (by
                          unfold nb090_alpha_dummy_835;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0888 A) 0))))
                      (show v ≠ (nb090_alpha_dummy_837 v) from (by
                          unfold nb090_alpha_dummy_837;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0890 v) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_841 A) from (by
                            unfold nb090_alpha_dummy_841;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0892 A) 0))))
                        (show v ≠ (nb090_alpha_dummy_842 v) from (by
                            unfold nb090_alpha_dummy_842;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0893 v) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_839 A) from (by
                              unfold nb090_alpha_dummy_839;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0889 A) 0))))
                          (show v ≠ (nb090_alpha_dummy_840 v) from (by
                              unfold nb090_alpha_dummy_840;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0891 v) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_827 A) from (by
                                unfold nb090_alpha_dummy_827;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0882 A) 0))))
                            (show v ≠ (nb090_alpha_dummy_828 v) from (by
                                unfold nb090_alpha_dummy_828;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0885 v) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_829 A) from
                                (by
                                  unfold nb090_alpha_dummy_829;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0883 A) 0))))
                              (show v ≠ (nb090_alpha_dummy_830 v) from (by
                                  unfold nb090_alpha_dummy_830;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0886 v) 0))))
                              (TAlphaVar.there (show
                                  (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_832 A) from (by
                                    unfold nb090_alpha_dummy_832;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0884 A)
                                            1)))) (show v ≠ (nb090_alpha_dummy_834 v) from (by
                                    unfold nb090_alpha_dummy_834;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0887 v)
                                            1)))) (TAlphaVar.there (show
                                    (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_831 A) from
                                    (by
                                      unfold nb090_alpha_dummy_831;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0884 A)
                                              0)))) (show v ≠ (nb090_alpha_dummy_833 v) from (by
                                      unfold nb090_alpha_dummy_833;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0887 v)
                                              0)))) (TAlphaVar.there (show
                                      (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_042 A) from
                                      (by
                                        unfold nb090_alpha_dummy_042;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0880 A)
                                                1))))
                                    (show v ≠ (nb090_alpha_dummy_044 v u h) from (by
                                        unfold nb090_alpha_dummy_044;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0881 v u h) 1))))
                                    (TAlphaVar.there (show (nb090_alpha_dummy_002 A) ≠
        (nb090_alpha_dummy_041 A) from (by
                                          unfold nb090_alpha_dummy_041;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0880 A) 0))))
                                      (show v ≠ (nb090_alpha_dummy_043 v u h) from (by
                                          unfold nb090_alpha_dummy_043;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0881 v u h) 0))))
                                      (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                                        (Ne.symm dv_h_v) (TAlphaVar.here _ _ _))))))))))))))
              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_827 A))).fv) (by decide))
                    (freshVar_injective
                      (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_828 v))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_836 A) ≠ (nb090_alpha_dummy_843 A) from (by
                                unfold nb090_alpha_dummy_843;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0894 A) 0))))
                            (show (nb090_alpha_dummy_838 v) ≠ (nb090_alpha_dummy_845 v) from (by
                                unfold nb090_alpha_dummy_845;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0895 v) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_836 A) ≠ (nb090_alpha_dummy_844 A) from
                                (by
                                  unfold nb090_alpha_dummy_844;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0894 A) 1))))
                              (show (nb090_alpha_dummy_838 v) ≠ (nb090_alpha_dummy_846 v) from
                                (by
                                  unfold nb090_alpha_dummy_846;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0895 v) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_836 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_838 v))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_843 A) ≠ (nb090_alpha_dummy_850 A) from (by
          unfold nb090_alpha_dummy_850;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0898 A) 1)))) (show (nb090_alpha_dummy_845 v) ≠
        (nb090_alpha_dummy_853 v) from (by
          unfold nb090_alpha_dummy_853;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0899 v) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_843 A) ≠ (nb090_alpha_dummy_849 A) from (by
          unfold nb090_alpha_dummy_849;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0898 A)
                  0)))) (show (nb090_alpha_dummy_845 v) ≠ (nb090_alpha_dummy_852 v) from (by
          unfold nb090_alpha_dummy_852;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0899 v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_843 A) ≠
        (nb090_alpha_dummy_847 A) from (by
          unfold nb090_alpha_dummy_847;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0896 A)
                  0)))) (show (nb090_alpha_dummy_845 v) ≠ (nb090_alpha_dummy_848 v) from (by
          unfold nb090_alpha_dummy_848;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0897 v)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_851 A), (nb090_alpha_dummy_854 v)), ((nb090_alpha_dummy_850 A),
        (nb090_alpha_dummy_853 v)), ((nb090_alpha_dummy_849 A), (nb090_alpha_dummy_852 v)),
        ((nb090_alpha_dummy_847 A), (nb090_alpha_dummy_848 v)), ((nb090_alpha_dummy_843 A),
        (nb090_alpha_dummy_845 v)), ((nb090_alpha_dummy_844 A), (nb090_alpha_dummy_846 v)),
        ((nb090_alpha_dummy_836 A), (nb090_alpha_dummy_838 v)), ((nb090_alpha_dummy_835 A),
        (nb090_alpha_dummy_837 v)), ((nb090_alpha_dummy_841 A), (nb090_alpha_dummy_842 v)),
        ((nb090_alpha_dummy_839 A), (nb090_alpha_dummy_840 v)), ((nb090_alpha_dummy_827 A),
        (nb090_alpha_dummy_828 v)), ((nb090_alpha_dummy_829 A), (nb090_alpha_dummy_830 v)),
        ((nb090_alpha_dummy_832 A), (nb090_alpha_dummy_834 v)), ((nb090_alpha_dummy_831 A),
        (nb090_alpha_dummy_833 v)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_850
        A) ≠ (nb090_alpha_dummy_857 A) from (by
          unfold
            nb090_alpha_dummy_857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0902
                    A)
                  0)))) (show (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_858 v) from (by
          unfold
            nb090_alpha_dummy_858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0903
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_850 A) ≠
        (nb090_alpha_dummy_855 A) from (by
          unfold
            nb090_alpha_dummy_855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0900
                    A)
                  0)))) (show (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_856 v) from (by
          unfold
            nb090_alpha_dummy_856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0901
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_843
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_851 A) ≠ (nb090_alpha_dummy_857 A) from (by
          unfold
            nb090_alpha_dummy_857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0906
                    A)
                  0)))) (show (nb090_alpha_dummy_854 v) ≠ (nb090_alpha_dummy_858 v) from (by
          unfold
            nb090_alpha_dummy_858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0907
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_851 A) ≠
        (nb090_alpha_dummy_855 A) from (by
          unfold
            nb090_alpha_dummy_855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0904
                    A)
                  0)))) (show (nb090_alpha_dummy_854 v) ≠ (nb090_alpha_dummy_856 v) from (by
          unfold
            nb090_alpha_dummy_856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0905
                    v)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_850 A) ≠ (nb090_alpha_dummy_857 A) from (by
          unfold
            nb090_alpha_dummy_857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0902
                    A)
                  0)))) (show (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_858 v) from (by
          unfold
            nb090_alpha_dummy_858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0903
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_850 A) ≠
        (nb090_alpha_dummy_855 A) from (by
          unfold
            nb090_alpha_dummy_855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0900
                    A)
                  0)))) (show (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_856 v) from (by
          unfold
            nb090_alpha_dummy_856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0901
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_843
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_851 A) ≠ (nb090_alpha_dummy_857 A) from (by
          unfold
            nb090_alpha_dummy_857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0906
                    A)
                  0)))) (show (nb090_alpha_dummy_854 v) ≠ (nb090_alpha_dummy_858 v) from (by
          unfold
            nb090_alpha_dummy_858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0907
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_851 A) ≠
        (nb090_alpha_dummy_855 A) from (by
          unfold
            nb090_alpha_dummy_855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0904
                    A)
                  0)))) (show (nb090_alpha_dummy_854 v) ≠ (nb090_alpha_dummy_856 v) from (by
          unfold
            nb090_alpha_dummy_856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0905
                    v)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_851 A), (nb090_alpha_dummy_854 v)), ((nb090_alpha_dummy_850 A),
        (nb090_alpha_dummy_853 v)), ((nb090_alpha_dummy_849 A), (nb090_alpha_dummy_852 v)),
        ((nb090_alpha_dummy_847 A), (nb090_alpha_dummy_848 v)), ((nb090_alpha_dummy_843 A),
        (nb090_alpha_dummy_845 v)), ((nb090_alpha_dummy_844 A), (nb090_alpha_dummy_846 v)),
        ((nb090_alpha_dummy_836 A), (nb090_alpha_dummy_838 v)), ((nb090_alpha_dummy_835 A),
        (nb090_alpha_dummy_837 v)), ((nb090_alpha_dummy_841 A), (nb090_alpha_dummy_842 v)),
        ((nb090_alpha_dummy_839 A), (nb090_alpha_dummy_840 v)), ((nb090_alpha_dummy_827 A),
        (nb090_alpha_dummy_828 v)), ((nb090_alpha_dummy_829 A), (nb090_alpha_dummy_830 v)),
        ((nb090_alpha_dummy_832 A), (nb090_alpha_dummy_834 v)), ((nb090_alpha_dummy_831 A),
        (nb090_alpha_dummy_833 v)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_843 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_843 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_845
        v))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_850 A) ≠ (nb090_alpha_dummy_861 A) from (by
          unfold
            nb090_alpha_dummy_861;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0910
                    A)
                  0)))) (show (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_862 v) from (by
          unfold
            nb090_alpha_dummy_862;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0911
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_850 A) ≠
        (nb090_alpha_dummy_859 A) from (by
          unfold
            nb090_alpha_dummy_859;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0908
                    A)
                  0)))) (show (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_860 v) from (by
          unfold
            nb090_alpha_dummy_860;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0909
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_843
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_850 A) ≠ (nb090_alpha_dummy_861 A) from (by
          unfold
            nb090_alpha_dummy_861;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0910
                    A)
                  0)))) (show (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_862 v) from (by
          unfold
            nb090_alpha_dummy_862;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0911
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_850 A) ≠
        (nb090_alpha_dummy_859 A) from (by
          unfold
            nb090_alpha_dummy_859;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0908
                    A)
                  0)))) (show (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_860 v) from (by
          unfold
            nb090_alpha_dummy_860;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0909
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_843
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_851
        A) ≠ (nb090_alpha_dummy_863 A) from (by
          unfold
            nb090_alpha_dummy_863;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0914
                    A)
                  0)))) (show (nb090_alpha_dummy_854 v) ≠ (nb090_alpha_dummy_864 v) from (by
          unfold
            nb090_alpha_dummy_864;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0915
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_851 A) ≠
        (nb090_alpha_dummy_859 A) from (by
          unfold
            nb090_alpha_dummy_859;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0912
                    A)
                  0)))) (show (nb090_alpha_dummy_854 v) ≠ (nb090_alpha_dummy_860 v) from (by
          unfold
            nb090_alpha_dummy_860;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0913
                    v)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_851
        A) ≠ (nb090_alpha_dummy_863 A) from (by
          unfold
            nb090_alpha_dummy_863;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0914
                    A)
                  0)))) (show (nb090_alpha_dummy_854 v) ≠ (nb090_alpha_dummy_864 v) from (by
          unfold
            nb090_alpha_dummy_864;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0915
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_851 A) ≠
        (nb090_alpha_dummy_859 A) from (by
          unfold
            nb090_alpha_dummy_859;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0912
                    A)
                  0)))) (show (nb090_alpha_dummy_854 v) ≠ (nb090_alpha_dummy_860 v) from (by
          unfold
            nb090_alpha_dummy_860;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0913
                    v)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_843 A) ≠ (nb090_alpha_dummy_847 A)
                                        from (by
                                          unfold nb090_alpha_dummy_847;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0896 A) 0)))) (show
                                        (nb090_alpha_dummy_845 v) ≠ (nb090_alpha_dummy_848 v)
                                        from (by
                                          unfold nb090_alpha_dummy_848;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0897 v) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_847 A), (nb090_alpha_dummy_848 v)),
                                      ((nb090_alpha_dummy_843 A), (nb090_alpha_dummy_845 v)),
                                      ((nb090_alpha_dummy_844 A), (nb090_alpha_dummy_846 v)),
                                      ((nb090_alpha_dummy_836 A), (nb090_alpha_dummy_838 v)),
                                      ((nb090_alpha_dummy_835 A), (nb090_alpha_dummy_837 v)),
                                      ((nb090_alpha_dummy_841 A), (nb090_alpha_dummy_842 v)),
                                      ((nb090_alpha_dummy_839 A), (nb090_alpha_dummy_840 v)),
                                      ((nb090_alpha_dummy_827 A), (nb090_alpha_dummy_828 v)),
                                      ((nb090_alpha_dummy_829 A), (nb090_alpha_dummy_830 v)),
                                      ((nb090_alpha_dummy_832 A), (nb090_alpha_dummy_834 v)),
                                      ((nb090_alpha_dummy_831 A), (nb090_alpha_dummy_833 v)),
                                      ((nb090_alpha_dummy_042 A),
                                        (nb090_alpha_dummy_044 v u h)),
                                      ((nb090_alpha_dummy_041 A),
                                        (nb090_alpha_dummy_043 v u h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_843 A) ≠ (nb090_alpha_dummy_847 A) from
                                      (by
                                        unfold nb090_alpha_dummy_847;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0896 A)
                                                0)))) (show (nb090_alpha_dummy_845 v) ≠
                                        (nb090_alpha_dummy_848 v) from (by
                                        unfold nb090_alpha_dummy_848;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0897 v)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_843 A) ≠ (nb090_alpha_dummy_847 A)
                                        from (by
                                          unfold nb090_alpha_dummy_847;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0896 A) 0)))) (show
                                        (nb090_alpha_dummy_845 v) ≠ (nb090_alpha_dummy_848 v)
                                        from (by
                                          unfold nb090_alpha_dummy_848;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0897 v) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_847 A), (nb090_alpha_dummy_848 v)),
                                      ((nb090_alpha_dummy_843 A), (nb090_alpha_dummy_845 v)),
                                      ((nb090_alpha_dummy_844 A), (nb090_alpha_dummy_846 v)),
                                      ((nb090_alpha_dummy_836 A), (nb090_alpha_dummy_838 v)),
                                      ((nb090_alpha_dummy_835 A), (nb090_alpha_dummy_837 v)),
                                      ((nb090_alpha_dummy_841 A), (nb090_alpha_dummy_842 v)),
                                      ((nb090_alpha_dummy_839 A), (nb090_alpha_dummy_840 v)),
                                      ((nb090_alpha_dummy_827 A), (nb090_alpha_dummy_828 v)),
                                      ((nb090_alpha_dummy_829 A), (nb090_alpha_dummy_830 v)),
                                      ((nb090_alpha_dummy_832 A), (nb090_alpha_dummy_834 v)),
                                      ((nb090_alpha_dummy_831 A), (nb090_alpha_dummy_833 v)),
                                      ((nb090_alpha_dummy_042 A),
                                        (nb090_alpha_dummy_044 v u h)),
                                      ((nb090_alpha_dummy_041 A),
                                        (nb090_alpha_dummy_043 v u h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
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

@[expose]
noncomputable def nb090_split_alpha_0095 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_869 A), (nb090_alpha_dummy_870 v)),
        ((nb090_alpha_dummy_867 A), (nb090_alpha_dummy_868 v)),
        ((nb090_alpha_dummy_836 A), (nb090_alpha_dummy_838 v)),
        ((nb090_alpha_dummy_835 A), (nb090_alpha_dummy_837 v)),
        ((nb090_alpha_dummy_865 A), (nb090_alpha_dummy_866 v)),
        ((nb090_alpha_dummy_839 A), (nb090_alpha_dummy_840 v)),
        ((nb090_alpha_dummy_827 A), (nb090_alpha_dummy_828 v)),
        ((nb090_alpha_dummy_829 A), (nb090_alpha_dummy_830 v)),
        ((nb090_alpha_dummy_832 A), (nb090_alpha_dummy_834 v)),
        ((nb090_alpha_dummy_831 A), (nb090_alpha_dummy_833 v)),
        ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_869 A))
          (syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_869 A))
            (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_870 v))
          (syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_870 v))
            (syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_836 A) ≠ (nb090_alpha_dummy_843 A) from (by
                      unfold nb090_alpha_dummy_843;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0894 A) 0))))
                  (show (nb090_alpha_dummy_838 v) ≠ (nb090_alpha_dummy_845 v) from (by
                      unfold nb090_alpha_dummy_845;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0895 v) 0))))
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_836 A) ≠ (nb090_alpha_dummy_844 A) from (by
                        unfold nb090_alpha_dummy_844;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0894 A) 1))))
                    (show (nb090_alpha_dummy_838 v) ≠ (nb090_alpha_dummy_846 v) from (by
                        unfold nb090_alpha_dummy_846;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0895 v) 1)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_836 A) ≠ (nb090_alpha_dummy_869 A) from (by
                          unfold nb090_alpha_dummy_869;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0924 A) 0))))
                      (show (nb090_alpha_dummy_838 v) ≠ (nb090_alpha_dummy_870 v) from (by
                          unfold nb090_alpha_dummy_870;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0925 v) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_836 A) ≠ (nb090_alpha_dummy_867 A) from (by
                            unfold nb090_alpha_dummy_867;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0922 A) 0))))
                        (show (nb090_alpha_dummy_838 v) ≠ (nb090_alpha_dummy_868 v) from (by
                            unfold nb090_alpha_dummy_868;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0923 v) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_836 A))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_838 v))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_843 A) ≠ (nb090_alpha_dummy_850 A) from
                                      (by
                                        unfold nb090_alpha_dummy_850;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0898 A)
                                                1)))) (show (nb090_alpha_dummy_845 v) ≠
                                        (nb090_alpha_dummy_853 v) from (by
                                        unfold nb090_alpha_dummy_853;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0899 v)
                                                1)))) (TAlphaVar.there (show
                                        (nb090_alpha_dummy_843 A) ≠ (nb090_alpha_dummy_849 A)
                                        from (by
                                          unfold nb090_alpha_dummy_849;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0898 A) 0)))) (show
                                        (nb090_alpha_dummy_845 v) ≠ (nb090_alpha_dummy_852 v)
                                        from (by
                                          unfold nb090_alpha_dummy_852;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0899 v) 0))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_843 A) ≠
        (nb090_alpha_dummy_847 A) from (by
          unfold nb090_alpha_dummy_847;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0896 A) 0)))) (show (nb090_alpha_dummy_845 v) ≠
        (nb090_alpha_dummy_848 v) from (by
          unfold nb090_alpha_dummy_848;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0897 v) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_851 A),
        (nb090_alpha_dummy_854 v)), ((nb090_alpha_dummy_850 A), (nb090_alpha_dummy_853 v)),
                                        ((nb090_alpha_dummy_849 A), (nb090_alpha_dummy_852 v)),
                                        ((nb090_alpha_dummy_847 A), (nb090_alpha_dummy_848 v)),
                                        ((nb090_alpha_dummy_843 A), (nb090_alpha_dummy_845 v)),
                                        ((nb090_alpha_dummy_844 A), (nb090_alpha_dummy_846 v)),
                                        ((nb090_alpha_dummy_869 A), (nb090_alpha_dummy_870 v)),
                                        ((nb090_alpha_dummy_867 A), (nb090_alpha_dummy_868 v)),
                                        ((nb090_alpha_dummy_836 A), (nb090_alpha_dummy_838 v)),
                                        ((nb090_alpha_dummy_835 A), (nb090_alpha_dummy_837 v)),
                                        ((nb090_alpha_dummy_865 A), (nb090_alpha_dummy_866 v)),
                                        ((nb090_alpha_dummy_839 A), (nb090_alpha_dummy_840 v)),
                                        ((nb090_alpha_dummy_827 A), (nb090_alpha_dummy_828 v)),
                                        ((nb090_alpha_dummy_829 A), (nb090_alpha_dummy_830 v)),
                                        ((nb090_alpha_dummy_832 A), (nb090_alpha_dummy_834 v)),
                                        ((nb090_alpha_dummy_831 A), (nb090_alpha_dummy_833 v)),
                                        ((nb090_alpha_dummy_042 A),
        (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
                                        ((nb090_alpha_dummy_002 A), v),
                                        ((nb090_alpha_dummy_001 A), u),
                                        ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_850 A) ≠ (nb090_alpha_dummy_857 A) from (by
          unfold
            nb090_alpha_dummy_857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0902
                    A)
                  0)))) (show (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_858 v) from (by
          unfold
            nb090_alpha_dummy_858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0903
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_850 A) ≠
        (nb090_alpha_dummy_855 A) from (by
          unfold
            nb090_alpha_dummy_855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0900
                    A)
                  0)))) (show (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_856 v) from (by
          unfold
            nb090_alpha_dummy_856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0901
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_843
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_851 A) ≠
        (nb090_alpha_dummy_857 A) from (by
          unfold
            nb090_alpha_dummy_857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0906
                    A)
                  0)))) (show (nb090_alpha_dummy_854 v) ≠ (nb090_alpha_dummy_858 v) from (by
          unfold
            nb090_alpha_dummy_858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0907
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_851 A) ≠
        (nb090_alpha_dummy_855 A) from (by
          unfold
            nb090_alpha_dummy_855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0904
                    A)
                  0)))) (show (nb090_alpha_dummy_854 v) ≠ (nb090_alpha_dummy_856 v) from (by
          unfold
            nb090_alpha_dummy_856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0905
                    v)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_850 A) ≠ (nb090_alpha_dummy_857 A) from (by
          unfold
            nb090_alpha_dummy_857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0902
                    A)
                  0)))) (show (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_858 v) from (by
          unfold
            nb090_alpha_dummy_858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0903
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_850 A) ≠
        (nb090_alpha_dummy_855 A) from (by
          unfold
            nb090_alpha_dummy_855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0900
                    A)
                  0)))) (show (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_856 v) from (by
          unfold
            nb090_alpha_dummy_856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0901
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_843
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_851 A) ≠
        (nb090_alpha_dummy_857 A) from (by
          unfold
            nb090_alpha_dummy_857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0906
                    A)
                  0)))) (show (nb090_alpha_dummy_854 v) ≠ (nb090_alpha_dummy_858 v) from (by
          unfold
            nb090_alpha_dummy_858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0907
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_851 A) ≠
        (nb090_alpha_dummy_855 A) from (by
          unfold
            nb090_alpha_dummy_855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0904
                    A)
                  0)))) (show (nb090_alpha_dummy_854 v) ≠ (nb090_alpha_dummy_856 v) from (by
          unfold
            nb090_alpha_dummy_856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0905
                    v)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb090_alpha_dummy_851 A), (nb090_alpha_dummy_854 v)),
        ((nb090_alpha_dummy_850 A), (nb090_alpha_dummy_853 v)), ((nb090_alpha_dummy_849 A),
        (nb090_alpha_dummy_852 v)), ((nb090_alpha_dummy_847 A), (nb090_alpha_dummy_848 v)),
        ((nb090_alpha_dummy_843 A), (nb090_alpha_dummy_845 v)), ((nb090_alpha_dummy_844 A),
        (nb090_alpha_dummy_846 v)), ((nb090_alpha_dummy_869 A), (nb090_alpha_dummy_870 v)),
        ((nb090_alpha_dummy_867 A), (nb090_alpha_dummy_868 v)), ((nb090_alpha_dummy_836 A),
        (nb090_alpha_dummy_838 v)), ((nb090_alpha_dummy_835 A), (nb090_alpha_dummy_837 v)),
        ((nb090_alpha_dummy_865 A), (nb090_alpha_dummy_866 v)), ((nb090_alpha_dummy_839 A),
        (nb090_alpha_dummy_840 v)), ((nb090_alpha_dummy_827 A), (nb090_alpha_dummy_828 v)),
        ((nb090_alpha_dummy_829 A), (nb090_alpha_dummy_830 v)), ((nb090_alpha_dummy_832 A),
        (nb090_alpha_dummy_834 v)), ((nb090_alpha_dummy_831 A), (nb090_alpha_dummy_833 v)),
        ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_843 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_843 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_850 A) ≠ (nb090_alpha_dummy_861 A) from (by
          unfold
            nb090_alpha_dummy_861;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0910
                    A)
                  0)))) (show (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_862 v) from (by
          unfold
            nb090_alpha_dummy_862;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0911
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_850 A) ≠
        (nb090_alpha_dummy_859 A) from (by
          unfold
            nb090_alpha_dummy_859;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0908
                    A)
                  0)))) (show (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_860 v) from (by
          unfold
            nb090_alpha_dummy_860;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0909
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_843
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_850 A) ≠
        (nb090_alpha_dummy_861 A) from (by
          unfold
            nb090_alpha_dummy_861;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0910
                    A)
                  0)))) (show (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_862 v) from (by
          unfold
            nb090_alpha_dummy_862;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0911
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_850 A) ≠
        (nb090_alpha_dummy_859 A) from (by
          unfold
            nb090_alpha_dummy_859;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0908
                    A)
                  0)))) (show (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_860 v) from (by
          unfold
            nb090_alpha_dummy_860;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0909
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_843
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_851 A) ≠ (nb090_alpha_dummy_863 A) from (by
          unfold
            nb090_alpha_dummy_863;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0914
                    A)
                  0)))) (show (nb090_alpha_dummy_854 v) ≠ (nb090_alpha_dummy_864 v) from (by
          unfold
            nb090_alpha_dummy_864;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0915
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_851 A) ≠
        (nb090_alpha_dummy_859 A) from (by
          unfold
            nb090_alpha_dummy_859;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0912
                    A)
                  0)))) (show (nb090_alpha_dummy_854 v) ≠ (nb090_alpha_dummy_860 v) from (by
          unfold
            nb090_alpha_dummy_860;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0913
                    v)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_851 A) ≠ (nb090_alpha_dummy_863 A) from (by
          unfold
            nb090_alpha_dummy_863;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0914
                    A)
                  0)))) (show (nb090_alpha_dummy_854 v) ≠ (nb090_alpha_dummy_864 v) from (by
          unfold
            nb090_alpha_dummy_864;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0915
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_851 A) ≠
        (nb090_alpha_dummy_859 A) from (by
          unfold
            nb090_alpha_dummy_859;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0912
                    A)
                  0)))) (show (nb090_alpha_dummy_854 v) ≠ (nb090_alpha_dummy_860 v) from (by
          unfold
            nb090_alpha_dummy_860;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0913
                    v)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_843 A) ≠ (nb090_alpha_dummy_847 A) from (by
                                unfold nb090_alpha_dummy_847;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0896 A) 0))))
                            (show (nb090_alpha_dummy_845 v) ≠ (nb090_alpha_dummy_848 v) from (by
                                unfold nb090_alpha_dummy_848;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0897 v) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb090_alpha_dummy_847 A), (nb090_alpha_dummy_848 v)),
                            ((nb090_alpha_dummy_843 A), (nb090_alpha_dummy_845 v)),
                            ((nb090_alpha_dummy_844 A), (nb090_alpha_dummy_846 v)),
                            ((nb090_alpha_dummy_869 A), (nb090_alpha_dummy_870 v)),
                            ((nb090_alpha_dummy_867 A), (nb090_alpha_dummy_868 v)),
                            ((nb090_alpha_dummy_836 A), (nb090_alpha_dummy_838 v)),
                            ((nb090_alpha_dummy_835 A), (nb090_alpha_dummy_837 v)),
                            ((nb090_alpha_dummy_865 A), (nb090_alpha_dummy_866 v)),
                            ((nb090_alpha_dummy_839 A), (nb090_alpha_dummy_840 v)),
                            ((nb090_alpha_dummy_827 A), (nb090_alpha_dummy_828 v)),
                            ((nb090_alpha_dummy_829 A), (nb090_alpha_dummy_830 v)),
                            ((nb090_alpha_dummy_832 A), (nb090_alpha_dummy_834 v)),
                            ((nb090_alpha_dummy_831 A), (nb090_alpha_dummy_833 v)),
                            ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
                            ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                            ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                            ((nb090_alpha_dummy_001 A), u),
                            ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_843 A) ≠ (nb090_alpha_dummy_847 A) from (by
                              unfold nb090_alpha_dummy_847;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0896 A) 0))))
                          (show (nb090_alpha_dummy_845 v) ≠ (nb090_alpha_dummy_848 v) from (by
                              unfold nb090_alpha_dummy_848;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0897 v) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_843 A) ≠ (nb090_alpha_dummy_847 A) from (by
                                unfold nb090_alpha_dummy_847;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0896 A) 0))))
                            (show (nb090_alpha_dummy_845 v) ≠ (nb090_alpha_dummy_848 v) from (by
                                unfold nb090_alpha_dummy_848;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0897 v) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb090_alpha_dummy_847 A), (nb090_alpha_dummy_848 v)),
                            ((nb090_alpha_dummy_843 A), (nb090_alpha_dummy_845 v)),
                            ((nb090_alpha_dummy_844 A), (nb090_alpha_dummy_846 v)),
                            ((nb090_alpha_dummy_869 A), (nb090_alpha_dummy_870 v)),
                            ((nb090_alpha_dummy_867 A), (nb090_alpha_dummy_868 v)),
                            ((nb090_alpha_dummy_836 A), (nb090_alpha_dummy_838 v)),
                            ((nb090_alpha_dummy_835 A), (nb090_alpha_dummy_837 v)),
                            ((nb090_alpha_dummy_865 A), (nb090_alpha_dummy_866 v)),
                            ((nb090_alpha_dummy_839 A), (nb090_alpha_dummy_840 v)),
                            ((nb090_alpha_dummy_827 A), (nb090_alpha_dummy_828 v)),
                            ((nb090_alpha_dummy_829 A), (nb090_alpha_dummy_830 v)),
                            ((nb090_alpha_dummy_832 A), (nb090_alpha_dummy_834 v)),
                            ((nb090_alpha_dummy_831 A), (nb090_alpha_dummy_833 v)),
                            ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
                            ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                            ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                            ((nb090_alpha_dummy_001 A), u),
                            ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb090_alpha_dummy_836 A) ≠ (nb090_alpha_dummy_843 A) from (by
                        unfold nb090_alpha_dummy_843;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0894 A) 0))))
                    (show (nb090_alpha_dummy_838 v) ≠ (nb090_alpha_dummy_845 v) from (by
                        unfold nb090_alpha_dummy_845;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0895 v) 0)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_836 A) ≠ (nb090_alpha_dummy_844 A) from (by
                          unfold nb090_alpha_dummy_844;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0894 A) 1))))
                      (show (nb090_alpha_dummy_838 v) ≠ (nb090_alpha_dummy_846 v) from (by
                          unfold nb090_alpha_dummy_846;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0895 v) 1))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_836 A) ≠ (nb090_alpha_dummy_869 A) from (by
                            unfold nb090_alpha_dummy_869;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0924 A) 0))))
                        (show (nb090_alpha_dummy_838 v) ≠ (nb090_alpha_dummy_870 v) from (by
                            unfold nb090_alpha_dummy_870;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0925 v) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_836 A) ≠ (nb090_alpha_dummy_867 A) from (by
                              unfold nb090_alpha_dummy_867;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0922 A) 0))))
                          (show (nb090_alpha_dummy_838 v) ≠ (nb090_alpha_dummy_868 v) from (by
                              unfold nb090_alpha_dummy_868;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0923 v) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_836 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_838 v))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb090_alpha_dummy_843 A) ≠
        (nb090_alpha_dummy_850 A) from (by
                                          unfold nb090_alpha_dummy_850;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0898 A) 1)))) (show
                                        (nb090_alpha_dummy_845 v) ≠ (nb090_alpha_dummy_853 v)
                                        from (by
                                          unfold nb090_alpha_dummy_853;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0899 v) 1))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_843 A) ≠
        (nb090_alpha_dummy_849 A) from (by
          unfold nb090_alpha_dummy_849;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0898 A) 0)))) (show (nb090_alpha_dummy_845 v) ≠
        (nb090_alpha_dummy_852 v) from (by
          unfold nb090_alpha_dummy_852;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0899 v) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_843 A) ≠ (nb090_alpha_dummy_847 A) from (by
          unfold nb090_alpha_dummy_847;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0896 A) 0)))) (show (nb090_alpha_dummy_845 v) ≠
        (nb090_alpha_dummy_848 v) from (by
          unfold nb090_alpha_dummy_848;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0897 v) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_851 A),
        (nb090_alpha_dummy_854 v)), ((nb090_alpha_dummy_850 A), (nb090_alpha_dummy_853 v)),
        ((nb090_alpha_dummy_849 A), (nb090_alpha_dummy_852 v)), ((nb090_alpha_dummy_847 A),
        (nb090_alpha_dummy_848 v)), ((nb090_alpha_dummy_843 A), (nb090_alpha_dummy_845 v)),
        ((nb090_alpha_dummy_844 A), (nb090_alpha_dummy_846 v)), ((nb090_alpha_dummy_869 A),
        (nb090_alpha_dummy_870 v)), ((nb090_alpha_dummy_867 A), (nb090_alpha_dummy_868 v)),
        ((nb090_alpha_dummy_836 A), (nb090_alpha_dummy_838 v)), ((nb090_alpha_dummy_835 A),
        (nb090_alpha_dummy_837 v)), ((nb090_alpha_dummy_865 A), (nb090_alpha_dummy_866 v)),
        ((nb090_alpha_dummy_839 A), (nb090_alpha_dummy_840 v)), ((nb090_alpha_dummy_827 A),
        (nb090_alpha_dummy_828 v)), ((nb090_alpha_dummy_829 A), (nb090_alpha_dummy_830 v)),
        ((nb090_alpha_dummy_832 A), (nb090_alpha_dummy_834 v)), ((nb090_alpha_dummy_831 A),
        (nb090_alpha_dummy_833 v)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_850 A) ≠ (nb090_alpha_dummy_857 A) from (by
          unfold
            nb090_alpha_dummy_857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0902
                    A)
                  0)))) (show (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_858 v) from (by
          unfold
            nb090_alpha_dummy_858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0903
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_850 A) ≠
        (nb090_alpha_dummy_855 A) from (by
          unfold
            nb090_alpha_dummy_855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0900
                    A)
                  0)))) (show (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_856 v) from (by
          unfold
            nb090_alpha_dummy_856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0901
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_843
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_851 A) ≠ (nb090_alpha_dummy_857 A) from (by
          unfold
            nb090_alpha_dummy_857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0906
                    A)
                  0)))) (show (nb090_alpha_dummy_854 v) ≠ (nb090_alpha_dummy_858 v) from (by
          unfold
            nb090_alpha_dummy_858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0907
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_851 A) ≠
        (nb090_alpha_dummy_855 A) from (by
          unfold
            nb090_alpha_dummy_855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0904
                    A)
                  0)))) (show (nb090_alpha_dummy_854 v) ≠ (nb090_alpha_dummy_856 v) from (by
          unfold
            nb090_alpha_dummy_856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0905
                    v)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_850 A) ≠ (nb090_alpha_dummy_857 A) from (by
          unfold
            nb090_alpha_dummy_857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0902
                    A)
                  0)))) (show (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_858 v) from (by
          unfold
            nb090_alpha_dummy_858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0903
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_850 A) ≠
        (nb090_alpha_dummy_855 A) from (by
          unfold
            nb090_alpha_dummy_855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0900
                    A)
                  0)))) (show (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_856 v) from (by
          unfold
            nb090_alpha_dummy_856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0901
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_843
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_851 A) ≠ (nb090_alpha_dummy_857 A) from (by
          unfold
            nb090_alpha_dummy_857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0906
                    A)
                  0)))) (show (nb090_alpha_dummy_854 v) ≠ (nb090_alpha_dummy_858 v) from (by
          unfold
            nb090_alpha_dummy_858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0907
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_851 A) ≠
        (nb090_alpha_dummy_855 A) from (by
          unfold
            nb090_alpha_dummy_855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0904
                    A)
                  0)))) (show (nb090_alpha_dummy_854 v) ≠ (nb090_alpha_dummy_856 v) from (by
          unfold
            nb090_alpha_dummy_856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0905
                    v)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_851 A), (nb090_alpha_dummy_854 v)), ((nb090_alpha_dummy_850 A),
        (nb090_alpha_dummy_853 v)), ((nb090_alpha_dummy_849 A), (nb090_alpha_dummy_852 v)),
        ((nb090_alpha_dummy_847 A), (nb090_alpha_dummy_848 v)), ((nb090_alpha_dummy_843 A),
        (nb090_alpha_dummy_845 v)), ((nb090_alpha_dummy_844 A), (nb090_alpha_dummy_846 v)),
        ((nb090_alpha_dummy_869 A), (nb090_alpha_dummy_870 v)), ((nb090_alpha_dummy_867 A),
        (nb090_alpha_dummy_868 v)), ((nb090_alpha_dummy_836 A), (nb090_alpha_dummy_838 v)),
        ((nb090_alpha_dummy_835 A), (nb090_alpha_dummy_837 v)), ((nb090_alpha_dummy_865 A),
        (nb090_alpha_dummy_866 v)), ((nb090_alpha_dummy_839 A), (nb090_alpha_dummy_840 v)),
        ((nb090_alpha_dummy_827 A), (nb090_alpha_dummy_828 v)), ((nb090_alpha_dummy_829 A),
        (nb090_alpha_dummy_830 v)), ((nb090_alpha_dummy_832 A), (nb090_alpha_dummy_834 v)),
        ((nb090_alpha_dummy_831 A), (nb090_alpha_dummy_833 v)), ((nb090_alpha_dummy_042 A),
        (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_843 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_843 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_850 A) ≠ (nb090_alpha_dummy_861 A) from (by
          unfold
            nb090_alpha_dummy_861;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0910
                    A)
                  0)))) (show (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_862 v) from (by
          unfold
            nb090_alpha_dummy_862;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0911
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_850 A) ≠
        (nb090_alpha_dummy_859 A) from (by
          unfold
            nb090_alpha_dummy_859;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0908
                    A)
                  0)))) (show (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_860 v) from (by
          unfold
            nb090_alpha_dummy_860;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0909
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_843
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_850 A) ≠ (nb090_alpha_dummy_861 A) from (by
          unfold
            nb090_alpha_dummy_861;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0910
                    A)
                  0)))) (show (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_862 v) from (by
          unfold
            nb090_alpha_dummy_862;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0911
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_850 A) ≠
        (nb090_alpha_dummy_859 A) from (by
          unfold
            nb090_alpha_dummy_859;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0908
                    A)
                  0)))) (show (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_860 v) from (by
          unfold
            nb090_alpha_dummy_860;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0909
                    v)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_843
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_851 A) ≠ (nb090_alpha_dummy_863 A) from (by
          unfold
            nb090_alpha_dummy_863;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0914
                    A)
                  0)))) (show (nb090_alpha_dummy_854 v) ≠ (nb090_alpha_dummy_864 v) from (by
          unfold
            nb090_alpha_dummy_864;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0915
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_851 A) ≠
        (nb090_alpha_dummy_859 A) from (by
          unfold
            nb090_alpha_dummy_859;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0912
                    A)
                  0)))) (show (nb090_alpha_dummy_854 v) ≠ (nb090_alpha_dummy_860 v) from (by
          unfold
            nb090_alpha_dummy_860;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0913
                    v)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_851 A) ≠ (nb090_alpha_dummy_863 A) from (by
          unfold
            nb090_alpha_dummy_863;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0914
                    A)
                  0)))) (show (nb090_alpha_dummy_854 v) ≠ (nb090_alpha_dummy_864 v) from (by
          unfold
            nb090_alpha_dummy_864;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0915
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_851 A) ≠
        (nb090_alpha_dummy_859 A) from (by
          unfold
            nb090_alpha_dummy_859;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0912
                    A)
                  0)))) (show (nb090_alpha_dummy_854 v) ≠ (nb090_alpha_dummy_860 v) from (by
          unfold
            nb090_alpha_dummy_860;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0913
                    v)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090_alpha_dummy_843 A) ≠ (nb090_alpha_dummy_847 A) from
                                (by
                                  unfold nb090_alpha_dummy_847;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0896 A) 0))))
                              (show (nb090_alpha_dummy_845 v) ≠ (nb090_alpha_dummy_848 v) from
                                (by
                                  unfold nb090_alpha_dummy_848;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0897 v) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb090_alpha_dummy_847 A), (nb090_alpha_dummy_848 v)),
                              ((nb090_alpha_dummy_843 A), (nb090_alpha_dummy_845 v)),
                              ((nb090_alpha_dummy_844 A), (nb090_alpha_dummy_846 v)),
                              ((nb090_alpha_dummy_869 A), (nb090_alpha_dummy_870 v)),
                              ((nb090_alpha_dummy_867 A), (nb090_alpha_dummy_868 v)),
                              ((nb090_alpha_dummy_836 A), (nb090_alpha_dummy_838 v)),
                              ((nb090_alpha_dummy_835 A), (nb090_alpha_dummy_837 v)),
                              ((nb090_alpha_dummy_865 A), (nb090_alpha_dummy_866 v)),
                              ((nb090_alpha_dummy_839 A), (nb090_alpha_dummy_840 v)),
                              ((nb090_alpha_dummy_827 A), (nb090_alpha_dummy_828 v)),
                              ((nb090_alpha_dummy_829 A), (nb090_alpha_dummy_830 v)),
                              ((nb090_alpha_dummy_832 A), (nb090_alpha_dummy_834 v)),
                              ((nb090_alpha_dummy_831 A), (nb090_alpha_dummy_833 v)),
                              ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
                              ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                              ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                              ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                (nb090_alpha_dummy_004 v u A h))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_843 A) ≠ (nb090_alpha_dummy_847 A) from (by
                                unfold nb090_alpha_dummy_847;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0896 A) 0))))
                            (show (nb090_alpha_dummy_845 v) ≠ (nb090_alpha_dummy_848 v) from (by
                                unfold nb090_alpha_dummy_848;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0897 v) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090_alpha_dummy_843 A) ≠ (nb090_alpha_dummy_847 A) from
                                (by
                                  unfold nb090_alpha_dummy_847;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0896 A) 0))))
                              (show (nb090_alpha_dummy_845 v) ≠ (nb090_alpha_dummy_848 v) from
                                (by
                                  unfold nb090_alpha_dummy_848;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0897 v) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb090_alpha_dummy_847 A), (nb090_alpha_dummy_848 v)),
                              ((nb090_alpha_dummy_843 A), (nb090_alpha_dummy_845 v)),
                              ((nb090_alpha_dummy_844 A), (nb090_alpha_dummy_846 v)),
                              ((nb090_alpha_dummy_869 A), (nb090_alpha_dummy_870 v)),
                              ((nb090_alpha_dummy_867 A), (nb090_alpha_dummy_868 v)),
                              ((nb090_alpha_dummy_836 A), (nb090_alpha_dummy_838 v)),
                              ((nb090_alpha_dummy_835 A), (nb090_alpha_dummy_837 v)),
                              ((nb090_alpha_dummy_865 A), (nb090_alpha_dummy_866 v)),
                              ((nb090_alpha_dummy_839 A), (nb090_alpha_dummy_840 v)),
                              ((nb090_alpha_dummy_827 A), (nb090_alpha_dummy_828 v)),
                              ((nb090_alpha_dummy_829 A), (nb090_alpha_dummy_830 v)),
                              ((nb090_alpha_dummy_832 A), (nb090_alpha_dummy_834 v)),
                              ((nb090_alpha_dummy_831 A), (nb090_alpha_dummy_833 v)),
                              ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
                              ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                              ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                              ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                (nb090_alpha_dummy_004 v u A h))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

theorem nb090_wpp_notmem_2250 (A : Class) : (nb090_alpha_dummy_827 A) ∉ ((syn_c1st)).fv :=
  by simpa only [nb090_alpha_dummy_827, fv_syn_c1st] using (nb090_compact_fv_empty_0640 A)

theorem nb090_wpp_notmem_2251 (v : Var) : (nb090_alpha_dummy_828 v) ∉ ((syn_c1st)).fv :=
  by simpa only [nb090_alpha_dummy_828, fv_syn_c1st] using (nb090_compact_fv_empty_0641 v)

theorem nb090_wpp_notmem_2252 (A : Class) : (nb090_alpha_dummy_829 A) ∉ ((syn_c1st)).fv :=
  by simpa only [nb090_alpha_dummy_829, fv_syn_c1st] using (nb090_compact_fv_empty_0642 A)

theorem nb090_wpp_notmem_2253 (v : Var) : (nb090_alpha_dummy_830 v) ∉ ((syn_c1st)).fv :=
  by simpa only [nb090_alpha_dummy_830, fv_syn_c1st] using (nb090_compact_fv_empty_0643 v)

theorem nb090_wpp_notmem_2254 (A : Class) : (nb090_alpha_dummy_832 A) ∉ ((syn_c1st)).fv :=
  by simpa only [nb090_alpha_dummy_832, fv_syn_c1st] using (nb090_compact_fv_empty_0644 A)

theorem nb090_wpp_notmem_2255 (v : Var) : (nb090_alpha_dummy_834 v) ∉ ((syn_c1st)).fv :=
  by simpa only [nb090_alpha_dummy_834, fv_syn_c1st] using (nb090_compact_fv_empty_0645 v)

theorem nb090_wpp_notmem_2256 (A : Class) : (nb090_alpha_dummy_831 A) ∉ ((syn_c1st)).fv :=
  by simpa only [nb090_alpha_dummy_831, fv_syn_c1st] using (nb090_compact_fv_empty_0646 A)

theorem nb090_wpp_notmem_2257 (v : Var) : (nb090_alpha_dummy_833 v) ∉ ((syn_c1st)).fv :=
  by simpa only [nb090_alpha_dummy_833, fv_syn_c1st] using (nb090_compact_fv_empty_0647 v)

theorem nb090_compact_envfresh_0327 (v : Var) (u : Var) (A : Class) (h : Var) :
    TEnvFresh
      [((nb090_alpha_dummy_827 A), (nb090_alpha_dummy_828 v)),
        ((nb090_alpha_dummy_829 A), (nb090_alpha_dummy_830 v)),
        ((nb090_alpha_dummy_832 A), (nb090_alpha_dummy_834 v)),
        ((nb090_alpha_dummy_831 A), (nb090_alpha_dummy_833 v)),
        ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      ((syn_c1st)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb090_alpha_dummy_827 A) (nb090_alpha_dummy_828 v)
      (nb090_wpp_notmem_2250 A) (nb090_wpp_notmem_2251 v)
      (TEnvFresh.consFresh (nb090_alpha_dummy_829 A) (nb090_alpha_dummy_830 v)
        (nb090_wpp_notmem_2252 A) (nb090_wpp_notmem_2253 v)
        (TEnvFresh.consFresh (nb090_alpha_dummy_832 A) (nb090_alpha_dummy_834 v)
          (nb090_wpp_notmem_2254 A) (nb090_wpp_notmem_2255 v)
          (TEnvFresh.consFresh (nb090_alpha_dummy_831 A) (nb090_alpha_dummy_833 v)
            (nb090_wpp_notmem_2256 A) (nb090_wpp_notmem_2257 v)
            (TEnvFresh.consFresh (nb090_alpha_dummy_042 A) (nb090_alpha_dummy_044 v u h)
              (nb090_wpp_notmem_1812 A) (nb090_wpp_notmem_1813 v u h)
              (TEnvFresh.consFresh (nb090_alpha_dummy_041 A) (nb090_alpha_dummy_043 v u h)
                (nb090_wpp_notmem_1814 A) (nb090_wpp_notmem_1815 v u h)
                (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_1816 A)
                  (nb090_wpp_notmem_1817 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v
                    (nb090_wpp_notmem_1818 A) (nb090_wpp_notmem_1819 v)
                    (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u
                      (nb090_wpp_notmem_1820 A) (nb090_wpp_notmem_1821 u)
                      (TEnvFresh.consFresh (nb090_alpha_dummy_003 A)
                        (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_1822 A)
                        (nb090_wpp_notmem_1823 v u A h)
                        (TEnvFresh.nil ((syn_c1st)).fv)))))))))))

@[expose]
noncomputable def nb090_wpp_refl_0327 (v : Var) (u : Var) (A : Class) (h : Var) :
    TReflOn
      [((nb090_alpha_dummy_827 A), (nb090_alpha_dummy_828 v)),
        ((nb090_alpha_dummy_829 A), (nb090_alpha_dummy_830 v)),
        ((nb090_alpha_dummy_832 A), (nb090_alpha_dummy_834 v)),
        ((nb090_alpha_dummy_831 A), (nb090_alpha_dummy_833 v)),
        ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      ((syn_c1st)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0327 v u A h)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
