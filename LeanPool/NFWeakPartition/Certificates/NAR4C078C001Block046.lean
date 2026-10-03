/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block045

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part138`. -/


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
noncomputable def nb078_split_alpha_0116 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_843), (nb078_alpha_dummy_844 h)),
        ((nb078_alpha_dummy_812), (nb078_alpha_dummy_814 h)),
        ((nb078_alpha_dummy_811), (nb078_alpha_dummy_813 h)),
        ((nb078_alpha_dummy_841), (nb078_alpha_dummy_842 h)),
        ((nb078_alpha_dummy_815), (nb078_alpha_dummy_816 h)),
        ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
        ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
        ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb078_alpha_dummy_843))
            (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_812)))))
          (Wff.classMem (Class.cv (nb078_alpha_dummy_843)) (syn_ccompl (syn_csn (syn_c0c))))))
      (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb078_alpha_dummy_844 h))
            (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))))
          (Wff.classMem (Class.cv (nb078_alpha_dummy_844 h))
            (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_812) ≠ (nb078_alpha_dummy_819) from (by
                                unfold nb078_alpha_dummy_819;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0846) 0))))
                            (show (nb078_alpha_dummy_814 h) ≠ (nb078_alpha_dummy_821 h) from (by
                                unfold nb078_alpha_dummy_821;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0847 h) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_812) ≠ (nb078_alpha_dummy_820) from (by
                                  unfold nb078_alpha_dummy_820;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0846) 1))))
                              (show (nb078_alpha_dummy_814 h) ≠ (nb078_alpha_dummy_822 h) from
                                (by
                                  unfold nb078_alpha_dummy_822;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0847 h) 1))))
                              (TAlphaVar.there
                                (show (nb078_alpha_dummy_812) ≠ (nb078_alpha_dummy_845) from (by
                                    unfold nb078_alpha_dummy_845;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0876) 0)))) (show
                                  (nb078_alpha_dummy_814 h) ≠ (nb078_alpha_dummy_846 h) from (by
                                    unfold nb078_alpha_dummy_846;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0877 h)
                                            0)))) (TAlphaVar.there
                                  (show (nb078_alpha_dummy_812) ≠ (nb078_alpha_dummy_843) from
                                    (by
                                      unfold nb078_alpha_dummy_843;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0874)
                                              0)))) (show
                                    (nb078_alpha_dummy_814 h) ≠ (nb078_alpha_dummy_844 h) from
                                    (by
                                      unfold nb078_alpha_dummy_844;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0875 h)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_812))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_814 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_819) ≠ (nb078_alpha_dummy_826) from (by
          unfold nb078_alpha_dummy_826;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0850) 1)))) (show (nb078_alpha_dummy_821 h) ≠
        (nb078_alpha_dummy_829 h) from (by
          unfold nb078_alpha_dummy_829;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0851 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_819) ≠ (nb078_alpha_dummy_825) from (by
          unfold nb078_alpha_dummy_825;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0850) 0)))) (show (nb078_alpha_dummy_821 h) ≠
        (nb078_alpha_dummy_828 h) from (by
          unfold nb078_alpha_dummy_828;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0851 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_819) ≠ (nb078_alpha_dummy_823)
        from (by
          unfold nb078_alpha_dummy_823;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0848)
                  0)))) (show (nb078_alpha_dummy_821 h) ≠ (nb078_alpha_dummy_824 h) from (by
          unfold nb078_alpha_dummy_824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0849 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_827), (nb078_alpha_dummy_830 h)), ((nb078_alpha_dummy_826),
        (nb078_alpha_dummy_829 h)), ((nb078_alpha_dummy_825), (nb078_alpha_dummy_828 h)),
        ((nb078_alpha_dummy_823), (nb078_alpha_dummy_824 h)), ((nb078_alpha_dummy_819),
        (nb078_alpha_dummy_821 h)), ((nb078_alpha_dummy_820), (nb078_alpha_dummy_822 h)),
        ((nb078_alpha_dummy_845), (nb078_alpha_dummy_846 h)), ((nb078_alpha_dummy_843),
        (nb078_alpha_dummy_844 h)), ((nb078_alpha_dummy_812), (nb078_alpha_dummy_814 h)),
        ((nb078_alpha_dummy_811), (nb078_alpha_dummy_813 h)), ((nb078_alpha_dummy_841),
        (nb078_alpha_dummy_842 h)), ((nb078_alpha_dummy_815), (nb078_alpha_dummy_816 h)),
        ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768),
        (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
        ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_826) ≠ (nb078_alpha_dummy_833) from (by
          unfold
            nb078_alpha_dummy_833;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0854)
                  0)))) (show (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_834 h) from (by
          unfold
            nb078_alpha_dummy_834;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0855
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_826) ≠ (nb078_alpha_dummy_831)
        from (by
          unfold
            nb078_alpha_dummy_831;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0852)
                  0)))) (show (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_832 h) from (by
          unfold
            nb078_alpha_dummy_832;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0853
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_827) ≠ (nb078_alpha_dummy_833)
        from (by
          unfold
            nb078_alpha_dummy_833;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0858)
                  0)))) (show (nb078_alpha_dummy_830 h) ≠ (nb078_alpha_dummy_834 h) from (by
          unfold
            nb078_alpha_dummy_834;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0859
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_827) ≠ (nb078_alpha_dummy_831)
        from (by
          unfold
            nb078_alpha_dummy_831;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0856)
                  0)))) (show (nb078_alpha_dummy_830 h) ≠ (nb078_alpha_dummy_832 h) from (by
          unfold
            nb078_alpha_dummy_832;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0857
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_826) ≠ (nb078_alpha_dummy_833) from (by
          unfold
            nb078_alpha_dummy_833;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0854)
                  0)))) (show (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_834 h) from (by
          unfold
            nb078_alpha_dummy_834;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0855
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_826) ≠ (nb078_alpha_dummy_831)
        from (by
          unfold
            nb078_alpha_dummy_831;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0852)
                  0)))) (show (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_832 h) from (by
          unfold
            nb078_alpha_dummy_832;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0853
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_827) ≠ (nb078_alpha_dummy_833)
        from (by
          unfold
            nb078_alpha_dummy_833;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0858)
                  0)))) (show (nb078_alpha_dummy_830 h) ≠ (nb078_alpha_dummy_834 h) from (by
          unfold
            nb078_alpha_dummy_834;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0859
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_827) ≠ (nb078_alpha_dummy_831)
        from (by
          unfold
            nb078_alpha_dummy_831;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0856)
                  0)))) (show (nb078_alpha_dummy_830 h) ≠ (nb078_alpha_dummy_832 h) from (by
          unfold
            nb078_alpha_dummy_832;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0857
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_827), (nb078_alpha_dummy_830 h)), ((nb078_alpha_dummy_826),
        (nb078_alpha_dummy_829 h)), ((nb078_alpha_dummy_825), (nb078_alpha_dummy_828 h)),
        ((nb078_alpha_dummy_823), (nb078_alpha_dummy_824 h)), ((nb078_alpha_dummy_819),
        (nb078_alpha_dummy_821 h)), ((nb078_alpha_dummy_820), (nb078_alpha_dummy_822 h)),
        ((nb078_alpha_dummy_845), (nb078_alpha_dummy_846 h)), ((nb078_alpha_dummy_843),
        (nb078_alpha_dummy_844 h)), ((nb078_alpha_dummy_812), (nb078_alpha_dummy_814 h)),
        ((nb078_alpha_dummy_811), (nb078_alpha_dummy_813 h)), ((nb078_alpha_dummy_841),
        (nb078_alpha_dummy_842 h)), ((nb078_alpha_dummy_815), (nb078_alpha_dummy_816 h)),
        ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768),
        (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
        ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_819))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_821
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_826) ≠
        (nb078_alpha_dummy_837) from (by
          unfold
            nb078_alpha_dummy_837;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0862)
                  0)))) (show (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_838 h) from (by
          unfold
            nb078_alpha_dummy_838;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0863
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_826) ≠ (nb078_alpha_dummy_835)
        from (by
          unfold
            nb078_alpha_dummy_835;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0860)
                  0)))) (show (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_836 h) from (by
          unfold
            nb078_alpha_dummy_836;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0861
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_826) ≠ (nb078_alpha_dummy_837)
        from (by
          unfold
            nb078_alpha_dummy_837;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0862)
                  0)))) (show (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_838 h) from (by
          unfold
            nb078_alpha_dummy_838;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0863
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_826) ≠ (nb078_alpha_dummy_835)
        from (by
          unfold
            nb078_alpha_dummy_835;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0860)
                  0)))) (show (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_836 h) from (by
          unfold
            nb078_alpha_dummy_836;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0861
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_827) ≠ (nb078_alpha_dummy_839) from (by
          unfold
            nb078_alpha_dummy_839;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0866)
                  0)))) (show (nb078_alpha_dummy_830 h) ≠ (nb078_alpha_dummy_840 h) from (by
          unfold
            nb078_alpha_dummy_840;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0867
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_827) ≠ (nb078_alpha_dummy_835)
        from (by
          unfold
            nb078_alpha_dummy_835;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0864)
                  0)))) (show (nb078_alpha_dummy_830 h) ≠ (nb078_alpha_dummy_836 h) from (by
          unfold
            nb078_alpha_dummy_836;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0865
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_827) ≠
        (nb078_alpha_dummy_839) from (by
          unfold
            nb078_alpha_dummy_839;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0866)
                  0)))) (show (nb078_alpha_dummy_830 h) ≠ (nb078_alpha_dummy_840 h) from (by
          unfold
            nb078_alpha_dummy_840;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0867
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_827) ≠ (nb078_alpha_dummy_835)
        from (by
          unfold
            nb078_alpha_dummy_835;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0864)
                  0)))) (show (nb078_alpha_dummy_830 h) ≠ (nb078_alpha_dummy_836 h) from (by
          unfold
            nb078_alpha_dummy_836;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0865
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_819) ≠ (nb078_alpha_dummy_823) from
                                        (by
                                          unfold nb078_alpha_dummy_823;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0848)
                                                  0)))) (show (nb078_alpha_dummy_821 h) ≠
        (nb078_alpha_dummy_824 h) from (by
                                          unfold nb078_alpha_dummy_824;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0849 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_823), (nb078_alpha_dummy_824 h)),
                                      ((nb078_alpha_dummy_819), (nb078_alpha_dummy_821 h)),
                                      ((nb078_alpha_dummy_820), (nb078_alpha_dummy_822 h)),
                                      ((nb078_alpha_dummy_845), (nb078_alpha_dummy_846 h)),
                                      ((nb078_alpha_dummy_843), (nb078_alpha_dummy_844 h)),
                                      ((nb078_alpha_dummy_812), (nb078_alpha_dummy_814 h)),
                                      ((nb078_alpha_dummy_811), (nb078_alpha_dummy_813 h)),
                                      ((nb078_alpha_dummy_841), (nb078_alpha_dummy_842 h)),
                                      ((nb078_alpha_dummy_815), (nb078_alpha_dummy_816 h)),
                                      ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
                                      ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                                      ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                                      ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
                                      ((nb078_alpha_dummy_002), h),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_819) ≠ (nb078_alpha_dummy_823) from (by
                                        unfold nb078_alpha_dummy_823;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0848)
                                                0)))) (show (nb078_alpha_dummy_821 h) ≠
                                        (nb078_alpha_dummy_824 h) from (by
                                        unfold nb078_alpha_dummy_824;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0849 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_819) ≠ (nb078_alpha_dummy_823) from
                                        (by
                                          unfold nb078_alpha_dummy_823;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0848)
                                                  0)))) (show (nb078_alpha_dummy_821 h) ≠
        (nb078_alpha_dummy_824 h) from (by
                                          unfold nb078_alpha_dummy_824;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0849 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_823), (nb078_alpha_dummy_824 h)),
                                      ((nb078_alpha_dummy_819), (nb078_alpha_dummy_821 h)),
                                      ((nb078_alpha_dummy_820), (nb078_alpha_dummy_822 h)),
                                      ((nb078_alpha_dummy_845), (nb078_alpha_dummy_846 h)),
                                      ((nb078_alpha_dummy_843), (nb078_alpha_dummy_844 h)),
                                      ((nb078_alpha_dummy_812), (nb078_alpha_dummy_814 h)),
                                      ((nb078_alpha_dummy_811), (nb078_alpha_dummy_813 h)),
                                      ((nb078_alpha_dummy_841), (nb078_alpha_dummy_842 h)),
                                      ((nb078_alpha_dummy_815), (nb078_alpha_dummy_816 h)),
                                      ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
                                      ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                                      ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                                      ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
                                      ((nb078_alpha_dummy_002), h),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_812) ≠ (nb078_alpha_dummy_819) from (by
                                unfold nb078_alpha_dummy_819;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0846) 0))))
                            (show (nb078_alpha_dummy_814 h) ≠ (nb078_alpha_dummy_821 h) from (by
                                unfold nb078_alpha_dummy_821;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0847 h) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_812) ≠ (nb078_alpha_dummy_820) from (by
                                  unfold nb078_alpha_dummy_820;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0846) 1))))
                              (show (nb078_alpha_dummy_814 h) ≠ (nb078_alpha_dummy_822 h) from
                                (by
                                  unfold nb078_alpha_dummy_822;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0847 h) 1))))
                              (TAlphaVar.there
                                (show (nb078_alpha_dummy_812) ≠ (nb078_alpha_dummy_845) from (by
                                    unfold nb078_alpha_dummy_845;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0876) 0)))) (show
                                  (nb078_alpha_dummy_814 h) ≠ (nb078_alpha_dummy_846 h) from (by
                                    unfold nb078_alpha_dummy_846;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0877 h)
                                            0)))) (TAlphaVar.there
                                  (show (nb078_alpha_dummy_812) ≠ (nb078_alpha_dummy_843) from
                                    (by
                                      unfold nb078_alpha_dummy_843;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0874)
                                              0)))) (show
                                    (nb078_alpha_dummy_814 h) ≠ (nb078_alpha_dummy_844 h) from
                                    (by
                                      unfold nb078_alpha_dummy_844;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0875 h)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_812))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_814 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_819) ≠ (nb078_alpha_dummy_826) from (by
          unfold nb078_alpha_dummy_826;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0850) 1)))) (show (nb078_alpha_dummy_821 h) ≠
        (nb078_alpha_dummy_829 h) from (by
          unfold nb078_alpha_dummy_829;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0851 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_819) ≠ (nb078_alpha_dummy_825) from (by
          unfold nb078_alpha_dummy_825;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0850) 0)))) (show (nb078_alpha_dummy_821 h) ≠
        (nb078_alpha_dummy_828 h) from (by
          unfold nb078_alpha_dummy_828;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0851 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_819) ≠ (nb078_alpha_dummy_823)
        from (by
          unfold nb078_alpha_dummy_823;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0848)
                  0)))) (show (nb078_alpha_dummy_821 h) ≠ (nb078_alpha_dummy_824 h) from (by
          unfold nb078_alpha_dummy_824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0849 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_827), (nb078_alpha_dummy_830 h)), ((nb078_alpha_dummy_826),
        (nb078_alpha_dummy_829 h)), ((nb078_alpha_dummy_825), (nb078_alpha_dummy_828 h)),
        ((nb078_alpha_dummy_823), (nb078_alpha_dummy_824 h)), ((nb078_alpha_dummy_819),
        (nb078_alpha_dummy_821 h)), ((nb078_alpha_dummy_820), (nb078_alpha_dummy_822 h)),
        ((nb078_alpha_dummy_845), (nb078_alpha_dummy_846 h)), ((nb078_alpha_dummy_843),
        (nb078_alpha_dummy_844 h)), ((nb078_alpha_dummy_812), (nb078_alpha_dummy_814 h)),
        ((nb078_alpha_dummy_811), (nb078_alpha_dummy_813 h)), ((nb078_alpha_dummy_841),
        (nb078_alpha_dummy_842 h)), ((nb078_alpha_dummy_815), (nb078_alpha_dummy_816 h)),
        ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768),
        (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
        ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_826) ≠ (nb078_alpha_dummy_833) from (by
          unfold
            nb078_alpha_dummy_833;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0854)
                  0)))) (show (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_834 h) from (by
          unfold
            nb078_alpha_dummy_834;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0855
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_826) ≠ (nb078_alpha_dummy_831)
        from (by
          unfold
            nb078_alpha_dummy_831;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0852)
                  0)))) (show (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_832 h) from (by
          unfold
            nb078_alpha_dummy_832;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0853
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_827) ≠ (nb078_alpha_dummy_833)
        from (by
          unfold
            nb078_alpha_dummy_833;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0858)
                  0)))) (show (nb078_alpha_dummy_830 h) ≠ (nb078_alpha_dummy_834 h) from (by
          unfold
            nb078_alpha_dummy_834;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0859
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_827) ≠ (nb078_alpha_dummy_831)
        from (by
          unfold
            nb078_alpha_dummy_831;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0856)
                  0)))) (show (nb078_alpha_dummy_830 h) ≠ (nb078_alpha_dummy_832 h) from (by
          unfold
            nb078_alpha_dummy_832;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0857
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_826) ≠ (nb078_alpha_dummy_833) from (by
          unfold
            nb078_alpha_dummy_833;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0854)
                  0)))) (show (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_834 h) from (by
          unfold
            nb078_alpha_dummy_834;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0855
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_826) ≠ (nb078_alpha_dummy_831)
        from (by
          unfold
            nb078_alpha_dummy_831;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0852)
                  0)))) (show (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_832 h) from (by
          unfold
            nb078_alpha_dummy_832;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0853
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_827) ≠ (nb078_alpha_dummy_833)
        from (by
          unfold
            nb078_alpha_dummy_833;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0858)
                  0)))) (show (nb078_alpha_dummy_830 h) ≠ (nb078_alpha_dummy_834 h) from (by
          unfold
            nb078_alpha_dummy_834;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0859
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_827) ≠ (nb078_alpha_dummy_831)
        from (by
          unfold
            nb078_alpha_dummy_831;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0856)
                  0)))) (show (nb078_alpha_dummy_830 h) ≠ (nb078_alpha_dummy_832 h) from (by
          unfold
            nb078_alpha_dummy_832;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0857
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_827), (nb078_alpha_dummy_830 h)), ((nb078_alpha_dummy_826),
        (nb078_alpha_dummy_829 h)), ((nb078_alpha_dummy_825), (nb078_alpha_dummy_828 h)),
        ((nb078_alpha_dummy_823), (nb078_alpha_dummy_824 h)), ((nb078_alpha_dummy_819),
        (nb078_alpha_dummy_821 h)), ((nb078_alpha_dummy_820), (nb078_alpha_dummy_822 h)),
        ((nb078_alpha_dummy_845), (nb078_alpha_dummy_846 h)), ((nb078_alpha_dummy_843),
        (nb078_alpha_dummy_844 h)), ((nb078_alpha_dummy_812), (nb078_alpha_dummy_814 h)),
        ((nb078_alpha_dummy_811), (nb078_alpha_dummy_813 h)), ((nb078_alpha_dummy_841),
        (nb078_alpha_dummy_842 h)), ((nb078_alpha_dummy_815), (nb078_alpha_dummy_816 h)),
        ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768),
        (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
        ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_819))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_821
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_826) ≠
        (nb078_alpha_dummy_837) from (by
          unfold
            nb078_alpha_dummy_837;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0862)
                  0)))) (show (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_838 h) from (by
          unfold
            nb078_alpha_dummy_838;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0863
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_826) ≠ (nb078_alpha_dummy_835)
        from (by
          unfold
            nb078_alpha_dummy_835;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0860)
                  0)))) (show (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_836 h) from (by
          unfold
            nb078_alpha_dummy_836;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0861
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_826) ≠ (nb078_alpha_dummy_837)
        from (by
          unfold
            nb078_alpha_dummy_837;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0862)
                  0)))) (show (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_838 h) from (by
          unfold
            nb078_alpha_dummy_838;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0863
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_826) ≠ (nb078_alpha_dummy_835)
        from (by
          unfold
            nb078_alpha_dummy_835;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0860)
                  0)))) (show (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_836 h) from (by
          unfold
            nb078_alpha_dummy_836;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0861
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_827) ≠ (nb078_alpha_dummy_839) from (by
          unfold
            nb078_alpha_dummy_839;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0866)
                  0)))) (show (nb078_alpha_dummy_830 h) ≠ (nb078_alpha_dummy_840 h) from (by
          unfold
            nb078_alpha_dummy_840;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0867
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_827) ≠ (nb078_alpha_dummy_835)
        from (by
          unfold
            nb078_alpha_dummy_835;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0864)
                  0)))) (show (nb078_alpha_dummy_830 h) ≠ (nb078_alpha_dummy_836 h) from (by
          unfold
            nb078_alpha_dummy_836;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0865
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_827) ≠
        (nb078_alpha_dummy_839) from (by
          unfold
            nb078_alpha_dummy_839;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0866)
                  0)))) (show (nb078_alpha_dummy_830 h) ≠ (nb078_alpha_dummy_840 h) from (by
          unfold
            nb078_alpha_dummy_840;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0867
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_827) ≠ (nb078_alpha_dummy_835)
        from (by
          unfold
            nb078_alpha_dummy_835;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0864)
                  0)))) (show (nb078_alpha_dummy_830 h) ≠ (nb078_alpha_dummy_836 h) from (by
          unfold
            nb078_alpha_dummy_836;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0865
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_819) ≠ (nb078_alpha_dummy_823) from
                                        (by
                                          unfold nb078_alpha_dummy_823;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0848)
                                                  0)))) (show (nb078_alpha_dummy_821 h) ≠
        (nb078_alpha_dummy_824 h) from (by
                                          unfold nb078_alpha_dummy_824;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0849 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_823), (nb078_alpha_dummy_824 h)),
                                      ((nb078_alpha_dummy_819), (nb078_alpha_dummy_821 h)),
                                      ((nb078_alpha_dummy_820), (nb078_alpha_dummy_822 h)),
                                      ((nb078_alpha_dummy_845), (nb078_alpha_dummy_846 h)),
                                      ((nb078_alpha_dummy_843), (nb078_alpha_dummy_844 h)),
                                      ((nb078_alpha_dummy_812), (nb078_alpha_dummy_814 h)),
                                      ((nb078_alpha_dummy_811), (nb078_alpha_dummy_813 h)),
                                      ((nb078_alpha_dummy_841), (nb078_alpha_dummy_842 h)),
                                      ((nb078_alpha_dummy_815), (nb078_alpha_dummy_816 h)),
                                      ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
                                      ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                                      ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                                      ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
                                      ((nb078_alpha_dummy_002), h),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_819) ≠ (nb078_alpha_dummy_823) from (by
                                        unfold nb078_alpha_dummy_823;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0848)
                                                0)))) (show (nb078_alpha_dummy_821 h) ≠
                                        (nb078_alpha_dummy_824 h) from (by
                                        unfold nb078_alpha_dummy_824;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0849 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_819) ≠ (nb078_alpha_dummy_823) from
                                        (by
                                          unfold nb078_alpha_dummy_823;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0848)
                                                  0)))) (show (nb078_alpha_dummy_821 h) ≠
        (nb078_alpha_dummy_824 h) from (by
                                          unfold nb078_alpha_dummy_824;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0849 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_823), (nb078_alpha_dummy_824 h)),
                                      ((nb078_alpha_dummy_819), (nb078_alpha_dummy_821 h)),
                                      ((nb078_alpha_dummy_820), (nb078_alpha_dummy_822 h)),
                                      ((nb078_alpha_dummy_845), (nb078_alpha_dummy_846 h)),
                                      ((nb078_alpha_dummy_843), (nb078_alpha_dummy_844 h)),
                                      ((nb078_alpha_dummy_812), (nb078_alpha_dummy_814 h)),
                                      ((nb078_alpha_dummy_811), (nb078_alpha_dummy_813 h)),
                                      ((nb078_alpha_dummy_841), (nb078_alpha_dummy_842 h)),
                                      ((nb078_alpha_dummy_815), (nb078_alpha_dummy_816 h)),
                                      ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
                                      ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                                      ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                                      ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
                                      ((nb078_alpha_dummy_002), h),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
          [((nb078_alpha_dummy_843), (nb078_alpha_dummy_844 h)),
            ((nb078_alpha_dummy_812), (nb078_alpha_dummy_814 h)),
            ((nb078_alpha_dummy_811), (nb078_alpha_dummy_813 h)),
            ((nb078_alpha_dummy_841), (nb078_alpha_dummy_842 h)),
            ((nb078_alpha_dummy_815), (nb078_alpha_dummy_816 h)),
            ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
            ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
            ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
            ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
            ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
            ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part139`. -/


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
noncomputable def nb078_split_alpha_0117 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_859), (nb078_alpha_dummy_860 h)),
        ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)),
        ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
        ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
        ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
        ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
        ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_859))
          (Class.cab (nb078_alpha_dummy_853)
            (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_847))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_853))
                (syn_cphi (Class.cv (nb078_alpha_dummy_854))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_859)) (Class.cab (nb078_alpha_dummy_853)
              (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_847))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_853))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_854)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_860 h))
          (Class.cab (nb078_alpha_dummy_855 h)
            (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_849 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_860 h))
            (Class.cab (nb078_alpha_dummy_855 h)
              (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_849 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_854) from
                    (by
                      unfold nb078_alpha_dummy_854;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0882) 1))))
                  (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_856 h) from (by
                      unfold nb078_alpha_dummy_856;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0884 h) 1))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_853) from
                      (by
                        unfold nb078_alpha_dummy_853;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0882) 0))))
                    (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_855 h) from (by
                        unfold nb078_alpha_dummy_855;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0884 h) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_859) from (by
                          unfold nb078_alpha_dummy_859;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0886) 0))))
                      (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_860 h) from (by
                          unfold nb078_alpha_dummy_860;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0887 h) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_857) from (by
                            unfold nb078_alpha_dummy_857;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0883) 0))))
                        (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_858 h) from (by
                            unfold nb078_alpha_dummy_858;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0885 h) 0))))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_002))).fv)
                            (by decide)) (freshVar_injective (((Class.cv h)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_847))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_848))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_849 h))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_850 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_854) ≠ (nb078_alpha_dummy_861) from (by
                              unfold nb078_alpha_dummy_861;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0888) 0))))
                          (show (nb078_alpha_dummy_856 h) ≠ (nb078_alpha_dummy_863 h) from (by
                              unfold nb078_alpha_dummy_863;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0889 h) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_854) ≠ (nb078_alpha_dummy_862) from (by
                                unfold nb078_alpha_dummy_862;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0888) 1))))
                            (show (nb078_alpha_dummy_856 h) ≠ (nb078_alpha_dummy_864 h) from (by
                                unfold nb078_alpha_dummy_864;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0889 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_854))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_856 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_868) from (by
          unfold nb078_alpha_dummy_868;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0892) 1)))) (show (nb078_alpha_dummy_863 h) ≠
        (nb078_alpha_dummy_871 h) from (by
          unfold nb078_alpha_dummy_871;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0893 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_867) from (by
          unfold nb078_alpha_dummy_867;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0892) 0)))) (show (nb078_alpha_dummy_863 h) ≠
        (nb078_alpha_dummy_870 h) from (by
          unfold nb078_alpha_dummy_870;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0893 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_865) from (by
          unfold nb078_alpha_dummy_865;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0890) 0)))) (show (nb078_alpha_dummy_863 h) ≠
        (nb078_alpha_dummy_866 h) from (by
          unfold nb078_alpha_dummy_866;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0891 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_869), (nb078_alpha_dummy_872 h)), ((nb078_alpha_dummy_868),
        (nb078_alpha_dummy_871 h)), ((nb078_alpha_dummy_867), (nb078_alpha_dummy_870 h)),
        ((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)), ((nb078_alpha_dummy_861),
        (nb078_alpha_dummy_863 h)), ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)),
        ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853),
        (nb078_alpha_dummy_855 h)), ((nb078_alpha_dummy_859), (nb078_alpha_dummy_860 h)),
        ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848),
        (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769),
        (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773),
        (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_875) from (by
          unfold
            nb078_alpha_dummy_875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0896)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_876 h) from (by
          unfold
            nb078_alpha_dummy_876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0897
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_873)
        from (by
          unfold
            nb078_alpha_dummy_873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0894)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_874 h) from (by
          unfold
            nb078_alpha_dummy_874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0895
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_875)
        from (by
          unfold
            nb078_alpha_dummy_875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0900)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_876 h) from (by
          unfold
            nb078_alpha_dummy_876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0901
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_873)
        from (by
          unfold
            nb078_alpha_dummy_873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0898)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_874 h) from (by
          unfold
            nb078_alpha_dummy_874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0899
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_875) from (by
          unfold
            nb078_alpha_dummy_875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0896)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_876 h) from (by
          unfold
            nb078_alpha_dummy_876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0897
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_873)
        from (by
          unfold
            nb078_alpha_dummy_873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0894)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_874 h) from (by
          unfold
            nb078_alpha_dummy_874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0895
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_875)
        from (by
          unfold
            nb078_alpha_dummy_875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0900)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_876 h) from (by
          unfold
            nb078_alpha_dummy_876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0901
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_873)
        from (by
          unfold
            nb078_alpha_dummy_873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0898)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_874 h) from (by
          unfold
            nb078_alpha_dummy_874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0899
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_869), (nb078_alpha_dummy_872 h)), ((nb078_alpha_dummy_868),
        (nb078_alpha_dummy_871 h)), ((nb078_alpha_dummy_867), (nb078_alpha_dummy_870 h)),
        ((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)), ((nb078_alpha_dummy_861),
        (nb078_alpha_dummy_863 h)), ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)),
        ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853),
        (nb078_alpha_dummy_855 h)), ((nb078_alpha_dummy_859), (nb078_alpha_dummy_860 h)),
        ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848),
        (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769),
        (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773),
        (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_861))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_863
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_879) from (by
          unfold
            nb078_alpha_dummy_879;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0904)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_880 h) from (by
          unfold
            nb078_alpha_dummy_880;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0905
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_877)
        from (by
          unfold
            nb078_alpha_dummy_877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0902)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_878 h) from (by
          unfold
            nb078_alpha_dummy_878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0903
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_879)
        from (by
          unfold
            nb078_alpha_dummy_879;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0904)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_880 h) from (by
          unfold
            nb078_alpha_dummy_880;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0905
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_877)
        from (by
          unfold
            nb078_alpha_dummy_877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0902)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_878 h) from (by
          unfold
            nb078_alpha_dummy_878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0903
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_881) from (by
          unfold
            nb078_alpha_dummy_881;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0908)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_882 h) from (by
          unfold
            nb078_alpha_dummy_882;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0909
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_877)
        from (by
          unfold
            nb078_alpha_dummy_877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0906)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_878 h) from (by
          unfold
            nb078_alpha_dummy_878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0907
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠
        (nb078_alpha_dummy_881) from (by
          unfold
            nb078_alpha_dummy_881;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0908)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_882 h) from (by
          unfold
            nb078_alpha_dummy_882;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0909
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_877)
        from (by
          unfold
            nb078_alpha_dummy_877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0906)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_878 h) from (by
          unfold
            nb078_alpha_dummy_878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0907
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_865) from (by
                                        unfold nb078_alpha_dummy_865;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0890)
                                                0)))) (show (nb078_alpha_dummy_863 h) ≠
                                        (nb078_alpha_dummy_866 h) from (by
                                        unfold nb078_alpha_dummy_866;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0891 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)),
                                    ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)),
                                    ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)),
                                    ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)),
                                    ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)),
                                    ((nb078_alpha_dummy_859), (nb078_alpha_dummy_860 h)),
                                    ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)),
                                    ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                                    ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                                    ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
                                    ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
                                    ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                                    ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                                    ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_865) from
                                    (by
                                      unfold nb078_alpha_dummy_865;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0890)
                                              0)))) (show
                                    (nb078_alpha_dummy_863 h) ≠ (nb078_alpha_dummy_866 h) from
                                    (by
                                      unfold nb078_alpha_dummy_866;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0891 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_865) from (by
                                        unfold nb078_alpha_dummy_865;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0890)
                                                0)))) (show (nb078_alpha_dummy_863 h) ≠
                                        (nb078_alpha_dummy_866 h) from (by
                                        unfold nb078_alpha_dummy_866;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0891 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)),
                                    ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)),
                                    ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)),
                                    ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)),
                                    ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)),
                                    ((nb078_alpha_dummy_859), (nb078_alpha_dummy_860 h)),
                                    ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)),
                                    ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                                    ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                                    ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
                                    ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
                                    ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                                    ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                                    ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_854) from
                      (by
                        unfold nb078_alpha_dummy_854;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0882) 1))))
                    (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_856 h) from (by
                        unfold nb078_alpha_dummy_856;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0884 h) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_853) from (by
                          unfold nb078_alpha_dummy_853;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0882) 0))))
                      (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_855 h) from (by
                          unfold nb078_alpha_dummy_855;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0884 h) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_859) from (by
                            unfold nb078_alpha_dummy_859;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0886) 0))))
                        (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_860 h) from (by
                            unfold nb078_alpha_dummy_860;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0887 h) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_857) from (by
                              unfold nb078_alpha_dummy_857;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0883) 0))))
                          (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_858 h) from (by
                              unfold nb078_alpha_dummy_858;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0885 h) 0))))
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_002))).fv)
                              (by decide)) (freshVar_injective (((Class.cv h)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078_alpha_dummy_847))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_848))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_849 h))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_850 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_854) ≠ (nb078_alpha_dummy_861) from (by
                                unfold nb078_alpha_dummy_861;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0888) 0))))
                            (show (nb078_alpha_dummy_856 h) ≠ (nb078_alpha_dummy_863 h) from (by
                                unfold nb078_alpha_dummy_863;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0889 h) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_854) ≠ (nb078_alpha_dummy_862) from (by
                                  unfold nb078_alpha_dummy_862;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0888) 1))))
                              (show (nb078_alpha_dummy_856 h) ≠ (nb078_alpha_dummy_864 h) from
                                (by
                                  unfold nb078_alpha_dummy_864;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0889 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_854))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_856 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_868) from (by
          unfold nb078_alpha_dummy_868;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0892) 1)))) (show (nb078_alpha_dummy_863 h) ≠
        (nb078_alpha_dummy_871 h) from (by
          unfold nb078_alpha_dummy_871;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0893 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_867) from (by
          unfold nb078_alpha_dummy_867;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0892) 0)))) (show (nb078_alpha_dummy_863 h) ≠
        (nb078_alpha_dummy_870 h) from (by
          unfold nb078_alpha_dummy_870;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0893 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_865)
        from (by
          unfold nb078_alpha_dummy_865;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0890)
                  0)))) (show (nb078_alpha_dummy_863 h) ≠ (nb078_alpha_dummy_866 h) from (by
          unfold nb078_alpha_dummy_866;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0891 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_869), (nb078_alpha_dummy_872 h)), ((nb078_alpha_dummy_868),
        (nb078_alpha_dummy_871 h)), ((nb078_alpha_dummy_867), (nb078_alpha_dummy_870 h)),
        ((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)), ((nb078_alpha_dummy_861),
        (nb078_alpha_dummy_863 h)), ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)),
        ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853),
        (nb078_alpha_dummy_855 h)), ((nb078_alpha_dummy_859), (nb078_alpha_dummy_860 h)),
        ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848),
        (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769),
        (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773),
        (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_875) from (by
          unfold
            nb078_alpha_dummy_875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0896)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_876 h) from (by
          unfold
            nb078_alpha_dummy_876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0897
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_873)
        from (by
          unfold
            nb078_alpha_dummy_873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0894)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_874 h) from (by
          unfold
            nb078_alpha_dummy_874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0895
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_875)
        from (by
          unfold
            nb078_alpha_dummy_875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0900)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_876 h) from (by
          unfold
            nb078_alpha_dummy_876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0901
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_873)
        from (by
          unfold
            nb078_alpha_dummy_873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0898)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_874 h) from (by
          unfold
            nb078_alpha_dummy_874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0899
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_875) from (by
          unfold
            nb078_alpha_dummy_875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0896)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_876 h) from (by
          unfold
            nb078_alpha_dummy_876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0897
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_873)
        from (by
          unfold
            nb078_alpha_dummy_873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0894)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_874 h) from (by
          unfold
            nb078_alpha_dummy_874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0895
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_875)
        from (by
          unfold
            nb078_alpha_dummy_875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0900)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_876 h) from (by
          unfold
            nb078_alpha_dummy_876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0901
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_873)
        from (by
          unfold
            nb078_alpha_dummy_873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0898)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_874 h) from (by
          unfold
            nb078_alpha_dummy_874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0899
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_869), (nb078_alpha_dummy_872 h)), ((nb078_alpha_dummy_868),
        (nb078_alpha_dummy_871 h)), ((nb078_alpha_dummy_867), (nb078_alpha_dummy_870 h)),
        ((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)), ((nb078_alpha_dummy_861),
        (nb078_alpha_dummy_863 h)), ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)),
        ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853),
        (nb078_alpha_dummy_855 h)), ((nb078_alpha_dummy_859), (nb078_alpha_dummy_860 h)),
        ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848),
        (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769),
        (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773),
        (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_861))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_863
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_879) from (by
          unfold
            nb078_alpha_dummy_879;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0904)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_880 h) from (by
          unfold
            nb078_alpha_dummy_880;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0905
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_877)
        from (by
          unfold
            nb078_alpha_dummy_877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0902)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_878 h) from (by
          unfold
            nb078_alpha_dummy_878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0903
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_879)
        from (by
          unfold
            nb078_alpha_dummy_879;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0904)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_880 h) from (by
          unfold
            nb078_alpha_dummy_880;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0905
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_877)
        from (by
          unfold
            nb078_alpha_dummy_877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0902)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_878 h) from (by
          unfold
            nb078_alpha_dummy_878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0903
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_881) from (by
          unfold
            nb078_alpha_dummy_881;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0908)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_882 h) from (by
          unfold
            nb078_alpha_dummy_882;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0909
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_877)
        from (by
          unfold
            nb078_alpha_dummy_877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0906)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_878 h) from (by
          unfold
            nb078_alpha_dummy_878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0907
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠
        (nb078_alpha_dummy_881) from (by
          unfold
            nb078_alpha_dummy_881;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0908)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_882 h) from (by
          unfold
            nb078_alpha_dummy_882;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0909
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_877)
        from (by
          unfold
            nb078_alpha_dummy_877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0906)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_878 h) from (by
          unfold
            nb078_alpha_dummy_878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0907
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_865) from
                                        (by
                                          unfold nb078_alpha_dummy_865;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0890)
                                                  0)))) (show (nb078_alpha_dummy_863 h) ≠
        (nb078_alpha_dummy_866 h) from (by
                                          unfold nb078_alpha_dummy_866;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0891 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)),
                                      ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)),
                                      ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)),
                                      ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)),
                                      ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)),
                                      ((nb078_alpha_dummy_859), (nb078_alpha_dummy_860 h)),
                                      ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)),
                                      ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                                      ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                                      ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
                                      ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
                                      ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                                      ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                                      ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
                                      ((nb078_alpha_dummy_002), h),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_865) from (by
                                        unfold nb078_alpha_dummy_865;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0890)
                                                0)))) (show (nb078_alpha_dummy_863 h) ≠
                                        (nb078_alpha_dummy_866 h) from (by
                                        unfold nb078_alpha_dummy_866;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0891 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_865) from
                                        (by
                                          unfold nb078_alpha_dummy_865;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0890)
                                                  0)))) (show (nb078_alpha_dummy_863 h) ≠
        (nb078_alpha_dummy_866 h) from (by
                                          unfold nb078_alpha_dummy_866;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0891 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)),
                                      ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)),
                                      ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)),
                                      ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)),
                                      ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)),
                                      ((nb078_alpha_dummy_859), (nb078_alpha_dummy_860 h)),
                                      ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)),
                                      ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                                      ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                                      ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
                                      ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
                                      ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                                      ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                                      ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
                                      ((nb078_alpha_dummy_002), h),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part140`. -/


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
noncomputable def nb078_split_alpha_0118 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_887), (nb078_alpha_dummy_888 h)),
        ((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)),
        ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)),
        ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)),
        ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)),
        ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)),
        ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
        ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
        ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
        ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
        ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_887))
          (syn_cphi (Class.cv (nb078_alpha_dummy_854)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_887))
            (syn_cphi (Class.cv (nb078_alpha_dummy_854))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_888 h))
          (syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_888 h))
            (syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_854) ≠ (nb078_alpha_dummy_861) from
                    (by
                      unfold nb078_alpha_dummy_861;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0888) 0))))
                  (show (nb078_alpha_dummy_856 h) ≠ (nb078_alpha_dummy_863 h) from (by
                      unfold nb078_alpha_dummy_863;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0889 h) 0))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_854) ≠ (nb078_alpha_dummy_862) from
                      (by
                        unfold nb078_alpha_dummy_862;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0888) 1))))
                    (show (nb078_alpha_dummy_856 h) ≠ (nb078_alpha_dummy_864 h) from (by
                        unfold nb078_alpha_dummy_864;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0889 h) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_854) ≠ (nb078_alpha_dummy_887) from (by
                          unfold nb078_alpha_dummy_887;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0918) 0))))
                      (show (nb078_alpha_dummy_856 h) ≠ (nb078_alpha_dummy_888 h) from (by
                          unfold nb078_alpha_dummy_888;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0919 h) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_854) ≠ (nb078_alpha_dummy_885) from (by
                            unfold nb078_alpha_dummy_885;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0916) 0))))
                        (show (nb078_alpha_dummy_856 h) ≠ (nb078_alpha_dummy_886 h) from (by
                            unfold nb078_alpha_dummy_886;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0917 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_854))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_856 h))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_868) from (by
                                        unfold nb078_alpha_dummy_868;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0892)
                                                1)))) (show (nb078_alpha_dummy_863 h) ≠
                                        (nb078_alpha_dummy_871 h) from (by
                                        unfold nb078_alpha_dummy_871;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0893 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_867) from
                                        (by
                                          unfold nb078_alpha_dummy_867;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0892)
                                                  0)))) (show (nb078_alpha_dummy_863 h) ≠
        (nb078_alpha_dummy_870 h) from (by
                                          unfold nb078_alpha_dummy_870;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0893 h) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_861) ≠
        (nb078_alpha_dummy_865) from (by
          unfold nb078_alpha_dummy_865;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0890) 0)))) (show (nb078_alpha_dummy_863 h) ≠
        (nb078_alpha_dummy_866 h) from (by
          unfold nb078_alpha_dummy_866;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0891 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_869),
        (nb078_alpha_dummy_872 h)), ((nb078_alpha_dummy_868), (nb078_alpha_dummy_871 h)),
                                        ((nb078_alpha_dummy_867), (nb078_alpha_dummy_870 h)),
                                        ((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)),
                                        ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)),
                                        ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)),
                                        ((nb078_alpha_dummy_887), (nb078_alpha_dummy_888 h)),
                                        ((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)),
                                        ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)),
                                        ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)),
                                        ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)),
                                        ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)),
                                        ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                                        ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                                        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
                                        ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
                                        ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                                        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                                        ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
                                        ((nb078_alpha_dummy_002), h),
                                        ((nb078_alpha_dummy_004), y),
                                        ((nb078_alpha_dummy_003), x)]
                                      (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠
        (nb078_alpha_dummy_875) from (by
          unfold
            nb078_alpha_dummy_875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0896)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_876 h) from (by
          unfold
            nb078_alpha_dummy_876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0897
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_873)
        from (by
          unfold
            nb078_alpha_dummy_873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0894)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_874 h) from (by
          unfold
            nb078_alpha_dummy_874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0895
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_875)
        from (by
          unfold
            nb078_alpha_dummy_875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0900)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_876 h) from (by
          unfold
            nb078_alpha_dummy_876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0901
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_873)
        from (by
          unfold
            nb078_alpha_dummy_873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0898)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_874 h) from (by
          unfold
            nb078_alpha_dummy_874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0899
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_875) from (by
          unfold
            nb078_alpha_dummy_875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0896)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_876 h) from (by
          unfold
            nb078_alpha_dummy_876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0897
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_873)
        from (by
          unfold
            nb078_alpha_dummy_873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0894)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_874 h) from (by
          unfold
            nb078_alpha_dummy_874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0895
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_875)
        from (by
          unfold
            nb078_alpha_dummy_875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0900)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_876 h) from (by
          unfold
            nb078_alpha_dummy_876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0901
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_873)
        from (by
          unfold
            nb078_alpha_dummy_873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0898)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_874 h) from (by
          unfold
            nb078_alpha_dummy_874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0899
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb078_alpha_dummy_869), (nb078_alpha_dummy_872 h)),
        ((nb078_alpha_dummy_868), (nb078_alpha_dummy_871 h)), ((nb078_alpha_dummy_867),
        (nb078_alpha_dummy_870 h)), ((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)),
        ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)), ((nb078_alpha_dummy_862),
        (nb078_alpha_dummy_864 h)), ((nb078_alpha_dummy_887), (nb078_alpha_dummy_888 h)),
        ((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)), ((nb078_alpha_dummy_854),
        (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)),
        ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)), ((nb078_alpha_dummy_857),
        (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
        ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851),
        (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
        ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767),
        (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠
        (nb078_alpha_dummy_879) from (by
          unfold
            nb078_alpha_dummy_879;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0904)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_880 h) from (by
          unfold
            nb078_alpha_dummy_880;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0905
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_877)
        from (by
          unfold
            nb078_alpha_dummy_877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0902)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_878 h) from (by
          unfold
            nb078_alpha_dummy_878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0903
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_879)
        from (by
          unfold
            nb078_alpha_dummy_879;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0904)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_880 h) from (by
          unfold
            nb078_alpha_dummy_880;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0905
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_877)
        from (by
          unfold
            nb078_alpha_dummy_877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0902)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_878 h) from (by
          unfold
            nb078_alpha_dummy_878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0903
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_881) from (by
          unfold
            nb078_alpha_dummy_881;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0908)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_882 h) from (by
          unfold
            nb078_alpha_dummy_882;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0909
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_877)
        from (by
          unfold
            nb078_alpha_dummy_877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0906)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_878 h) from (by
          unfold
            nb078_alpha_dummy_878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0907
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠
        (nb078_alpha_dummy_881) from (by
          unfold
            nb078_alpha_dummy_881;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0908)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_882 h) from (by
          unfold
            nb078_alpha_dummy_882;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0909
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_877)
        from (by
          unfold
            nb078_alpha_dummy_877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0906)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_878 h) from (by
          unfold
            nb078_alpha_dummy_878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0907
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_865) from (by
                                unfold nb078_alpha_dummy_865;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0890) 0))))
                            (show (nb078_alpha_dummy_863 h) ≠ (nb078_alpha_dummy_866 h) from (by
                                unfold nb078_alpha_dummy_866;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0891 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)),
                            ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)),
                            ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)),
                            ((nb078_alpha_dummy_887), (nb078_alpha_dummy_888 h)),
                            ((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)),
                            ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)),
                            ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)),
                            ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)),
                            ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)),
                            ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                            ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                            ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
                            ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
                            ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                            ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                            ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
                            ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                            ((nb078_alpha_dummy_003), x)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_865) from (by
                              unfold nb078_alpha_dummy_865;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0890) 0))))
                          (show (nb078_alpha_dummy_863 h) ≠ (nb078_alpha_dummy_866 h) from (by
                              unfold nb078_alpha_dummy_866;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0891 h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_865) from (by
                                unfold nb078_alpha_dummy_865;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0890) 0))))
                            (show (nb078_alpha_dummy_863 h) ≠ (nb078_alpha_dummy_866 h) from (by
                                unfold nb078_alpha_dummy_866;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0891 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)),
                            ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)),
                            ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)),
                            ((nb078_alpha_dummy_887), (nb078_alpha_dummy_888 h)),
                            ((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)),
                            ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)),
                            ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)),
                            ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)),
                            ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)),
                            ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                            ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                            ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
                            ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
                            ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                            ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                            ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
                            ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                            ((nb078_alpha_dummy_003), x)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb078_alpha_dummy_854) ≠ (nb078_alpha_dummy_861) from (by
                        unfold nb078_alpha_dummy_861;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0888) 0))))
                    (show (nb078_alpha_dummy_856 h) ≠ (nb078_alpha_dummy_863 h) from (by
                        unfold nb078_alpha_dummy_863;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0889 h) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_854) ≠ (nb078_alpha_dummy_862) from (by
                          unfold nb078_alpha_dummy_862;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0888) 1))))
                      (show (nb078_alpha_dummy_856 h) ≠ (nb078_alpha_dummy_864 h) from (by
                          unfold nb078_alpha_dummy_864;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0889 h) 1))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_854) ≠ (nb078_alpha_dummy_887) from (by
                            unfold nb078_alpha_dummy_887;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0918) 0))))
                        (show (nb078_alpha_dummy_856 h) ≠ (nb078_alpha_dummy_888 h) from (by
                            unfold nb078_alpha_dummy_888;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0919 h) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_854) ≠ (nb078_alpha_dummy_885) from (by
                              unfold nb078_alpha_dummy_885;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0916) 0))))
                          (show (nb078_alpha_dummy_856 h) ≠ (nb078_alpha_dummy_886 h) from (by
                              unfold nb078_alpha_dummy_886;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0917 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_854))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_856 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_868) from
                                        (by
                                          unfold nb078_alpha_dummy_868;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0892)
                                                  1)))) (show (nb078_alpha_dummy_863 h) ≠
        (nb078_alpha_dummy_871 h) from (by
                                          unfold nb078_alpha_dummy_871;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0893 h) 1))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_861) ≠
        (nb078_alpha_dummy_867) from (by
          unfold nb078_alpha_dummy_867;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0892) 0)))) (show (nb078_alpha_dummy_863 h) ≠
        (nb078_alpha_dummy_870 h) from (by
          unfold nb078_alpha_dummy_870;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0893 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_865) from (by
          unfold nb078_alpha_dummy_865;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0890) 0)))) (show (nb078_alpha_dummy_863 h) ≠
        (nb078_alpha_dummy_866 h) from (by
          unfold nb078_alpha_dummy_866;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0891 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_869),
        (nb078_alpha_dummy_872 h)), ((nb078_alpha_dummy_868), (nb078_alpha_dummy_871 h)),
        ((nb078_alpha_dummy_867), (nb078_alpha_dummy_870 h)), ((nb078_alpha_dummy_865),
        (nb078_alpha_dummy_866 h)), ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)),
        ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)), ((nb078_alpha_dummy_887),
        (nb078_alpha_dummy_888 h)), ((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)),
        ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853),
        (nb078_alpha_dummy_855 h)), ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)),
        ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848),
        (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769),
        (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773),
        (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠
        (nb078_alpha_dummy_875) from (by
          unfold
            nb078_alpha_dummy_875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0896)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_876 h) from (by
          unfold
            nb078_alpha_dummy_876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0897
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_873)
        from (by
          unfold
            nb078_alpha_dummy_873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0894)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_874 h) from (by
          unfold
            nb078_alpha_dummy_874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0895
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_875)
        from (by
          unfold
            nb078_alpha_dummy_875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0900)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_876 h) from (by
          unfold
            nb078_alpha_dummy_876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0901
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_873)
        from (by
          unfold
            nb078_alpha_dummy_873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0898)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_874 h) from (by
          unfold
            nb078_alpha_dummy_874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0899
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_875) from (by
          unfold
            nb078_alpha_dummy_875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0896)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_876 h) from (by
          unfold
            nb078_alpha_dummy_876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0897
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_873)
        from (by
          unfold
            nb078_alpha_dummy_873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0894)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_874 h) from (by
          unfold
            nb078_alpha_dummy_874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0895
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_875)
        from (by
          unfold
            nb078_alpha_dummy_875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0900)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_876 h) from (by
          unfold
            nb078_alpha_dummy_876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0901
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_873)
        from (by
          unfold
            nb078_alpha_dummy_873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0898)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_874 h) from (by
          unfold
            nb078_alpha_dummy_874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0899
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_869), (nb078_alpha_dummy_872 h)), ((nb078_alpha_dummy_868),
        (nb078_alpha_dummy_871 h)), ((nb078_alpha_dummy_867), (nb078_alpha_dummy_870 h)),
        ((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)), ((nb078_alpha_dummy_861),
        (nb078_alpha_dummy_863 h)), ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)),
        ((nb078_alpha_dummy_887), (nb078_alpha_dummy_888 h)), ((nb078_alpha_dummy_885),
        (nb078_alpha_dummy_886 h)), ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)),
        ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)), ((nb078_alpha_dummy_883),
        (nb078_alpha_dummy_884 h)), ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)),
        ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847),
        (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
        ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768),
        (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
        ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_861))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_861))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠
        (nb078_alpha_dummy_879) from (by
          unfold
            nb078_alpha_dummy_879;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0904)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_880 h) from (by
          unfold
            nb078_alpha_dummy_880;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0905
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_877)
        from (by
          unfold
            nb078_alpha_dummy_877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0902)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_878 h) from (by
          unfold
            nb078_alpha_dummy_878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0903
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_879)
        from (by
          unfold
            nb078_alpha_dummy_879;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0904)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_880 h) from (by
          unfold
            nb078_alpha_dummy_880;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0905
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_877)
        from (by
          unfold
            nb078_alpha_dummy_877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0902)
                  0)))) (show (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_878 h) from (by
          unfold
            nb078_alpha_dummy_878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0903
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_881) from (by
          unfold
            nb078_alpha_dummy_881;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0908)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_882 h) from (by
          unfold
            nb078_alpha_dummy_882;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0909
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_877)
        from (by
          unfold
            nb078_alpha_dummy_877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0906)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_878 h) from (by
          unfold
            nb078_alpha_dummy_878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0907
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠
        (nb078_alpha_dummy_881) from (by
          unfold
            nb078_alpha_dummy_881;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0908)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_882 h) from (by
          unfold
            nb078_alpha_dummy_882;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0909
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_869) ≠ (nb078_alpha_dummy_877)
        from (by
          unfold
            nb078_alpha_dummy_877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0906)
                  0)))) (show (nb078_alpha_dummy_872 h) ≠ (nb078_alpha_dummy_878 h) from (by
          unfold
            nb078_alpha_dummy_878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0907
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_865) from (by
                                  unfold nb078_alpha_dummy_865;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0890) 0))))
                              (show (nb078_alpha_dummy_863 h) ≠ (nb078_alpha_dummy_866 h) from
                                (by
                                  unfold nb078_alpha_dummy_866;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0891 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)),
                              ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)),
                              ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)),
                              ((nb078_alpha_dummy_887), (nb078_alpha_dummy_888 h)),
                              ((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)),
                              ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)),
                              ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)),
                              ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)),
                              ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)),
                              ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                              ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                              ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
                              ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
                              ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                              ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                              ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
                              ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                              ((nb078_alpha_dummy_003), x)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_865) from (by
                                unfold nb078_alpha_dummy_865;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0890) 0))))
                            (show (nb078_alpha_dummy_863 h) ≠ (nb078_alpha_dummy_866 h) from (by
                                unfold nb078_alpha_dummy_866;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0891 h) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_865) from (by
                                  unfold nb078_alpha_dummy_865;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0890) 0))))
                              (show (nb078_alpha_dummy_863 h) ≠ (nb078_alpha_dummy_866 h) from
                                (by
                                  unfold nb078_alpha_dummy_866;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0891 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)),
                              ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)),
                              ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)),
                              ((nb078_alpha_dummy_887), (nb078_alpha_dummy_888 h)),
                              ((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)),
                              ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)),
                              ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)),
                              ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)),
                              ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)),
                              ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                              ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                              ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
                              ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
                              ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                              ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                              ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
                              ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                              ((nb078_alpha_dummy_003), x)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
