/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block054

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part163`. -/


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
noncomputable def nb078_split_alpha_0143 (x : Var) (y : Var) (h : Var) :
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
        ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
        ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
        ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
        ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
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
                                        ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
                                        ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
                                        ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
                                        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                                        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                                        ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                                        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
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
        (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
        ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133),
        (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049),
        (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
        ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045),
        (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
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
                            ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
                            ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
                            ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
                            ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                            ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                            ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                            ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                            ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                            ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
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
                            ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
                            ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
                            ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
                            ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                            ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                            ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                            ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                            ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                            ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
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
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_1130),
        (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
        ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
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
        ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129),
        (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050),
        (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047),
        (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
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
                              ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
                              ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
                              ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
                              ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                              ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                              ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                              ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                              ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                              ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
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
                              ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
                              ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
                              ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
                              ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                              ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                              ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                              ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                              ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                              ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                              ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                              ((nb078_alpha_dummy_003), x)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part164`. -/


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
noncomputable def nb078_split_alpha_0144 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_895), (nb078_alpha_dummy_896 h)),
        ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)),
        ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
        ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
        ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
        ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
        ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
        ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_895))
          (Class.cab (nb078_alpha_dummy_889)
            (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_848))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_889))
                (syn_cphi (Class.cv (nb078_alpha_dummy_890))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_895)) (Class.cab (nb078_alpha_dummy_889)
              (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_848))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_889))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_890)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_896 h))
          (Class.cab (nb078_alpha_dummy_891 h)
            (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_850 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_896 h))
            (Class.cab (nb078_alpha_dummy_891 h)
              (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_850 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_890) from
                    (by
                      unfold nb078_alpha_dummy_890;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0920) 1))))
                  (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_892 h) from (by
                      unfold nb078_alpha_dummy_892;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0922 h) 1))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_889) from
                      (by
                        unfold nb078_alpha_dummy_889;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0920) 0))))
                    (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_891 h) from (by
                        unfold nb078_alpha_dummy_891;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0922 h) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_895) from (by
                          unfold nb078_alpha_dummy_895;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0924) 0))))
                      (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_896 h) from (by
                          unfold nb078_alpha_dummy_896;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0925 h) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_893) from (by
                            unfold nb078_alpha_dummy_893;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0921) 0))))
                        (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_894 h) from (by
                            unfold nb078_alpha_dummy_894;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0923 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_848))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_847))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_850 h))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_849 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_890) ≠ (nb078_alpha_dummy_897) from (by
                              unfold nb078_alpha_dummy_897;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0926) 0))))
                          (show (nb078_alpha_dummy_892 h) ≠ (nb078_alpha_dummy_899 h) from (by
                              unfold nb078_alpha_dummy_899;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0927 h) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_890) ≠ (nb078_alpha_dummy_898) from (by
                                unfold nb078_alpha_dummy_898;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0926) 1))))
                            (show (nb078_alpha_dummy_892 h) ≠ (nb078_alpha_dummy_900 h) from (by
                                unfold nb078_alpha_dummy_900;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0927 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_890))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_892 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_904) from (by
          unfold nb078_alpha_dummy_904;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0930) 1)))) (show (nb078_alpha_dummy_899 h) ≠
        (nb078_alpha_dummy_907 h) from (by
          unfold nb078_alpha_dummy_907;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0931 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_903) from (by
          unfold nb078_alpha_dummy_903;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0930) 0)))) (show (nb078_alpha_dummy_899 h) ≠
        (nb078_alpha_dummy_906 h) from (by
          unfold nb078_alpha_dummy_906;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0931 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_901) from (by
          unfold nb078_alpha_dummy_901;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0928) 0)))) (show (nb078_alpha_dummy_899 h) ≠
        (nb078_alpha_dummy_902 h) from (by
          unfold nb078_alpha_dummy_902;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0929 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_905), (nb078_alpha_dummy_908 h)), ((nb078_alpha_dummy_904),
        (nb078_alpha_dummy_907 h)), ((nb078_alpha_dummy_903), (nb078_alpha_dummy_906 h)),
        ((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)), ((nb078_alpha_dummy_897),
        (nb078_alpha_dummy_899 h)), ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)),
        ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889),
        (nb078_alpha_dummy_891 h)), ((nb078_alpha_dummy_895), (nb078_alpha_dummy_896 h)),
        ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848),
        (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_1130),
        (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
        ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠ (nb078_alpha_dummy_911) from (by
          unfold
            nb078_alpha_dummy_911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0934)
                  0)))) (show (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_912 h) from (by
          unfold
            nb078_alpha_dummy_912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0935
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠ (nb078_alpha_dummy_909)
        from (by
          unfold
            nb078_alpha_dummy_909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0932)
                  0)))) (show (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_910 h) from (by
          unfold
            nb078_alpha_dummy_910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0933
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_905) ≠ (nb078_alpha_dummy_911)
        from (by
          unfold
            nb078_alpha_dummy_911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0938)
                  0)))) (show (nb078_alpha_dummy_908 h) ≠ (nb078_alpha_dummy_912 h) from (by
          unfold
            nb078_alpha_dummy_912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0939
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_905) ≠ (nb078_alpha_dummy_909)
        from (by
          unfold
            nb078_alpha_dummy_909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0936)
                  0)))) (show (nb078_alpha_dummy_908 h) ≠ (nb078_alpha_dummy_910 h) from (by
          unfold
            nb078_alpha_dummy_910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0937
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠ (nb078_alpha_dummy_911) from (by
          unfold
            nb078_alpha_dummy_911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0934)
                  0)))) (show (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_912 h) from (by
          unfold
            nb078_alpha_dummy_912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0935
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠ (nb078_alpha_dummy_909)
        from (by
          unfold
            nb078_alpha_dummy_909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0932)
                  0)))) (show (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_910 h) from (by
          unfold
            nb078_alpha_dummy_910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0933
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_905) ≠ (nb078_alpha_dummy_911)
        from (by
          unfold
            nb078_alpha_dummy_911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0938)
                  0)))) (show (nb078_alpha_dummy_908 h) ≠ (nb078_alpha_dummy_912 h) from (by
          unfold
            nb078_alpha_dummy_912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0939
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_905) ≠ (nb078_alpha_dummy_909)
        from (by
          unfold
            nb078_alpha_dummy_909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0936)
                  0)))) (show (nb078_alpha_dummy_908 h) ≠ (nb078_alpha_dummy_910 h) from (by
          unfold
            nb078_alpha_dummy_910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0937
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_905), (nb078_alpha_dummy_908 h)), ((nb078_alpha_dummy_904),
        (nb078_alpha_dummy_907 h)), ((nb078_alpha_dummy_903), (nb078_alpha_dummy_906 h)),
        ((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)), ((nb078_alpha_dummy_897),
        (nb078_alpha_dummy_899 h)), ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)),
        ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889),
        (nb078_alpha_dummy_891 h)), ((nb078_alpha_dummy_895), (nb078_alpha_dummy_896 h)),
        ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848),
        (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_1130),
        (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
        ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_897))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠
        (nb078_alpha_dummy_915) from (by
          unfold
            nb078_alpha_dummy_915;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0942)
                  0)))) (show (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_916 h) from (by
          unfold
            nb078_alpha_dummy_916;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0943
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠ (nb078_alpha_dummy_913)
        from (by
          unfold
            nb078_alpha_dummy_913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0940)
                  0)))) (show (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_914 h) from (by
          unfold
            nb078_alpha_dummy_914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0941
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠ (nb078_alpha_dummy_915)
        from (by
          unfold
            nb078_alpha_dummy_915;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0942)
                  0)))) (show (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_916 h) from (by
          unfold
            nb078_alpha_dummy_916;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0943
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠ (nb078_alpha_dummy_913)
        from (by
          unfold
            nb078_alpha_dummy_913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0940)
                  0)))) (show (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_914 h) from (by
          unfold
            nb078_alpha_dummy_914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0941
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_905) ≠ (nb078_alpha_dummy_917) from (by
          unfold
            nb078_alpha_dummy_917;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0946)
                  0)))) (show (nb078_alpha_dummy_908 h) ≠ (nb078_alpha_dummy_918 h) from (by
          unfold
            nb078_alpha_dummy_918;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0947
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_905) ≠ (nb078_alpha_dummy_913)
        from (by
          unfold
            nb078_alpha_dummy_913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0944)
                  0)))) (show (nb078_alpha_dummy_908 h) ≠ (nb078_alpha_dummy_914 h) from (by
          unfold
            nb078_alpha_dummy_914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0945
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_905) ≠
        (nb078_alpha_dummy_917) from (by
          unfold
            nb078_alpha_dummy_917;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0946)
                  0)))) (show (nb078_alpha_dummy_908 h) ≠ (nb078_alpha_dummy_918 h) from (by
          unfold
            nb078_alpha_dummy_918;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0947
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_905) ≠ (nb078_alpha_dummy_913)
        from (by
          unfold
            nb078_alpha_dummy_913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0944)
                  0)))) (show (nb078_alpha_dummy_908 h) ≠ (nb078_alpha_dummy_914 h) from (by
          unfold
            nb078_alpha_dummy_914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0945
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_901) from (by
                                        unfold nb078_alpha_dummy_901;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0928)
                                                0)))) (show (nb078_alpha_dummy_899 h) ≠
                                        (nb078_alpha_dummy_902 h) from (by
                                        unfold nb078_alpha_dummy_902;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0929 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)),
                                    ((nb078_alpha_dummy_897), (nb078_alpha_dummy_899 h)),
                                    ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)),
                                    ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)),
                                    ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)),
                                    ((nb078_alpha_dummy_895), (nb078_alpha_dummy_896 h)),
                                    ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)),
                                    ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                                    ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                                    ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
                                    ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
                                    ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
                                    ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
                                    ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                                    ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                    ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                    ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                                    ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                                    ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_901) from
                                    (by
                                      unfold nb078_alpha_dummy_901;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0928)
                                              0)))) (show
                                    (nb078_alpha_dummy_899 h) ≠ (nb078_alpha_dummy_902 h) from
                                    (by
                                      unfold nb078_alpha_dummy_902;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0929 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_901) from (by
                                        unfold nb078_alpha_dummy_901;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0928)
                                                0)))) (show (nb078_alpha_dummy_899 h) ≠
                                        (nb078_alpha_dummy_902 h) from (by
                                        unfold nb078_alpha_dummy_902;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0929 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)),
                                    ((nb078_alpha_dummy_897), (nb078_alpha_dummy_899 h)),
                                    ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)),
                                    ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)),
                                    ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)),
                                    ((nb078_alpha_dummy_895), (nb078_alpha_dummy_896 h)),
                                    ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)),
                                    ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                                    ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                                    ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
                                    ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
                                    ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
                                    ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
                                    ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                                    ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                    ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                    ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                                    ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                                    ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_890) from
                      (by
                        unfold nb078_alpha_dummy_890;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0920) 1))))
                    (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_892 h) from (by
                        unfold nb078_alpha_dummy_892;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0922 h) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_889) from (by
                          unfold nb078_alpha_dummy_889;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0920) 0))))
                      (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_891 h) from (by
                          unfold nb078_alpha_dummy_891;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0922 h) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_895) from (by
                            unfold nb078_alpha_dummy_895;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0924) 0))))
                        (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_896 h) from (by
                            unfold nb078_alpha_dummy_896;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0925 h) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_893) from (by
                              unfold nb078_alpha_dummy_893;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0921) 0))))
                          (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_894 h) from (by
                              unfold nb078_alpha_dummy_894;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0923 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078_alpha_dummy_848))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_847))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_850 h))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_849 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_890) ≠ (nb078_alpha_dummy_897) from (by
                                unfold nb078_alpha_dummy_897;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0926) 0))))
                            (show (nb078_alpha_dummy_892 h) ≠ (nb078_alpha_dummy_899 h) from (by
                                unfold nb078_alpha_dummy_899;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0927 h) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_890) ≠ (nb078_alpha_dummy_898) from (by
                                  unfold nb078_alpha_dummy_898;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0926) 1))))
                              (show (nb078_alpha_dummy_892 h) ≠ (nb078_alpha_dummy_900 h) from
                                (by
                                  unfold nb078_alpha_dummy_900;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0927 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_890))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_892 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_904) from (by
          unfold nb078_alpha_dummy_904;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0930) 1)))) (show (nb078_alpha_dummy_899 h) ≠
        (nb078_alpha_dummy_907 h) from (by
          unfold nb078_alpha_dummy_907;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0931 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_903) from (by
          unfold nb078_alpha_dummy_903;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0930) 0)))) (show (nb078_alpha_dummy_899 h) ≠
        (nb078_alpha_dummy_906 h) from (by
          unfold nb078_alpha_dummy_906;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0931 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_901)
        from (by
          unfold nb078_alpha_dummy_901;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0928)
                  0)))) (show (nb078_alpha_dummy_899 h) ≠ (nb078_alpha_dummy_902 h) from (by
          unfold nb078_alpha_dummy_902;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0929 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_905), (nb078_alpha_dummy_908 h)), ((nb078_alpha_dummy_904),
        (nb078_alpha_dummy_907 h)), ((nb078_alpha_dummy_903), (nb078_alpha_dummy_906 h)),
        ((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)), ((nb078_alpha_dummy_897),
        (nb078_alpha_dummy_899 h)), ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)),
        ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889),
        (nb078_alpha_dummy_891 h)), ((nb078_alpha_dummy_895), (nb078_alpha_dummy_896 h)),
        ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848),
        (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_1130),
        (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
        ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠ (nb078_alpha_dummy_911) from (by
          unfold
            nb078_alpha_dummy_911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0934)
                  0)))) (show (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_912 h) from (by
          unfold
            nb078_alpha_dummy_912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0935
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠ (nb078_alpha_dummy_909)
        from (by
          unfold
            nb078_alpha_dummy_909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0932)
                  0)))) (show (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_910 h) from (by
          unfold
            nb078_alpha_dummy_910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0933
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_905) ≠ (nb078_alpha_dummy_911)
        from (by
          unfold
            nb078_alpha_dummy_911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0938)
                  0)))) (show (nb078_alpha_dummy_908 h) ≠ (nb078_alpha_dummy_912 h) from (by
          unfold
            nb078_alpha_dummy_912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0939
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_905) ≠ (nb078_alpha_dummy_909)
        from (by
          unfold
            nb078_alpha_dummy_909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0936)
                  0)))) (show (nb078_alpha_dummy_908 h) ≠ (nb078_alpha_dummy_910 h) from (by
          unfold
            nb078_alpha_dummy_910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0937
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠ (nb078_alpha_dummy_911) from (by
          unfold
            nb078_alpha_dummy_911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0934)
                  0)))) (show (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_912 h) from (by
          unfold
            nb078_alpha_dummy_912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0935
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠ (nb078_alpha_dummy_909)
        from (by
          unfold
            nb078_alpha_dummy_909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0932)
                  0)))) (show (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_910 h) from (by
          unfold
            nb078_alpha_dummy_910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0933
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_905) ≠ (nb078_alpha_dummy_911)
        from (by
          unfold
            nb078_alpha_dummy_911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0938)
                  0)))) (show (nb078_alpha_dummy_908 h) ≠ (nb078_alpha_dummy_912 h) from (by
          unfold
            nb078_alpha_dummy_912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0939
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_905) ≠ (nb078_alpha_dummy_909)
        from (by
          unfold
            nb078_alpha_dummy_909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0936)
                  0)))) (show (nb078_alpha_dummy_908 h) ≠ (nb078_alpha_dummy_910 h) from (by
          unfold
            nb078_alpha_dummy_910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0937
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_905), (nb078_alpha_dummy_908 h)), ((nb078_alpha_dummy_904),
        (nb078_alpha_dummy_907 h)), ((nb078_alpha_dummy_903), (nb078_alpha_dummy_906 h)),
        ((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)), ((nb078_alpha_dummy_897),
        (nb078_alpha_dummy_899 h)), ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)),
        ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889),
        (nb078_alpha_dummy_891 h)), ((nb078_alpha_dummy_895), (nb078_alpha_dummy_896 h)),
        ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848),
        (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_1130),
        (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
        ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_897))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_899
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠
        (nb078_alpha_dummy_915) from (by
          unfold
            nb078_alpha_dummy_915;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0942)
                  0)))) (show (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_916 h) from (by
          unfold
            nb078_alpha_dummy_916;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0943
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠ (nb078_alpha_dummy_913)
        from (by
          unfold
            nb078_alpha_dummy_913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0940)
                  0)))) (show (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_914 h) from (by
          unfold
            nb078_alpha_dummy_914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0941
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠ (nb078_alpha_dummy_915)
        from (by
          unfold
            nb078_alpha_dummy_915;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0942)
                  0)))) (show (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_916 h) from (by
          unfold
            nb078_alpha_dummy_916;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0943
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠ (nb078_alpha_dummy_913)
        from (by
          unfold
            nb078_alpha_dummy_913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0940)
                  0)))) (show (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_914 h) from (by
          unfold
            nb078_alpha_dummy_914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0941
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_905) ≠ (nb078_alpha_dummy_917) from (by
          unfold
            nb078_alpha_dummy_917;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0946)
                  0)))) (show (nb078_alpha_dummy_908 h) ≠ (nb078_alpha_dummy_918 h) from (by
          unfold
            nb078_alpha_dummy_918;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0947
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_905) ≠ (nb078_alpha_dummy_913)
        from (by
          unfold
            nb078_alpha_dummy_913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0944)
                  0)))) (show (nb078_alpha_dummy_908 h) ≠ (nb078_alpha_dummy_914 h) from (by
          unfold
            nb078_alpha_dummy_914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0945
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_905) ≠
        (nb078_alpha_dummy_917) from (by
          unfold
            nb078_alpha_dummy_917;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0946)
                  0)))) (show (nb078_alpha_dummy_908 h) ≠ (nb078_alpha_dummy_918 h) from (by
          unfold
            nb078_alpha_dummy_918;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0947
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_905) ≠ (nb078_alpha_dummy_913)
        from (by
          unfold
            nb078_alpha_dummy_913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0944)
                  0)))) (show (nb078_alpha_dummy_908 h) ≠ (nb078_alpha_dummy_914 h) from (by
          unfold
            nb078_alpha_dummy_914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0945
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_901) from
                                        (by
                                          unfold nb078_alpha_dummy_901;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0928)
                                                  0)))) (show (nb078_alpha_dummy_899 h) ≠
        (nb078_alpha_dummy_902 h) from (by
                                          unfold nb078_alpha_dummy_902;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0929 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)),
                                      ((nb078_alpha_dummy_897), (nb078_alpha_dummy_899 h)),
                                      ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)),
                                      ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)),
                                      ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)),
                                      ((nb078_alpha_dummy_895), (nb078_alpha_dummy_896 h)),
                                      ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)),
                                      ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                                      ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                                      ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
                                      ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
                                      ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
                                      ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
                                      ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                                      ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                      ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                      ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                                      ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                                      ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                                      ((nb078_alpha_dummy_002), h),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_901) from (by
                                        unfold nb078_alpha_dummy_901;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0928)
                                                0)))) (show (nb078_alpha_dummy_899 h) ≠
                                        (nb078_alpha_dummy_902 h) from (by
                                        unfold nb078_alpha_dummy_902;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0929 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_901) from
                                        (by
                                          unfold nb078_alpha_dummy_901;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0928)
                                                  0)))) (show (nb078_alpha_dummy_899 h) ≠
        (nb078_alpha_dummy_902 h) from (by
                                          unfold nb078_alpha_dummy_902;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0929 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)),
                                      ((nb078_alpha_dummy_897), (nb078_alpha_dummy_899 h)),
                                      ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)),
                                      ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)),
                                      ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)),
                                      ((nb078_alpha_dummy_895), (nb078_alpha_dummy_896 h)),
                                      ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)),
                                      ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                                      ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                                      ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
                                      ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
                                      ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
                                      ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
                                      ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                                      ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                      ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                      ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                                      ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                                      ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                                      ((nb078_alpha_dummy_002), h),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
