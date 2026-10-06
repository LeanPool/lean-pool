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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0143`. -/
@[expose]
noncomputable def nb078SplitAlpha0143 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy887), (nb078AlphaDummy888 h)),
        ((nb078AlphaDummy885), (nb078AlphaDummy886 h)),
        ((nb078AlphaDummy854), (nb078AlphaDummy856 h)),
        ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
        ((nb078AlphaDummy883), (nb078AlphaDummy884 h)),
        ((nb078AlphaDummy857), (nb078AlphaDummy858 h)),
        ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
        ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
        ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
        ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
        ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy887))
          (synCphi (Class.cv (nb078AlphaDummy854)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy887))
            (synCphi (Class.cv (nb078AlphaDummy854))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy888 h))
          (synCphi (Class.cv (nb078AlphaDummy856 h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy888 h))
            (synCphi (Class.cv (nb078AlphaDummy856 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy854) ≠ (nb078AlphaDummy861) from
                    (by
                      unfold nb078AlphaDummy861;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0888) 0))))
                  (show (nb078AlphaDummy856 h) ≠ (nb078AlphaDummy863 h) from (by
                      unfold nb078AlphaDummy863;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0889 h) 0))))
                  (TAlphaVar.there (show (nb078AlphaDummy854) ≠ (nb078AlphaDummy862) from
                      (by
                        unfold nb078AlphaDummy862;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0888) 1))))
                    (show (nb078AlphaDummy856 h) ≠ (nb078AlphaDummy864 h) from (by
                        unfold nb078AlphaDummy864;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0889 h) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy854) ≠ (nb078AlphaDummy887) from (by
                          unfold nb078AlphaDummy887;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0918) 0))))
                      (show (nb078AlphaDummy856 h) ≠ (nb078AlphaDummy888 h) from (by
                          unfold nb078AlphaDummy888;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0919 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy854) ≠ (nb078AlphaDummy885) from (by
                            unfold nb078AlphaDummy885;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0916) 0))))
                        (show (nb078AlphaDummy856 h) ≠ (nb078AlphaDummy886 h) from (by
                            unfold nb078AlphaDummy886;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0917 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy854))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy856 h))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy861) ≠ (nb078AlphaDummy868) from (by
                                        unfold nb078AlphaDummy868;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0892)
                                                1)))) (show (nb078AlphaDummy863 h) ≠
                                        (nb078AlphaDummy871 h) from (by
                                        unfold nb078AlphaDummy871;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0893 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy861) ≠ (nb078AlphaDummy867) from
                                        (by
                                          unfold nb078AlphaDummy867;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0892)
                                                  0)))) (show (nb078AlphaDummy863 h) ≠
        (nb078AlphaDummy870 h) from (by
                                          unfold nb078AlphaDummy870;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0893 h) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy861) ≠
        (nb078AlphaDummy865) from (by
          unfold nb078AlphaDummy865;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0890) 0)))) (show (nb078AlphaDummy863 h) ≠
        (nb078AlphaDummy866 h) from (by
          unfold nb078AlphaDummy866;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0891 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb078AlphaDummy869),
        (nb078AlphaDummy872 h)), ((nb078AlphaDummy868), (nb078AlphaDummy871 h)),
                                        ((nb078AlphaDummy867), (nb078AlphaDummy870 h)),
                                        ((nb078AlphaDummy865), (nb078AlphaDummy866 h)),
                                        ((nb078AlphaDummy861), (nb078AlphaDummy863 h)),
                                        ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
                                        ((nb078AlphaDummy887), (nb078AlphaDummy888 h)),
                                        ((nb078AlphaDummy885), (nb078AlphaDummy886 h)),
                                        ((nb078AlphaDummy854), (nb078AlphaDummy856 h)),
                                        ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
                                        ((nb078AlphaDummy883), (nb078AlphaDummy884 h)),
                                        ((nb078AlphaDummy857), (nb078AlphaDummy858 h)),
                                        ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                                        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                                        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                                        ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                                        ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                                        ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
                                        ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                                        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                        ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                                        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                                        ((nb078AlphaDummy002), h),
                                        ((nb078AlphaDummy004), y),
                                        ((nb078AlphaDummy003), x)]
                                      (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy868) ≠
        (nb078AlphaDummy875) from (by
          unfold
            nb078AlphaDummy875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0896)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy876 h) from (by
          unfold
            nb078AlphaDummy876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0897
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy873)
        from (by
          unfold
            nb078AlphaDummy873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0894)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy874 h) from (by
          unfold
            nb078AlphaDummy874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0895
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy875)
        from (by
          unfold
            nb078AlphaDummy875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0900)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy876 h) from (by
          unfold
            nb078AlphaDummy876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0901
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy873)
        from (by
          unfold
            nb078AlphaDummy873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0898)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy874 h) from (by
          unfold
            nb078AlphaDummy874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0899
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy875) from (by
          unfold
            nb078AlphaDummy875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0896)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy876 h) from (by
          unfold
            nb078AlphaDummy876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0897
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy873)
        from (by
          unfold
            nb078AlphaDummy873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0894)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy874 h) from (by
          unfold
            nb078AlphaDummy874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0895
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy875)
        from (by
          unfold
            nb078AlphaDummy875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0900)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy876 h) from (by
          unfold
            nb078AlphaDummy876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0901
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy873)
        from (by
          unfold
            nb078AlphaDummy873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0898)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy874 h) from (by
          unfold
            nb078AlphaDummy874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0899
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb078AlphaDummy869), (nb078AlphaDummy872 h)),
        ((nb078AlphaDummy868), (nb078AlphaDummy871 h)), ((nb078AlphaDummy867),
        (nb078AlphaDummy870 h)), ((nb078AlphaDummy865), (nb078AlphaDummy866 h)),
        ((nb078AlphaDummy861), (nb078AlphaDummy863 h)), ((nb078AlphaDummy862),
        (nb078AlphaDummy864 h)), ((nb078AlphaDummy887), (nb078AlphaDummy888 h)),
        ((nb078AlphaDummy885), (nb078AlphaDummy886 h)), ((nb078AlphaDummy854),
        (nb078AlphaDummy856 h)), ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
        ((nb078AlphaDummy883), (nb078AlphaDummy884 h)), ((nb078AlphaDummy857),
        (nb078AlphaDummy858 h)), ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)), ((nb078AlphaDummy851),
        (nb078AlphaDummy852 h)), ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
        ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)), ((nb078AlphaDummy1133),
        (nb078AlphaDummy1134 h)), ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049),
        (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)), ((nb078AlphaDummy1045),
        (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy868) ≠
        (nb078AlphaDummy879) from (by
          unfold
            nb078AlphaDummy879;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0904)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy880 h) from (by
          unfold
            nb078AlphaDummy880;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0905
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy877)
        from (by
          unfold
            nb078AlphaDummy877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0902)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy878 h) from (by
          unfold
            nb078AlphaDummy878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0903
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy879)
        from (by
          unfold
            nb078AlphaDummy879;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0904)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy880 h) from (by
          unfold
            nb078AlphaDummy880;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0905
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy877)
        from (by
          unfold
            nb078AlphaDummy877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0902)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy878 h) from (by
          unfold
            nb078AlphaDummy878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0903
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy881) from (by
          unfold
            nb078AlphaDummy881;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0908)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy882 h) from (by
          unfold
            nb078AlphaDummy882;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0909
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy877)
        from (by
          unfold
            nb078AlphaDummy877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0906)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy878 h) from (by
          unfold
            nb078AlphaDummy878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0907
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy869) ≠
        (nb078AlphaDummy881) from (by
          unfold
            nb078AlphaDummy881;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0908)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy882 h) from (by
          unfold
            nb078AlphaDummy882;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0909
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy877)
        from (by
          unfold
            nb078AlphaDummy877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0906)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy878 h) from (by
          unfold
            nb078AlphaDummy878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0907
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from (by
                                unfold nb078AlphaDummy865;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0890) 0))))
                            (show (nb078AlphaDummy863 h) ≠ (nb078AlphaDummy866 h) from (by
                                unfold nb078AlphaDummy866;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0891 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb078AlphaDummy865), (nb078AlphaDummy866 h)),
                            ((nb078AlphaDummy861), (nb078AlphaDummy863 h)),
                            ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
                            ((nb078AlphaDummy887), (nb078AlphaDummy888 h)),
                            ((nb078AlphaDummy885), (nb078AlphaDummy886 h)),
                            ((nb078AlphaDummy854), (nb078AlphaDummy856 h)),
                            ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
                            ((nb078AlphaDummy883), (nb078AlphaDummy884 h)),
                            ((nb078AlphaDummy857), (nb078AlphaDummy858 h)),
                            ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                            ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                            ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                            ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                            ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                            ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
                            ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                            ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                            ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                            ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                            ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                            ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                            ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                            ((nb078AlphaDummy003), x)]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from (by
                              unfold nb078AlphaDummy865;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0890) 0))))
                          (show (nb078AlphaDummy863 h) ≠ (nb078AlphaDummy866 h) from (by
                              unfold nb078AlphaDummy866;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0891 h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from (by
                                unfold nb078AlphaDummy865;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0890) 0))))
                            (show (nb078AlphaDummy863 h) ≠ (nb078AlphaDummy866 h) from (by
                                unfold nb078AlphaDummy866;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0891 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb078AlphaDummy865), (nb078AlphaDummy866 h)),
                            ((nb078AlphaDummy861), (nb078AlphaDummy863 h)),
                            ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
                            ((nb078AlphaDummy887), (nb078AlphaDummy888 h)),
                            ((nb078AlphaDummy885), (nb078AlphaDummy886 h)),
                            ((nb078AlphaDummy854), (nb078AlphaDummy856 h)),
                            ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
                            ((nb078AlphaDummy883), (nb078AlphaDummy884 h)),
                            ((nb078AlphaDummy857), (nb078AlphaDummy858 h)),
                            ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                            ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                            ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                            ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                            ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                            ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
                            ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                            ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                            ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                            ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                            ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                            ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                            ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                            ((nb078AlphaDummy003), x)]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb078AlphaDummy854) ≠ (nb078AlphaDummy861) from (by
                        unfold nb078AlphaDummy861;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0888) 0))))
                    (show (nb078AlphaDummy856 h) ≠ (nb078AlphaDummy863 h) from (by
                        unfold nb078AlphaDummy863;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0889 h) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy854) ≠ (nb078AlphaDummy862) from (by
                          unfold nb078AlphaDummy862;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0888) 1))))
                      (show (nb078AlphaDummy856 h) ≠ (nb078AlphaDummy864 h) from (by
                          unfold nb078AlphaDummy864;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0889 h) 1))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy854) ≠ (nb078AlphaDummy887) from (by
                            unfold nb078AlphaDummy887;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0918) 0))))
                        (show (nb078AlphaDummy856 h) ≠ (nb078AlphaDummy888 h) from (by
                            unfold nb078AlphaDummy888;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0919 h) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy854) ≠ (nb078AlphaDummy885) from (by
                              unfold nb078AlphaDummy885;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0916) 0))))
                          (show (nb078AlphaDummy856 h) ≠ (nb078AlphaDummy886 h) from (by
                              unfold nb078AlphaDummy886;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0917 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy854))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy856 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb078AlphaDummy861) ≠ (nb078AlphaDummy868) from
                                        (by
                                          unfold nb078AlphaDummy868;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0892)
                                                  1)))) (show (nb078AlphaDummy863 h) ≠
        (nb078AlphaDummy871 h) from (by
                                          unfold nb078AlphaDummy871;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0893 h) 1))))
                                      (TAlphaVar.there (show (nb078AlphaDummy861) ≠
        (nb078AlphaDummy867) from (by
          unfold nb078AlphaDummy867;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0892) 0)))) (show (nb078AlphaDummy863 h) ≠
        (nb078AlphaDummy870 h) from (by
          unfold nb078AlphaDummy870;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0893 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from (by
          unfold nb078AlphaDummy865;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0890) 0)))) (show (nb078AlphaDummy863 h) ≠
        (nb078AlphaDummy866 h) from (by
          unfold nb078AlphaDummy866;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0891 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb078AlphaDummy869),
        (nb078AlphaDummy872 h)), ((nb078AlphaDummy868), (nb078AlphaDummy871 h)),
        ((nb078AlphaDummy867), (nb078AlphaDummy870 h)), ((nb078AlphaDummy865),
        (nb078AlphaDummy866 h)), ((nb078AlphaDummy861), (nb078AlphaDummy863 h)),
        ((nb078AlphaDummy862), (nb078AlphaDummy864 h)), ((nb078AlphaDummy887),
        (nb078AlphaDummy888 h)), ((nb078AlphaDummy885), (nb078AlphaDummy886 h)),
        ((nb078AlphaDummy854), (nb078AlphaDummy856 h)), ((nb078AlphaDummy853),
        (nb078AlphaDummy855 h)), ((nb078AlphaDummy883), (nb078AlphaDummy884 h)),
        ((nb078AlphaDummy857), (nb078AlphaDummy858 h)), ((nb078AlphaDummy848),
        (nb078AlphaDummy850 h)), ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)), ((nb078AlphaDummy1130),
        (nb078AlphaDummy1132 h)), ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
        ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
                                        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy868) ≠
        (nb078AlphaDummy875) from (by
          unfold
            nb078AlphaDummy875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0896)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy876 h) from (by
          unfold
            nb078AlphaDummy876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0897
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy873)
        from (by
          unfold
            nb078AlphaDummy873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0894)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy874 h) from (by
          unfold
            nb078AlphaDummy874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0895
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy875)
        from (by
          unfold
            nb078AlphaDummy875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0900)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy876 h) from (by
          unfold
            nb078AlphaDummy876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0901
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy873)
        from (by
          unfold
            nb078AlphaDummy873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0898)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy874 h) from (by
          unfold
            nb078AlphaDummy874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0899
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy875) from (by
          unfold
            nb078AlphaDummy875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0896)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy876 h) from (by
          unfold
            nb078AlphaDummy876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0897
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy873)
        from (by
          unfold
            nb078AlphaDummy873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0894)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy874 h) from (by
          unfold
            nb078AlphaDummy874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0895
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy875)
        from (by
          unfold
            nb078AlphaDummy875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0900)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy876 h) from (by
          unfold
            nb078AlphaDummy876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0901
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy873)
        from (by
          unfold
            nb078AlphaDummy873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0898)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy874 h) from (by
          unfold
            nb078AlphaDummy874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0899
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy869), (nb078AlphaDummy872 h)), ((nb078AlphaDummy868),
        (nb078AlphaDummy871 h)), ((nb078AlphaDummy867), (nb078AlphaDummy870 h)),
        ((nb078AlphaDummy865), (nb078AlphaDummy866 h)), ((nb078AlphaDummy861),
        (nb078AlphaDummy863 h)), ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
        ((nb078AlphaDummy887), (nb078AlphaDummy888 h)), ((nb078AlphaDummy885),
        (nb078AlphaDummy886 h)), ((nb078AlphaDummy854), (nb078AlphaDummy856 h)),
        ((nb078AlphaDummy853), (nb078AlphaDummy855 h)), ((nb078AlphaDummy883),
        (nb078AlphaDummy884 h)), ((nb078AlphaDummy857), (nb078AlphaDummy858 h)),
        ((nb078AlphaDummy848), (nb078AlphaDummy850 h)), ((nb078AlphaDummy847),
        (nb078AlphaDummy849 h)), ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
        ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)), ((nb078AlphaDummy1129),
        (nb078AlphaDummy1131 h)), ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
        ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050),
        (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)), ((nb078AlphaDummy1047),
        (nb078AlphaDummy1048 h)), ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy868) ≠
        (nb078AlphaDummy879) from (by
          unfold
            nb078AlphaDummy879;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0904)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy880 h) from (by
          unfold
            nb078AlphaDummy880;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0905
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy877)
        from (by
          unfold
            nb078AlphaDummy877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0902)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy878 h) from (by
          unfold
            nb078AlphaDummy878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0903
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy879)
        from (by
          unfold
            nb078AlphaDummy879;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0904)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy880 h) from (by
          unfold
            nb078AlphaDummy880;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0905
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy877)
        from (by
          unfold
            nb078AlphaDummy877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0902)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy878 h) from (by
          unfold
            nb078AlphaDummy878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0903
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy881) from (by
          unfold
            nb078AlphaDummy881;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0908)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy882 h) from (by
          unfold
            nb078AlphaDummy882;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0909
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy877)
        from (by
          unfold
            nb078AlphaDummy877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0906)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy878 h) from (by
          unfold
            nb078AlphaDummy878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0907
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy869) ≠
        (nb078AlphaDummy881) from (by
          unfold
            nb078AlphaDummy881;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0908)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy882 h) from (by
          unfold
            nb078AlphaDummy882;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0909
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy877)
        from (by
          unfold
            nb078AlphaDummy877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0906)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy878 h) from (by
          unfold
            nb078AlphaDummy878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0907
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from (by
                                  unfold nb078AlphaDummy865;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0890) 0))))
                              (show (nb078AlphaDummy863 h) ≠ (nb078AlphaDummy866 h) from
                                (by
                                  unfold nb078AlphaDummy866;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0891 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb078AlphaDummy865), (nb078AlphaDummy866 h)),
                              ((nb078AlphaDummy861), (nb078AlphaDummy863 h)),
                              ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
                              ((nb078AlphaDummy887), (nb078AlphaDummy888 h)),
                              ((nb078AlphaDummy885), (nb078AlphaDummy886 h)),
                              ((nb078AlphaDummy854), (nb078AlphaDummy856 h)),
                              ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
                              ((nb078AlphaDummy883), (nb078AlphaDummy884 h)),
                              ((nb078AlphaDummy857), (nb078AlphaDummy858 h)),
                              ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                              ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                              ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                              ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                              ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                              ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
                              ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                              ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                              ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                              ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                              ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                              ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                              ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                              ((nb078AlphaDummy003), x)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from (by
                                unfold nb078AlphaDummy865;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0890) 0))))
                            (show (nb078AlphaDummy863 h) ≠ (nb078AlphaDummy866 h) from (by
                                unfold nb078AlphaDummy866;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0891 h) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from (by
                                  unfold nb078AlphaDummy865;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0890) 0))))
                              (show (nb078AlphaDummy863 h) ≠ (nb078AlphaDummy866 h) from
                                (by
                                  unfold nb078AlphaDummy866;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0891 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb078AlphaDummy865), (nb078AlphaDummy866 h)),
                              ((nb078AlphaDummy861), (nb078AlphaDummy863 h)),
                              ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
                              ((nb078AlphaDummy887), (nb078AlphaDummy888 h)),
                              ((nb078AlphaDummy885), (nb078AlphaDummy886 h)),
                              ((nb078AlphaDummy854), (nb078AlphaDummy856 h)),
                              ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
                              ((nb078AlphaDummy883), (nb078AlphaDummy884 h)),
                              ((nb078AlphaDummy857), (nb078AlphaDummy858 h)),
                              ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                              ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                              ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                              ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                              ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                              ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
                              ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                              ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                              ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                              ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                              ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                              ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                              ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                              ((nb078AlphaDummy003), x)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0144`. -/
@[expose]
noncomputable def nb078SplitAlpha0144 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy895), (nb078AlphaDummy896 h)),
        ((nb078AlphaDummy893), (nb078AlphaDummy894 h)),
        ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
        ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
        ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
        ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
        ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy895))
          (Class.cab (nb078AlphaDummy889)
            (synWrex (nb078AlphaDummy890) (Class.cv (nb078AlphaDummy848))
              (Wff.classEq (Class.cv (nb078AlphaDummy889))
                (synCphi (Class.cv (nb078AlphaDummy890))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy895)) (Class.cab (nb078AlphaDummy889)
              (synWrex (nb078AlphaDummy890) (Class.cv (nb078AlphaDummy848))
                (Wff.classEq (Class.cv (nb078AlphaDummy889))
                  (synCphi (Class.cv (nb078AlphaDummy890)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy896 h))
          (Class.cab (nb078AlphaDummy891 h)
            (synWrex (nb078AlphaDummy892 h) (Class.cv (nb078AlphaDummy850 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy891 h))
                (synCphi (Class.cv (nb078AlphaDummy892 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy896 h))
            (Class.cab (nb078AlphaDummy891 h)
              (synWrex (nb078AlphaDummy892 h) (Class.cv (nb078AlphaDummy850 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy891 h))
                  (synCphi (Class.cv (nb078AlphaDummy892 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy890) from
                    (by
                      unfold nb078AlphaDummy890;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0920) 1))))
                  (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy892 h) from (by
                      unfold nb078AlphaDummy892;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0922 h) 1))))
                  (TAlphaVar.there (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy889) from
                      (by
                        unfold nb078AlphaDummy889;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0920) 0))))
                    (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy891 h) from (by
                        unfold nb078AlphaDummy891;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0922 h) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy895) from (by
                          unfold nb078AlphaDummy895;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0924) 0))))
                      (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy896 h) from (by
                          unfold nb078AlphaDummy896;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0925 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy893) from (by
                            unfold nb078AlphaDummy893;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0921) 0))))
                        (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy894 h) from (by
                            unfold nb078AlphaDummy894;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0923 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy848))).fv ∪
                      ((Class.cv (nb078AlphaDummy847))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078AlphaDummy850 h))).fv ∪
                      ((Class.cv (nb078AlphaDummy849 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy890) ≠ (nb078AlphaDummy897) from (by
                              unfold nb078AlphaDummy897;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0926) 0))))
                          (show (nb078AlphaDummy892 h) ≠ (nb078AlphaDummy899 h) from (by
                              unfold nb078AlphaDummy899;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0927 h) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy890) ≠ (nb078AlphaDummy898) from (by
                                unfold nb078AlphaDummy898;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0926) 1))))
                            (show (nb078AlphaDummy892 h) ≠ (nb078AlphaDummy900 h) from (by
                                unfold nb078AlphaDummy900;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0927 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy890))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy892 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy897) ≠ (nb078AlphaDummy904) from (by
          unfold nb078AlphaDummy904;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0930) 1)))) (show (nb078AlphaDummy899 h) ≠
        (nb078AlphaDummy907 h) from (by
          unfold nb078AlphaDummy907;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0931 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy897) ≠ (nb078AlphaDummy903) from (by
          unfold nb078AlphaDummy903;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0930) 0)))) (show (nb078AlphaDummy899 h) ≠
        (nb078AlphaDummy906 h) from (by
          unfold nb078AlphaDummy906;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0931 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy897) ≠ (nb078AlphaDummy901) from (by
          unfold nb078AlphaDummy901;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0928) 0)))) (show (nb078AlphaDummy899 h) ≠
        (nb078AlphaDummy902 h) from (by
          unfold nb078AlphaDummy902;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0929 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy905), (nb078AlphaDummy908 h)), ((nb078AlphaDummy904),
        (nb078AlphaDummy907 h)), ((nb078AlphaDummy903), (nb078AlphaDummy906 h)),
        ((nb078AlphaDummy901), (nb078AlphaDummy902 h)), ((nb078AlphaDummy897),
        (nb078AlphaDummy899 h)), ((nb078AlphaDummy898), (nb078AlphaDummy900 h)),
        ((nb078AlphaDummy890), (nb078AlphaDummy892 h)), ((nb078AlphaDummy889),
        (nb078AlphaDummy891 h)), ((nb078AlphaDummy895), (nb078AlphaDummy896 h)),
        ((nb078AlphaDummy893), (nb078AlphaDummy894 h)), ((nb078AlphaDummy848),
        (nb078AlphaDummy850 h)), ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)), ((nb078AlphaDummy1130),
        (nb078AlphaDummy1132 h)), ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
        ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy911) from (by
          unfold
            nb078AlphaDummy911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0934)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy912 h) from (by
          unfold
            nb078AlphaDummy912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0935
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy909)
        from (by
          unfold
            nb078AlphaDummy909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0932)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy910 h) from (by
          unfold
            nb078AlphaDummy910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0933
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy911)
        from (by
          unfold
            nb078AlphaDummy911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0938)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy912 h) from (by
          unfold
            nb078AlphaDummy912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0939
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy909)
        from (by
          unfold
            nb078AlphaDummy909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0936)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy910 h) from (by
          unfold
            nb078AlphaDummy910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0937
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy911) from (by
          unfold
            nb078AlphaDummy911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0934)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy912 h) from (by
          unfold
            nb078AlphaDummy912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0935
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy909)
        from (by
          unfold
            nb078AlphaDummy909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0932)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy910 h) from (by
          unfold
            nb078AlphaDummy910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0933
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy911)
        from (by
          unfold
            nb078AlphaDummy911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0938)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy912 h) from (by
          unfold
            nb078AlphaDummy912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0939
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy909)
        from (by
          unfold
            nb078AlphaDummy909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0936)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy910 h) from (by
          unfold
            nb078AlphaDummy910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0937
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy905), (nb078AlphaDummy908 h)), ((nb078AlphaDummy904),
        (nb078AlphaDummy907 h)), ((nb078AlphaDummy903), (nb078AlphaDummy906 h)),
        ((nb078AlphaDummy901), (nb078AlphaDummy902 h)), ((nb078AlphaDummy897),
        (nb078AlphaDummy899 h)), ((nb078AlphaDummy898), (nb078AlphaDummy900 h)),
        ((nb078AlphaDummy890), (nb078AlphaDummy892 h)), ((nb078AlphaDummy889),
        (nb078AlphaDummy891 h)), ((nb078AlphaDummy895), (nb078AlphaDummy896 h)),
        ((nb078AlphaDummy893), (nb078AlphaDummy894 h)), ((nb078AlphaDummy848),
        (nb078AlphaDummy850 h)), ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)), ((nb078AlphaDummy1130),
        (nb078AlphaDummy1132 h)), ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
        ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy897))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy899 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy904) ≠
        (nb078AlphaDummy915) from (by
          unfold
            nb078AlphaDummy915;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0942)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy916 h) from (by
          unfold
            nb078AlphaDummy916;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0943
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy913)
        from (by
          unfold
            nb078AlphaDummy913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0940)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy914 h) from (by
          unfold
            nb078AlphaDummy914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0941
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy915)
        from (by
          unfold
            nb078AlphaDummy915;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0942)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy916 h) from (by
          unfold
            nb078AlphaDummy916;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0943
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy913)
        from (by
          unfold
            nb078AlphaDummy913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0940)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy914 h) from (by
          unfold
            nb078AlphaDummy914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0941
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy917) from (by
          unfold
            nb078AlphaDummy917;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0946)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy918 h) from (by
          unfold
            nb078AlphaDummy918;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0947
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy913)
        from (by
          unfold
            nb078AlphaDummy913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0944)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy914 h) from (by
          unfold
            nb078AlphaDummy914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0945
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy905) ≠
        (nb078AlphaDummy917) from (by
          unfold
            nb078AlphaDummy917;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0946)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy918 h) from (by
          unfold
            nb078AlphaDummy918;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0947
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy913)
        from (by
          unfold
            nb078AlphaDummy913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0944)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy914 h) from (by
          unfold
            nb078AlphaDummy914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0945
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy897) ≠ (nb078AlphaDummy901) from (by
                                        unfold nb078AlphaDummy901;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0928)
                                                0)))) (show (nb078AlphaDummy899 h) ≠
                                        (nb078AlphaDummy902 h) from (by
                                        unfold nb078AlphaDummy902;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0929 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy901), (nb078AlphaDummy902 h)),
                                    ((nb078AlphaDummy897), (nb078AlphaDummy899 h)),
                                    ((nb078AlphaDummy898), (nb078AlphaDummy900 h)),
                                    ((nb078AlphaDummy890), (nb078AlphaDummy892 h)),
                                    ((nb078AlphaDummy889), (nb078AlphaDummy891 h)),
                                    ((nb078AlphaDummy895), (nb078AlphaDummy896 h)),
                                    ((nb078AlphaDummy893), (nb078AlphaDummy894 h)),
                                    ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                                    ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                                    ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                                    ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                                    ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                                    ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
                                    ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                                    ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                    ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                    ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                    ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                                    ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy897) ≠ (nb078AlphaDummy901) from
                                    (by
                                      unfold nb078AlphaDummy901;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0928)
                                              0)))) (show
                                    (nb078AlphaDummy899 h) ≠ (nb078AlphaDummy902 h) from
                                    (by
                                      unfold nb078AlphaDummy902;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0929 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy897) ≠ (nb078AlphaDummy901) from (by
                                        unfold nb078AlphaDummy901;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0928)
                                                0)))) (show (nb078AlphaDummy899 h) ≠
                                        (nb078AlphaDummy902 h) from (by
                                        unfold nb078AlphaDummy902;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0929 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy901), (nb078AlphaDummy902 h)),
                                    ((nb078AlphaDummy897), (nb078AlphaDummy899 h)),
                                    ((nb078AlphaDummy898), (nb078AlphaDummy900 h)),
                                    ((nb078AlphaDummy890), (nb078AlphaDummy892 h)),
                                    ((nb078AlphaDummy889), (nb078AlphaDummy891 h)),
                                    ((nb078AlphaDummy895), (nb078AlphaDummy896 h)),
                                    ((nb078AlphaDummy893), (nb078AlphaDummy894 h)),
                                    ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                                    ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                                    ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                                    ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                                    ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                                    ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
                                    ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                                    ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                    ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                    ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                    ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                                    ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy890) from
                      (by
                        unfold nb078AlphaDummy890;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0920) 1))))
                    (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy892 h) from (by
                        unfold nb078AlphaDummy892;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0922 h) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy889) from (by
                          unfold nb078AlphaDummy889;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0920) 0))))
                      (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy891 h) from (by
                          unfold nb078AlphaDummy891;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0922 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy895) from (by
                            unfold nb078AlphaDummy895;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0924) 0))))
                        (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy896 h) from (by
                            unfold nb078AlphaDummy896;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0925 h) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy893) from (by
                              unfold nb078AlphaDummy893;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0921) 0))))
                          (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy894 h) from (by
                              unfold nb078AlphaDummy894;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0923 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078AlphaDummy848))).fv ∪
                        ((Class.cv (nb078AlphaDummy847))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy850 h))).fv ∪
                        ((Class.cv (nb078AlphaDummy849 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy890) ≠ (nb078AlphaDummy897) from (by
                                unfold nb078AlphaDummy897;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0926) 0))))
                            (show (nb078AlphaDummy892 h) ≠ (nb078AlphaDummy899 h) from (by
                                unfold nb078AlphaDummy899;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0927 h) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy890) ≠ (nb078AlphaDummy898) from (by
                                  unfold nb078AlphaDummy898;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0926) 1))))
                              (show (nb078AlphaDummy892 h) ≠ (nb078AlphaDummy900 h) from
                                (by
                                  unfold nb078AlphaDummy900;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0927 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy890))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy892 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy897) ≠ (nb078AlphaDummy904) from (by
          unfold nb078AlphaDummy904;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0930) 1)))) (show (nb078AlphaDummy899 h) ≠
        (nb078AlphaDummy907 h) from (by
          unfold nb078AlphaDummy907;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0931 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy897) ≠ (nb078AlphaDummy903) from (by
          unfold nb078AlphaDummy903;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0930) 0)))) (show (nb078AlphaDummy899 h) ≠
        (nb078AlphaDummy906 h) from (by
          unfold nb078AlphaDummy906;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0931 h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy897) ≠ (nb078AlphaDummy901)
        from (by
          unfold nb078AlphaDummy901;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0928)
                  0)))) (show (nb078AlphaDummy899 h) ≠ (nb078AlphaDummy902 h) from (by
          unfold nb078AlphaDummy902;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0929 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy905), (nb078AlphaDummy908 h)), ((nb078AlphaDummy904),
        (nb078AlphaDummy907 h)), ((nb078AlphaDummy903), (nb078AlphaDummy906 h)),
        ((nb078AlphaDummy901), (nb078AlphaDummy902 h)), ((nb078AlphaDummy897),
        (nb078AlphaDummy899 h)), ((nb078AlphaDummy898), (nb078AlphaDummy900 h)),
        ((nb078AlphaDummy890), (nb078AlphaDummy892 h)), ((nb078AlphaDummy889),
        (nb078AlphaDummy891 h)), ((nb078AlphaDummy895), (nb078AlphaDummy896 h)),
        ((nb078AlphaDummy893), (nb078AlphaDummy894 h)), ((nb078AlphaDummy848),
        (nb078AlphaDummy850 h)), ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)), ((nb078AlphaDummy1130),
        (nb078AlphaDummy1132 h)), ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
        ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy911) from (by
          unfold
            nb078AlphaDummy911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0934)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy912 h) from (by
          unfold
            nb078AlphaDummy912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0935
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy909)
        from (by
          unfold
            nb078AlphaDummy909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0932)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy910 h) from (by
          unfold
            nb078AlphaDummy910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0933
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy911)
        from (by
          unfold
            nb078AlphaDummy911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0938)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy912 h) from (by
          unfold
            nb078AlphaDummy912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0939
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy909)
        from (by
          unfold
            nb078AlphaDummy909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0936)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy910 h) from (by
          unfold
            nb078AlphaDummy910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0937
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy911) from (by
          unfold
            nb078AlphaDummy911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0934)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy912 h) from (by
          unfold
            nb078AlphaDummy912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0935
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy909)
        from (by
          unfold
            nb078AlphaDummy909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0932)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy910 h) from (by
          unfold
            nb078AlphaDummy910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0933
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy911)
        from (by
          unfold
            nb078AlphaDummy911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0938)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy912 h) from (by
          unfold
            nb078AlphaDummy912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0939
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy909)
        from (by
          unfold
            nb078AlphaDummy909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0936)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy910 h) from (by
          unfold
            nb078AlphaDummy910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0937
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy905), (nb078AlphaDummy908 h)), ((nb078AlphaDummy904),
        (nb078AlphaDummy907 h)), ((nb078AlphaDummy903), (nb078AlphaDummy906 h)),
        ((nb078AlphaDummy901), (nb078AlphaDummy902 h)), ((nb078AlphaDummy897),
        (nb078AlphaDummy899 h)), ((nb078AlphaDummy898), (nb078AlphaDummy900 h)),
        ((nb078AlphaDummy890), (nb078AlphaDummy892 h)), ((nb078AlphaDummy889),
        (nb078AlphaDummy891 h)), ((nb078AlphaDummy895), (nb078AlphaDummy896 h)),
        ((nb078AlphaDummy893), (nb078AlphaDummy894 h)), ((nb078AlphaDummy848),
        (nb078AlphaDummy850 h)), ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)), ((nb078AlphaDummy1130),
        (nb078AlphaDummy1132 h)), ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
        ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy897))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy899
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy904) ≠
        (nb078AlphaDummy915) from (by
          unfold
            nb078AlphaDummy915;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0942)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy916 h) from (by
          unfold
            nb078AlphaDummy916;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0943
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy913)
        from (by
          unfold
            nb078AlphaDummy913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0940)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy914 h) from (by
          unfold
            nb078AlphaDummy914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0941
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy915)
        from (by
          unfold
            nb078AlphaDummy915;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0942)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy916 h) from (by
          unfold
            nb078AlphaDummy916;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0943
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy913)
        from (by
          unfold
            nb078AlphaDummy913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0940)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy914 h) from (by
          unfold
            nb078AlphaDummy914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0941
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy917) from (by
          unfold
            nb078AlphaDummy917;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0946)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy918 h) from (by
          unfold
            nb078AlphaDummy918;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0947
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy913)
        from (by
          unfold
            nb078AlphaDummy913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0944)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy914 h) from (by
          unfold
            nb078AlphaDummy914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0945
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy905) ≠
        (nb078AlphaDummy917) from (by
          unfold
            nb078AlphaDummy917;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0946)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy918 h) from (by
          unfold
            nb078AlphaDummy918;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0947
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy913)
        from (by
          unfold
            nb078AlphaDummy913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0944)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy914 h) from (by
          unfold
            nb078AlphaDummy914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0945
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy897) ≠ (nb078AlphaDummy901) from
                                        (by
                                          unfold nb078AlphaDummy901;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0928)
                                                  0)))) (show (nb078AlphaDummy899 h) ≠
        (nb078AlphaDummy902 h) from (by
                                          unfold nb078AlphaDummy902;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0929 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy901), (nb078AlphaDummy902 h)),
                                      ((nb078AlphaDummy897), (nb078AlphaDummy899 h)),
                                      ((nb078AlphaDummy898), (nb078AlphaDummy900 h)),
                                      ((nb078AlphaDummy890), (nb078AlphaDummy892 h)),
                                      ((nb078AlphaDummy889), (nb078AlphaDummy891 h)),
                                      ((nb078AlphaDummy895), (nb078AlphaDummy896 h)),
                                      ((nb078AlphaDummy893), (nb078AlphaDummy894 h)),
                                      ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                                      ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                                      ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                                      ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                                      ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                                      ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
                                      ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                                      ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                      ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                      ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                      ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                                      ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                                      ((nb078AlphaDummy002), h),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy897) ≠ (nb078AlphaDummy901) from (by
                                        unfold nb078AlphaDummy901;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0928)
                                                0)))) (show (nb078AlphaDummy899 h) ≠
                                        (nb078AlphaDummy902 h) from (by
                                        unfold nb078AlphaDummy902;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0929 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy897) ≠ (nb078AlphaDummy901) from
                                        (by
                                          unfold nb078AlphaDummy901;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0928)
                                                  0)))) (show (nb078AlphaDummy899 h) ≠
        (nb078AlphaDummy902 h) from (by
                                          unfold nb078AlphaDummy902;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0929 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy901), (nb078AlphaDummy902 h)),
                                      ((nb078AlphaDummy897), (nb078AlphaDummy899 h)),
                                      ((nb078AlphaDummy898), (nb078AlphaDummy900 h)),
                                      ((nb078AlphaDummy890), (nb078AlphaDummy892 h)),
                                      ((nb078AlphaDummy889), (nb078AlphaDummy891 h)),
                                      ((nb078AlphaDummy895), (nb078AlphaDummy896 h)),
                                      ((nb078AlphaDummy893), (nb078AlphaDummy894 h)),
                                      ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                                      ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                                      ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                                      ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                                      ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                                      ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
                                      ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                                      ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                      ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                      ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                      ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                                      ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                                      ((nb078AlphaDummy002), h),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
