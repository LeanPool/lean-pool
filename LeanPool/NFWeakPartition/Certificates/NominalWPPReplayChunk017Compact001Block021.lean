/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.CodeCoverBlock001
public import LeanPool.NFWeakPartition.Certificates.CodeCoverBlock002
public import LeanPool.NFWeakPartition.Certificates.CodeCoverBlock003

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk017Compact001Part088`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_cfbhnqinjcodecoverddndv (u : Var) (P : Class) (k : Var) (Y : Class)
    (_dv_P_k : k ∉ P.fv) (dv_P_u : u ∉ P.fv) (_dv_Y_k : k ∉ Y.fv) (_dv_Y_u : u ∉ Y.fv)
    (_dv_k_u : k ≠ u)
    (hyp_cfbhnqinjcodecoverddndv_1 : Nominal.NPrf (.classMem P (syn_cvv)))
    (hyp_cfbhnqinjcodecoverddndv_2 : Nominal.NPrf (.classMem Y (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (syn_chwcn P))
        (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) (.classMem
            (syn_cfv (syn_chnqinc P (syn_cun P Y)) (syn_cec (.cv u) (syn_chwniso P)))
            (syn_crn (syn_chnqinc Y (syn_cun P Y)))))) :=
  by
  exact
    (g_cfbhnqinjcodecoverddndv_stage1 u P k Y dv_P_u hyp_cfbhnqinjcodecoverddndv_1
      hyp_cfbhnqinjcodecoverddndv_2
      (fun p0000 p0001 p0006 p0010 p0011 p0013 p0022 p0023 p0036 p0050 p0069 p0082 p0084
          p0140 p0282 p0286 p0288 p0291 p0292 p0296 p0306 p0310 p0330 p0340 p0346 p0348
          p0359 p0360 p0363 =>
        (g_cfbhnqinjcodecoverddndv_stage2 u P k Y dv_P_u hyp_cfbhnqinjcodecoverddndv_1
          p0001 p0010 p0011 p0023 p0291 p0292 p0359 p0360 p0363
          (fun p0364 p0370 p0374 p0395 p0400 p0403 p0406 p0415 p0417 p0419 p0420 p0421
              p0424 p0425 p0430 p0431 p0440 p0442 p0444 p0451 p0453 p0455 p0458 p0462
              p0466 p0469 p0478 p0480 p0481 p0489 p0494 p0503 p0534 p0541 p0548 p0553
              p0555 p0557 p0558 p0560 p0562 p0565 p0570 p0580 p0585 p0586 p0590 p0605
              p0609 p0621 p0624 p0626 p0628 p0630 p0639 p0641 p0653 p0657 p0660 p0668
              p0677 p0679 p0684 p0689 p0690 =>
            (g_cfbhnqinjcodecoverddndv_stage3 u P k Y p0001 p0006 p0011 p0023 p0082 p0370
              p0395 p0419 p0421 p0424 p0425 p0430 p0431 p0440 p0444 p0458 p0469 p0481
              p0494 p0555 p0557 p0565 p0585 p0590 p0605 p0609 p0626 p0628 p0677 p0689 p0690
              (fun p0691 p0697 p0705 p0715 p0717 p0719 p0721 p0722 p0724 p0726 p0734 p0736
                  p0738 p0742 p0744 p0746 p0747 p0752 p0754 p0764 p0766 p0771 p0773 p0779
                  p0781 p0791 p0794 p0796 p0798 p0805 p0807 p0809 p0815 p0820 p0824 p0825
                  p0827 p0828 p0831 p0834 p0839 p0842 p0846 p0848 p0853 p0859 p0860 p0871
                  p0880 p0888 p0902 p0903 p0906 p0907 p0938 p0939 p0955 p0957 p0961 =>
                (g_cfbhnqinjcodecoverddndv_stage4 u P k Y p0011 p0374 p0400 p0403 p0406
                  p0415 p0417 p0420 p0424 p0425 p0430 p0431 p0444 p0451 p0453 p0455 p0462
                  p0466 p0478 p0480 p0489 p0503 p0565 p0570 p0580 p0586 p0590 p0605 p0621
                  p0624 p0626 p0677 p0679 p0697 p0705 p0722 p0724 p0726 p0747 p0752 p0754
                  p0766 p0771 p0773 p0779 p0781 p0825 p0827 p0828 p0834 p0846 p0938 p0939
                  p0955 p0961
                  (fun p0973 p0974 p0977 p0986 p0997 p1023 p1089 p1121 p1123 p1161 p1163
                      p1208 p1248 p1345 =>
                    (g_cfbhnqinjcodecoverddndv_stage5 u P k Y p0000 p0001 p0011 p0013
                      p0022 p0036 p0050 p0069 p0082 p0084 p0140 p0282 p0286 p0288 p0296
                      p0306 p0310 p0330 p0364 p0534 p0541 p0548 p0553 p0791 p0794 p0796
                      p0798 p0805 p0807 p0809 p0815 p0820 p0825 p0827 p0831 p0839 p0848
                      p0973 p0974 p0977 p0986 p0997 p1023 p1089 p1345
                      (fun p1618 p1621 p1642 p1643 p1645 p1646 p1649 p1652 p1653 p1654
                          p1655 p1656 p1658 p1659 p1662 =>
                        (g_cfbhnqinjcodecoverddndv_stage6 u P k Y p0001 p0286 p0370 p0442
                          p0558 p0560 p0562 p0839 p0842 p0853 p0859 p0860 p0871 p0880
                          p0888 p0902 p0903 p0906 p0907 p0939 p0957 p1123 p1618 p1621
                          p1643 p1645 p1646 p1652 p1653 p1654 p1655 p1656 p1658 p1659 p1662
                          (fun p1664 p1789 p1790 p1793 p1802 p1813 p1841 p1843 p1844 p1847
                              p1853 p1855 p1858 p1859 p1864 p1865 p1877 p1890 p1904 p1915
                              p1934 p1943 p1945 p1953 p1958 p1963 p1966 p1968 =>
                            (g_cfbhnqinjcodecoverddndv_stage7 u P k Y p0628 p0630 p0639
                              p0641 p0653 p0657 p0660 p0668 p0677 p0684 p0691 p0697 p0715
                              p0717 p0719 p0721 p0724 p0726 p0734 p0736 p0738 p0742 p0744
                              p0746 p0752 p0754 p0764 p0773 p0781 p0805 p1121 p1161 p1163
                              p1208 p1248 p1618 p1662 p1664 p1789 p1853 p1858 p1859 p1864
                              p1865 p1877 p1890 p1904 p1915 p1934 p1943 p1945 p1953 p1958
                              p1963 p1966 p1968
                              (fun p2292 p2294 p2309 p2310 p2311 p2312 p2314 =>
                                (g_cfbhnqinjcodecoverddndv_stage8 u P k Y
                                  hyp_cfbhnqinjcodecoverddndv_2 p0286 p0340 p0346 p0348
                                  p0824 p1642 p1643 p1645 p1649 p1789 p1790 p1793 p1802
                                  p1813 p1841 p1843 p1844 p1847 p1855 p2292 p2294 p2309
                                  p2310 p2311 p2312 p2314 (fun p2489 => p2489))))))))))))))))

end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part089`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_cfbhnqinjcodecoverdclndv (C : Class) (P : Class) (k : Var) (Y : Class)
    (dv_P_k : k ∉ P.fv) (dv_Y_k : k ∉ Y.fv)
    (hyp_cfbhnqinjcodecoverdclndv_1 : Nominal.NPrf (.classMem P (syn_cvv)))
    (hyp_cfbhnqinjcodecoverdclndv_2 : Nominal.NPrf (.classMem Y (syn_cvv)))
    (hyp_cfbhnqinjcodecoverdclndv_3 : Nominal.NPrf (.classMem C (syn_chwcn P))) :
    Nominal.NPrf
      (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) C) Y)
        (.classMem (syn_cfv (syn_chnqinc P (syn_cun P Y)) (syn_cec C (syn_chwniso P)))
          (syn_crn (syn_chnqinc Y (syn_cun P Y))))) :=
  by
  let proofSupport : Finset Var := C.fv ∪ P.fv ∪ ({ k } : Finset Var) ∪ Y.fv
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_u_not_P : u ∉ P.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_ne_k : u ≠ k := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_k_ne_u : k ≠ u := Ne.symm fresh_u_ne_k
  have fresh_u_not_Y : u ∉ Y.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have dv_cache_0001 : k ∉ (P).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_P_k, not_false_eq_true])
  have dv_cache_0002 : u ∉ (P).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_P, not_false_eq_true])
  have dv_cache_0003 : k ∉ (Y).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_Y_k, not_false_eq_true])
  have dv_cache_0004 : u ∉ (Y).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_Y, not_false_eq_true])
  have dv_cache_0005 : k ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show k ≠ u from (by exact fresh_k_ne_u))
  have dv_cache_0006 : u ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_C, not_false_eq_true])
  have dv_cache_0007 :
    u ∉
      ((Wff.imp (.classMem C (syn_chwcn P)) (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) C) Y)
            (.classMem (syn_cfv (syn_chnqinc P (syn_cun P Y)) (syn_cec C (syn_chwniso P)))
              (syn_crn (syn_chnqinc Y (syn_cun P Y))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union,
          Finset.mem_singleton, fresh_u_not_C, fresh_u_not_P, fresh_u_not_Y, fresh_u_ne_k,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_elex C (syn_chwcn P)
  have p0001 := Nominal.mp hyp_cfbhnqinjcodecoverdclndv_3 p0000
  have p0002 := @g_id (.classEq (.cv u) C)
  have p0003 := @g_eleq1d (.classEq (.cv u) C) (.cv u) C (syn_chwcn P) p0002
  have p0005 := @g_fveq2d (.classEq (.cv u) C) (.cv u) C (syn_c2nd) p0002
  have p0006 := @g_f1eq2 (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) C) Y (.cv k)
  have p0007 :=
    @g_syl (.classEq (.cv u) C)
      (.classEq (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) C))
      (syn_wb (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) C) Y))
      p0005 p0006
  have p0009 := @g_eceq1 (.cv u) C (syn_chwniso P)
  have p0010 :=
    @g_syl (.classEq (.cv u) C) (.classEq (.cv u) C)
      (.classEq (syn_cec (.cv u) (syn_chwniso P)) (syn_cec C (syn_chwniso P))) p0002 p0009
  have p0011 :=
    @g_fveq2d (.classEq (.cv u) C) (syn_cec (.cv u) (syn_chwniso P))
      (syn_cec C (syn_chwniso P)) (syn_chnqinc P (syn_cun P Y)) p0010
  have p0012 :=
    @g_eleq1d (.classEq (.cv u) C)
      (syn_cfv (syn_chnqinc P (syn_cun P Y)) (syn_cec (.cv u) (syn_chwniso P)))
      (syn_cfv (syn_chnqinc P (syn_cun P Y)) (syn_cec C (syn_chwniso P)))
      (syn_crn (syn_chnqinc Y (syn_cun P Y))) p0011
  have p0013 :=
    @g_imbi12d (.classEq (.cv u) C) (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
      (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) C) Y)
      (.classMem (syn_cfv (syn_chnqinc P (syn_cun P Y)) (syn_cec (.cv u) (syn_chwniso P)))
        (syn_crn (syn_chnqinc Y (syn_cun P Y))))
      (.classMem (syn_cfv (syn_chnqinc P (syn_cun P Y)) (syn_cec C (syn_chwniso P)))
        (syn_crn (syn_chnqinc Y (syn_cun P Y))))
      p0007 p0012
  have p0014 :=
    @g_imbi12d (.classEq (.cv u) C) (.classMem (.cv u) (syn_chwcn P))
      (.classMem C (syn_chwcn P))
      (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) (.classMem
          (syn_cfv (syn_chnqinc P (syn_cun P Y)) (syn_cec (.cv u) (syn_chwniso P)))
          (syn_crn (syn_chnqinc Y (syn_cun P Y)))))
      (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) C) Y)
        (.classMem (syn_cfv (syn_chnqinc P (syn_cun P Y)) (syn_cec C (syn_chwniso P)))
          (syn_crn (syn_chnqinc Y (syn_cun P Y)))))
      p0003 p0013
  have p0015 :=
    @g_cfbhnqinjcodecoverddndv u P k Y dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 hyp_cfbhnqinjcodecoverdclndv_1
      hyp_cfbhnqinjcodecoverdclndv_2
  have p0016 :=
    @g_vtoclg
      (.imp (.classMem (.cv u) (syn_chwcn P))
        (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) (.classMem
            (syn_cfv (syn_chnqinc P (syn_cun P Y)) (syn_cec (.cv u) (syn_chwniso P)))
            (syn_crn (syn_chnqinc Y (syn_cun P Y))))))
      (.imp (.classMem C (syn_chwcn P)) (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) C) Y)
          (.classMem (syn_cfv (syn_chnqinc P (syn_cun P Y)) (syn_cec C (syn_chwniso P)))
            (syn_crn (syn_chnqinc Y (syn_cun P Y))))))
      u C (syn_cvv) dv_cache_0006 dv_cache_0007 p0014 p0015
  have p0017 := Nominal.mp p0001 p0016
  have p0018 := Nominal.mp hyp_cfbhnqinjcodecoverdclndv_3 p0017
  exact p0018


end NFChoice.DirectNominalPrf.WPPReplay

end
