/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk016Compact001Block010

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk016Compact001Part048`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wpphitnestndv (m : Var) (n : Var) (F : Class) (H : Class) (I : Class)
    (L : Class) (dv_F_m : m ∉ F.fv) (dv_F_n : n ∉ F.fv) (_dv_H_m : m ∉ H.fv)
    (dv_H_n : n ∉ H.fv) (dv_I_m : m ∉ I.fv) (dv_I_n : n ∉ I.fv) (_dv_L_m : m ∉ L.fv)
    (dv_L_n : n ∉ L.fv) (dv_m_n : m ≠ n) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
              (syn_wss (syn_crn F) (syn_cdm F)))
            (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
              (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc)
            (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))) (syn_wral n (syn_cnnc)
          (.imp (.classMem (.cv n) (syn_cwpphit F I H))
            (.classMem (.cv n) (syn_cwpphit F I L))))) :=
  by
  have dv_cache_0001 : m ∉ ((Class.cv n)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_m_n,
          not_false_eq_true])
  have dv_cache_0002 : m ∉ ((syn_cnnc)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 :
    m ∉ ((Wff.classMem (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cncs))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          Finset.mem_singleton, dv_m_n, dv_F_m, dv_I_m, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0004 : Disjoint (F).fv ((Class.cv n)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint (F).fv ((Class.cv n)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((F).fv) (({ n } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show n ∉ (F).fv from (by exact dv_F_n))))))
  have dv_cache_0005 : Disjoint (I).fv ((Class.cv n)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (show Disjoint (I).fv ((Class.cv n)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((I).fv) (({ n } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show n ∉ (I).fv from (by exact dv_I_n))))))
  have dv_cache_0006 :
    n ∉
      ((syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
              (syn_wss (syn_crn F) (syn_cdm F)))
            (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
              (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc)
            (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfuns,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, dv_F_n, dv_I_n, dv_L_n, dv_H_n, (Ne.symm dv_m_n),
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F)))
          (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H)))
        (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs))))
      (.classMem (.cv n) (syn_cnnc))
  have p0001 :=
    @g_simpl
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F)))
        (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H)))
      (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))
  have p0002 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
              (syn_wss (syn_crn F) (syn_cdm F)))
            (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
              (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc)
            (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs))))
        (.classMem (.cv n) (syn_cnnc)))
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F)))
          (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H)))
        (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs))))
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F)))
        (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H)))
      p0000 p0001
  have p0003 :=
    @g_simpl
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))
  have p0004 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
              (syn_wss (syn_crn F) (syn_cdm F)))
            (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
              (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc)
            (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs))))
        (.classMem (.cv n) (syn_cnnc)))
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F)))
        (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H)))
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      p0002 p0003
  have p0005 :=
    @g_simpr
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F)))
          (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H)))
        (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs))))
      (.classMem (.cv n) (syn_cnnc))
  have p0006 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
              (syn_wss (syn_crn F) (syn_cdm F)))
            (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
              (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc)
            (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs))))
        (.classMem (.cv n) (syn_cnnc)))
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (.classMem (.cv n) (syn_cnnc)) p0004 p0005
  have p0010 :=
    @g_simpr
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))
  have p0011 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
              (syn_wss (syn_crn F) (syn_cdm F)))
            (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
              (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc)
            (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs))))
        (.classMem (.cv n) (syn_cnnc)))
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F)))
        (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H)))
      (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))
      p0002 p0010
  have p0012 :=
    @g_simp1 (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H)
  have p0013 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
              (syn_wss (syn_crn F) (syn_cdm F)))
            (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
              (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc)
            (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs))))
        (.classMem (.cv n) (syn_cnnc)))
      (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))
      (.classMem L (syn_cncs)) p0011 p0012
  have p0019 :=
    @g_simp2 (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H)
  have p0020 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
              (syn_wss (syn_crn F) (syn_cdm F)))
            (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
              (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc)
            (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs))))
        (.classMem (.cv n) (syn_cnnc)))
      (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))
      (.classMem H (syn_cncs)) p0011 p0019
  have p0022 :=
    @g_simpr
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F)))
        (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H)))
      (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))
  have p0023 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
              (syn_wss (syn_crn F) (syn_cdm F)))
            (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
              (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc)
            (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs))))
        (.classMem (.cv n) (syn_cnnc)))
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F)))
          (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H)))
        (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs))))
      (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))
      p0000 p0022
  have p0025 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
              (syn_wss (syn_crn F) (syn_cdm F)))
            (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
              (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc)
            (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs))))
        (.classMem (.cv n) (syn_cnnc)))
      (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))
      (.classMem (.cv n) (syn_cnnc)) p0023 p0005
  have p0026 := @g_fveq2 (.cv m) (.cv n) (syn_cfrec F I)
  have p0027 :=
    @g_eleq1d (.classEq (.cv m) (.cv n)) (syn_cfv (syn_cfrec F I) (.cv m))
      (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cncs) p0026
  have p0028 :=
    @g_rspccva (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs))
      (.classMem (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cncs)) m (.cv n) (syn_cnnc)
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0027
  have p0029 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
              (syn_wss (syn_crn F) (syn_cdm F)))
            (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
              (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc)
            (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs))))
        (.classMem (.cv n) (syn_cnnc)))
      (syn_wa (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs)))
        (.classMem (.cv n) (syn_cnnc)))
      (.classMem (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cncs)) p0025 p0028
  have p0030 :=
    @g_n_3jca
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
              (syn_wss (syn_crn F) (syn_cdm F)))
            (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
              (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc)
            (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs))))
        (.classMem (.cv n) (syn_cnnc)))
      (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
      (.classMem (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cncs)) p0013 p0020 p0029
  have p0036 :=
    @g_simp3 (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H)
  have p0037 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
              (syn_wss (syn_crn F) (syn_cdm F)))
            (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
              (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc)
            (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs))))
        (.classMem (.cv n) (syn_cnnc)))
      (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))
      (syn_wbr L (syn_clec) H) p0011 p0036
  have p0038 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
              (syn_wss (syn_crn F) (syn_cdm F)))
            (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
              (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc)
            (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs))))
        (.classMem (.cv n) (syn_cnnc)))
      (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
        (.classMem (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cncs)))
      (syn_wbr L (syn_clec) H) p0030 p0037
  have p0039 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
              (syn_wss (syn_crn F) (syn_cdm F)))
            (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
              (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc)
            (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs))))
        (.classMem (.cv n) (syn_cnnc)))
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (.classMem (.cv n) (syn_cnnc)))
      (syn_wa (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
          (.classMem (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cncs))) (syn_wbr L (syn_clec) H))
      p0006 p0038
  have p0040 := @g_wpphitnestptndv F H I L (.cv n) dv_cache_0004 dv_cache_0005
  have p0041 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
              (syn_wss (syn_crn F) (syn_cdm F)))
            (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
              (syn_wbr L (syn_clec) H))) (syn_wral m (syn_cnnc)
            (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs))))
        (.classMem (.cv n) (syn_cnnc)))
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (.classMem (.cv n) (syn_cnnc))) (syn_wa
          (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
            (.classMem (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cncs))) (syn_wbr L (syn_clec) H)))
      (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (.classMem (.cv n) (syn_cwpphit F I L)))
      p0039 p0040
  have p0042 :=
    @g_ralrimiva
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F)))
          (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H)))
        (syn_wral m (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv m)) (syn_cncs))))
      (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (.classMem (.cv n) (syn_cwpphit F I L)))
      n (syn_cnnc) dv_cache_0006 p0041
  exact p0042

@[expose]
noncomputable def g_wpphitstepptndv (F : Class) (H : Class) (I : Class) (L : Class)
    (N : Class) (_dv_F_N : Disjoint F.fv N.fv) (_dv_I_N : Disjoint I.fv N.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
              (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
          (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N))
            (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N)))))
        (.imp (.classMem N (syn_cwpphit F I L))
          (.classMem (syn_cplc N (syn_c1c)) (syn_cwpphit F I H)))) :=
  by
  have p0000 :=
    @g_simpl
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
      (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N))
        (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))))
  have p0001 :=
    @g_simpl
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (.classMem N (syn_cnnc))
  have p0002 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
        (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N))
          (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N)))))
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      p0000 p0001
  have p0003 := @g_elwpphitvndv L F I N
  have p0004 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
        (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N))
          (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N)))))
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (syn_wb (.classMem N (syn_cwpphit F I L)) (syn_wa (.classMem N (syn_cnnc))
          (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N))))
      p0002 p0003
  have p0005 :=
    @g_biimpd
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
        (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N))
          (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N)))))
      (.classMem N (syn_cwpphit F I L))
      (syn_wa (.classMem N (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N)))
      p0004
  have p0006 :=
    @g_simpr (.classMem N (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N))
  have p0007 :=
    @g_syl6
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
        (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N))
          (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N)))))
      (.classMem N (syn_cwpphit F I L))
      (syn_wa (.classMem N (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N)))
      (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N)) p0005 p0006
  have p0008 :=
    @g_simpr
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
      (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N))
        (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))))
  have p0009 :=
    @g_syld
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
        (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N))
          (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N)))))
      (.classMem N (syn_cwpphit F I L)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N))
      (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))) p0007 p0008
  have p0014 :=
    @g_simpr
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (.classMem N (syn_cnnc))
  have p0015 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
        (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N))
          (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N)))))
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
      (.classMem N (syn_cnnc)) p0000 p0014
  have p0016 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
        (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N))
          (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N)))))
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (.classMem N (syn_cnnc)) p0002 p0015
  have p0017 := @g_elwpphitsucvndv H F I N
  have p0018 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
        (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N))
          (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N)))))
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
      (syn_wb (.classMem (syn_cplc N (syn_c1c)) (syn_cwpphit F I H))
        (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))))
      p0016 p0017
  have p0019 :=
    @g_biimprd
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
        (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N))
          (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N)))))
      (.classMem (syn_cplc N (syn_c1c)) (syn_cwpphit F I H))
      (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))) p0018
  have p0020 :=
    @g_syld
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
        (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N))
          (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N)))))
      (.classMem N (syn_cwpphit F I L))
      (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N)))
      (.classMem (syn_cplc N (syn_c1c)) (syn_cwpphit F I H)) p0009 p0019
  exact p0020

@[expose]
noncomputable def g_wpphitstepndv (m : Var) (n : Var) (F : Class) (H : Class) (I : Class)
    (L : Class) (dv_F_m : m ∉ F.fv) (dv_F_n : n ∉ F.fv) (dv_H_m : m ∉ H.fv)
    (dv_H_n : n ∉ H.fv) (dv_I_m : m ∉ I.fv) (dv_I_n : n ∉ I.fv) (dv_L_m : m ∉ L.fv)
    (dv_L_n : n ∉ L.fv) (dv_m_n : m ≠ n) :
    Nominal.NPrf
      (.imp (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral m (syn_cnnc)
            (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m)))
              (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))))))
        (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L))
            (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cwpphit F I H))))) :=
  by
  have dv_cache_0001 : m ∉ ((Class.cv n)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_m_n,
          not_false_eq_true])
  have dv_cache_0002 : m ∉ ((syn_cnnc)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 :
    m ∉
      ((Wff.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv n)))
          (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv n)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_L_m, dv_m_n, dv_F_m, dv_I_m, dv_H_m,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 : Disjoint (F).fv ((Class.cv n)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint (F).fv ((Class.cv n)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((F).fv) (({ n } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show n ∉ (F).fv from (by exact dv_F_n))))))
  have dv_cache_0005 : Disjoint (I).fv ((Class.cv n)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (show Disjoint (I).fv ((Class.cv n)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((I).fv) (({ n } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show n ∉ (I).fv from (by exact dv_I_n))))))
  have dv_cache_0006 :
    n ∉
      ((syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral m (syn_cnnc)
            (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m))) (syn_wbr H (syn_clec)
                (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfuns,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, dv_F_n, dv_I_n, dv_L_n, (Ne.symm dv_m_n), dv_H_n,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral m (syn_cnnc)
          (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m)))
            (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))))))
      (.classMem (.cv n) (syn_cnnc))
  have p0001 :=
    @g_simpl
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (syn_wral m (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m)))
          (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))))
  have p0002 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral m (syn_cnnc)
            (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m)))
              (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))))))
        (.classMem (.cv n) (syn_cnnc)))
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral m (syn_cnnc)
          (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m)))
            (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))))))
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      p0000 p0001
  have p0003 :=
    @g_simpr
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral m (syn_cnnc)
          (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m)))
            (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))))))
      (.classMem (.cv n) (syn_cnnc))
  have p0004 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral m (syn_cnnc)
            (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m)))
              (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))))))
        (.classMem (.cv n) (syn_cnnc)))
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (.classMem (.cv n) (syn_cnnc)) p0002 p0003
  have p0006 :=
    @g_simpr
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (syn_wral m (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m)))
          (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))))
  have p0007 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral m (syn_cnnc)
            (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m)))
              (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))))))
        (.classMem (.cv n) (syn_cnnc)))
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral m (syn_cnnc)
          (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m)))
            (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))))))
      (syn_wral m (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m)))
          (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))))
      p0000 p0006
  have p0009 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral m (syn_cnnc)
            (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m)))
              (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))))))
        (.classMem (.cv n) (syn_cnnc)))
      (syn_wral m (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m)))
          (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))))
      (.classMem (.cv n) (syn_cnnc)) p0007 p0003
  have p0010 := @g_fveq2 (.cv m) (.cv n) (syn_cfrec F I)
  have p0011 :=
    @g_breq2d (.classEq (.cv m) (.cv n)) (syn_cfv (syn_cfrec F I) (.cv m))
      (syn_cfv (syn_cfrec F I) (.cv n)) L (syn_clec) p0010
  have p0013 :=
    @g_fveq2d (.classEq (.cv m) (.cv n)) (syn_cfv (syn_cfrec F I) (.cv m))
      (syn_cfv (syn_cfrec F I) (.cv n)) F p0010
  have p0014 :=
    @g_breq2d (.classEq (.cv m) (.cv n)) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))
      (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv n))) H (syn_clec) p0013
  have p0015 :=
    @g_imbi12d (.classEq (.cv m) (.cv n))
      (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m)))
      (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv n)))
      (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))
      (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv n)))) p0011 p0014
  have p0016 :=
    @g_rspccva
      (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m)))
        (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))))
      (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv n)))
        (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv n)))))
      m (.cv n) (syn_cnnc) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0015
  have p0017 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral m (syn_cnnc)
            (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m)))
              (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))))))
        (.classMem (.cv n) (syn_cnnc)))
      (syn_wa (syn_wral m (syn_cnnc)
          (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m)))
            (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m))))))
        (.classMem (.cv n) (syn_cnnc)))
      (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv n)))
        (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv n)))))
      p0009 p0016
  have p0018 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral m (syn_cnnc)
            (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m)))
              (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))))))
        (.classMem (.cv n) (syn_cnnc)))
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (.classMem (.cv n) (syn_cnnc)))
      (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv n)))
        (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv n)))))
      p0004 p0017
  have p0019 := @g_wpphitstepptndv F H I L (.cv n) dv_cache_0004 dv_cache_0005
  have p0020 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral m (syn_cnnc)
            (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m)))
              (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))))))
        (.classMem (.cv n) (syn_cnnc)))
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (.classMem (.cv n) (syn_cnnc)))
        (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv n)))
          (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv n))))))
      (.imp (.classMem (.cv n) (syn_cwpphit F I L))
        (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cwpphit F I H)))
      p0018 p0019
  have p0021 :=
    @g_ralrimiva
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral m (syn_cnnc)
          (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv m)))
            (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv m)))))))
      (.imp (.classMem (.cv n) (syn_cwpphit F I L))
        (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cwpphit F I H)))
      n (syn_cnnc) dv_cache_0006 p0020
  exact p0021


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part049`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wpphitminadjndv (k : Var) (m : Var) (n : Var) (F : Class) (H : Class)
    (I : Class) (L : Class) (r : Var) (q : Var) (dv_F_k : k ∉ F.fv) (dv_F_m : m ∉ F.fv)
    (dv_F_n : n ∉ F.fv) (dv_F_q : q ∉ F.fv) (dv_F_r : r ∉ F.fv) (dv_H_k : k ∉ H.fv)
    (dv_H_m : m ∉ H.fv) (dv_H_n : n ∉ H.fv) (dv_H_q : q ∉ H.fv) (dv_H_r : r ∉ H.fv)
    (dv_I_k : k ∉ I.fv) (dv_I_m : m ∉ I.fv) (dv_I_n : n ∉ I.fv) (dv_I_q : q ∉ I.fv)
    (dv_I_r : r ∉ I.fv) (dv_L_k : k ∉ L.fv) (dv_L_m : m ∉ L.fv) (dv_L_n : n ∉ L.fv)
    (dv_L_q : q ∉ L.fv) (dv_L_r : r ∉ L.fv) (dv_k_m : k ≠ m) (dv_k_n : k ≠ n)
    (dv_m_n : m ≠ n) (dv_n_q : n ≠ q) (dv_n_r : n ≠ r) :
    Nominal.NPrf
      (.imp (syn_w3a (syn_wa
            (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
              (syn_wa (.classMem (.cv m) (syn_cwpphit F I H))
                (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc)
                (.imp (.classMem (.cv n) (syn_cwpphit F I H))
                  (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
                (.imp (.classMem (.cv n) (syn_cwpphit F I L))
                  (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa
              (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
                (syn_wss (syn_crn F) (syn_cdm F)))
              (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
                (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc)
              (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc)
            (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r)))
              (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r)))))))
        (syn_wo (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))))) :=
  by
  have dv_cache_0001 : q ∉ (F).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_q, not_false_eq_true])
  have dv_cache_0002 : n ∉ (F).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_n, not_false_eq_true])
  have dv_cache_0003 : q ∉ (H).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_H_q, not_false_eq_true])
  have dv_cache_0004 : n ∉ (H).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_H_n, not_false_eq_true])
  have dv_cache_0005 : q ∉ (I).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_I_q, not_false_eq_true])
  have dv_cache_0006 : n ∉ (I).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_I_n, not_false_eq_true])
  have dv_cache_0007 : q ∉ (L).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_L_q, not_false_eq_true])
  have dv_cache_0008 : n ∉ (L).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_L_n, not_false_eq_true])
  have dv_cache_0009 : q ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show q ≠ n from (by exact Ne.symm dv_n_q))
  have dv_cache_0010 : r ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_r, not_false_eq_true])
  have dv_cache_0011 : r ∉ (H).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_H_r, not_false_eq_true])
  have dv_cache_0012 : r ∉ (I).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_I_r, not_false_eq_true])
  have dv_cache_0013 : r ∉ (L).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_L_r, not_false_eq_true])
  have dv_cache_0014 : r ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show r ≠ n from (by exact Ne.symm dv_n_r))
  have dv_cache_0015 : k ∉ ((syn_cwpphit F I H)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          Finset.mem_union, dv_H_k, dv_F_k, dv_I_k, or_false, not_false_eq_true])
  have dv_cache_0016 : m ∉ ((syn_cwpphit F I H)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          Finset.mem_union, dv_H_m, dv_F_m, dv_I_m, or_false, not_false_eq_true])
  have dv_cache_0017 : n ∉ ((syn_cwpphit F I H)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          Finset.mem_union, dv_H_n, dv_F_n, dv_I_n, or_false, not_false_eq_true])
  have dv_cache_0018 : k ∉ ((syn_cwpphit F I L)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          Finset.mem_union, dv_L_k, dv_F_k, dv_I_k, or_false, not_false_eq_true])
  have dv_cache_0019 : m ∉ ((syn_cwpphit F I L)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          Finset.mem_union, dv_L_m, dv_F_m, dv_I_m, or_false, not_false_eq_true])
  have dv_cache_0020 : n ∉ ((syn_cwpphit F I L)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          Finset.mem_union, dv_L_n, dv_F_n, dv_I_n, or_false, not_false_eq_true])
  have dv_cache_0021 : k ≠ m :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show k ≠ m from (by exact dv_k_m))
  have dv_cache_0022 : k ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show k ≠ n from (by exact dv_k_n))
  have dv_cache_0023 : m ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show m ≠ n from (by exact dv_m_n))
  have p0000 :=
    @g_simp1
      (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
          (syn_wa (.classMem (.cv m) (syn_cwpphit F I H))
            (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc)
            (.imp (.classMem (.cv n) (syn_cwpphit F I H))
              (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
            (.imp (.classMem (.cv n) (syn_cwpphit F I L))
              (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))))
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F)))
          (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H)))
        (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs))))
      (syn_wral r (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r)))
          (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r))))))
  have p0001 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) (syn_cwpphit F I H))
          (.classMem (.cv k) (syn_cwpphit F I L))))
      (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H))
            (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
          (.imp (.classMem (.cv n) (syn_cwpphit F I L))
            (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
  have p0002 :=
    @g_syl
      (syn_w3a (syn_wa
          (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
            (syn_wa (.classMem (.cv m) (syn_cwpphit F I H))
              (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) (syn_cwpphit F I H))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) (syn_cwpphit F I L))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa
            (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
              (syn_wss (syn_crn F) (syn_cdm F)))
            (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
              (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc)
            (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc)
          (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r)))
            (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r)))))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
          (syn_wa (.classMem (.cv m) (syn_cwpphit F I H))
            (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc)
            (.imp (.classMem (.cv n) (syn_cwpphit F I H))
              (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
            (.imp (.classMem (.cv n) (syn_cwpphit F I L))
              (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))))
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) (syn_cwpphit F I H))
          (.classMem (.cv k) (syn_cwpphit F I L))))
      p0000 p0001
  have p0003 :=
    @g_simpl (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
      (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))
  have p0004 :=
    @g_syl
      (syn_w3a (syn_wa
          (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
            (syn_wa (.classMem (.cv m) (syn_cwpphit F I H))
              (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) (syn_cwpphit F I H))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) (syn_cwpphit F I L))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa
            (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
              (syn_wss (syn_crn F) (syn_cdm F)))
            (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
              (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc)
            (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc)
          (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r)))
            (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r)))))))
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) (syn_cwpphit F I H))
          (.classMem (.cv k) (syn_cwpphit F I L))))
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) p0002 p0003
  have p0008 :=
    @g_simpr (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
      (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))
  have p0009 :=
    @g_syl
      (syn_w3a (syn_wa
          (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
            (syn_wa (.classMem (.cv m) (syn_cwpphit F I H))
              (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) (syn_cwpphit F I H))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) (syn_cwpphit F I L))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa
            (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
              (syn_wss (syn_crn F) (syn_cdm F)))
            (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
              (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc)
            (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc)
          (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r)))
            (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r)))))))
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) (syn_cwpphit F I H))
          (.classMem (.cv k) (syn_cwpphit F I L))))
      (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))
      p0002 p0008
  have p0011 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) (syn_cwpphit F I H))
          (.classMem (.cv k) (syn_cwpphit F I L))))
      (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H))
            (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
          (.imp (.classMem (.cv n) (syn_cwpphit F I L))
            (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
  have p0012 :=
    @g_syl
      (syn_w3a (syn_wa
          (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
            (syn_wa (.classMem (.cv m) (syn_cwpphit F I H))
              (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) (syn_cwpphit F I H))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) (syn_cwpphit F I L))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa
            (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
              (syn_wss (syn_crn F) (syn_cdm F)))
            (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
              (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc)
            (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc)
          (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r)))
            (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r)))))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
          (syn_wa (.classMem (.cv m) (syn_cwpphit F I H))
            (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc)
            (.imp (.classMem (.cv n) (syn_cwpphit F I H))
              (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
            (.imp (.classMem (.cv n) (syn_cwpphit F I L))
              (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))))
      (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H))
            (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
          (.imp (.classMem (.cv n) (syn_cwpphit F I L))
            (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
      p0000 p0011
  have p0013 :=
    @g_simp2
      (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
          (syn_wa (.classMem (.cv m) (syn_cwpphit F I H))
            (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc)
            (.imp (.classMem (.cv n) (syn_cwpphit F I H))
              (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
            (.imp (.classMem (.cv n) (syn_cwpphit F I L))
              (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))))
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F)))
          (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H)))
        (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs))))
      (syn_wral r (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r)))
          (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r))))))
  have p0014 :=
    @g_wpphitnestndv q n F H I L dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0015 :=
    @g_syl
      (syn_w3a (syn_wa
          (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
            (syn_wa (.classMem (.cv m) (syn_cwpphit F I H))
              (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) (syn_cwpphit F I H))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) (syn_cwpphit F I L))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa
            (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
              (syn_wss (syn_crn F) (syn_cdm F)))
            (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
              (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc)
            (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc)
          (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r)))
            (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r)))))))
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F)))
          (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H)))
        (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs))))
      (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H))
          (.classMem (.cv n) (syn_cwpphit F I L))))
      p0013 p0014
  have p0017 :=
    @g_simpl
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F)))
        (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H)))
      (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))
  have p0018 :=
    @g_syl
      (syn_w3a (syn_wa
          (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
            (syn_wa (.classMem (.cv m) (syn_cwpphit F I H))
              (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) (syn_cwpphit F I H))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) (syn_cwpphit F I L))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa
            (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
              (syn_wss (syn_crn F) (syn_cdm F)))
            (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
              (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc)
            (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc)
          (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r)))
            (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r)))))))
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F)))
          (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H)))
        (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs))))
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F)))
        (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H)))
      p0013 p0017
  have p0019 :=
    @g_simpl
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))
  have p0020 :=
    @g_syl
      (syn_w3a (syn_wa
          (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
            (syn_wa (.classMem (.cv m) (syn_cwpphit F I H))
              (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) (syn_cwpphit F I H))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) (syn_cwpphit F I L))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa
            (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
              (syn_wss (syn_crn F) (syn_cdm F)))
            (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
              (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc)
            (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc)
          (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r)))
            (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r)))))))
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F)))
        (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H)))
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      p0018 p0019
  have p0021 :=
    @g_simp3
      (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
          (syn_wa (.classMem (.cv m) (syn_cwpphit F I H))
            (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc)
            (.imp (.classMem (.cv n) (syn_cwpphit F I H))
              (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
            (.imp (.classMem (.cv n) (syn_cwpphit F I L))
              (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))))
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F)))
          (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H)))
        (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs))))
      (syn_wral r (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r)))
          (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r))))))
  have p0022 :=
    @g_jca
      (syn_w3a (syn_wa
          (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
            (syn_wa (.classMem (.cv m) (syn_cwpphit F I H))
              (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) (syn_cwpphit F I H))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) (syn_cwpphit F I L))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa
            (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
              (syn_wss (syn_crn F) (syn_cdm F)))
            (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
              (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc)
            (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc)
          (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r)))
            (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r)))))))
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (syn_wral r (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r)))
          (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r))))))
      p0020 p0021
  have p0023 :=
    @g_wpphitstepndv r n F H I L dv_cache_0010 dv_cache_0002 dv_cache_0011 dv_cache_0004
      dv_cache_0012 dv_cache_0006 dv_cache_0013 dv_cache_0008 dv_cache_0014
  have p0024 :=
    @g_syl
      (syn_w3a (syn_wa
          (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
            (syn_wa (.classMem (.cv m) (syn_cwpphit F I H))
              (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) (syn_cwpphit F I H))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) (syn_cwpphit F I L))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa
            (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
              (syn_wss (syn_crn F) (syn_cdm F)))
            (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
              (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc)
            (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc)
          (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r)))
            (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r)))))))
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral r (syn_cnnc)
          (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r)))
            (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r)))))))
      (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L))
          (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cwpphit F I H))))
      p0022 p0023
  have p0025 :=
    @g_jca
      (syn_w3a (syn_wa
          (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
            (syn_wa (.classMem (.cv m) (syn_cwpphit F I H))
              (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) (syn_cwpphit F I H))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) (syn_cwpphit F I L))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa
            (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
              (syn_wss (syn_crn F) (syn_cdm F)))
            (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
              (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc)
            (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc)
          (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r)))
            (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r)))))))
      (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H))
          (.classMem (.cv n) (syn_cwpphit F I L))))
      (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L))
          (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cwpphit F I H))))
      p0015 p0024
  have p0026 :=
    @g_jca
      (syn_w3a (syn_wa
          (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
            (syn_wa (.classMem (.cv m) (syn_cwpphit F I H))
              (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) (syn_cwpphit F I H))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) (syn_cwpphit F I L))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa
            (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
              (syn_wss (syn_crn F) (syn_cdm F)))
            (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
              (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc)
            (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc)
          (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r)))
            (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r)))))))
      (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H))
            (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
          (.imp (.classMem (.cv n) (syn_cwpphit F I L))
            (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
      (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H))
            (.classMem (.cv n) (syn_cwpphit F I L)))) (syn_wral n (syn_cnnc)
          (.imp (.classMem (.cv n) (syn_cwpphit F I L))
            (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cwpphit F I H)))))
      p0012 p0025
  have p0027 :=
    @g_n_3jca
      (syn_w3a (syn_wa
          (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
            (syn_wa (.classMem (.cv m) (syn_cwpphit F I H))
              (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) (syn_cwpphit F I H))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) (syn_cwpphit F I L))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa
            (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
              (syn_wss (syn_crn F) (syn_cdm F)))
            (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
              (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc)
            (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc)
          (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r)))
            (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r)))))))
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
      (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))
      (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H))
              (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
            (.imp (.classMem (.cv n) (syn_cwpphit F I L))
              (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa
          (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H))
              (.classMem (.cv n) (syn_cwpphit F I L)))) (syn_wral n (syn_cnnc)
            (.imp (.classMem (.cv n) (syn_cwpphit F I L))
              (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cwpphit F I H))))))
      p0004 p0009 p0026
  have p0028 :=
    @g_finleastadjndv k m n (syn_cwpphit F I H) (syn_cwpphit F I L) dv_cache_0015
      dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
      dv_cache_0022 dv_cache_0023
  have p0029 :=
    @g_syl
      (syn_w3a (syn_wa
          (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
            (syn_wa (.classMem (.cv m) (syn_cwpphit F I H))
              (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) (syn_cwpphit F I H))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) (syn_cwpphit F I L))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa
            (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
              (syn_wss (syn_crn F) (syn_cdm F)))
            (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
              (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc)
            (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc)
          (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r)))
            (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r)))))))
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))
        (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) (syn_cwpphit F I L))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H))
                (.classMem (.cv n) (syn_cwpphit F I L)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) (syn_cwpphit F I L))
                (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cwpphit F I H)))))))
      (syn_wo (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))))
      p0027 p0028
  exact p0029

@[expose]
noncomputable def g_wppcardt2fnexndv :
    Nominal.NPrf (.classMem (syn_cwppcardt2fn) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppcardt2fn))
  have p0001 := @g_wppcardtfnexndv
  have p0003 := @g_siex (syn_cwppcardtfn) p0001
  have p0004 := @g_coex (syn_cwppcardtfn) (syn_csi (syn_cwppcardtfn)) p0001 p0003
  have p0005 :=
    @g_eqeltri (syn_cwppcardt2fn) (syn_ccom (syn_cwppcardtfn) (syn_csi (syn_cwppcardtfn)))
      (syn_cvv) p0000 p0004
  exact p0005

@[expose]
noncomputable def g_wppcardt2fnmapndv :
    Nominal.NPrf
      (syn_wf (syn_cwppcardt2fn) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs)) :=
  by
  have p0000 := @g_wppcardtfnmapndv
  have p0002 := @g_sifmap (syn_cpw1 (syn_cncs)) (syn_cncs) (syn_cwppcardtfn)
  have p0003 := Nominal.mp p0000 p0002
  have p0004 :=
    @g_pm3_2i (syn_wf (syn_cwppcardtfn) (syn_cpw1 (syn_cncs)) (syn_cncs))
      (syn_wf (syn_csi (syn_cwppcardtfn)) (syn_cpw1 (syn_cpw1 (syn_cncs)))
        (syn_cpw1 (syn_cncs)))
      p0000 p0003
  have p0005 :=
    @g_fco (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cpw1 (syn_cncs)) (syn_cncs)
      (syn_cwppcardtfn) (syn_csi (syn_cwppcardtfn))
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := (Nominal.classEqRefl (syn_cwppcardt2fn))
  have p0008 :=
    @g_feq1i (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs) (syn_cwppcardt2fn)
      (syn_ccom (syn_cwppcardtfn) (syn_csi (syn_cwppcardtfn))) p0007
  have p0009 :=
    @g_mpbir (syn_wf (syn_cwppcardt2fn) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs))
      (syn_wf (syn_ccom (syn_cwppcardtfn) (syn_csi (syn_cwppcardtfn)))
        (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs))
      p0006 p0008
  exact p0009

@[expose]
noncomputable def g_wppcardt2fnvalsingndv (D : Class) :
    Nominal.NPrf
      (.imp (.classMem D (syn_cncs))
        (.classEq (syn_cfv (syn_cwppcardt2fn) (syn_csn (syn_csn D))) (syn_ctc (syn_ctc D)))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppcardt2fn))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_csn D)) (syn_cwppcardt2fn)
      (syn_ccom (syn_cwppcardtfn) (syn_csi (syn_cwppcardtfn))) p0000
  have p0002 :=
    @g_a1i
      (.classEq (syn_cfv (syn_cwppcardt2fn) (syn_csn (syn_csn D)))
        (syn_cfv (syn_ccom (syn_cwppcardtfn) (syn_csi (syn_cwppcardtfn)))
          (syn_csn (syn_csn D))))
      (.classMem D (syn_cncs)) p0001
  have p0003 := @g_wppcardtfnmapndv
  have p0004 := @g_sifmap (syn_cpw1 (syn_cncs)) (syn_cncs) (syn_cwppcardtfn)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @g_a1i
      (syn_wf (syn_csi (syn_cwppcardtfn)) (syn_cpw1 (syn_cpw1 (syn_cncs)))
        (syn_cpw1 (syn_cncs)))
      (.classMem D (syn_cncs)) p0005
  have p0007 := @g_snelpw1 D (syn_cncs)
  have p0008 :=
    @g_biimpri (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) (.classMem D (syn_cncs))
      p0007
  have p0009 := @g_snelpw1 (syn_csn D) (syn_cpw1 (syn_cncs))
  have p0010 :=
    @g_biimpri (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs))))
      (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) p0009
  have p0011 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_csn D) (syn_cpw1 (syn_cncs)))
      (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0008 p0010
  have p0012 :=
    @g_jca (.classMem D (syn_cncs))
      (syn_wf (syn_csi (syn_cwppcardtfn)) (syn_cpw1 (syn_cpw1 (syn_cncs)))
        (syn_cpw1 (syn_cncs)))
      (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0006 p0011
  have p0013 :=
    @g_fvco3 (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cpw1 (syn_cncs)) (syn_csn (syn_csn D))
      (syn_cwppcardtfn) (syn_csi (syn_cwppcardtfn))
  have p0014 :=
    @g_syl (.classMem D (syn_cncs))
      (syn_wa (syn_wf (syn_csi (syn_cwppcardtfn)) (syn_cpw1 (syn_cpw1 (syn_cncs)))
          (syn_cpw1 (syn_cncs)))
        (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))))
      (.classEq (syn_cfv (syn_ccom (syn_cwppcardtfn) (syn_csi (syn_cwppcardtfn)))
          (syn_csn (syn_csn D))) (syn_cfv (syn_cwppcardtfn)
          (syn_cfv (syn_csi (syn_cwppcardtfn)) (syn_csn (syn_csn D)))))
      p0012 p0013
  have p0015 :=
    @g_eqtrd (.classMem D (syn_cncs)) (syn_cfv (syn_cwppcardt2fn) (syn_csn (syn_csn D)))
      (syn_cfv (syn_ccom (syn_cwppcardtfn) (syn_csi (syn_cwppcardtfn))) (syn_csn (syn_csn D)))
      (syn_cfv (syn_cwppcardtfn) (syn_cfv (syn_csi (syn_cwppcardtfn)) (syn_csn (syn_csn D))))
      p0002 p0014
  have p0019 :=
    @g_sifvald (syn_cpw1 (syn_cncs)) (syn_cncs) (syn_csn D) (syn_cwppcardtfn) p0003
  have p0020 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_csn D) (syn_cpw1 (syn_cncs)))
      (.classEq (syn_cfv (syn_csi (syn_cwppcardtfn)) (syn_csn (syn_csn D)))
        (syn_csn (syn_cfv (syn_cwppcardtfn) (syn_csn D))))
      p0008 p0019
  have p0021 := @g_wppcardtfnvalsingndv D
  have p0022 :=
    @g_sneqd (.classMem D (syn_cncs)) (syn_cfv (syn_cwppcardtfn) (syn_csn D)) (syn_ctc D)
      p0021
  have p0023 :=
    @g_eqtrd (.classMem D (syn_cncs))
      (syn_cfv (syn_csi (syn_cwppcardtfn)) (syn_csn (syn_csn D)))
      (syn_csn (syn_cfv (syn_cwppcardtfn) (syn_csn D))) (syn_csn (syn_ctc D)) p0020 p0022
  have p0024 :=
    @g_fveq2d (.classMem D (syn_cncs))
      (syn_cfv (syn_csi (syn_cwppcardtfn)) (syn_csn (syn_csn D))) (syn_csn (syn_ctc D))
      (syn_cwppcardtfn) p0023
  have p0025 :=
    @g_eqtrd (.classMem D (syn_cncs)) (syn_cfv (syn_cwppcardt2fn) (syn_csn (syn_csn D)))
      (syn_cfv (syn_cwppcardtfn) (syn_cfv (syn_csi (syn_cwppcardtfn)) (syn_csn (syn_csn D))))
      (syn_cfv (syn_cwppcardtfn) (syn_csn (syn_ctc D))) p0015 p0024
  have p0026 := @g_tccl D
  have p0027 := @g_wppcardtfnvalsingndv (syn_ctc D)
  have p0028 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_ctc D) (syn_cncs))
      (.classEq (syn_cfv (syn_cwppcardtfn) (syn_csn (syn_ctc D))) (syn_ctc (syn_ctc D)))
      p0026 p0027
  have p0029 :=
    @g_eqtrd (.classMem D (syn_cncs)) (syn_cfv (syn_cwppcardt2fn) (syn_csn (syn_csn D)))
      (syn_cfv (syn_cwppcardtfn) (syn_csn (syn_ctc D))) (syn_ctc (syn_ctc D)) p0025 p0028
  exact p0029

@[expose]
noncomputable def g_hwgenvalclndv (B : Class) (C : Class)
    (hyp_hwgenvalclndv_1 : Nominal.NPrf (.classMem B (syn_cvv)))
    (hyp_hwgenvalclndv_2 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_chwgen) (syn_cop B C)) (syn_cop (syn_cop C (syn_cdm B))
          (syn_cop (syn_ccom (syn_ccom B C) (syn_ccnv B)) (syn_crn B)))) :=
  by
  let proofSupport : Finset Var := B.fv ∪ C.fv
  let f : Var := freshVar proofSupport 0
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_B : f ∉ B.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (h))
  have fresh_f_not_C : f ∉ C.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have dv_cache_0001 : f ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_B, not_false_eq_true])
  have dv_cache_0002 :
    f ∉
      ((Wff.classEq (syn_cfv (syn_chwgen) (syn_cop B C)) (syn_cop (syn_cop C (syn_cdm B))
            (syn_cop (syn_ccom (syn_ccom B C) (syn_ccnv B)) (syn_crn B))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union,
          fresh_f_not_B, fresh_f_not_C, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @g_id (.classEq (.cv f) B)
  have p0001 := @g_opeq1d (.classEq (.cv f) B) (.cv f) B C p0000
  have p0002 :=
    @g_fveq2d (.classEq (.cv f) B) (syn_cop (.cv f) C) (syn_cop B C) (syn_chwgen) p0001
  have p0004 := @g_dmeqd (.classEq (.cv f) B) (.cv f) B p0000
  have p0005 := @g_opeq2d (.classEq (.cv f) B) (syn_cdm (.cv f)) (syn_cdm B) C p0004
  have p0007 := @g_coeq1d (.classEq (.cv f) B) (.cv f) B C p0000
  have p0009 := @g_cnveqd (.classEq (.cv f) B) (.cv f) B p0000
  have p0010 :=
    @g_coeq12d (.classEq (.cv f) B) (syn_ccom (.cv f) C) (syn_ccom B C) (syn_ccnv (.cv f))
      (syn_ccnv B) p0007 p0009
  have p0012 := @g_rneqd (.classEq (.cv f) B) (.cv f) B p0000
  have p0013 :=
    @g_opeq12d (.classEq (.cv f) B) (syn_ccom (syn_ccom (.cv f) C) (syn_ccnv (.cv f)))
      (syn_ccom (syn_ccom B C) (syn_ccnv B)) (syn_crn (.cv f)) (syn_crn B) p0010 p0012
  have p0014 :=
    @g_opeq12d (.classEq (.cv f) B) (syn_cop C (syn_cdm (.cv f))) (syn_cop C (syn_cdm B))
      (syn_cop (syn_ccom (syn_ccom (.cv f) C) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
      (syn_cop (syn_ccom (syn_ccom B C) (syn_ccnv B)) (syn_crn B)) p0005 p0013
  have p0015 :=
    @g_eqeq12d (.classEq (.cv f) B) (syn_cfv (syn_chwgen) (syn_cop (.cv f) C))
      (syn_cfv (syn_chwgen) (syn_cop B C))
      (syn_cop (syn_cop C (syn_cdm (.cv f)))
        (syn_cop (syn_ccom (syn_ccom (.cv f) C) (syn_ccnv (.cv f))) (syn_crn (.cv f))))
      (syn_cop (syn_cop C (syn_cdm B))
        (syn_cop (syn_ccom (syn_ccom B C) (syn_ccnv B)) (syn_crn B)))
      p0002 p0014
  have p0016 := @g_hwgenval C f hyp_hwgenvalclndv_2
  have p0017 :=
    @g_vtoclg
      (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) C))
        (syn_cop (syn_cop C (syn_cdm (.cv f)))
          (syn_cop (syn_ccom (syn_ccom (.cv f) C) (syn_ccnv (.cv f))) (syn_crn (.cv f)))))
      (.classEq (syn_cfv (syn_chwgen) (syn_cop B C)) (syn_cop (syn_cop C (syn_cdm B))
          (syn_cop (syn_ccom (syn_ccom B C) (syn_ccnv B)) (syn_crn B))))
      f B (syn_cvv) dv_cache_0001 dv_cache_0002 p0015 p0016
  have p0018 := Nominal.mp hyp_hwgenvalclndv_1 p0017
  exact p0018

@[expose]
noncomputable def g_hnbaseresfnvalndv (u : Var) (F : Class)
    (hyp_hnbaseresfnvalndv_1 : Nominal.NPrf (.classMem F (syn_cvv)))
    (hyp_hnbaseresfnvalndv_2 : Nominal.NPrf (.classMem (.cv u) (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_chnbaseresfn F) (.cv u))
        (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chnbaseresfn F))
  have p0001 :=
    @g_fveq1i (.cv u) (syn_chnbaseresfn F)
      (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)))
      p0000
  have p0002 := @g_fnconstg (syn_cvv) F (syn_cvv)
  have p0003 := Nominal.mp hyp_hnbaseresfnvalndv_1 p0002
  have p0004 := @g_ln2ndfn
  have p0005 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn F)) (syn_cvv))
      (syn_wfn (syn_c2nd) (syn_cvv)) p0003 p0004
  have p0006 := @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 := @g_inidm (syn_cvv)
  have p0009 := @g_eqcomi (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) p0008
  have p0010 :=
    @g_fneq2i (syn_cvv) (syn_cin (syn_cvv) (syn_cvv))
      (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)) p0009
  have p0011 :=
    @g_mpbir (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)) (syn_cvv))
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd))
        (syn_cin (syn_cvv) (syn_cvv)))
      p0007 p0010
  have p0012 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)) (syn_cvv))
      (.classMem (.cv u) (syn_cvv)) p0011 hyp_hnbaseresfnvalndv_2
  have p0013 :=
    @g_fvco2 (syn_cvv) (.cv u) (syn_clnimageresfn)
      (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd))
  have p0014 := Nominal.mp p0012 p0013
  have p0018 :=
    @g_fvtxpvv (.cv u) (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd) p0003 p0004
      hyp_hnbaseresfnvalndv_2
  have p0019 := @g_fvconst2 (syn_cvv) F (.cv u) hyp_hnbaseresfnvalndv_1
  have p0020 := Nominal.mp hyp_hnbaseresfnvalndv_2 p0019
  have p0021 := @g_eqid (syn_cfv (syn_c2nd) (.cv u))
  have p0022 :=
    @g_opeq12i (syn_cfv (syn_cxp (syn_cvv) (syn_csn F)) (.cv u)) F
      (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) p0020 p0021
  have p0023 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)) (.cv u))
      (syn_cop (syn_cfv (syn_cxp (syn_cvv) (syn_csn F)) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_cop F (syn_cfv (syn_c2nd) (.cv u))) p0018 p0022
  have p0024 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)) (.cv u))
      (syn_cop F (syn_cfv (syn_c2nd) (.cv u))) (syn_clnimageresfn) p0023
  have p0025 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_clnimageresfn)
          (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd))) (.cv u))
      (syn_cfv (syn_clnimageresfn)
        (syn_cfv (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)) (.cv u)))
      (syn_cfv (syn_clnimageresfn) (syn_cop F (syn_cfv (syn_c2nd) (.cv u)))) p0014 p0024
  have p0026 := @g_fvex (.cv u) (syn_c2nd)
  have p0027 :=
    @g_lnimageresfnval (syn_cfv (syn_c2nd) (.cv u)) F hyp_hnbaseresfnvalndv_1 p0026
  have p0028 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_clnimageresfn)
          (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd))) (.cv u))
      (syn_cfv (syn_clnimageresfn) (syn_cop F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0025 p0027
  have p0029 :=
    @g_eqtri (syn_cfv (syn_chnbaseresfn F) (.cv u))
      (syn_cfv (syn_ccom (syn_clnimageresfn)
          (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd))) (.cv u))
      (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0001 p0028
  exact p0029


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part050`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hncodetrnfnvalndv (u : Var) (F : Class)
    (hyp_hncodetrnfnvalndv_1 : Nominal.NPrf (.classMem F (syn_cvv)))
    (hyp_hncodetrnfnvalndv_2 : Nominal.NPrf (.classMem (.cv u) (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_cop (syn_ccom
            (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
            (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chncodetrnfn F))
  have p0001 :=
    @g_fveq1i (.cv u) (syn_chncodetrnfn F)
      (syn_ccom (syn_c2nd) (syn_ccom (syn_chwgen) (syn_ctxp (syn_chnbaseresfn F) (syn_c1st))))
      p0000
  have p0002 := @g_hwgenfn
  have p0003 := @g_lnimageresfnfn
  have p0004 := @g_fnconstg (syn_cvv) F (syn_cvv)
  have p0005 := Nominal.mp hyp_hncodetrnfnvalndv_1 p0004
  have p0006 := @g_ln2ndfn
  have p0007 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn F)) (syn_cvv))
      (syn_wfn (syn_c2nd) (syn_cvv)) p0005 p0006
  have p0008 := @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @g_inidm (syn_cvv)
  have p0011 := @g_eqcomi (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) p0010
  have p0012 :=
    @g_fneq2i (syn_cvv) (syn_cin (syn_cvv) (syn_cvv))
      (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)) p0011
  have p0013 :=
    @g_mpbir (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)) (syn_cvv))
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd))
        (syn_cin (syn_cvv) (syn_cvv)))
      p0009 p0012
  have p0014 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd))
      p0003 p0013
  have p0015 := (Nominal.classEqRefl (syn_chnbaseresfn F))
  have p0016 :=
    @g_fneq1i (syn_cvv) (syn_chnbaseresfn F)
      (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)))
      p0015
  have p0017 :=
    @g_mpbir (syn_wfn (syn_chnbaseresfn F) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clnimageresfn)
          (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd))) (syn_cvv))
      p0014 p0016
  have p0018 := @g_ln1stfn
  have p0019 :=
    @g_pm3_2i (syn_wfn (syn_chnbaseresfn F) (syn_cvv)) (syn_wfn (syn_c1st) (syn_cvv))
      p0017 p0018
  have p0020 := @g_fntxp (syn_cvv) (syn_cvv) (syn_chnbaseresfn F) (syn_c1st)
  have p0021 := Nominal.mp p0019 p0020
  have p0024 :=
    @g_fneq2i (syn_cvv) (syn_cin (syn_cvv) (syn_cvv))
      (syn_ctxp (syn_chnbaseresfn F) (syn_c1st)) p0011
  have p0025 :=
    @g_mpbir (syn_wfn (syn_ctxp (syn_chnbaseresfn F) (syn_c1st)) (syn_cvv))
      (syn_wfn (syn_ctxp (syn_chnbaseresfn F) (syn_c1st)) (syn_cin (syn_cvv) (syn_cvv)))
      p0021 p0024
  have p0026 :=
    @g_fncovv (syn_chwgen) (syn_ctxp (syn_chnbaseresfn F) (syn_c1st)) p0002 p0025
  have p0027 :=
    @g_pm3_2i
      (syn_wfn (syn_ccom (syn_chwgen) (syn_ctxp (syn_chnbaseresfn F) (syn_c1st))) (syn_cvv))
      (.classMem (.cv u) (syn_cvv)) p0026 hyp_hncodetrnfnvalndv_2
  have p0028 :=
    @g_fvco2 (syn_cvv) (.cv u) (syn_c2nd)
      (syn_ccom (syn_chwgen) (syn_ctxp (syn_chnbaseresfn F) (syn_c1st)))
  have p0029 := Nominal.mp p0027 p0028
  have p0053 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_chnbaseresfn F) (syn_c1st)) (syn_cvv))
      (.classMem (.cv u) (syn_cvv)) p0025 hyp_hncodetrnfnvalndv_2
  have p0054 :=
    @g_fvco2 (syn_cvv) (.cv u) (syn_chwgen) (syn_ctxp (syn_chnbaseresfn F) (syn_c1st))
  have p0055 := Nominal.mp p0053 p0054
  have p0072 :=
    @g_fvtxpvv (.cv u) (syn_chnbaseresfn F) (syn_c1st) p0017 p0018 hyp_hncodetrnfnvalndv_2
  have p0073 := @g_hnbaseresfnvalndv u F hyp_hncodetrnfnvalndv_1 hyp_hncodetrnfnvalndv_2
  have p0074 := @g_eqid (syn_cfv (syn_c1st) (.cv u))
  have p0075 :=
    @g_opeq12i (syn_cfv (syn_chnbaseresfn F) (.cv u))
      (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))
      (syn_cfv (syn_c1st) (.cv u)) p0073 p0074
  have p0076 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_chnbaseresfn F) (syn_c1st)) (.cv u))
      (syn_cop (syn_cfv (syn_chnbaseresfn F) (.cv u)) (syn_cfv (syn_c1st) (.cv u)))
      (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
      p0072 p0075
  have p0077 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_chnbaseresfn F) (syn_c1st)) (.cv u))
      (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
      (syn_chwgen) p0076
  have p0078 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_chwgen) (syn_ctxp (syn_chnbaseresfn F) (syn_c1st))) (.cv u))
      (syn_cfv (syn_chwgen) (syn_cfv (syn_ctxp (syn_chnbaseresfn F) (syn_c1st)) (.cv u)))
      (syn_cfv (syn_chwgen)
        (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))))
      p0055 p0077
  have p0079 := @g_fvex (.cv u) (syn_c2nd)
  have p0080 := @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hncodetrnfnvalndv_1 p0079
  have p0081 := @g_fvex (.cv u) (syn_c1st)
  have p0082 :=
    @g_hwgenvalclndv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
      (syn_cfv (syn_c1st) (.cv u)) p0080 p0081
  have p0083 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_chwgen) (syn_ctxp (syn_chnbaseresfn F) (syn_c1st))) (.cv u))
      (syn_cfv (syn_chwgen)
        (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))))
      (syn_cop (syn_cop (syn_cfv (syn_c1st) (.cv u))
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cop (syn_ccom
            (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
            (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      p0078 p0082
  have p0084 :=
    @g_fveq2i
      (syn_cfv (syn_ccom (syn_chwgen) (syn_ctxp (syn_chnbaseresfn F) (syn_c1st))) (.cv u))
      (syn_cop (syn_cop (syn_cfv (syn_c1st) (.cv u))
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cop (syn_ccom
            (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
            (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_c2nd) p0083
  have p0085 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_c2nd)
          (syn_ccom (syn_chwgen) (syn_ctxp (syn_chnbaseresfn F) (syn_c1st)))) (.cv u))
      (syn_cfv (syn_c2nd)
        (syn_cfv (syn_ccom (syn_chwgen) (syn_ctxp (syn_chnbaseresfn F) (syn_c1st))) (.cv u)))
      (syn_cfv (syn_c2nd) (syn_cop (syn_cop (syn_cfv (syn_c1st) (.cv u))
            (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cop (syn_ccom
              (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
              (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))
      p0029 p0084
  have p0089 := @g_dmex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0080
  have p0090 :=
    @g_opex (syn_cfv (syn_c1st) (.cv u))
      (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0081 p0089
  have p0094 :=
    @g_coex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)) p0080
      p0081
  have p0097 := @g_cnvex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0080
  have p0098 :=
    @g_coex
      (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
      (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0094 p0097
  have p0101 := @g_rnex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0080
  have p0102 :=
    @g_opex
      (syn_ccom
        (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
        (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0098 p0101
  have p0103 :=
    @g_opfv2nd
      (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
            (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0090 p0102
  have p0104 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_c2nd)
          (syn_ccom (syn_chwgen) (syn_ctxp (syn_chnbaseresfn F) (syn_c1st)))) (.cv u))
      (syn_cfv (syn_c2nd) (syn_cop (syn_cop (syn_cfv (syn_c1st) (.cv u))
            (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cop (syn_ccom
              (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
              (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))
      (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
            (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0085 p0103
  have p0105 :=
    @g_eqtri (syn_cfv (syn_chncodetrnfn F) (.cv u))
      (syn_cfv (syn_ccom (syn_c2nd)
          (syn_ccom (syn_chwgen) (syn_ctxp (syn_chnbaseresfn F) (syn_c1st)))) (.cv u))
      (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
            (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0001 p0104
  exact p0105


end NFChoice.DirectNominalPrf.WPPReplay

end
