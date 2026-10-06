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

/-- Checked nominal proof certificate identified upstream as `g_wpphitnestndv`. -/
@[expose]
noncomputable def gWpphitnestndv (m : Var) (n : Var) (F : Class) (H : Class) (I : Class)
    (L : Class) (dv_F_m : m ∉ F.fv) (dv_F_n : n ∉ F.fv) (_dv_H_m : m ∉ H.fv)
    (dv_H_n : n ∉ H.fv) (dv_I_m : m ∉ I.fv) (dv_I_n : n ∉ I.fv) (_dv_L_m : m ∉ L.fv)
    (dv_L_n : n ∉ L.fv) (dv_m_n : m ≠ n) :
    Nominal.NPrf
      (.imp (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
              (synWss (synCrn F) (synCdm F)))
            (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
              (synWbr L (synClec) H))) (synWral m (synCnnc)
            (.classMem (synCfv (synCfrec F I) (.cv m)) (synCncs)))) (synWral n (synCnnc)
          (.imp (.classMem (.cv n) (synCwpphit F I H))
            (.classMem (.cv n) (synCwpphit F I L))))) :=
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
  have dv_cache_0002 : m ∉ ((synCnnc)).fv :=
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
    m ∉ ((Wff.classMem (synCfv (synCfrec F I) (.cv n)) (synCncs))).fv :=
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
      ((synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
              (synWss (synCrn F) (synCdm F)))
            (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
              (synWbr L (synClec) H))) (synWral m (synCnnc)
            (.classMem (synCfv (synCfrec F I) (.cv m)) (synCncs))))).fv :=
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
    @gSimpl
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F)))
          (synW3a (.classMem L (synCncs)) (.classMem H (synCncs)) (synWbr L (synClec) H)))
        (synWral m (synCnnc) (.classMem (synCfv (synCfrec F I) (.cv m)) (synCncs))))
      (.classMem (.cv n) (synCnnc))
  have p0001 :=
    @gSimpl
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F)))
        (synW3a (.classMem L (synCncs)) (.classMem H (synCncs)) (synWbr L (synClec) H)))
      (synWral m (synCnnc) (.classMem (synCfv (synCfrec F I) (.cv m)) (synCncs)))
  have p0002 :=
    @gSyl
      (synWa (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
              (synWss (synCrn F) (synCdm F)))
            (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
              (synWbr L (synClec) H))) (synWral m (synCnnc)
            (.classMem (synCfv (synCfrec F I) (.cv m)) (synCncs))))
        (.classMem (.cv n) (synCnnc)))
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F)))
          (synW3a (.classMem L (synCncs)) (.classMem H (synCncs)) (synWbr L (synClec) H)))
        (synWral m (synCnnc) (.classMem (synCfv (synCfrec F I) (.cv m)) (synCncs))))
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F)))
        (synW3a (.classMem L (synCncs)) (.classMem H (synCncs)) (synWbr L (synClec) H)))
      p0000 p0001
  have p0003 :=
    @gSimpl
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (synW3a (.classMem L (synCncs)) (.classMem H (synCncs)) (synWbr L (synClec) H))
  have p0004 :=
    @gSyl
      (synWa (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
              (synWss (synCrn F) (synCdm F)))
            (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
              (synWbr L (synClec) H))) (synWral m (synCnnc)
            (.classMem (synCfv (synCfrec F I) (.cv m)) (synCncs))))
        (.classMem (.cv n) (synCnnc)))
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F)))
        (synW3a (.classMem L (synCncs)) (.classMem H (synCncs)) (synWbr L (synClec) H)))
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      p0002 p0003
  have p0005 :=
    @gSimpr
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F)))
          (synW3a (.classMem L (synCncs)) (.classMem H (synCncs)) (synWbr L (synClec) H)))
        (synWral m (synCnnc) (.classMem (synCfv (synCfrec F I) (.cv m)) (synCncs))))
      (.classMem (.cv n) (synCnnc))
  have p0006 :=
    @gJca
      (synWa (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
              (synWss (synCrn F) (synCdm F)))
            (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
              (synWbr L (synClec) H))) (synWral m (synCnnc)
            (.classMem (synCfv (synCfrec F I) (.cv m)) (synCncs))))
        (.classMem (.cv n) (synCnnc)))
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (.classMem (.cv n) (synCnnc)) p0004 p0005
  have p0010 :=
    @gSimpr
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (synW3a (.classMem L (synCncs)) (.classMem H (synCncs)) (synWbr L (synClec) H))
  have p0011 :=
    @gSyl
      (synWa (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
              (synWss (synCrn F) (synCdm F)))
            (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
              (synWbr L (synClec) H))) (synWral m (synCnnc)
            (.classMem (synCfv (synCfrec F I) (.cv m)) (synCncs))))
        (.classMem (.cv n) (synCnnc)))
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F)))
        (synW3a (.classMem L (synCncs)) (.classMem H (synCncs)) (synWbr L (synClec) H)))
      (synW3a (.classMem L (synCncs)) (.classMem H (synCncs)) (synWbr L (synClec) H))
      p0002 p0010
  have p0012 :=
    @gSimp1 (.classMem L (synCncs)) (.classMem H (synCncs)) (synWbr L (synClec) H)
  have p0013 :=
    @gSyl
      (synWa (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
              (synWss (synCrn F) (synCdm F)))
            (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
              (synWbr L (synClec) H))) (synWral m (synCnnc)
            (.classMem (synCfv (synCfrec F I) (.cv m)) (synCncs))))
        (.classMem (.cv n) (synCnnc)))
      (synW3a (.classMem L (synCncs)) (.classMem H (synCncs)) (synWbr L (synClec) H))
      (.classMem L (synCncs)) p0011 p0012
  have p0019 :=
    @gSimp2 (.classMem L (synCncs)) (.classMem H (synCncs)) (synWbr L (synClec) H)
  have p0020 :=
    @gSyl
      (synWa (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
              (synWss (synCrn F) (synCdm F)))
            (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
              (synWbr L (synClec) H))) (synWral m (synCnnc)
            (.classMem (synCfv (synCfrec F I) (.cv m)) (synCncs))))
        (.classMem (.cv n) (synCnnc)))
      (synW3a (.classMem L (synCncs)) (.classMem H (synCncs)) (synWbr L (synClec) H))
      (.classMem H (synCncs)) p0011 p0019
  have p0022 :=
    @gSimpr
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F)))
        (synW3a (.classMem L (synCncs)) (.classMem H (synCncs)) (synWbr L (synClec) H)))
      (synWral m (synCnnc) (.classMem (synCfv (synCfrec F I) (.cv m)) (synCncs)))
  have p0023 :=
    @gSyl
      (synWa (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
              (synWss (synCrn F) (synCdm F)))
            (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
              (synWbr L (synClec) H))) (synWral m (synCnnc)
            (.classMem (synCfv (synCfrec F I) (.cv m)) (synCncs))))
        (.classMem (.cv n) (synCnnc)))
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F)))
          (synW3a (.classMem L (synCncs)) (.classMem H (synCncs)) (synWbr L (synClec) H)))
        (synWral m (synCnnc) (.classMem (synCfv (synCfrec F I) (.cv m)) (synCncs))))
      (synWral m (synCnnc) (.classMem (synCfv (synCfrec F I) (.cv m)) (synCncs)))
      p0000 p0022
  have p0025 :=
    @gJca
      (synWa (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
              (synWss (synCrn F) (synCdm F)))
            (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
              (synWbr L (synClec) H))) (synWral m (synCnnc)
            (.classMem (synCfv (synCfrec F I) (.cv m)) (synCncs))))
        (.classMem (.cv n) (synCnnc)))
      (synWral m (synCnnc) (.classMem (synCfv (synCfrec F I) (.cv m)) (synCncs)))
      (.classMem (.cv n) (synCnnc)) p0023 p0005
  have p0026 := @gFveq2 (.cv m) (.cv n) (synCfrec F I)
  have p0027 :=
    @gEleq1d (.classEq (.cv m) (.cv n)) (synCfv (synCfrec F I) (.cv m))
      (synCfv (synCfrec F I) (.cv n)) (synCncs) p0026
  have p0028 :=
    @gRspccva (.classMem (synCfv (synCfrec F I) (.cv m)) (synCncs))
      (.classMem (synCfv (synCfrec F I) (.cv n)) (synCncs)) m (.cv n) (synCnnc)
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0027
  have p0029 :=
    @gSyl
      (synWa (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
              (synWss (synCrn F) (synCdm F)))
            (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
              (synWbr L (synClec) H))) (synWral m (synCnnc)
            (.classMem (synCfv (synCfrec F I) (.cv m)) (synCncs))))
        (.classMem (.cv n) (synCnnc)))
      (synWa (synWral m (synCnnc) (.classMem (synCfv (synCfrec F I) (.cv m)) (synCncs)))
        (.classMem (.cv n) (synCnnc)))
      (.classMem (synCfv (synCfrec F I) (.cv n)) (synCncs)) p0025 p0028
  have p0030 :=
    @gN3jca
      (synWa (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
              (synWss (synCrn F) (synCdm F)))
            (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
              (synWbr L (synClec) H))) (synWral m (synCnnc)
            (.classMem (synCfv (synCfrec F I) (.cv m)) (synCncs))))
        (.classMem (.cv n) (synCnnc)))
      (.classMem L (synCncs)) (.classMem H (synCncs))
      (.classMem (synCfv (synCfrec F I) (.cv n)) (synCncs)) p0013 p0020 p0029
  have p0036 :=
    @gSimp3 (.classMem L (synCncs)) (.classMem H (synCncs)) (synWbr L (synClec) H)
  have p0037 :=
    @gSyl
      (synWa (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
              (synWss (synCrn F) (synCdm F)))
            (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
              (synWbr L (synClec) H))) (synWral m (synCnnc)
            (.classMem (synCfv (synCfrec F I) (.cv m)) (synCncs))))
        (.classMem (.cv n) (synCnnc)))
      (synW3a (.classMem L (synCncs)) (.classMem H (synCncs)) (synWbr L (synClec) H))
      (synWbr L (synClec) H) p0011 p0036
  have p0038 :=
    @gJca
      (synWa (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
              (synWss (synCrn F) (synCdm F)))
            (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
              (synWbr L (synClec) H))) (synWral m (synCnnc)
            (.classMem (synCfv (synCfrec F I) (.cv m)) (synCncs))))
        (.classMem (.cv n) (synCnnc)))
      (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
        (.classMem (synCfv (synCfrec F I) (.cv n)) (synCncs)))
      (synWbr L (synClec) H) p0030 p0037
  have p0039 :=
    @gJca
      (synWa (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
              (synWss (synCrn F) (synCdm F)))
            (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
              (synWbr L (synClec) H))) (synWral m (synCnnc)
            (.classMem (synCfv (synCfrec F I) (.cv m)) (synCncs))))
        (.classMem (.cv n) (synCnnc)))
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (.classMem (.cv n) (synCnnc)))
      (synWa (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
          (.classMem (synCfv (synCfrec F I) (.cv n)) (synCncs))) (synWbr L (synClec) H))
      p0006 p0038
  have p0040 := @gWpphitnestptndv F H I L (.cv n) dv_cache_0004 dv_cache_0005
  have p0041 :=
    @gSyl
      (synWa (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
              (synWss (synCrn F) (synCdm F)))
            (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
              (synWbr L (synClec) H))) (synWral m (synCnnc)
            (.classMem (synCfv (synCfrec F I) (.cv m)) (synCncs))))
        (.classMem (.cv n) (synCnnc)))
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (.classMem (.cv n) (synCnnc))) (synWa
          (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
            (.classMem (synCfv (synCfrec F I) (.cv n)) (synCncs))) (synWbr L (synClec) H)))
      (.imp (.classMem (.cv n) (synCwpphit F I H)) (.classMem (.cv n) (synCwpphit F I L)))
      p0039 p0040
  have p0042 :=
    @gRalrimiva
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F)))
          (synW3a (.classMem L (synCncs)) (.classMem H (synCncs)) (synWbr L (synClec) H)))
        (synWral m (synCnnc) (.classMem (synCfv (synCfrec F I) (.cv m)) (synCncs))))
      (.imp (.classMem (.cv n) (synCwpphit F I H)) (.classMem (.cv n) (synCwpphit F I L)))
      n (synCnnc) dv_cache_0006 p0041
  exact p0042

/-- Checked nominal proof certificate identified upstream as `g_wpphitstepptndv`. -/
@[expose]
noncomputable def gWpphitstepptndv (F : Class) (H : Class) (I : Class) (L : Class)
    (N : Class) (_dv_F_N : Disjoint F.fv N.fv) (_dv_I_N : Disjoint I.fv N.fv) :
    Nominal.NPrf
      (.imp (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
              (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
          (.imp (synWbr L (synClec) (synCfv (synCfrec F I) N))
            (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) N)))))
        (.imp (.classMem N (synCwpphit F I L))
          (.classMem (synCplc N (synC1c)) (synCwpphit F I H)))) :=
  by
  have p0000 :=
    @gSimpl
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
      (.imp (synWbr L (synClec) (synCfv (synCfrec F I) N))
        (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) N))))
  have p0001 :=
    @gSimpl
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (.classMem N (synCnnc))
  have p0002 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
        (.imp (synWbr L (synClec) (synCfv (synCfrec F I) N))
          (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) N)))))
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      p0000 p0001
  have p0003 := @gElwpphitvndv L F I N
  have p0004 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
        (.imp (synWbr L (synClec) (synCfv (synCfrec F I) N))
          (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) N)))))
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (synWb (.classMem N (synCwpphit F I L)) (synWa (.classMem N (synCnnc))
          (synWbr L (synClec) (synCfv (synCfrec F I) N))))
      p0002 p0003
  have p0005 :=
    @gBiimpd
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
        (.imp (synWbr L (synClec) (synCfv (synCfrec F I) N))
          (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) N)))))
      (.classMem N (synCwpphit F I L))
      (synWa (.classMem N (synCnnc)) (synWbr L (synClec) (synCfv (synCfrec F I) N)))
      p0004
  have p0006 :=
    @gSimpr (.classMem N (synCnnc)) (synWbr L (synClec) (synCfv (synCfrec F I) N))
  have p0007 :=
    @gSyl6
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
        (.imp (synWbr L (synClec) (synCfv (synCfrec F I) N))
          (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) N)))))
      (.classMem N (synCwpphit F I L))
      (synWa (.classMem N (synCnnc)) (synWbr L (synClec) (synCfv (synCfrec F I) N)))
      (synWbr L (synClec) (synCfv (synCfrec F I) N)) p0005 p0006
  have p0008 :=
    @gSimpr
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
      (.imp (synWbr L (synClec) (synCfv (synCfrec F I) N))
        (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) N))))
  have p0009 :=
    @gSyld
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
        (.imp (synWbr L (synClec) (synCfv (synCfrec F I) N))
          (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) N)))))
      (.classMem N (synCwpphit F I L)) (synWbr L (synClec) (synCfv (synCfrec F I) N))
      (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) N))) p0007 p0008
  have p0014 :=
    @gSimpr
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (.classMem N (synCnnc))
  have p0015 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
        (.imp (synWbr L (synClec) (synCfv (synCfrec F I) N))
          (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) N)))))
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
      (.classMem N (synCnnc)) p0000 p0014
  have p0016 :=
    @gJca
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
        (.imp (synWbr L (synClec) (synCfv (synCfrec F I) N))
          (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) N)))))
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (.classMem N (synCnnc)) p0002 p0015
  have p0017 := @gElwpphitsucvndv H F I N
  have p0018 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
        (.imp (synWbr L (synClec) (synCfv (synCfrec F I) N))
          (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) N)))))
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
      (synWb (.classMem (synCplc N (synC1c)) (synCwpphit F I H))
        (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) N))))
      p0016 p0017
  have p0019 :=
    @gBiimprd
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
        (.imp (synWbr L (synClec) (synCfv (synCfrec F I) N))
          (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) N)))))
      (.classMem (synCplc N (synC1c)) (synCwpphit F I H))
      (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) N))) p0018
  have p0020 :=
    @gSyld
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
        (.imp (synWbr L (synClec) (synCfv (synCfrec F I) N))
          (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) N)))))
      (.classMem N (synCwpphit F I L))
      (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) N)))
      (.classMem (synCplc N (synC1c)) (synCwpphit F I H)) p0009 p0019
  exact p0020

/-- Checked nominal proof certificate identified upstream as `g_wpphitstepndv`. -/
@[expose]
noncomputable def gWpphitstepndv (m : Var) (n : Var) (F : Class) (H : Class) (I : Class)
    (L : Class) (dv_F_m : m ∉ F.fv) (dv_F_n : n ∉ F.fv) (dv_H_m : m ∉ H.fv)
    (dv_H_n : n ∉ H.fv) (dv_I_m : m ∉ I.fv) (dv_I_n : n ∉ I.fv) (dv_L_m : m ∉ L.fv)
    (dv_L_n : n ∉ L.fv) (dv_m_n : m ≠ n) :
    Nominal.NPrf
      (.imp (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (synWral m (synCnnc)
            (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv m)))
              (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv m)))))))
        (synWral n (synCnnc) (.imp (.classMem (.cv n) (synCwpphit F I L))
            (.classMem (synCplc (.cv n) (synC1c)) (synCwpphit F I H))))) :=
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
  have dv_cache_0002 : m ∉ ((synCnnc)).fv :=
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
      ((Wff.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv n)))
          (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv n)))))).fv :=
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
      ((synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (synWral m (synCnnc)
            (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv m))) (synWbr H (synClec)
                (synCfv F (synCfv (synCfrec F I) (.cv m)))))))).fv :=
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
    @gSimpl
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (synWral m (synCnnc)
          (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv m)))
            (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv m)))))))
      (.classMem (.cv n) (synCnnc))
  have p0001 :=
    @gSimpl
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (synWral m (synCnnc) (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv m)))
          (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv m))))))
  have p0002 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (synWral m (synCnnc)
            (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv m)))
              (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv m)))))))
        (.classMem (.cv n) (synCnnc)))
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (synWral m (synCnnc)
          (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv m)))
            (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv m)))))))
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      p0000 p0001
  have p0003 :=
    @gSimpr
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (synWral m (synCnnc)
          (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv m)))
            (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv m)))))))
      (.classMem (.cv n) (synCnnc))
  have p0004 :=
    @gJca
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (synWral m (synCnnc)
            (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv m)))
              (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv m)))))))
        (.classMem (.cv n) (synCnnc)))
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (.classMem (.cv n) (synCnnc)) p0002 p0003
  have p0006 :=
    @gSimpr
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (synWral m (synCnnc) (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv m)))
          (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv m))))))
  have p0007 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (synWral m (synCnnc)
            (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv m)))
              (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv m)))))))
        (.classMem (.cv n) (synCnnc)))
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (synWral m (synCnnc)
          (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv m)))
            (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv m)))))))
      (synWral m (synCnnc) (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv m)))
          (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv m))))))
      p0000 p0006
  have p0009 :=
    @gJca
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (synWral m (synCnnc)
            (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv m)))
              (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv m)))))))
        (.classMem (.cv n) (synCnnc)))
      (synWral m (synCnnc) (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv m)))
          (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv m))))))
      (.classMem (.cv n) (synCnnc)) p0007 p0003
  have p0010 := @gFveq2 (.cv m) (.cv n) (synCfrec F I)
  have p0011 :=
    @gBreq2d (.classEq (.cv m) (.cv n)) (synCfv (synCfrec F I) (.cv m))
      (synCfv (synCfrec F I) (.cv n)) L (synClec) p0010
  have p0013 :=
    @gFveq2d (.classEq (.cv m) (.cv n)) (synCfv (synCfrec F I) (.cv m))
      (synCfv (synCfrec F I) (.cv n)) F p0010
  have p0014 :=
    @gBreq2d (.classEq (.cv m) (.cv n)) (synCfv F (synCfv (synCfrec F I) (.cv m)))
      (synCfv F (synCfv (synCfrec F I) (.cv n))) H (synClec) p0013
  have p0015 :=
    @gImbi12d (.classEq (.cv m) (.cv n))
      (synWbr L (synClec) (synCfv (synCfrec F I) (.cv m)))
      (synWbr L (synClec) (synCfv (synCfrec F I) (.cv n)))
      (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv m))))
      (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv n)))) p0011 p0014
  have p0016 :=
    @gRspccva
      (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv m)))
        (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv m)))))
      (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv n)))
        (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv n)))))
      m (.cv n) (synCnnc) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0015
  have p0017 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (synWral m (synCnnc)
            (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv m)))
              (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv m)))))))
        (.classMem (.cv n) (synCnnc)))
      (synWa (synWral m (synCnnc)
          (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv m)))
            (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv m))))))
        (.classMem (.cv n) (synCnnc)))
      (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv n)))
        (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv n)))))
      p0009 p0016
  have p0018 :=
    @gJca
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (synWral m (synCnnc)
            (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv m)))
              (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv m)))))))
        (.classMem (.cv n) (synCnnc)))
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (.classMem (.cv n) (synCnnc)))
      (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv n)))
        (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv n)))))
      p0004 p0017
  have p0019 := @gWpphitstepptndv F H I L (.cv n) dv_cache_0004 dv_cache_0005
  have p0020 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (synWral m (synCnnc)
            (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv m)))
              (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv m)))))))
        (.classMem (.cv n) (synCnnc)))
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (.classMem (.cv n) (synCnnc)))
        (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv n)))
          (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv n))))))
      (.imp (.classMem (.cv n) (synCwpphit F I L))
        (.classMem (synCplc (.cv n) (synC1c)) (synCwpphit F I H)))
      p0018 p0019
  have p0021 :=
    @gRalrimiva
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (synWral m (synCnnc)
          (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv m)))
            (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv m)))))))
      (.imp (.classMem (.cv n) (synCwpphit F I L))
        (.classMem (synCplc (.cv n) (synC1c)) (synCwpphit F I H)))
      n (synCnnc) dv_cache_0006 p0020
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

/-- Checked nominal proof certificate identified upstream as `g_wpphitminadjndv`. -/
@[expose]
noncomputable def gWpphitminadjndv (k : Var) (m : Var) (n : Var) (F : Class) (H : Class)
    (I : Class) (L : Class) (r : Var) (q : Var) (dv_F_k : k ∉ F.fv) (dv_F_m : m ∉ F.fv)
    (dv_F_n : n ∉ F.fv) (dv_F_q : q ∉ F.fv) (dv_F_r : r ∉ F.fv) (dv_H_k : k ∉ H.fv)
    (dv_H_m : m ∉ H.fv) (dv_H_n : n ∉ H.fv) (dv_H_q : q ∉ H.fv) (dv_H_r : r ∉ H.fv)
    (dv_I_k : k ∉ I.fv) (dv_I_m : m ∉ I.fv) (dv_I_n : n ∉ I.fv) (dv_I_q : q ∉ I.fv)
    (dv_I_r : r ∉ I.fv) (dv_L_k : k ∉ L.fv) (dv_L_m : m ∉ L.fv) (dv_L_n : n ∉ L.fv)
    (dv_L_q : q ∉ L.fv) (dv_L_r : r ∉ L.fv) (dv_k_m : k ≠ m) (dv_k_n : k ≠ n)
    (dv_m_n : m ≠ n) (dv_n_q : n ≠ q) (dv_n_r : n ≠ r) :
    Nominal.NPrf
      (.imp (synW3a (synWa
            (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
              (synWa (.classMem (.cv m) (synCwpphit F I H))
                (.classMem (.cv k) (synCwpphit F I L)))) (synWa (synWral n (synCnnc)
                (.imp (.classMem (.cv n) (synCwpphit F I H))
                  (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
                (.imp (.classMem (.cv n) (synCwpphit F I L))
                  (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))) (synWa (synWa
              (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
                (synWss (synCrn F) (synCdm F)))
              (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
                (synWbr L (synClec) H))) (synWral q (synCnnc)
              (.classMem (synCfv (synCfrec F I) (.cv q)) (synCncs)))) (synWral r (synCnnc)
            (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv r)))
              (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv r)))))))
        (synWo (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (synCplc (.cv k) (synC1c))))) :=
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
  have dv_cache_0015 : k ∉ ((synCwpphit F I H)).fv :=
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
  have dv_cache_0016 : m ∉ ((synCwpphit F I H)).fv :=
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
  have dv_cache_0017 : n ∉ ((synCwpphit F I H)).fv :=
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
  have dv_cache_0018 : k ∉ ((synCwpphit F I L)).fv :=
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
  have dv_cache_0019 : m ∉ ((synCwpphit F I L)).fv :=
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
  have dv_cache_0020 : n ∉ ((synCwpphit F I L)).fv :=
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
    @gSimp1
      (synWa (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
          (synWa (.classMem (.cv m) (synCwpphit F I H))
            (.classMem (.cv k) (synCwpphit F I L)))) (synWa (synWral n (synCnnc)
            (.imp (.classMem (.cv n) (synCwpphit F I H))
              (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
            (.imp (.classMem (.cv n) (synCwpphit F I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n))))))
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F)))
          (synW3a (.classMem L (synCncs)) (.classMem H (synCncs)) (synWbr L (synClec) H)))
        (synWral q (synCnnc) (.classMem (synCfv (synCfrec F I) (.cv q)) (synCncs))))
      (synWral r (synCnnc) (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv r)))
          (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv r))))))
  have p0001 :=
    @gSimpl
      (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) (synCwpphit F I H))
          (.classMem (.cv k) (synCwpphit F I L))))
      (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) (synCwpphit F I H))
            (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
          (.imp (.classMem (.cv n) (synCwpphit F I L))
            (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
  have p0002 :=
    @gSyl
      (synW3a (synWa
          (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
            (synWa (.classMem (.cv m) (synCwpphit F I H))
              (.classMem (.cv k) (synCwpphit F I L)))) (synWa (synWral n (synCnnc)
              (.imp (.classMem (.cv n) (synCwpphit F I H))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) (synCwpphit F I L))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))) (synWa (synWa
            (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
              (synWss (synCrn F) (synCdm F)))
            (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
              (synWbr L (synClec) H))) (synWral q (synCnnc)
            (.classMem (synCfv (synCfrec F I) (.cv q)) (synCncs)))) (synWral r (synCnnc)
          (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv r)))
            (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv r)))))))
      (synWa (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
          (synWa (.classMem (.cv m) (synCwpphit F I H))
            (.classMem (.cv k) (synCwpphit F I L)))) (synWa (synWral n (synCnnc)
            (.imp (.classMem (.cv n) (synCwpphit F I H))
              (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
            (.imp (.classMem (.cv n) (synCwpphit F I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n))))))
      (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) (synCwpphit F I H))
          (.classMem (.cv k) (synCwpphit F I L))))
      p0000 p0001
  have p0003 :=
    @gSimpl (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
      (synWa (.classMem (.cv m) (synCwpphit F I H)) (.classMem (.cv k) (synCwpphit F I L)))
  have p0004 :=
    @gSyl
      (synW3a (synWa
          (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
            (synWa (.classMem (.cv m) (synCwpphit F I H))
              (.classMem (.cv k) (synCwpphit F I L)))) (synWa (synWral n (synCnnc)
              (.imp (.classMem (.cv n) (synCwpphit F I H))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) (synCwpphit F I L))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))) (synWa (synWa
            (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
              (synWss (synCrn F) (synCdm F)))
            (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
              (synWbr L (synClec) H))) (synWral q (synCnnc)
            (.classMem (synCfv (synCfrec F I) (.cv q)) (synCncs)))) (synWral r (synCnnc)
          (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv r)))
            (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv r)))))))
      (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) (synCwpphit F I H))
          (.classMem (.cv k) (synCwpphit F I L))))
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc))) p0002 p0003
  have p0008 :=
    @gSimpr (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
      (synWa (.classMem (.cv m) (synCwpphit F I H)) (.classMem (.cv k) (synCwpphit F I L)))
  have p0009 :=
    @gSyl
      (synW3a (synWa
          (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
            (synWa (.classMem (.cv m) (synCwpphit F I H))
              (.classMem (.cv k) (synCwpphit F I L)))) (synWa (synWral n (synCnnc)
              (.imp (.classMem (.cv n) (synCwpphit F I H))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) (synCwpphit F I L))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))) (synWa (synWa
            (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
              (synWss (synCrn F) (synCdm F)))
            (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
              (synWbr L (synClec) H))) (synWral q (synCnnc)
            (.classMem (synCfv (synCfrec F I) (.cv q)) (synCncs)))) (synWral r (synCnnc)
          (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv r)))
            (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv r)))))))
      (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) (synCwpphit F I H))
          (.classMem (.cv k) (synCwpphit F I L))))
      (synWa (.classMem (.cv m) (synCwpphit F I H)) (.classMem (.cv k) (synCwpphit F I L)))
      p0002 p0008
  have p0011 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) (synCwpphit F I H))
          (.classMem (.cv k) (synCwpphit F I L))))
      (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) (synCwpphit F I H))
            (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
          (.imp (.classMem (.cv n) (synCwpphit F I L))
            (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
  have p0012 :=
    @gSyl
      (synW3a (synWa
          (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
            (synWa (.classMem (.cv m) (synCwpphit F I H))
              (.classMem (.cv k) (synCwpphit F I L)))) (synWa (synWral n (synCnnc)
              (.imp (.classMem (.cv n) (synCwpphit F I H))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) (synCwpphit F I L))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))) (synWa (synWa
            (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
              (synWss (synCrn F) (synCdm F)))
            (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
              (synWbr L (synClec) H))) (synWral q (synCnnc)
            (.classMem (synCfv (synCfrec F I) (.cv q)) (synCncs)))) (synWral r (synCnnc)
          (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv r)))
            (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv r)))))))
      (synWa (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
          (synWa (.classMem (.cv m) (synCwpphit F I H))
            (.classMem (.cv k) (synCwpphit F I L)))) (synWa (synWral n (synCnnc)
            (.imp (.classMem (.cv n) (synCwpphit F I H))
              (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
            (.imp (.classMem (.cv n) (synCwpphit F I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n))))))
      (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) (synCwpphit F I H))
            (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
          (.imp (.classMem (.cv n) (synCwpphit F I L))
            (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
      p0000 p0011
  have p0013 :=
    @gSimp2
      (synWa (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
          (synWa (.classMem (.cv m) (synCwpphit F I H))
            (.classMem (.cv k) (synCwpphit F I L)))) (synWa (synWral n (synCnnc)
            (.imp (.classMem (.cv n) (synCwpphit F I H))
              (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
            (.imp (.classMem (.cv n) (synCwpphit F I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n))))))
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F)))
          (synW3a (.classMem L (synCncs)) (.classMem H (synCncs)) (synWbr L (synClec) H)))
        (synWral q (synCnnc) (.classMem (synCfv (synCfrec F I) (.cv q)) (synCncs))))
      (synWral r (synCnnc) (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv r)))
          (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv r))))))
  have p0014 :=
    @gWpphitnestndv q n F H I L dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0015 :=
    @gSyl
      (synW3a (synWa
          (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
            (synWa (.classMem (.cv m) (synCwpphit F I H))
              (.classMem (.cv k) (synCwpphit F I L)))) (synWa (synWral n (synCnnc)
              (.imp (.classMem (.cv n) (synCwpphit F I H))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) (synCwpphit F I L))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))) (synWa (synWa
            (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
              (synWss (synCrn F) (synCdm F)))
            (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
              (synWbr L (synClec) H))) (synWral q (synCnnc)
            (.classMem (synCfv (synCfrec F I) (.cv q)) (synCncs)))) (synWral r (synCnnc)
          (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv r)))
            (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv r)))))))
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F)))
          (synW3a (.classMem L (synCncs)) (.classMem H (synCncs)) (synWbr L (synClec) H)))
        (synWral q (synCnnc) (.classMem (synCfv (synCfrec F I) (.cv q)) (synCncs))))
      (synWral n (synCnnc) (.imp (.classMem (.cv n) (synCwpphit F I H))
          (.classMem (.cv n) (synCwpphit F I L))))
      p0013 p0014
  have p0017 :=
    @gSimpl
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F)))
        (synW3a (.classMem L (synCncs)) (.classMem H (synCncs)) (synWbr L (synClec) H)))
      (synWral q (synCnnc) (.classMem (synCfv (synCfrec F I) (.cv q)) (synCncs)))
  have p0018 :=
    @gSyl
      (synW3a (synWa
          (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
            (synWa (.classMem (.cv m) (synCwpphit F I H))
              (.classMem (.cv k) (synCwpphit F I L)))) (synWa (synWral n (synCnnc)
              (.imp (.classMem (.cv n) (synCwpphit F I H))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) (synCwpphit F I L))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))) (synWa (synWa
            (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
              (synWss (synCrn F) (synCdm F)))
            (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
              (synWbr L (synClec) H))) (synWral q (synCnnc)
            (.classMem (synCfv (synCfrec F I) (.cv q)) (synCncs)))) (synWral r (synCnnc)
          (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv r)))
            (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv r)))))))
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F)))
          (synW3a (.classMem L (synCncs)) (.classMem H (synCncs)) (synWbr L (synClec) H)))
        (synWral q (synCnnc) (.classMem (synCfv (synCfrec F I) (.cv q)) (synCncs))))
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F)))
        (synW3a (.classMem L (synCncs)) (.classMem H (synCncs)) (synWbr L (synClec) H)))
      p0013 p0017
  have p0019 :=
    @gSimpl
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (synW3a (.classMem L (synCncs)) (.classMem H (synCncs)) (synWbr L (synClec) H))
  have p0020 :=
    @gSyl
      (synW3a (synWa
          (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
            (synWa (.classMem (.cv m) (synCwpphit F I H))
              (.classMem (.cv k) (synCwpphit F I L)))) (synWa (synWral n (synCnnc)
              (.imp (.classMem (.cv n) (synCwpphit F I H))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) (synCwpphit F I L))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))) (synWa (synWa
            (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
              (synWss (synCrn F) (synCdm F)))
            (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
              (synWbr L (synClec) H))) (synWral q (synCnnc)
            (.classMem (synCfv (synCfrec F I) (.cv q)) (synCncs)))) (synWral r (synCnnc)
          (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv r)))
            (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv r)))))))
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F)))
        (synW3a (.classMem L (synCncs)) (.classMem H (synCncs)) (synWbr L (synClec) H)))
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      p0018 p0019
  have p0021 :=
    @gSimp3
      (synWa (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
          (synWa (.classMem (.cv m) (synCwpphit F I H))
            (.classMem (.cv k) (synCwpphit F I L)))) (synWa (synWral n (synCnnc)
            (.imp (.classMem (.cv n) (synCwpphit F I H))
              (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
            (.imp (.classMem (.cv n) (synCwpphit F I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n))))))
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F)))
          (synW3a (.classMem L (synCncs)) (.classMem H (synCncs)) (synWbr L (synClec) H)))
        (synWral q (synCnnc) (.classMem (synCfv (synCfrec F I) (.cv q)) (synCncs))))
      (synWral r (synCnnc) (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv r)))
          (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv r))))))
  have p0022 :=
    @gJca
      (synW3a (synWa
          (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
            (synWa (.classMem (.cv m) (synCwpphit F I H))
              (.classMem (.cv k) (synCwpphit F I L)))) (synWa (synWral n (synCnnc)
              (.imp (.classMem (.cv n) (synCwpphit F I H))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) (synCwpphit F I L))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))) (synWa (synWa
            (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
              (synWss (synCrn F) (synCdm F)))
            (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
              (synWbr L (synClec) H))) (synWral q (synCnnc)
            (.classMem (synCfv (synCfrec F I) (.cv q)) (synCncs)))) (synWral r (synCnnc)
          (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv r)))
            (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv r)))))))
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (synWral r (synCnnc) (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv r)))
          (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv r))))))
      p0020 p0021
  have p0023 :=
    @gWpphitstepndv r n F H I L dv_cache_0010 dv_cache_0002 dv_cache_0011 dv_cache_0004
      dv_cache_0012 dv_cache_0006 dv_cache_0013 dv_cache_0008 dv_cache_0014
  have p0024 :=
    @gSyl
      (synW3a (synWa
          (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
            (synWa (.classMem (.cv m) (synCwpphit F I H))
              (.classMem (.cv k) (synCwpphit F I L)))) (synWa (synWral n (synCnnc)
              (.imp (.classMem (.cv n) (synCwpphit F I H))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) (synCwpphit F I L))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))) (synWa (synWa
            (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
              (synWss (synCrn F) (synCdm F)))
            (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
              (synWbr L (synClec) H))) (synWral q (synCnnc)
            (.classMem (synCfv (synCfrec F I) (.cv q)) (synCncs)))) (synWral r (synCnnc)
          (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv r)))
            (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv r)))))))
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (synWral r (synCnnc)
          (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv r)))
            (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv r)))))))
      (synWral n (synCnnc) (.imp (.classMem (.cv n) (synCwpphit F I L))
          (.classMem (synCplc (.cv n) (synC1c)) (synCwpphit F I H))))
      p0022 p0023
  have p0025 :=
    @gJca
      (synW3a (synWa
          (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
            (synWa (.classMem (.cv m) (synCwpphit F I H))
              (.classMem (.cv k) (synCwpphit F I L)))) (synWa (synWral n (synCnnc)
              (.imp (.classMem (.cv n) (synCwpphit F I H))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) (synCwpphit F I L))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))) (synWa (synWa
            (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
              (synWss (synCrn F) (synCdm F)))
            (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
              (synWbr L (synClec) H))) (synWral q (synCnnc)
            (.classMem (synCfv (synCfrec F I) (.cv q)) (synCncs)))) (synWral r (synCnnc)
          (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv r)))
            (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv r)))))))
      (synWral n (synCnnc) (.imp (.classMem (.cv n) (synCwpphit F I H))
          (.classMem (.cv n) (synCwpphit F I L))))
      (synWral n (synCnnc) (.imp (.classMem (.cv n) (synCwpphit F I L))
          (.classMem (synCplc (.cv n) (synC1c)) (synCwpphit F I H))))
      p0015 p0024
  have p0026 :=
    @gJca
      (synW3a (synWa
          (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
            (synWa (.classMem (.cv m) (synCwpphit F I H))
              (.classMem (.cv k) (synCwpphit F I L)))) (synWa (synWral n (synCnnc)
              (.imp (.classMem (.cv n) (synCwpphit F I H))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) (synCwpphit F I L))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))) (synWa (synWa
            (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
              (synWss (synCrn F) (synCdm F)))
            (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
              (synWbr L (synClec) H))) (synWral q (synCnnc)
            (.classMem (synCfv (synCfrec F I) (.cv q)) (synCncs)))) (synWral r (synCnnc)
          (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv r)))
            (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv r)))))))
      (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) (synCwpphit F I H))
            (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
          (.imp (.classMem (.cv n) (synCwpphit F I L))
            (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
      (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) (synCwpphit F I H))
            (.classMem (.cv n) (synCwpphit F I L)))) (synWral n (synCnnc)
          (.imp (.classMem (.cv n) (synCwpphit F I L))
            (.classMem (synCplc (.cv n) (synC1c)) (synCwpphit F I H)))))
      p0012 p0025
  have p0027 :=
    @gN3jca
      (synW3a (synWa
          (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
            (synWa (.classMem (.cv m) (synCwpphit F I H))
              (.classMem (.cv k) (synCwpphit F I L)))) (synWa (synWral n (synCnnc)
              (.imp (.classMem (.cv n) (synCwpphit F I H))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) (synCwpphit F I L))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))) (synWa (synWa
            (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
              (synWss (synCrn F) (synCdm F)))
            (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
              (synWbr L (synClec) H))) (synWral q (synCnnc)
            (.classMem (synCfv (synCfrec F I) (.cv q)) (synCncs)))) (synWral r (synCnnc)
          (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv r)))
            (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv r)))))))
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
      (synWa (.classMem (.cv m) (synCwpphit F I H)) (.classMem (.cv k) (synCwpphit F I L)))
      (synWa (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) (synCwpphit F I H))
              (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
            (.imp (.classMem (.cv n) (synCwpphit F I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n))))) (synWa
          (synWral n (synCnnc) (.imp (.classMem (.cv n) (synCwpphit F I H))
              (.classMem (.cv n) (synCwpphit F I L)))) (synWral n (synCnnc)
            (.imp (.classMem (.cv n) (synCwpphit F I L))
              (.classMem (synCplc (.cv n) (synC1c)) (synCwpphit F I H))))))
      p0004 p0009 p0026
  have p0028 :=
    @gFinleastadjndv k m n (synCwpphit F I H) (synCwpphit F I L) dv_cache_0015
      dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
      dv_cache_0022 dv_cache_0023
  have p0029 :=
    @gSyl
      (synW3a (synWa
          (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
            (synWa (.classMem (.cv m) (synCwpphit F I H))
              (.classMem (.cv k) (synCwpphit F I L)))) (synWa (synWral n (synCnnc)
              (.imp (.classMem (.cv n) (synCwpphit F I H))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) (synCwpphit F I L))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))) (synWa (synWa
            (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
              (synWss (synCrn F) (synCdm F)))
            (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
              (synWbr L (synClec) H))) (synWral q (synCnnc)
            (.classMem (synCfv (synCfrec F I) (.cv q)) (synCncs)))) (synWral r (synCnnc)
          (.imp (synWbr L (synClec) (synCfv (synCfrec F I) (.cv r)))
            (synWbr H (synClec) (synCfv F (synCfv (synCfrec F I) (.cv r)))))))
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) (synCwpphit F I H)) (.classMem (.cv k) (synCwpphit F I L)))
        (synWa (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) (synCwpphit F I H))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) (synCwpphit F I L))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n))))) (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) (synCwpphit F I H))
                (.classMem (.cv n) (synCwpphit F I L)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) (synCwpphit F I L))
                (.classMem (synCplc (.cv n) (synC1c)) (synCwpphit F I H)))))))
      (synWo (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (synCplc (.cv k) (synC1c))))
      p0027 p0028
  exact p0029

/-- Checked nominal proof certificate identified upstream as `g_wppcardt2fnexndv`. -/
@[expose]
noncomputable def gWppcardt2fnexndv :
    Nominal.NPrf (.classMem (synCwppcardt2fn) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppcardt2fn))
  have p0001 := @gWppcardtfnexndv
  have p0003 := @gSiex (synCwppcardtfn) p0001
  have p0004 := @gCoex (synCwppcardtfn) (synCsi (synCwppcardtfn)) p0001 p0003
  have p0005 :=
    @gEqeltri (synCwppcardt2fn) (synCcom (synCwppcardtfn) (synCsi (synCwppcardtfn)))
      (synCvv) p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_wppcardt2fnmapndv`. -/
@[expose]
noncomputable def gWppcardt2fnmapndv :
    Nominal.NPrf
      (synWf (synCwppcardt2fn) (synCpw1 (synCpw1 (synCncs))) (synCncs)) :=
  by
  have p0000 := @gWppcardtfnmapndv
  have p0002 := @gSifmap (synCpw1 (synCncs)) (synCncs) (synCwppcardtfn)
  have p0003 := Nominal.mp p0000 p0002
  have p0004 :=
    @gPm32i (synWf (synCwppcardtfn) (synCpw1 (synCncs)) (synCncs))
      (synWf (synCsi (synCwppcardtfn)) (synCpw1 (synCpw1 (synCncs)))
        (synCpw1 (synCncs)))
      p0000 p0003
  have p0005 :=
    @gFco (synCpw1 (synCpw1 (synCncs))) (synCpw1 (synCncs)) (synCncs)
      (synCwppcardtfn) (synCsi (synCwppcardtfn))
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := (Nominal.classEqRefl (synCwppcardt2fn))
  have p0008 :=
    @gFeq1i (synCpw1 (synCpw1 (synCncs))) (synCncs) (synCwppcardt2fn)
      (synCcom (synCwppcardtfn) (synCsi (synCwppcardtfn))) p0007
  have p0009 :=
    @gMpbir (synWf (synCwppcardt2fn) (synCpw1 (synCpw1 (synCncs))) (synCncs))
      (synWf (synCcom (synCwppcardtfn) (synCsi (synCwppcardtfn)))
        (synCpw1 (synCpw1 (synCncs))) (synCncs))
      p0006 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_wppcardt2fnvalsingndv`. -/
@[expose]
noncomputable def gWppcardt2fnvalsingndv (D : Class) :
    Nominal.NPrf
      (.imp (.classMem D (synCncs))
        (.classEq (synCfv (synCwppcardt2fn) (synCsn (synCsn D))) (synCtc (synCtc D)))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppcardt2fn))
  have p0001 :=
    @gFveq1i (synCsn (synCsn D)) (synCwppcardt2fn)
      (synCcom (synCwppcardtfn) (synCsi (synCwppcardtfn))) p0000
  have p0002 :=
    @gA1i
      (.classEq (synCfv (synCwppcardt2fn) (synCsn (synCsn D)))
        (synCfv (synCcom (synCwppcardtfn) (synCsi (synCwppcardtfn)))
          (synCsn (synCsn D))))
      (.classMem D (synCncs)) p0001
  have p0003 := @gWppcardtfnmapndv
  have p0004 := @gSifmap (synCpw1 (synCncs)) (synCncs) (synCwppcardtfn)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @gA1i
      (synWf (synCsi (synCwppcardtfn)) (synCpw1 (synCpw1 (synCncs)))
        (synCpw1 (synCncs)))
      (.classMem D (synCncs)) p0005
  have p0007 := @gSnelpw1 D (synCncs)
  have p0008 :=
    @gBiimpri (.classMem (synCsn D) (synCpw1 (synCncs))) (.classMem D (synCncs))
      p0007
  have p0009 := @gSnelpw1 (synCsn D) (synCpw1 (synCncs))
  have p0010 :=
    @gBiimpri (.classMem (synCsn (synCsn D)) (synCpw1 (synCpw1 (synCncs))))
      (.classMem (synCsn D) (synCpw1 (synCncs))) p0009
  have p0011 :=
    @gSyl (.classMem D (synCncs)) (.classMem (synCsn D) (synCpw1 (synCncs)))
      (.classMem (synCsn (synCsn D)) (synCpw1 (synCpw1 (synCncs)))) p0008 p0010
  have p0012 :=
    @gJca (.classMem D (synCncs))
      (synWf (synCsi (synCwppcardtfn)) (synCpw1 (synCpw1 (synCncs)))
        (synCpw1 (synCncs)))
      (.classMem (synCsn (synCsn D)) (synCpw1 (synCpw1 (synCncs)))) p0006 p0011
  have p0013 :=
    @gFvco3 (synCpw1 (synCpw1 (synCncs))) (synCpw1 (synCncs)) (synCsn (synCsn D))
      (synCwppcardtfn) (synCsi (synCwppcardtfn))
  have p0014 :=
    @gSyl (.classMem D (synCncs))
      (synWa (synWf (synCsi (synCwppcardtfn)) (synCpw1 (synCpw1 (synCncs)))
          (synCpw1 (synCncs)))
        (.classMem (synCsn (synCsn D)) (synCpw1 (synCpw1 (synCncs)))))
      (.classEq (synCfv (synCcom (synCwppcardtfn) (synCsi (synCwppcardtfn)))
          (synCsn (synCsn D))) (synCfv (synCwppcardtfn)
          (synCfv (synCsi (synCwppcardtfn)) (synCsn (synCsn D)))))
      p0012 p0013
  have p0015 :=
    @gEqtrd (.classMem D (synCncs)) (synCfv (synCwppcardt2fn) (synCsn (synCsn D)))
      (synCfv (synCcom (synCwppcardtfn) (synCsi (synCwppcardtfn))) (synCsn (synCsn D)))
      (synCfv (synCwppcardtfn) (synCfv (synCsi (synCwppcardtfn)) (synCsn (synCsn D))))
      p0002 p0014
  have p0019 :=
    @gSifvald (synCpw1 (synCncs)) (synCncs) (synCsn D) (synCwppcardtfn) p0003
  have p0020 :=
    @gSyl (.classMem D (synCncs)) (.classMem (synCsn D) (synCpw1 (synCncs)))
      (.classEq (synCfv (synCsi (synCwppcardtfn)) (synCsn (synCsn D)))
        (synCsn (synCfv (synCwppcardtfn) (synCsn D))))
      p0008 p0019
  have p0021 := @gWppcardtfnvalsingndv D
  have p0022 :=
    @gSneqd (.classMem D (synCncs)) (synCfv (synCwppcardtfn) (synCsn D)) (synCtc D)
      p0021
  have p0023 :=
    @gEqtrd (.classMem D (synCncs))
      (synCfv (synCsi (synCwppcardtfn)) (synCsn (synCsn D)))
      (synCsn (synCfv (synCwppcardtfn) (synCsn D))) (synCsn (synCtc D)) p0020 p0022
  have p0024 :=
    @gFveq2d (.classMem D (synCncs))
      (synCfv (synCsi (synCwppcardtfn)) (synCsn (synCsn D))) (synCsn (synCtc D))
      (synCwppcardtfn) p0023
  have p0025 :=
    @gEqtrd (.classMem D (synCncs)) (synCfv (synCwppcardt2fn) (synCsn (synCsn D)))
      (synCfv (synCwppcardtfn) (synCfv (synCsi (synCwppcardtfn)) (synCsn (synCsn D))))
      (synCfv (synCwppcardtfn) (synCsn (synCtc D))) p0015 p0024
  have p0026 := @gTccl D
  have p0027 := @gWppcardtfnvalsingndv (synCtc D)
  have p0028 :=
    @gSyl (.classMem D (synCncs)) (.classMem (synCtc D) (synCncs))
      (.classEq (synCfv (synCwppcardtfn) (synCsn (synCtc D))) (synCtc (synCtc D)))
      p0026 p0027
  have p0029 :=
    @gEqtrd (.classMem D (synCncs)) (synCfv (synCwppcardt2fn) (synCsn (synCsn D)))
      (synCfv (synCwppcardtfn) (synCsn (synCtc D))) (synCtc (synCtc D)) p0025 p0028
  exact p0029

/-- Checked nominal proof certificate identified upstream as `g_hwgenvalclndv`. -/
@[expose]
noncomputable def gHwgenvalclndv (B : Class) (C : Class)
    (hyp_hwgenvalclndv_1 : Nominal.NPrf (.classMem B (synCvv)))
    (hyp_hwgenvalclndv_2 : Nominal.NPrf (.classMem C (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synChwgen) (synCop B C)) (synCop (synCop C (synCdm B))
          (synCop (synCcom (synCcom B C) (synCcnv B)) (synCrn B)))) :=
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
      ((Wff.classEq (synCfv (synChwgen) (synCop B C)) (synCop (synCop C (synCdm B))
            (synCop (synCcom (synCcom B C) (synCcnv B)) (synCrn B))))).fv :=
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
  have p0000 := @gId (.classEq (.cv f) B)
  have p0001 := @gOpeq1d (.classEq (.cv f) B) (.cv f) B C p0000
  have p0002 :=
    @gFveq2d (.classEq (.cv f) B) (synCop (.cv f) C) (synCop B C) (synChwgen) p0001
  have p0004 := @gDmeqd (.classEq (.cv f) B) (.cv f) B p0000
  have p0005 := @gOpeq2d (.classEq (.cv f) B) (synCdm (.cv f)) (synCdm B) C p0004
  have p0007 := @gCoeq1d (.classEq (.cv f) B) (.cv f) B C p0000
  have p0009 := @gCnveqd (.classEq (.cv f) B) (.cv f) B p0000
  have p0010 :=
    @gCoeq12d (.classEq (.cv f) B) (synCcom (.cv f) C) (synCcom B C) (synCcnv (.cv f))
      (synCcnv B) p0007 p0009
  have p0012 := @gRneqd (.classEq (.cv f) B) (.cv f) B p0000
  have p0013 :=
    @gOpeq12d (.classEq (.cv f) B) (synCcom (synCcom (.cv f) C) (synCcnv (.cv f)))
      (synCcom (synCcom B C) (synCcnv B)) (synCrn (.cv f)) (synCrn B) p0010 p0012
  have p0014 :=
    @gOpeq12d (.classEq (.cv f) B) (synCop C (synCdm (.cv f))) (synCop C (synCdm B))
      (synCop (synCcom (synCcom (.cv f) C) (synCcnv (.cv f))) (synCrn (.cv f)))
      (synCop (synCcom (synCcom B C) (synCcnv B)) (synCrn B)) p0005 p0013
  have p0015 :=
    @gEqeq12d (.classEq (.cv f) B) (synCfv (synChwgen) (synCop (.cv f) C))
      (synCfv (synChwgen) (synCop B C))
      (synCop (synCop C (synCdm (.cv f)))
        (synCop (synCcom (synCcom (.cv f) C) (synCcnv (.cv f))) (synCrn (.cv f))))
      (synCop (synCop C (synCdm B))
        (synCop (synCcom (synCcom B C) (synCcnv B)) (synCrn B)))
      p0002 p0014
  have p0016 := @gHwgenval C f hyp_hwgenvalclndv_2
  have p0017 :=
    @gVtoclg
      (.classEq (synCfv (synChwgen) (synCop (.cv f) C))
        (synCop (synCop C (synCdm (.cv f)))
          (synCop (synCcom (synCcom (.cv f) C) (synCcnv (.cv f))) (synCrn (.cv f)))))
      (.classEq (synCfv (synChwgen) (synCop B C)) (synCop (synCop C (synCdm B))
          (synCop (synCcom (synCcom B C) (synCcnv B)) (synCrn B))))
      f B (synCvv) dv_cache_0001 dv_cache_0002 p0015 p0016
  have p0018 := Nominal.mp hyp_hwgenvalclndv_1 p0017
  exact p0018

/-- Checked nominal proof certificate identified upstream as `g_hnbaseresfnvalndv`. -/
@[expose]
noncomputable def gHnbaseresfnvalndv (u : Var) (F : Class)
    (hyp_hnbaseresfnvalndv_1 : Nominal.NPrf (.classMem F (synCvv)))
    (hyp_hnbaseresfnvalndv_2 : Nominal.NPrf (.classMem (.cv u) (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synChnbaseresfn F) (.cv u))
        (synCres F (synCfv (synC2nd) (.cv u)))) :=
  by
  have p0000 := (Nominal.classEqRefl (synChnbaseresfn F))
  have p0001 :=
    @gFveq1i (.cv u) (synChnbaseresfn F)
      (synCcom (synClnimageresfn) (synCtxp (synCxp (synCvv) (synCsn F)) (synC2nd)))
      p0000
  have p0002 := @gFnconstg (synCvv) F (synCvv)
  have p0003 := Nominal.mp hyp_hnbaseresfnvalndv_1 p0002
  have p0004 := @gLn2ndfn
  have p0005 :=
    @gPm32i (synWfn (synCxp (synCvv) (synCsn F)) (synCvv))
      (synWfn (synC2nd) (synCvv)) p0003 p0004
  have p0006 := @gFntxp (synCvv) (synCvv) (synCxp (synCvv) (synCsn F)) (synC2nd)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 := @gInidm (synCvv)
  have p0009 := @gEqcomi (synCin (synCvv) (synCvv)) (synCvv) p0008
  have p0010 :=
    @gFneq2i (synCvv) (synCin (synCvv) (synCvv))
      (synCtxp (synCxp (synCvv) (synCsn F)) (synC2nd)) p0009
  have p0011 :=
    @gMpbir (synWfn (synCtxp (synCxp (synCvv) (synCsn F)) (synC2nd)) (synCvv))
      (synWfn (synCtxp (synCxp (synCvv) (synCsn F)) (synC2nd))
        (synCin (synCvv) (synCvv)))
      p0007 p0010
  have p0012 :=
    @gPm32i (synWfn (synCtxp (synCxp (synCvv) (synCsn F)) (synC2nd)) (synCvv))
      (.classMem (.cv u) (synCvv)) p0011 hyp_hnbaseresfnvalndv_2
  have p0013 :=
    @gFvco2 (synCvv) (.cv u) (synClnimageresfn)
      (synCtxp (synCxp (synCvv) (synCsn F)) (synC2nd))
  have p0014 := Nominal.mp p0012 p0013
  have p0018 :=
    @gFvtxpvv (.cv u) (synCxp (synCvv) (synCsn F)) (synC2nd) p0003 p0004
      hyp_hnbaseresfnvalndv_2
  have p0019 := @gFvconst2 (synCvv) F (.cv u) hyp_hnbaseresfnvalndv_1
  have p0020 := Nominal.mp hyp_hnbaseresfnvalndv_2 p0019
  have p0021 := @gEqid (synCfv (synC2nd) (.cv u))
  have p0022 :=
    @gOpeq12i (synCfv (synCxp (synCvv) (synCsn F)) (.cv u)) F
      (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)) p0020 p0021
  have p0023 :=
    @gEqtri (synCfv (synCtxp (synCxp (synCvv) (synCsn F)) (synC2nd)) (.cv u))
      (synCop (synCfv (synCxp (synCvv) (synCsn F)) (.cv u)) (synCfv (synC2nd) (.cv u)))
      (synCop F (synCfv (synC2nd) (.cv u))) p0018 p0022
  have p0024 :=
    @gFveq2i (synCfv (synCtxp (synCxp (synCvv) (synCsn F)) (synC2nd)) (.cv u))
      (synCop F (synCfv (synC2nd) (.cv u))) (synClnimageresfn) p0023
  have p0025 :=
    @gEqtri
      (synCfv (synCcom (synClnimageresfn)
          (synCtxp (synCxp (synCvv) (synCsn F)) (synC2nd))) (.cv u))
      (synCfv (synClnimageresfn)
        (synCfv (synCtxp (synCxp (synCvv) (synCsn F)) (synC2nd)) (.cv u)))
      (synCfv (synClnimageresfn) (synCop F (synCfv (synC2nd) (.cv u)))) p0014 p0024
  have p0026 := @gFvex (.cv u) (synC2nd)
  have p0027 :=
    @gLnimageresfnval (synCfv (synC2nd) (.cv u)) F hyp_hnbaseresfnvalndv_1 p0026
  have p0028 :=
    @gEqtri
      (synCfv (synCcom (synClnimageresfn)
          (synCtxp (synCxp (synCvv) (synCsn F)) (synC2nd))) (.cv u))
      (synCfv (synClnimageresfn) (synCop F (synCfv (synC2nd) (.cv u))))
      (synCres F (synCfv (synC2nd) (.cv u))) p0025 p0027
  have p0029 :=
    @gEqtri (synCfv (synChnbaseresfn F) (.cv u))
      (synCfv (synCcom (synClnimageresfn)
          (synCtxp (synCxp (synCvv) (synCsn F)) (synC2nd))) (.cv u))
      (synCres F (synCfv (synC2nd) (.cv u))) p0001 p0028
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

/-- Checked nominal proof certificate identified upstream as `g_hncodetrnfnvalndv`. -/
@[expose]
noncomputable def gHncodetrnfnvalndv (u : Var) (F : Class)
    (hyp_hncodetrnfnvalndv_1 : Nominal.NPrf (.classMem F (synCvv)))
    (hyp_hncodetrnfnvalndv_2 : Nominal.NPrf (.classMem (.cv u) (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synChncodetrnfn F) (.cv u)) (synCop (synCcom
            (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
            (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))) :=
  by
  have p0000 := (Nominal.classEqRefl (synChncodetrnfn F))
  have p0001 :=
    @gFveq1i (.cv u) (synChncodetrnfn F)
      (synCcom (synC2nd) (synCcom (synChwgen) (synCtxp (synChnbaseresfn F) (synC1st))))
      p0000
  have p0002 := @gHwgenfn
  have p0003 := @gLnimageresfnfn
  have p0004 := @gFnconstg (synCvv) F (synCvv)
  have p0005 := Nominal.mp hyp_hncodetrnfnvalndv_1 p0004
  have p0006 := @gLn2ndfn
  have p0007 :=
    @gPm32i (synWfn (synCxp (synCvv) (synCsn F)) (synCvv))
      (synWfn (synC2nd) (synCvv)) p0005 p0006
  have p0008 := @gFntxp (synCvv) (synCvv) (synCxp (synCvv) (synCsn F)) (synC2nd)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @gInidm (synCvv)
  have p0011 := @gEqcomi (synCin (synCvv) (synCvv)) (synCvv) p0010
  have p0012 :=
    @gFneq2i (synCvv) (synCin (synCvv) (synCvv))
      (synCtxp (synCxp (synCvv) (synCsn F)) (synC2nd)) p0011
  have p0013 :=
    @gMpbir (synWfn (synCtxp (synCxp (synCvv) (synCsn F)) (synC2nd)) (synCvv))
      (synWfn (synCtxp (synCxp (synCvv) (synCsn F)) (synC2nd))
        (synCin (synCvv) (synCvv)))
      p0009 p0012
  have p0014 :=
    @gFncovv (synClnimageresfn) (synCtxp (synCxp (synCvv) (synCsn F)) (synC2nd))
      p0003 p0013
  have p0015 := (Nominal.classEqRefl (synChnbaseresfn F))
  have p0016 :=
    @gFneq1i (synCvv) (synChnbaseresfn F)
      (synCcom (synClnimageresfn) (synCtxp (synCxp (synCvv) (synCsn F)) (synC2nd)))
      p0015
  have p0017 :=
    @gMpbir (synWfn (synChnbaseresfn F) (synCvv))
      (synWfn (synCcom (synClnimageresfn)
          (synCtxp (synCxp (synCvv) (synCsn F)) (synC2nd))) (synCvv))
      p0014 p0016
  have p0018 := @gLn1stfn
  have p0019 :=
    @gPm32i (synWfn (synChnbaseresfn F) (synCvv)) (synWfn (synC1st) (synCvv))
      p0017 p0018
  have p0020 := @gFntxp (synCvv) (synCvv) (synChnbaseresfn F) (synC1st)
  have p0021 := Nominal.mp p0019 p0020
  have p0024 :=
    @gFneq2i (synCvv) (synCin (synCvv) (synCvv))
      (synCtxp (synChnbaseresfn F) (synC1st)) p0011
  have p0025 :=
    @gMpbir (synWfn (synCtxp (synChnbaseresfn F) (synC1st)) (synCvv))
      (synWfn (synCtxp (synChnbaseresfn F) (synC1st)) (synCin (synCvv) (synCvv)))
      p0021 p0024
  have p0026 :=
    @gFncovv (synChwgen) (synCtxp (synChnbaseresfn F) (synC1st)) p0002 p0025
  have p0027 :=
    @gPm32i
      (synWfn (synCcom (synChwgen) (synCtxp (synChnbaseresfn F) (synC1st))) (synCvv))
      (.classMem (.cv u) (synCvv)) p0026 hyp_hncodetrnfnvalndv_2
  have p0028 :=
    @gFvco2 (synCvv) (.cv u) (synC2nd)
      (synCcom (synChwgen) (synCtxp (synChnbaseresfn F) (synC1st)))
  have p0029 := Nominal.mp p0027 p0028
  have p0053 :=
    @gPm32i (synWfn (synCtxp (synChnbaseresfn F) (synC1st)) (synCvv))
      (.classMem (.cv u) (synCvv)) p0025 hyp_hncodetrnfnvalndv_2
  have p0054 :=
    @gFvco2 (synCvv) (.cv u) (synChwgen) (synCtxp (synChnbaseresfn F) (synC1st))
  have p0055 := Nominal.mp p0053 p0054
  have p0072 :=
    @gFvtxpvv (.cv u) (synChnbaseresfn F) (synC1st) p0017 p0018 hyp_hncodetrnfnvalndv_2
  have p0073 := @gHnbaseresfnvalndv u F hyp_hncodetrnfnvalndv_1 hyp_hncodetrnfnvalndv_2
  have p0074 := @gEqid (synCfv (synC1st) (.cv u))
  have p0075 :=
    @gOpeq12i (synCfv (synChnbaseresfn F) (.cv u))
      (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u))
      (synCfv (synC1st) (.cv u)) p0073 p0074
  have p0076 :=
    @gEqtri (synCfv (synCtxp (synChnbaseresfn F) (synC1st)) (.cv u))
      (synCop (synCfv (synChnbaseresfn F) (.cv u)) (synCfv (synC1st) (.cv u)))
      (synCop (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
      p0072 p0075
  have p0077 :=
    @gFveq2i (synCfv (synCtxp (synChnbaseresfn F) (synC1st)) (.cv u))
      (synCop (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
      (synChwgen) p0076
  have p0078 :=
    @gEqtri
      (synCfv (synCcom (synChwgen) (synCtxp (synChnbaseresfn F) (synC1st))) (.cv u))
      (synCfv (synChwgen) (synCfv (synCtxp (synChnbaseresfn F) (synC1st)) (.cv u)))
      (synCfv (synChwgen)
        (synCop (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u))))
      p0055 p0077
  have p0079 := @gFvex (.cv u) (synC2nd)
  have p0080 := @gResex F (synCfv (synC2nd) (.cv u)) hyp_hncodetrnfnvalndv_1 p0079
  have p0081 := @gFvex (.cv u) (synC1st)
  have p0082 :=
    @gHwgenvalclndv (synCres F (synCfv (synC2nd) (.cv u)))
      (synCfv (synC1st) (.cv u)) p0080 p0081
  have p0083 :=
    @gEqtri
      (synCfv (synCcom (synChwgen) (synCtxp (synChnbaseresfn F) (synC1st))) (.cv u))
      (synCfv (synChwgen)
        (synCop (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u))))
      (synCop (synCop (synCfv (synC1st) (.cv u))
          (synCdm (synCres F (synCfv (synC2nd) (.cv u))))) (synCop (synCcom
            (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
            (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      p0078 p0082
  have p0084 :=
    @gFveq2i
      (synCfv (synCcom (synChwgen) (synCtxp (synChnbaseresfn F) (synC1st))) (.cv u))
      (synCop (synCop (synCfv (synC1st) (.cv u))
          (synCdm (synCres F (synCfv (synC2nd) (.cv u))))) (synCop (synCcom
            (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
            (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      (synC2nd) p0083
  have p0085 :=
    @gEqtri
      (synCfv (synCcom (synC2nd)
          (synCcom (synChwgen) (synCtxp (synChnbaseresfn F) (synC1st)))) (.cv u))
      (synCfv (synC2nd)
        (synCfv (synCcom (synChwgen) (synCtxp (synChnbaseresfn F) (synC1st))) (.cv u)))
      (synCfv (synC2nd) (synCop (synCop (synCfv (synC1st) (.cv u))
            (synCdm (synCres F (synCfv (synC2nd) (.cv u))))) (synCop (synCcom
              (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
              (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))))
      p0029 p0084
  have p0089 := @gDmex (synCres F (synCfv (synC2nd) (.cv u))) p0080
  have p0090 :=
    @gOpex (synCfv (synC1st) (.cv u))
      (synCdm (synCres F (synCfv (synC2nd) (.cv u)))) p0081 p0089
  have p0094 :=
    @gCoex (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)) p0080
      p0081
  have p0097 := @gCnvex (synCres F (synCfv (synC2nd) (.cv u))) p0080
  have p0098 :=
    @gCoex
      (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
      (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) p0094 p0097
  have p0101 := @gRnex (synCres F (synCfv (synC2nd) (.cv u))) p0080
  have p0102 :=
    @gOpex
      (synCcom
        (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
        (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) p0098 p0101
  have p0103 :=
    @gOpfv2nd
      (synCop (synCfv (synC1st) (.cv u)) (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCop (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
            (synCfv (synC1st) (.cv u))) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      p0090 p0102
  have p0104 :=
    @gEqtri
      (synCfv (synCcom (synC2nd)
          (synCcom (synChwgen) (synCtxp (synChnbaseresfn F) (synC1st)))) (.cv u))
      (synCfv (synC2nd) (synCop (synCop (synCfv (synC1st) (.cv u))
            (synCdm (synCres F (synCfv (synC2nd) (.cv u))))) (synCop (synCcom
              (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
              (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))))
      (synCop (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
            (synCfv (synC1st) (.cv u))) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      p0085 p0103
  have p0105 :=
    @gEqtri (synCfv (synChncodetrnfn F) (.cv u))
      (synCfv (synCcom (synC2nd)
          (synCcom (synChwgen) (synCtxp (synChnbaseresfn F) (synC1st)))) (.cv u))
      (synCop (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
            (synCfv (synC1st) (.cv u))) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      p0001 p0104
  exact p0105


end NFChoice.DirectNominalPrf.WPPReplay

end
