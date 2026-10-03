/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk016Compact001Block003

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk016Compact001Part016`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_weincsegcutorwholendv (x : Var) (y : Var) (D : Class) (R : Class)
    (dv_D_y : y ∉ D.fv) (dv_R_y : y ∉ R.fv) (dv_x_y : x ≠ y)
    (hyp_weincsegcutorwholendv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (.classMem (.cv x) D) (syn_wo (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))) D) (syn_wrex y D (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ D.fv ∪ R.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : z ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_D, not_false_eq_true])
  have dv_cache_0002 :
    z ∉
      ((syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_csn (.cv x)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_D, fresh_z_not_R, fresh_z_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 :
    y ∉
      ((syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_csn (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_D_y, dv_R_y, (Ne.symm dv_x_y),
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_y, not_false_eq_true])
  have dv_cache_0005 : z ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_R, not_false_eq_true])
  have dv_cache_0006 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_y, not_false_eq_true])
  have dv_cache_0007 : z ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show z ≠ y from (by exact fresh_z_ne_y))
  have dv_cache_0008 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0009 :
    y ∉
      ((syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x))) D)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_y), dv_D_y, dv_R_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @g_orc
      (.classEq (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_csn (.cv x))) D)
      (syn_wrex y D (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
  have p0001 :=
    @g_a1i
      (.imp (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x))) D) (syn_wo (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))) D) (syn_wrex y D (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))))
      (.classMem (.cv x) D) p0000
  have p0002 :=
    @g_simpl (.classMem (.cv x) D)
      (.neg (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x))) D))
  have p0003 := @g_inss1 D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0004 :=
    @g_a1i
      (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) D)
      (.classMem (.cv x) D) p0003
  have p0005 := @g_snssi (.cv x) D
  have p0006 :=
    @g_jca (.classMem (.cv x) D)
      (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) D)
      (syn_wss (syn_csn (.cv x)) D) p0004 p0005
  have p0007 :=
    @g_unss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_csn (.cv x)) D
  have p0008 :=
    @g_sylib (.classMem (.cv x) D)
      (syn_wa (syn_wss
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) D)
        (syn_wss (syn_csn (.cv x)) D))
      (syn_wss (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_csn (.cv x))) D)
      p0006 p0007
  have p0009 :=
    @g_syl
      (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))) D)))
      (.classMem (.cv x) D)
      (syn_wss (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_csn (.cv x))) D)
      p0002 p0008
  have p0010 :=
    @g_simpr (.classMem (.cv x) D)
      (.neg (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x))) D))
  have p0011 :=
    @g_jca
      (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))) D)))
      (syn_wss (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_csn (.cv x))) D)
      (.neg (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x))) D))
      p0009 p0010
  have p0012 :=
    @g_dfpss2
      (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_csn (.cv x)))
      D
  have p0013 :=
    @g_sylibr
      (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))) D)))
      (syn_wa (syn_wss (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x))) D) (.neg (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))) D)))
      (syn_wpss (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_csn (.cv x))) D)
      p0011 p0012
  have p0014 :=
    @g_dfpss3
      (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_csn (.cv x)))
      D
  have p0015 :=
    @g_sylib
      (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))) D)))
      (syn_wpss (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_csn (.cv x))) D)
      (syn_wa (syn_wss (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x))) D) (.neg (syn_wss D (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))))
      p0013 p0014
  have p0016 :=
    @g_simpr
      (syn_wss (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_csn (.cv x))) D)
      (.neg (syn_wss D (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))))
  have p0017 :=
    @g_syl
      (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))) D)))
      (syn_wa (syn_wss (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x))) D) (.neg (syn_wss D (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))))
      (.neg (syn_wss D (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))))
      p0015 p0016
  have p0018 :=
    @g_nss z D
      (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_csn (.cv x)))
      dv_cache_0001 dv_cache_0002
  have p0019 :=
    @g_sylib
      (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))) D)))
      (.neg (syn_wss D (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))))
      (syn_wex z (syn_wa (.classMem (.cv z) D) (.neg (.classMem (.cv z) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))))))
      p0017 p0018
  have p0020 :=
    (Nominal.biimpRefl (syn_wrex z D (.neg (.classMem (.cv z) (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x)))))))
  have p0021 :=
    @g_sylibr
      (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))) D)))
      (syn_wex z (syn_wa (.classMem (.cv z) D) (.neg (.classMem (.cv z) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))))))
      (syn_wrex z D (.neg (.classMem (.cv z) (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))))
      p0019 p0020
  have p0022 := @g_brex R D (syn_cwe)
  have p0023 := Nominal.mp hyp_weincsegcutorwholendv_1 p0022
  have p0024 := @g_simpr (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
  have p0025 := Nominal.mp p0023 p0024
  have p0028 := @g_simpl (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
  have p0029 := Nominal.mp p0023 p0028
  have p0030 := @g_idex
  have p0031 := @g_difex R (syn_cid) p0029 p0030
  have p0032 := @g_cnvex (syn_cdif R (syn_cid)) p0031
  have p0033 := @g_snex (.cv x)
  have p0034 := @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) p0032 p0033
  have p0035 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0025 p0034
  have p0037 :=
    @g_unex (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_csn (.cv x)) p0035 p0033
  have p0038 :=
    @g_wedifleastssndv z y
      (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_csn (.cv x)))
      D R dv_cache_0002 dv_cache_0003 dv_cache_0001 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 hyp_weincsegcutorwholendv_1 p0037
  have p0039 :=
    @g_syl
      (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))) D)))
      (syn_wrex z D (.neg (.classMem (.cv z) (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))))
      (syn_wrex y D (syn_wa (.neg (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y))))))
      p0021 p0038
  have p0040 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x))) D))) (.classMem (.cv y) D))
      (syn_wa (.neg (.classMem (.cv y) (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y)))))
  have p0041 :=
    @g_simpr
      (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))) D)))
      (.classMem (.cv y) D)
  have p0042 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                  (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y))))))
      (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x))) D))) (.classMem (.cv y) D))
      (.classMem (.cv y) D) p0040 p0041
  have p0043 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x))) D))) (.classMem (.cv y) D))
      (syn_wa (.neg (.classMem (.cv y) (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y)))))
  have p0044 :=
    @g_simpl
      (.neg (.classMem (.cv y) (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))))
      (syn_wss (syn_cdif D (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y))))
  have p0045 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                  (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y))))))
      (syn_wa (.neg (.classMem (.cv y) (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y)))))
      (.neg (.classMem (.cv y) (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))))
      p0043 p0044
  have p0046 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                  (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y))))))
      (.classMem (.cv y) D)
      (.neg (.classMem (.cv y) (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))))
      p0042 p0045
  have p0048 :=
    @g_simpr
      (.neg (.classMem (.cv y) (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))))
      (syn_wss (syn_cdif D (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y))))
  have p0049 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                  (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y))))))
      (syn_wa (.neg (.classMem (.cv y) (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y)))))
      (syn_wss (syn_cdif D (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y))))
      p0043 p0048
  have p0050 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                  (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y))))))
      (syn_wa (.classMem (.cv y) D) (.neg (.classMem (.cv y) (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))))
      (syn_wss (syn_cdif D (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y))))
      p0046 p0049
  have p0052 :=
    @g_simpl
      (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))) D)))
      (.classMem (.cv y) D)
  have p0053 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                  (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y))))))
      (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x))) D))) (.classMem (.cv y) D))
      (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))) D)))
      p0040 p0052
  have p0055 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                  (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y))))))
      (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))) D)))
      (.classMem (.cv x) D) p0053 p0002
  have p0059 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                  (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y))))))
      (.classMem (.cv x) D) (.classMem (.cv y) D) p0055 p0042
  have p0063 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                  (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y))))))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (.neg (.classMem (.cv y) (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))))
      p0059 p0045
  have p0064 := @g_weincsegsscutndv x y D R dv_cache_0008 hyp_weincsegcutorwholendv_1
  have p0065 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                  (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y))))))
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))))
      (syn_wss (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_csn (.cv x)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0063 p0064
  have p0066 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                  (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y))))))
      (syn_wa (syn_wa (.classMem (.cv y) D) (.neg (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))))) (syn_wss (syn_cdif D (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y)))))
      (syn_wss (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_csn (.cv x)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0050 p0065
  have p0067 :=
    @g_wedownexactcutndv y
      (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_csn (.cv x)))
      D R hyp_weincsegcutorwholendv_1
  have p0068 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                  (syn_csn (.cv x))) D))) (.classMem (.cv y) D)) (syn_wa (.neg
            (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y))))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.neg (.classMem (.cv y) (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                  (syn_csn (.cv x)))))) (syn_wss (syn_cdif D (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y))))) (syn_wss (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_csn (.cv x)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0066 p0067
  have p0069 :=
    @g_ex
      (syn_wa (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x))) D))) (.classMem (.cv y) D))
      (syn_wa (.neg (.classMem (.cv y) (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y)))))
      (.classEq (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_csn (.cv x)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0068
  have p0070 :=
    @g_reximdva
      (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))) D)))
      (syn_wa (.neg (.classMem (.cv y) (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y)))))
      (.classEq (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_csn (.cv x)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      y D dv_cache_0009 p0069
  have p0071 :=
    @g_mpd
      (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))) D)))
      (syn_wrex y D (syn_wa (.neg (.classMem (.cv y) (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x))))) (syn_wss (syn_cdif D (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_csn (.cv x)))) (syn_cima R (syn_csn (.cv y))))))
      (syn_wrex y D (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0039 p0070
  have p0072 :=
    @g_olcd
      (syn_wa (.classMem (.cv x) D) (.neg (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x))) D)))
      (syn_wrex y D (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_csn (.cv x))) D)
      p0071
  have p0073 :=
    @g_ex (.classMem (.cv x) D)
      (.neg (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x))) D))
      (syn_wo (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x))) D) (syn_wrex y D (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      p0072
  have p0074 :=
    @g_pm2_61d (.classMem (.cv x) D)
      (.classEq (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_csn (.cv x))) D)
      (syn_wo (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_csn (.cv x))) D) (syn_wrex y D (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_csn (.cv x)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      p0001 p0073
  exact p0074

@[expose]
noncomputable def g_elwecutisoclterminalndv (x : Var) (u : Var) (D : Class) (R : Class)
    (S : Class) (E : Class) (K : Class) (dv_D_u : u ∉ D.fv) (dv_D_x : x ∉ D.fv)
    (dv_E_u : u ∉ E.fv) (dv_E_x : x ∉ E.fv) (dv_K_u : u ∉ K.fv) (dv_K_x : x ∉ K.fv)
    (dv_R_u : u ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_S_u : u ∉ S.fv) (dv_S_x : x ∉ S.fv)
    (dv_u_x : u ≠ x) :
    Nominal.NPrf
      (.imp (.classMem K (syn_cvv)) (syn_wb (.classMem K (syn_cwecutiso R D S E)) (syn_wrex x D
            (syn_wrex u E (syn_wiso K (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ u } : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv ∪ K.fv
  let h : Var := freshVar proofSupport 0
  have fresh_h : h ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_h_ne_x : h ≠ x := by
    intro h
    exact
      fresh_h
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_h : x ≠ h := Ne.symm fresh_h_ne_x
  have fresh_h_ne_u : h ≠ u := by
    intro h
    exact
      fresh_h
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_u_ne_h : u ≠ h := Ne.symm fresh_h_ne_u
  have fresh_h_not_D : h ∉ D.fv := by
    intro h
    exact
      fresh_h
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_h_not_R : h ∉ R.fv := by
    intro h
    exact
      fresh_h
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_h_not_S : h ∉ S.fv := by
    intro h
    exact
      fresh_h
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_h_not_E : h ∉ E.fv := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_h_not_K : h ∉ K.fv := by
    intro h
    exact fresh_h (Finset.mem_union_right _ (h))
  have dv_cache_0001 : u ∉ ((Wff.classEq (.cv h) K)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_h, dv_K_u, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classEq (.cv h) K)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_h, dv_K_x, or_false, not_false_eq_true])
  have dv_cache_0003 : u ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_u, not_false_eq_true])
  have dv_cache_0004 : x ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_x, not_false_eq_true])
  have dv_cache_0005 : u ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_E_u, not_false_eq_true])
  have dv_cache_0006 : x ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_E_x, not_false_eq_true])
  have dv_cache_0007 : u ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_u, not_false_eq_true])
  have dv_cache_0008 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_x, not_false_eq_true])
  have dv_cache_0009 : u ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_S_u, not_false_eq_true])
  have dv_cache_0010 : x ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_S_x, not_false_eq_true])
  have dv_cache_0011 : h ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show h ≠ u from (by exact fresh_h_ne_u))
  have dv_cache_0012 : h ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show h ≠ x from (by exact fresh_h_ne_x))
  have dv_cache_0013 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show u ≠ x from (by exact dv_u_x))
  have dv_cache_0014 : h ∉ (K).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_h_not_K, not_false_eq_true])
  have dv_cache_0015 :
    h ∉
      ((syn_wb (.classMem K (syn_cwecutiso R D S E)) (syn_wrex x D (syn_wrex u E (syn_wiso K
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                    (syn_csn (.cv u))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_h_not_K, fresh_h_not_D, fresh_h_not_E,
          fresh_h_not_R, fresh_h_not_S, fresh_h_ne_x, fresh_h_ne_u,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 := @g_id (.classEq (.cv h) K)
  have p0001 := @g_eleq1d (.classEq (.cv h) K) (.cv h) K (syn_cwecutiso R D S E) p0000
  have p0002 :=
    @g_isoeq1 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin S (syn_cxp
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      K (.cv h)
  have p0003 :=
    @g_rexbidv (.classEq (.cv h) K)
      (syn_wiso (.cv h) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      (syn_wiso K (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      u E dv_cache_0001 p0002
  have p0004 :=
    @g_rexbidv (.classEq (.cv h) K)
      (syn_wrex u E (syn_wiso (.cv h) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wrex u E (syn_wiso K (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      x D dv_cache_0002 p0003
  have p0005 :=
    @g_bibi12d (.classEq (.cv h) K) (.classMem (.cv h) (syn_cwecutiso R D S E))
      (.classMem K (syn_cwecutiso R D S E))
      (syn_wrex x D (syn_wrex u E (syn_wiso (.cv h) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))))
      (syn_wrex x D (syn_wrex u E (syn_wiso K (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))))
      p0001 p0004
  have p0006 :=
    @g_elwecutiso x u D R S h E dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013
  have p0007 :=
    @g_vtoclg
      (syn_wb (.classMem (.cv h) (syn_cwecutiso R D S E)) (syn_wrex x D (syn_wrex u E
            (syn_wiso (.cv h) (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))))
      (syn_wb (.classMem K (syn_cwecutiso R D S E)) (syn_wrex x D (syn_wrex u E (syn_wiso K
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S
                (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))))
      h K (syn_cvv) dv_cache_0014 dv_cache_0015 p0005 p0006
  exact p0007


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part017`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wecutisouniondmcutorwholendv (y : Var) (D : Class) (R : Class)
    (S : Class) (E : Class) (dv_D_y : y ∉ D.fv) (dv_E_y : y ∉ E.fv) (dv_R_y : y ∉ R.fv)
    (dv_S_y : y ∉ S.fv)
    (hyp_wecutisouniondmcutorwholendv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D))
    (hyp_wecutisouniondmcutorwholendv_2 :
      Nominal.NPrf (.classMem (syn_cuni (syn_cwecutiso R D S E)) (syn_cvv))) :
    Nominal.NPrf
      (syn_wo (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (syn_wrex y D
          (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) :=
  by
  let proofSupport : Finset Var := ({ y } : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_y : x ≠ y := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_E : x ∉ E.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_D, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cdm (syn_cuni (syn_cwecutiso R D S E)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          fresh_x_not_D, fresh_x_not_E, fresh_x_not_R, fresh_x_not_S, or_false,
          not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_cdm (syn_cuni (syn_cwecutiso R D S E)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          dv_D_y, dv_E_y, dv_R_y, dv_S_y, or_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_y, not_false_eq_true])
  have dv_cache_0005 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0006 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_y, not_false_eq_true])
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0008 :
    y ∉ ((Wff.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          dv_D_y, dv_E_y, dv_R_y, dv_S_y, or_false, not_false_eq_true])
  have p0000 :=
    @g_orc (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
      (syn_wrex y D (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
  have p0001 := @g_wecutisouniondmrnss D R S E
  have p0002 :=
    @g_simpl (syn_wss (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
      (syn_wss (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @g_a1i (syn_wss (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
      (.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)) p0003
  have p0005 := @g_id (.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D))
  have p0006 :=
    @g_jca (.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D))
      (syn_wss (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
      (.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)) p0004 p0005
  have p0007 := @g_dfpss2 (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D
  have p0008 :=
    @g_sylibr (.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D))
      (syn_wa (syn_wss (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
        (.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)))
      (syn_wpss (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) p0006 p0007
  have p0009 := @g_dfpss3 (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D
  have p0010 :=
    @g_sylib (.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D))
      (syn_wpss (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
      (syn_wa (syn_wss (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
        (.neg (syn_wss D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
      p0008 p0009
  have p0011 :=
    @g_simpr (syn_wss (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
      (.neg (syn_wss D (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
  have p0012 :=
    @g_syl (.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D))
      (syn_wa (syn_wss (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
        (.neg (syn_wss D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
      (.neg (syn_wss D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) p0010 p0011
  have p0013 :=
    @g_nss x D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) dv_cache_0001 dv_cache_0002
  have p0014 :=
    @g_sylib (.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D))
      (.neg (syn_wss D (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      (syn_wex x (syn_wa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))))
      p0012 p0013
  have p0015 :=
    (Nominal.biimpRefl (syn_wrex x D
        (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))))
  have p0016 :=
    @g_sylibr (.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D))
      (syn_wex x (syn_wa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))))
      (syn_wrex x D (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
      p0014 p0015
  have p0017 :=
    @g_dmex (syn_cuni (syn_cwecutiso R D S E)) hyp_wecutisouniondmcutorwholendv_2
  have p0018 :=
    @g_wedifleastssndv x y (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D R dv_cache_0002
      dv_cache_0003 dv_cache_0001 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      hyp_wecutisouniondmcutorwholendv_1 p0017
  have p0019 :=
    @g_syl (.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D))
      (syn_wrex x D (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))
      (syn_wrex y D
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima R (syn_csn (.cv y))))))
      p0016 p0018
  have p0020 := @g_wecutisouniondmexactcutndv y D R S E hyp_wecutisouniondmcutorwholendv_1
  have p0021 :=
    @g_exp31 (.classMem (.cv y) D)
      (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
        (syn_cima R (syn_csn (.cv y))))
      (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0020
  have p0022 :=
    @g_imp3a (.classMem (.cv y) D)
      (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
        (syn_cima R (syn_csn (.cv y))))
      (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0021
  have p0023 :=
    @g_a1i
      (.imp (.classMem (.cv y) D) (.imp
          (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
            (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
              (syn_cima R (syn_csn (.cv y)))))
          (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      (.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)) p0022
  have p0024 :=
    @g_imp (.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D))
      (.classMem (.cv y) D)
      (.imp (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima R (syn_csn (.cv y)))))
        (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0023
  have p0025 :=
    @g_reximdva (.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D))
      (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
        (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
          (syn_cima R (syn_csn (.cv y)))))
      (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      y D dv_cache_0008 p0024
  have p0026 :=
    @g_mpd (.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D))
      (syn_wrex y D
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima R (syn_csn (.cv y))))))
      (syn_wrex y D (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0019 p0025
  have p0027 :=
    @g_olcd (.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D))
      (syn_wrex y D (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) p0026
  have p0028 :=
    @g_pm2_61i (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
      (syn_wo (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (syn_wrex y D
          (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      p0000 p0027
  exact p0028

@[expose]
noncomputable def g_wecutisounionrncutorwholendv (u : Var) (D : Class) (R : Class)
    (S : Class) (E : Class) (dv_D_u : u ∉ D.fv) (dv_E_u : u ∉ E.fv) (dv_R_u : u ∉ R.fv)
    (dv_S_u : u ∉ S.fv)
    (hyp_wecutisounionrncutorwholendv_1 : Nominal.NPrf (syn_wbr S (syn_cwe) E))
    (hyp_wecutisounionrncutorwholendv_2 :
      Nominal.NPrf (.classMem (syn_cuni (syn_cwecutiso R D S E)) (syn_cvv))) :
    Nominal.NPrf
      (syn_wo (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E) (syn_wrex u E
          (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))) :=
  by
  let proofSupport : Finset Var := ({ u } : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_u : x ≠ u := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_E : x ∉ E.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (E).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_E, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_crn (syn_cuni (syn_cwecutiso R D S E)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          fresh_x_not_D, fresh_x_not_E, fresh_x_not_R, fresh_x_not_S, or_false,
          not_false_eq_true])
  have dv_cache_0003 : u ∉ ((syn_crn (syn_cuni (syn_cwecutiso R D S E)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          dv_D_u, dv_E_u, dv_R_u, dv_S_u, or_false, not_false_eq_true])
  have dv_cache_0004 : u ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_E_u, not_false_eq_true])
  have dv_cache_0005 : x ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_S, not_false_eq_true])
  have dv_cache_0006 : u ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_S_u, not_false_eq_true])
  have dv_cache_0007 : x ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ u from (by exact fresh_x_ne_u))
  have dv_cache_0008 :
    u ∉ ((Wff.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          dv_D_u, dv_E_u, dv_R_u, dv_S_u, or_false, not_false_eq_true])
  have p0000 :=
    @g_orc (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)
      (syn_wrex u E (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
  have p0001 := @g_wecutisouniondmrnss D R S E
  have p0002 :=
    @g_simpr (syn_wss (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
      (syn_wss (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @g_a1i (syn_wss (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)
      (.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) p0003
  have p0005 := @g_id (.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))
  have p0006 :=
    @g_jca (.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))
      (syn_wss (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)
      (.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) p0004 p0005
  have p0007 := @g_dfpss2 (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E
  have p0008 :=
    @g_sylibr (.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))
      (syn_wa (syn_wss (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)
        (.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)))
      (syn_wpss (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E) p0006 p0007
  have p0009 := @g_dfpss3 (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E
  have p0010 :=
    @g_sylib (.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))
      (syn_wpss (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)
      (syn_wa (syn_wss (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)
        (.neg (syn_wss E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
      p0008 p0009
  have p0011 :=
    @g_simpr (syn_wss (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)
      (.neg (syn_wss E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
  have p0012 :=
    @g_syl (.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))
      (syn_wa (syn_wss (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)
        (.neg (syn_wss E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
      (.neg (syn_wss E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))) p0010 p0011
  have p0013 :=
    @g_nss x E (syn_crn (syn_cuni (syn_cwecutiso R D S E))) dv_cache_0001 dv_cache_0002
  have p0014 :=
    @g_sylib (.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))
      (.neg (syn_wss E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
      (syn_wex x (syn_wa (.classMem (.cv x) E)
          (.neg (.classMem (.cv x) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))))
      p0012 p0013
  have p0015 :=
    (Nominal.biimpRefl (syn_wrex x E
        (.neg (.classMem (.cv x) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))))
  have p0016 :=
    @g_sylibr (.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))
      (syn_wex x (syn_wa (.classMem (.cv x) E)
          (.neg (.classMem (.cv x) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))))
      (syn_wrex x E (.neg (.classMem (.cv x) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
      p0014 p0015
  have p0017 :=
    @g_rnex (syn_cuni (syn_cwecutiso R D S E)) hyp_wecutisounionrncutorwholendv_2
  have p0018 :=
    @g_wedifleastssndv x u (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E S dv_cache_0002
      dv_cache_0003 dv_cache_0001 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      hyp_wecutisounionrncutorwholendv_1 p0017
  have p0019 :=
    @g_syl (.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))
      (syn_wrex x E (.neg (.classMem (.cv x) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))
      (syn_wrex u E
        (syn_wa (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima S (syn_csn (.cv u))))))
      p0016 p0018
  have p0020 := @g_wecutisounionrnexactcutndv u D R S E hyp_wecutisounionrncutorwholendv_1
  have p0021 :=
    @g_exp31 (.classMem (.cv u) E)
      (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
      (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
        (syn_cima S (syn_csn (.cv u))))
      (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      p0020
  have p0022 :=
    @g_imp3a (.classMem (.cv u) E)
      (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
      (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
        (syn_cima S (syn_csn (.cv u))))
      (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      p0021
  have p0023 :=
    @g_a1i
      (.imp (.classMem (.cv u) E) (.imp
          (syn_wa (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
            (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
              (syn_cima S (syn_csn (.cv u)))))
          (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))))
      (.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) p0022
  have p0024 :=
    @g_imp (.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))
      (.classMem (.cv u) E)
      (.imp (syn_wa (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima S (syn_csn (.cv u)))))
        (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      p0023
  have p0025 :=
    @g_reximdva (.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))
      (syn_wa (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
        (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
          (syn_cima S (syn_csn (.cv u)))))
      (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      u E dv_cache_0008 p0024
  have p0026 :=
    @g_mpd (.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))
      (syn_wrex u E
        (syn_wa (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
            (syn_cima S (syn_csn (.cv u))))))
      (syn_wrex u E (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      p0019 p0025
  have p0027 :=
    @g_olcd (.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))
      (syn_wrex u E (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E) p0026
  have p0028 :=
    @g_pm2_61i (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)
      (syn_wo (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E) (syn_wrex u E
          (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))))
      p0000 p0027
  exact p0028

@[expose]
noncomputable def g_wecutisogencodeparts (x : Var) (D : Class) (R : Class)
    (hyp_wecutisogencodeparts_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (.classMem (.cv x) D) (syn_wa
          (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
          (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ D.fv ∪ R.fv
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_ne_x : u ≠ x := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_u_not_D : u ∉ D.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have dv_cache_0001 : u ∉ ((syn_chnwcutcode R D (.cv x))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_x, fresh_u_not_D, fresh_u_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0002 :
    u ∉
      ((Wff.imp (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D))
          (.classEq (syn_chnwcutcode R D (.cv x))
            (syn_cop (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x)))
              (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_x, fresh_u_not_D, fresh_u_not_R,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_hnwcutcodecnndv x D R hyp_wecutisogencodeparts_1
  have p0002 := @g_elex (syn_chnwcutcode R D (.cv x)) (syn_chwcn D)
  have p0003 :=
    @g_syl (.classMem (.cv x) D) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D))
      (.classMem (syn_chnwcutcode R D (.cv x)) (syn_cvv)) p0000 p0002
  have p0004 := @g_id (.classEq (.cv u) (syn_chnwcutcode R D (.cv x)))
  have p0005 :=
    @g_eleq1d (.classEq (.cv u) (syn_chnwcutcode R D (.cv x))) (.cv u)
      (syn_chnwcutcode R D (.cv x)) (syn_chwcn D) p0004
  have p0008 :=
    @g_fveq2d (.classEq (.cv u) (syn_chnwcutcode R D (.cv x))) (.cv u)
      (syn_chnwcutcode R D (.cv x)) (syn_c1st) p0004
  have p0010 :=
    @g_fveq2d (.classEq (.cv u) (syn_chnwcutcode R D (.cv x))) (.cv u)
      (syn_chnwcutcode R D (.cv x)) (syn_c2nd) p0004
  have p0011 :=
    @g_opeq12d (.classEq (.cv u) (syn_chnwcutcode R D (.cv x)))
      (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x)))
      (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))
      p0008 p0010
  have p0012 :=
    @g_eqeq12d (.classEq (.cv u) (syn_chnwcutcode R D (.cv x))) (.cv u)
      (syn_chnwcutcode R D (.cv x))
      (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_cop (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x)))
        (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))))
      p0004 p0011
  have p0013 :=
    @g_imbi12d (.classEq (.cv u) (syn_chnwcutcode R D (.cv x)))
      (.classMem (.cv u) (syn_chwcn D))
      (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D))
      (.classEq (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (syn_chnwcutcode R D (.cv x))
        (syn_cop (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x)))
          (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))))
      p0005 p0012
  have p0014 := @g_hwcnpair u D
  have p0015 :=
    @g_vtoclg
      (.imp (.classMem (.cv u) (syn_chwcn D)) (.classEq (.cv u)
          (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
      (.imp (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D))
        (.classEq (syn_chnwcutcode R D (.cv x))
          (syn_cop (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x)))
            (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))))))
      u (syn_chnwcutcode R D (.cv x)) (syn_cvv) dv_cache_0001 dv_cache_0002 p0013 p0014
  have p0016 :=
    @g_syl (.classMem (.cv x) D) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_cvv))
      (.imp (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D))
        (.classEq (syn_chnwcutcode R D (.cv x))
          (syn_cop (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x)))
            (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))))))
      p0003 p0015
  have p0017 :=
    @g_mpd (.classMem (.cv x) D) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D))
      (.classEq (syn_chnwcutcode R D (.cv x))
        (syn_cop (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x)))
          (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))))
      p0000 p0016
  have p0018 :=
    @g_eqcomd (.classMem (.cv x) D) (syn_chnwcutcode R D (.cv x))
      (syn_cop (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x)))
        (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))))
      p0017
  have p0019 := (Nominal.classEqRefl (syn_chnwcutcode R D (.cv x)))
  have p0020 :=
    @g_a1i
      (.classEq (syn_chnwcutcode R D (.cv x)) (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classMem (.cv x) D) p0019
  have p0021 :=
    @g_eqtrd (.classMem (.cv x) D)
      (syn_cop (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x)))
        (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))))
      (syn_chnwcutcode R D (.cv x))
      (syn_cop (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0018 p0020
  have p0022 :=
    @g_opth (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x)))
      (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
  have p0023 :=
    @g_sylib (.classMem (.cv x) D)
      (.classEq (syn_cop (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x)))
          (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))) (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
        (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      p0021 p0022
  exact p0023


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part018`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wecutisogenrawcl (A : Class) (B : Class) (C : Class) (f : Var)
    (r : Var) (dv_A_f : f ∉ A.fv) (dv_A_r : r ∉ A.fv) (_dv_B_f : f ∉ B.fv)
    (dv_B_r : r ∉ B.fv) (_dv_C_f : f ∉ C.fv) (dv_C_r : r ∉ C.fv) (dv_f_r : f ≠ r) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
            (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))) (syn_wrex r (syn_cvv) (syn_wa
            (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) C))))) :=
  by
  let proofSupport : Finset Var :=
    A.fv ∪ B.fv ∪ C.fv ∪ ({ f } : Finset Var) ∪ ({ r } : Finset Var)
  let v : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_v_not_B : v ∉ B.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_v_not_C : v ∉ C.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_v_ne_f : v ≠ f := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_v : f ≠ v := Ne.symm fresh_v_ne_f
  have fresh_v_ne_r : v ≠ r := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_v : r ≠ v := Ne.symm fresh_v_ne_r
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_u_ne_f : u ≠ f := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_u : f ≠ u := Ne.symm fresh_u_ne_f
  have fresh_u_ne_r : u ≠ r := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_u : r ≠ u := Ne.symm fresh_u_ne_r
  have fresh_v_ne_u : v ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_v : u ≠ v := Ne.symm fresh_v_ne_u
  have dv_cache_0001 : r ∉ ((Wff.classEq (.cv v) C)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_v, dv_C_r, or_false, not_false_eq_true])
  have dv_cache_0002 : r ∉ ((Wff.classEq (.cv u) B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_u, dv_B_r, or_false, not_false_eq_true])
  have dv_cache_0003 : f ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_f, not_false_eq_true])
  have dv_cache_0004 : r ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_r, not_false_eq_true])
  have dv_cache_0005 : f ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show f ≠ r from (by exact dv_f_r))
  have dv_cache_0006 : f ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show f ≠ u from (by exact fresh_f_ne_u))
  have dv_cache_0007 : f ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show f ≠ v from (by exact fresh_f_ne_v))
  have dv_cache_0008 : r ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show r ≠ u from (by exact fresh_r_ne_u))
  have dv_cache_0009 : r ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show r ≠ v from (by exact fresh_r_ne_v))
  have dv_cache_0010 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0011 : u ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_B, not_false_eq_true])
  have dv_cache_0012 :
    u ∉
      ((Wff.imp (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
              (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wrex r (syn_cvv)
            (syn_wa (syn_wiso (.cv f) (.cv r)
                (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
                (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
                (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                    (syn_crn (.cv f))) (.cv v))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_u_not_B, fresh_u_not_A,
          fresh_u_ne_v, fresh_u_ne_f, fresh_u_ne_r, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0013 : v ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_C, not_false_eq_true])
  have dv_cache_0014 :
    v ∉
      ((Wff.imp (.classMem B (syn_cvv)) (.imp
            (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
              (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
                (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))) (syn_wrex r (syn_cvv) (syn_wa
                (syn_wiso (.cv f) (.cv r)
                  (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_cdm (.cv f)) (syn_crn (.cv f)))
                (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq
                    (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                      (syn_crn (.cv f))) C))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_v_not_B, fresh_v_not_A,
          fresh_v_not_C, fresh_v_ne_f, fresh_v_ne_r, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have p0000 :=
    @g_id
      (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
          (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)))
  have p0001 :=
    @g_simpl (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
        (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))
  have p0002 := @g_simpl (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))
  have p0003 :=
    @g_syl
      (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
          (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)))
      (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
      (.classMem B (syn_chwcn A)) p0001 p0002
  have p0004 := @g_elex B (syn_chwcn A)
  have p0005 :=
    @g_syl
      (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
          (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)))
      (.classMem B (syn_chwcn A)) (.classMem B (syn_cvv)) p0003 p0004
  have p0007 := @g_simpr (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))
  have p0008 :=
    @g_syl
      (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
          (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)))
      (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
      (.classMem C (syn_chwcn A)) p0001 p0007
  have p0009 := @g_elex C (syn_chwcn A)
  have p0010 :=
    @g_syl
      (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
          (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)))
      (.classMem C (syn_chwcn A)) (.classMem C (syn_cvv)) p0008 p0009
  have p0011 := @g_biid (.classMem B (syn_chwcn A))
  have p0012 :=
    @g_a1i (syn_wb (.classMem B (syn_chwcn A)) (.classMem B (syn_chwcn A)))
      (.classEq (.cv v) C) p0011
  have p0013 := @g_id (.classEq (.cv v) C)
  have p0014 := @g_eleq1d (.classEq (.cv v) C) (.cv v) C (syn_chwcn A) p0013
  have p0015 :=
    @g_anbi12d (.classEq (.cv v) C) (.classMem B (syn_chwcn A))
      (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
      (.classMem C (syn_chwcn A)) p0012 p0014
  have p0017 := @g_fveq2d (.classEq (.cv v) C) (.cv v) C (syn_c1st) p0013
  have p0018 :=
    @g_isoeq3 (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c1st) B)
      (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) C) (.cv f)
  have p0019 :=
    @g_syl (.classEq (.cv v) C)
      (.classEq (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) C))
      (syn_wb (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
          (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))))
      p0017 p0018
  have p0021 := @g_fveq2d (.classEq (.cv v) C) (.cv v) C (syn_c2nd) p0013
  have p0022 :=
    @g_isoeq5 (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) C)
      (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (.cv f)
  have p0023 :=
    @g_syl (.classEq (.cv v) C)
      (.classEq (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) C))
      (syn_wb (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
          (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
          (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)))
      p0021 p0022
  have p0024 :=
    @g_bitrd (.classEq (.cv v) C)
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
        (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
        (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))
      p0019 p0023
  have p0025 :=
    @g_anbi12d (.classEq (.cv v) C)
      (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
        (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))
      p0015 p0024
  have p0026 :=
    @g_biid
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
  have p0027 :=
    @g_a1i
      (syn_wb (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f))))
      (.classEq (.cv v) C) p0026
  have p0028 := @g_biid (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
  have p0029 :=
    @g_a1i
      (syn_wb (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
        (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B))
      (.classEq (.cv v) C) p0028
  have p0031 :=
    @g_eqeq2d (.classEq (.cv v) C) (.cv v) C
      (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
      p0013
  have p0032 :=
    @g_anbi12d (.classEq (.cv v) C) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
      (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
      (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))) (.cv v))
      (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))) C)
      p0029 p0031
  have p0033 :=
    @g_anbi12d (.classEq (.cv v) C)
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
          (.cv v)))
      (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
          C))
      p0027 p0032
  have p0034 :=
    @g_rexbidv (.classEq (.cv v) C)
      (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            (.cv v))))
      (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            C)))
      r (syn_cvv) dv_cache_0001 p0033
  have p0035 :=
    @g_imbi12d (.classEq (.cv v) C)
      (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
          (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)))
      (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) C))))
      p0025 p0034
  have p0036 :=
    @g_imbi2d (.classEq (.cv v) C)
      (.imp (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wrex r (syn_cvv) (syn_wa
            (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) (.cv v))))))
      (.imp (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
            (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))) (syn_wrex r (syn_cvv) (syn_wa
            (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) C)))))
      (.classMem B (syn_cvv)) p0035
  have p0037 := @g_id (.classEq (.cv u) B)
  have p0038 := @g_eleq1d (.classEq (.cv u) B) (.cv u) B (syn_chwcn A) p0037
  have p0039 := @g_biid (.classMem (.cv v) (syn_chwcn A))
  have p0040 :=
    @g_a1i (syn_wb (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classEq (.cv u) B) p0039
  have p0041 :=
    @g_anbi12d (.classEq (.cv u) B) (.classMem (.cv u) (syn_chwcn A))
      (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
      (.classMem (.cv v) (syn_chwcn A)) p0038 p0040
  have p0043 := @g_fveq2d (.classEq (.cv u) B) (.cv u) B (syn_c1st) p0037
  have p0044 :=
    @g_isoeq2 (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))
      (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) B)
      (.cv f)
  have p0045 :=
    @g_syl (.classEq (.cv u) B)
      (.classEq (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) B))
      (syn_wb (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      p0043 p0044
  have p0047 := @g_fveq2d (.classEq (.cv u) B) (.cv u) B (syn_c2nd) p0037
  have p0048 :=
    @g_isoeq4 (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))
      (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (.cv f)
  have p0049 :=
    @g_syl (.classEq (.cv u) B)
      (.classEq (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) B))
      (syn_wb (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))))
      p0047 p0048
  have p0050 :=
    @g_bitrd (.classEq (.cv u) B)
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))
      p0045 p0049
  have p0051 :=
    @g_anbi12d (.classEq (.cv u) B)
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))
      p0041 p0050
  have p0053 :=
    @g_a1i
      (syn_wb (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f))))
      (.classEq (.cv u) B) p0026
  have p0055 :=
    @g_eqeq2d (.classEq (.cv u) B) (.cv u) B (syn_cop (.cv r) (syn_cdm (.cv f))) p0037
  have p0056 :=
    @g_biid
      (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))) (.cv v))
  have p0057 :=
    @g_a1i
      (syn_wb (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
            (syn_crn (.cv f))) (.cv v)) (.classEq
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
          (.cv v)))
      (.classEq (.cv u) B) p0056
  have p0058 :=
    @g_anbi12d (.classEq (.cv u) B) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
      (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
      (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))) (.cv v))
      (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))) (.cv v))
      p0055 p0057
  have p0059 :=
    @g_anbi12d (.classEq (.cv u) B)
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
          (.cv v)))
      (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
          (.cv v)))
      p0053 p0058
  have p0060 :=
    @g_rexbidv (.classEq (.cv u) B)
      (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            (.cv v))))
      (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            (.cv v))))
      r (syn_cvv) dv_cache_0002 p0059
  have p0061 :=
    @g_imbi12d (.classEq (.cv u) B)
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      p0051 p0060
  have p0062 :=
    @g_hwnisorawgeni v u A f r dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0063 :=
    @g_vtoclg
      (.imp (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wrex r (syn_cvv)
          (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) (.cv v))))))
      (.imp (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wrex r (syn_cvv) (syn_wa
            (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) (.cv v))))))
      u B (syn_cvv) dv_cache_0011 dv_cache_0012 p0061 p0062
  have p0064 :=
    @g_vtoclg
      (.imp (.classMem B (syn_cvv)) (.imp
          (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
              (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wrex r (syn_cvv)
            (syn_wa (syn_wiso (.cv f) (.cv r)
                (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
                (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
                (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                    (syn_crn (.cv f))) (.cv v)))))))
      (.imp (.classMem B (syn_cvv)) (.imp
          (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
            (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
              (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))) (syn_wrex r (syn_cvv) (syn_wa
              (syn_wiso (.cv f) (.cv r)
                (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
                (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
                (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                    (syn_crn (.cv f))) C))))))
      v C (syn_cvv) dv_cache_0013 dv_cache_0014 p0036 p0063
  have p0065 :=
    @g_syl
      (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
          (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)))
      (.classMem C (syn_cvv))
      (.imp (.classMem B (syn_cvv)) (.imp
          (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
            (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
              (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))) (syn_wrex r (syn_cvv) (syn_wa
              (syn_wiso (.cv f) (.cv r)
                (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
                (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
                (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                    (syn_crn (.cv f))) C))))))
      p0010 p0064
  have p0066 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
          (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)))
      (.classMem B (syn_cvv))
      (.imp (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
            (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))) (syn_wrex r (syn_cvv) (syn_wa
            (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) C)))))
      p0005 p0065
  have p0067 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
          (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)))
      (syn_wa (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
          (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)))
      (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) C))))
      p0000 p0066
  exact p0067

@[expose]
noncomputable def g_wecutisogencodeinran (x : Var) (D : Class) (R : Class)
    (hyp_wecutisogencodeinran_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (.classMem (.cv x) D)
        (.classMem (syn_chnwcutcode R D (.cv x)) (syn_crn (syn_chnwcutrel R D)))) :=
  by
  have p0000 := @g_hnwcutrelfn D R hyp_wecutisogencodeinran_1
  have p0001 :=
    @g_a1i (syn_wfn (syn_chnwcutrel R D) (syn_cpw1 D)) (.classMem (.cv x) D) p0000
  have p0002 := @g_snelpw1 (.cv x) D
  have p0003 :=
    @g_biimpri (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) (.classMem (.cv x) D) p0002
  have p0004 :=
    @g_jca (.classMem (.cv x) D) (syn_wfn (syn_chnwcutrel R D) (syn_cpw1 D))
      (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) p0001 p0003
  have p0005 := @g_fnfvelrn (syn_cpw1 D) (syn_csn (.cv x)) (syn_chnwcutrel R D)
  have p0006 :=
    @g_syl (.classMem (.cv x) D)
      (syn_wa (syn_wfn (syn_chnwcutrel R D) (syn_cpw1 D))
        (.classMem (syn_csn (.cv x)) (syn_cpw1 D)))
      (.classMem (syn_cfv (syn_chnwcutrel R D) (syn_csn (.cv x)))
        (syn_crn (syn_chnwcutrel R D)))
      p0004 p0005
  have p0007 := @g_hnwcutrelvalcld (.cv x) D R hyp_wecutisogencodeinran_1
  have p0008 :=
    @g_eleq1d (.classMem (.cv x) D) (syn_cfv (syn_chnwcutrel R D) (syn_csn (.cv x)))
      (syn_chnwcutcode R D (.cv x)) (syn_crn (syn_chnwcutrel R D)) p0007
  have p0009 :=
    @g_mpbid (.classMem (.cv x) D)
      (.classMem (syn_cfv (syn_chnwcutrel R D) (syn_csn (.cv x)))
        (syn_crn (syn_chnwcutrel R D)))
      (.classMem (syn_chnwcutcode R D (.cv x)) (syn_crn (syn_chnwcutrel R D))) p0006 p0008
  exact p0009

@[expose]
noncomputable def g_wecutisogenrangedecode (x : Var) (B : Class) (D : Class) (R : Class)
    (dv_B_x : x ∉ B.fv) (dv_D_x : x ∉ D.fv) (dv_R_x : x ∉ R.fv)
    (hyp_wecutisogenrangedecode_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (.classMem B (syn_crn (syn_chnwcutrel R D)))
        (syn_wrex x D (.classEq B (syn_chnwcutcode R D (.cv x))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ B.fv ∪ D.fv ∪ R.fv
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_ne_x : u ≠ x := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_u : x ≠ u := Ne.symm fresh_u_ne_x
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_not_D : u ∉ D.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have dv_cache_0001 : u ∉ ((syn_cpw1 D)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_u_not_D,
          not_false_eq_true])
  have dv_cache_0002 : u ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_B, not_false_eq_true])
  have dv_cache_0003 : u ∉ ((syn_chnwcutrel R D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel,
          Finset.mem_union, fresh_u_not_D, fresh_u_not_R, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_u, not_false_eq_true])
  have dv_cache_0005 : x ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_x, not_false_eq_true])
  have dv_cache_0006 :
    x ∉
      ((syn_wa (.classMem (.cv u) (syn_cpw1 D))
          (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel,
          Finset.mem_union, Finset.mem_singleton, fresh_x_ne_u, dv_D_x, dv_R_x, dv_B_x,
          or_false, not_false_eq_true])
  have dv_cache_0007 :
    u ∉ ((syn_wrex x D (.classEq B (syn_chnwcutcode R D (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_u_not_D, fresh_u_not_B, fresh_u_ne_x, fresh_u_not_R,
          or_false, and_false, not_false_eq_true])
  have p0000 := @g_hnwcutrelfn D R hyp_wecutisogenrangedecode_1
  have p0001 :=
    @g_fvelrnb u (syn_cpw1 D) B (syn_chnwcutrel R D) dv_cache_0001 dv_cache_0002
      dv_cache_0003
  have p0002 := Nominal.mp p0000 p0001
  have p0003 :=
    @g_biimpi (.classMem B (syn_crn (syn_chnwcutrel R D)))
      (syn_wrex u (syn_cpw1 D) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) p0002
  have p0004 :=
    @g_simpl (.classMem (.cv u) (syn_cpw1 D))
      (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)
  have p0005 := @g_elpw1 x (.cv u) D dv_cache_0004 dv_cache_0005
  have p0006 :=
    @g_biimpi (.classMem (.cv u) (syn_cpw1 D))
      (syn_wrex x D (.classEq (.cv u) (syn_csn (.cv x)))) p0005
  have p0007 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_cpw1 D))
        (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B))
      (.classMem (.cv u) (syn_cpw1 D)) (syn_wrex x D (.classEq (.cv u) (syn_csn (.cv x))))
      p0004 p0006
  have p0008 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_cpw1 D))
          (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D))
      (.classEq (.cv u) (syn_csn (.cv x)))
  have p0009 :=
    @g_simpl
      (syn_wa (.classMem (.cv u) (syn_cpw1 D))
        (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B))
      (.classMem (.cv x) D)
  have p0010 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_cpw1 D))
            (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D))
        (.classEq (.cv u) (syn_csn (.cv x))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_cpw1 D))
          (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D))
      (syn_wa (.classMem (.cv u) (syn_cpw1 D))
        (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B))
      p0008 p0009
  have p0011 :=
    @g_simpr (.classMem (.cv u) (syn_cpw1 D))
      (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)
  have p0012 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_cpw1 D))
            (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D))
        (.classEq (.cv u) (syn_csn (.cv x))))
      (syn_wa (.classMem (.cv u) (syn_cpw1 D))
        (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B))
      (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B) p0010 p0011
  have p0013 :=
    @g_eqcomd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_cpw1 D))
            (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D))
        (.classEq (.cv u) (syn_csn (.cv x))))
      (syn_cfv (syn_chnwcutrel R D) (.cv u)) B p0012
  have p0014 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (.cv u) (syn_cpw1 D))
          (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D))
      (.classEq (.cv u) (syn_csn (.cv x)))
  have p0015 := @g_id (.classEq (.cv u) (syn_csn (.cv x)))
  have p0016 :=
    @g_fveq2d (.classEq (.cv u) (syn_csn (.cv x))) (.cv u) (syn_csn (.cv x))
      (syn_chnwcutrel R D) p0015
  have p0017 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_cpw1 D))
            (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D))
        (.classEq (.cv u) (syn_csn (.cv x))))
      (.classEq (.cv u) (syn_csn (.cv x)))
      (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u))
        (syn_cfv (syn_chnwcutrel R D) (syn_csn (.cv x))))
      p0014 p0016
  have p0018 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_cpw1 D))
            (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D))
        (.classEq (.cv u) (syn_csn (.cv x))))
      B (syn_cfv (syn_chnwcutrel R D) (.cv u))
      (syn_cfv (syn_chnwcutrel R D) (syn_csn (.cv x))) p0013 p0017
  have p0020 :=
    @g_simpr
      (syn_wa (.classMem (.cv u) (syn_cpw1 D))
        (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B))
      (.classMem (.cv x) D)
  have p0021 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_cpw1 D))
            (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D))
        (.classEq (.cv u) (syn_csn (.cv x))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_cpw1 D))
          (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D))
      (.classMem (.cv x) D) p0008 p0020
  have p0022 := @g_hnwcutrelvalcld (.cv x) D R hyp_wecutisogenrangedecode_1
  have p0023 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_cpw1 D))
            (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D))
        (.classEq (.cv u) (syn_csn (.cv x))))
      (.classMem (.cv x) D)
      (.classEq (syn_cfv (syn_chnwcutrel R D) (syn_csn (.cv x))) (syn_chnwcutcode R D (.cv x)))
      p0021 p0022
  have p0024 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_cpw1 D))
            (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D))
        (.classEq (.cv u) (syn_csn (.cv x))))
      B (syn_cfv (syn_chnwcutrel R D) (syn_csn (.cv x))) (syn_chnwcutcode R D (.cv x))
      p0018 p0023
  have p0025 :=
    @g_ex
      (syn_wa (syn_wa (.classMem (.cv u) (syn_cpw1 D))
          (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D))
      (.classEq (.cv u) (syn_csn (.cv x))) (.classEq B (syn_chnwcutcode R D (.cv x)))
      p0024
  have p0026 :=
    @g_reximdva
      (syn_wa (.classMem (.cv u) (syn_cpw1 D))
        (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B))
      (.classEq (.cv u) (syn_csn (.cv x))) (.classEq B (syn_chnwcutcode R D (.cv x))) x D
      dv_cache_0006 p0025
  have p0027 :=
    @g_mpd
      (syn_wa (.classMem (.cv u) (syn_cpw1 D))
        (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B))
      (syn_wrex x D (.classEq (.cv u) (syn_csn (.cv x))))
      (syn_wrex x D (.classEq B (syn_chnwcutcode R D (.cv x)))) p0007 p0026
  have p0028 :=
    @g_rexlimiva (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B)
      (syn_wrex x D (.classEq B (syn_chnwcutcode R D (.cv x)))) u (syn_cpw1 D)
      dv_cache_0007 p0027
  have p0029 :=
    @g_syl (.classMem B (syn_crn (syn_chnwcutrel R D)))
      (syn_wrex u (syn_cpw1 D) (.classEq (syn_cfv (syn_chnwcutrel R D) (.cv u)) B))
      (syn_wrex x D (.classEq B (syn_chnwcutcode R D (.cv x)))) p0003 p0028
  exact p0029

@[expose]
noncomputable def g_wecutisogencodeambient (x : Var) (D : Class) (R : Class)
    (hyp_wecutisogencodeambient_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (.classMem (.cv x) D)
        (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn (syn_cvv)))) :=
  by
  have p0000 := @g_hnwcutcodecnndv x D R hyp_wecutisogencodeambient_1
  have p0001 := @g_ssv D
  have p0002 := @g_hwcnssbase (syn_cvv) D p0001
  have p0003 :=
    @g_sseli (syn_chwcn D) (syn_chwcn (syn_cvv)) (syn_chnwcutcode R D (.cv x)) p0002
  have p0004 :=
    @g_syl (.classMem (.cv x) D) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D))
      (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn (syn_cvv))) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_wecutisogennormbij (f : Var) (r : Var) :
    Nominal.NPrf
      (.imp (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f))) (.classMem (.cv f) (syn_chwbij))) :=
  by
  have p0000 := @g_hwtrnisob f r
  have p0001 :=
    @g_biimpri (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      p0000
  have p0002 := @g_hwbijf1o f
  have p0003 :=
    @g_biimpri (.classMem (.cv f) (syn_chwbij))
      (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) p0002
  have p0004 :=
    @g_syl
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (.classMem (.cv f) (syn_chwbij)) p0001 p0003
  exact p0004


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part019`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wecutisogenrawmem (B : Class) (C : Class) (D : Class) (R : Class)
    (S : Class) (f : Var) (E : Class) (r : Var) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D)))
            (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv))
            (syn_wa (syn_wiso (.cv f) (.cv r)
                (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
                (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
                (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                    (syn_crn (.cv f))) C))))) (.classMem (.cv f) (syn_cwecutisogen R D S E))) :=
  by
  have p0000 :=
    @g_simpr
      (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D)))
        (.classMem C (syn_crn (syn_chnwcutrel S E))))
      (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) C))))
  have p0001 :=
    @g_simpr (.classMem (.cv r) (syn_cvv))
      (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            C)))
  have p0002 :=
    @g_syl
      (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D)))
          (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv))
          (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) C)))))
      (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) C))))
      (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            C)))
      p0000 p0001
  have p0003 :=
    @g_simpl
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
          C))
  have p0004 :=
    @g_syl
      (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D)))
          (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv))
          (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) C)))))
      (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            C)))
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      p0002 p0003
  have p0005 := @g_wecutisogennormbij f r
  have p0006 :=
    @g_syl
      (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D)))
          (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv))
          (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) C)))))
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (.classMem (.cv f) (syn_chwbij)) p0004 p0005
  have p0008 :=
    @g_simpl (.classMem (.cv r) (syn_cvv))
      (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            C)))
  have p0009 :=
    @g_syl
      (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D)))
          (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv))
          (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) C)))))
      (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) C))))
      (.classMem (.cv r) (syn_cvv)) p0000 p0008
  have p0010 :=
    @g_jca
      (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D)))
          (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv))
          (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) C)))))
      (.classMem (.cv f) (syn_chwbij)) (.classMem (.cv r) (syn_cvv)) p0006 p0009
  have p0011 := @g_opelxp (.cv f) (.cv r) (syn_chwbij) (syn_cvv)
  have p0012 :=
    @g_biimpri (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv)))
      (syn_wa (.classMem (.cv f) (syn_chwbij)) (.classMem (.cv r) (syn_cvv))) p0011
  have p0013 :=
    @g_syl
      (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D)))
          (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv))
          (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) C)))))
      (syn_wa (.classMem (.cv f) (syn_chwbij)) (.classMem (.cv r) (syn_cvv)))
      (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv))) p0010 p0012
  have p0014 :=
    @g_simpl
      (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D)))
        (.classMem C (syn_crn (syn_chnwcutrel S E))))
      (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) C))))
  have p0015 :=
    @g_simpl (.classMem B (syn_crn (syn_chnwcutrel R D)))
      (.classMem C (syn_crn (syn_chnwcutrel S E)))
  have p0016 :=
    @g_syl
      (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D)))
          (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv))
          (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) C)))))
      (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D)))
        (.classMem C (syn_crn (syn_chnwcutrel S E))))
      (.classMem B (syn_crn (syn_chnwcutrel R D))) p0014 p0015
  have p0018 :=
    @g_simpr (.classMem B (syn_crn (syn_chnwcutrel R D)))
      (.classMem C (syn_crn (syn_chnwcutrel S E)))
  have p0019 :=
    @g_syl
      (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D)))
          (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv))
          (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) C)))))
      (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D)))
        (.classMem C (syn_crn (syn_chnwcutrel S E))))
      (.classMem C (syn_crn (syn_chnwcutrel S E))) p0014 p0018
  have p0020 :=
    @g_jca
      (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D)))
          (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv))
          (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) C)))))
      (.classMem B (syn_crn (syn_chnwcutrel R D)))
      (.classMem C (syn_crn (syn_chnwcutrel S E))) p0016 p0019
  have p0021 :=
    @g_opelxp B C (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))
  have p0022 :=
    @g_biimpri
      (.classMem (syn_cop B C)
        (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))
      (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D)))
        (.classMem C (syn_crn (syn_chnwcutrel S E))))
      p0021
  have p0023 :=
    @g_syl
      (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D)))
          (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv))
          (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) C)))))
      (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D)))
        (.classMem C (syn_crn (syn_chnwcutrel S E))))
      (.classMem (syn_cop B C)
        (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))
      p0020 p0022
  have p0024 := @g_vex r
  have p0025 := @g_hwgenval (.cv r) f p0024
  have p0026 :=
    @g_a1i
      (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
        (syn_cop (syn_cop (.cv r) (syn_cdm (.cv f)))
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))))
      (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D)))
          (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv))
          (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) C)))))
      p0025
  have p0030 :=
    @g_simpr
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
          C))
  have p0031 :=
    @g_syl
      (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D)))
          (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv))
          (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) C)))))
      (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            C)))
      (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
          C))
      p0002 p0030
  have p0032 :=
    @g_simpl (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
      (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))) C)
  have p0033 :=
    @g_syl
      (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D)))
          (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv))
          (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) C)))))
      (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
          C))
      (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) p0031 p0032
  have p0039 :=
    @g_simpr (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
      (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))) C)
  have p0040 :=
    @g_syl
      (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D)))
          (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv))
          (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) C)))))
      (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
          C))
      (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))) C)
      p0031 p0039
  have p0041 :=
    @g_opeq12d
      (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D)))
          (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv))
          (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) C)))))
      (syn_cop (.cv r) (syn_cdm (.cv f))) B
      (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
      C p0033 p0040
  have p0042 :=
    @g_eqtrd
      (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D)))
          (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv))
          (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) C)))))
      (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
      (syn_cop (syn_cop (.cv r) (syn_cdm (.cv f)))
        (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))))
      (syn_cop B C) p0026 p0041
  have p0043 :=
    @g_eleq1d
      (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D)))
          (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv))
          (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) C)))))
      (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop B C)
      (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))) p0042
  have p0044 :=
    @g_mpbird
      (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D)))
          (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv))
          (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) C)))))
      (.classMem (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
        (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))
      (.classMem (syn_cop B C)
        (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))
      p0023 p0043
  have p0045 := @g_hwgenfn
  have p0046 := @g_fnfun (syn_cvv) (syn_chwgen)
  have p0047 := Nominal.mp p0045 p0046
  have p0048 := @g_vex f
  have p0050 := @g_opex (.cv f) (.cv r) p0048 p0024
  have p0052 := @g_fndm (syn_cvv) (syn_chwgen)
  have p0053 := Nominal.mp p0045 p0052
  have p0054 := @g_eleq2i (syn_cdm (syn_chwgen)) (syn_cvv) (syn_cop (.cv f) (.cv r)) p0053
  have p0055 :=
    @g_mpbir (.classMem (syn_cop (.cv f) (.cv r)) (syn_cdm (syn_chwgen)))
      (.classMem (syn_cop (.cv f) (.cv r)) (syn_cvv)) p0050 p0054
  have p0056 :=
    @g_pm3_2i (syn_wfun (syn_chwgen))
      (.classMem (syn_cop (.cv f) (.cv r)) (syn_cdm (syn_chwgen))) p0047 p0055
  have p0057 :=
    @g_fvimacnv (syn_cop (.cv f) (.cv r))
      (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))) (syn_chwgen)
  have p0058 := Nominal.mp p0056 p0057
  have p0059 :=
    @g_a1i
      (syn_wb (.classMem (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
          (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))
        (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))))
      (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D)))
          (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv))
          (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) C)))))
      p0058
  have p0060 :=
    @g_mpbid
      (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D)))
          (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv))
          (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) C)))))
      (.classMem (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
        (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))
      (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen))
          (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))
      p0044 p0059
  have p0061 :=
    @g_jca
      (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D)))
          (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv))
          (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) C)))))
      (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv)))
      (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen))
          (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))
      p0013 p0060
  have p0062 :=
    @g_elin (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv))
      (syn_cima (syn_ccnv (syn_chwgen))
        (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))
  have p0063 :=
    @g_biimpri
      (.classMem (syn_cop (.cv f) (.cv r)) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
          (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))))
      (syn_wa (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv)))
        (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))))
      p0062
  have p0064 :=
    @g_syl
      (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D)))
          (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv))
          (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) C)))))
      (syn_wa (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv)))
        (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))))
      (.classMem (syn_cop (.cv f) (.cv r)) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
          (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))))
      p0061 p0063
  have p0065 :=
    (Nominal.biimpRefl (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
          (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r)))
  have p0066 :=
    @g_biimpri
      (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
          (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r))
      (.classMem (syn_cop (.cv f) (.cv r)) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
          (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))))
      p0065
  have p0067 :=
    @g_syl
      (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D)))
          (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv))
          (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) C)))))
      (.classMem (syn_cop (.cv f) (.cv r)) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
          (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))))
      (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
          (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r))
      p0064 p0066
  have p0068 :=
    @g_breldm (.cv f) (.cv r)
      (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen))
          (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))
  have p0069 :=
    @g_syl
      (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D)))
          (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv))
          (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) C)))))
      (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
          (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r))
      (.classMem (.cv f) (syn_cdm (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
            (syn_cima (syn_ccnv (syn_chwgen))
              (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))))
      p0067 p0068
  have p0070 := (Nominal.classEqRefl (syn_cwecutisogen R D S E))
  have p0071 :=
    @g_eleq2i (syn_cwecutisogen R D S E)
      (syn_cdm (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))))
      (.cv f) p0070
  have p0072 :=
    @g_a1i
      (syn_wb (.classMem (.cv f) (syn_cwecutisogen R D S E)) (.classMem (.cv f) (syn_cdm
            (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen))
                (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))))))
      (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D)))
          (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv))
          (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) C)))))
      p0071
  have p0073 :=
    @g_mpbird
      (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D)))
          (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv))
          (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B)
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) C)))))
      (.classMem (.cv f) (syn_cwecutisogen R D S E))
      (.classMem (.cv f) (syn_cdm (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
            (syn_cima (syn_ccnv (syn_chwgen))
              (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))))
      p0069 p0072
  exact p0073

@[expose]
noncomputable def g_wecutisogenrawout (D : Class) (R : Class) (S : Class) (f : Var)
    (E : Class) (r : Var) (dv_D_r : r ∉ D.fv) (dv_E_r : r ∉ E.fv) (dv_R_r : r ∉ R.fv)
    (dv_S_r : r ∉ S.fv) (dv_f_r : f ≠ r) :
    Nominal.NPrf
      (.imp (.classMem (.cv f) (syn_cwecutisogen R D S E)) (syn_wrex r (syn_cvv) (syn_wa
            (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f)))
                (syn_crn (syn_chnwcutrel R D))) (.classMem
                (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))) :=
  by
  have dv_cache_0001 : r ∉ ((Class.cv f)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_f_r), not_false_eq_true])
  have dv_cache_0002 :
    r ∉
      ((syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbij,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel,
          Finset.mem_union, dv_D_r, dv_R_r, dv_E_r, dv_S_r, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (syn_cwecutisogen R D S E))
  have p0001 :=
    @g_eleq2i (syn_cwecutisogen R D S E)
      (syn_cdm (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))))
      (.cv f) p0000
  have p0002 :=
    @g_biimpi (.classMem (.cv f) (syn_cwecutisogen R D S E))
      (.classMem (.cv f) (syn_cdm (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
            (syn_cima (syn_ccnv (syn_chwgen))
              (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))))
      p0001
  have p0003 :=
    @g_eldm r (.cv f)
      (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen))
          (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))
      dv_cache_0001 dv_cache_0002
  have p0004 :=
    @g_biimpi
      (.classMem (.cv f) (syn_cdm (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
            (syn_cima (syn_ccnv (syn_chwgen))
              (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))))
      (syn_wex r (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
            (syn_cima (syn_ccnv (syn_chwgen))
              (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))
          (.cv r)))
      p0003
  have p0005 :=
    @g_syl (.classMem (.cv f) (syn_cwecutisogen R D S E))
      (.classMem (.cv f) (syn_cdm (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
            (syn_cima (syn_ccnv (syn_chwgen))
              (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))))
      (syn_wex r (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
            (syn_cima (syn_ccnv (syn_chwgen))
              (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))
          (.cv r)))
      p0002 p0004
  have p0006 :=
    (Nominal.biimpRefl (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
          (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r)))
  have p0007 :=
    @g_biimpi
      (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
          (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r))
      (.classMem (syn_cop (.cv f) (.cv r)) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
          (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))))
      p0006
  have p0008 :=
    @g_elin (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv))
      (syn_cima (syn_ccnv (syn_chwgen))
        (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))
  have p0009 :=
    @g_biimpi
      (.classMem (syn_cop (.cv f) (.cv r)) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
          (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))))
      (syn_wa (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv)))
        (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))))
      p0008
  have p0010 :=
    @g_syl
      (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
          (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r))
      (.classMem (syn_cop (.cv f) (.cv r)) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
          (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))))
      (syn_wa (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv)))
        (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))))
      p0007 p0009
  have p0011 :=
    @g_simpl (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv)))
      (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen))
          (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))
  have p0012 :=
    @g_syl
      (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
          (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r))
      (syn_wa (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv)))
        (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))))
      (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv))) p0010 p0011
  have p0013 := @g_opelxp (.cv f) (.cv r) (syn_chwbij) (syn_cvv)
  have p0014 :=
    @g_biimpi (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv)))
      (syn_wa (.classMem (.cv f) (syn_chwbij)) (.classMem (.cv r) (syn_cvv))) p0013
  have p0015 :=
    @g_syl
      (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
          (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r))
      (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv)))
      (syn_wa (.classMem (.cv f) (syn_chwbij)) (.classMem (.cv r) (syn_cvv))) p0012 p0014
  have p0016 := @g_simpr (.classMem (.cv f) (syn_chwbij)) (.classMem (.cv r) (syn_cvv))
  have p0017 :=
    @g_syl
      (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
          (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r))
      (syn_wa (.classMem (.cv f) (syn_chwbij)) (.classMem (.cv r) (syn_cvv)))
      (.classMem (.cv r) (syn_cvv)) p0015 p0016
  have p0028 := @g_simpl (.classMem (.cv f) (syn_chwbij)) (.classMem (.cv r) (syn_cvv))
  have p0029 :=
    @g_syl
      (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
          (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r))
      (syn_wa (.classMem (.cv f) (syn_chwbij)) (.classMem (.cv r) (syn_cvv)))
      (.classMem (.cv f) (syn_chwbij)) p0015 p0028
  have p0030 := @g_hwbijf1o f
  have p0031 :=
    @g_biimpi (.classMem (.cv f) (syn_chwbij))
      (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) p0030
  have p0032 := @g_hwtrnisob f r
  have p0033 :=
    @g_biimpi (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      p0032
  have p0034 :=
    @g_syl (.classMem (.cv f) (syn_chwbij))
      (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      p0031 p0033
  have p0035 :=
    @g_syl
      (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
          (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r))
      (.classMem (.cv f) (syn_chwbij))
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      p0029 p0034
  have p0041 :=
    @g_simpr (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv)))
      (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen))
          (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))
  have p0042 :=
    @g_syl
      (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
          (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r))
      (syn_wa (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv)))
        (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))))
      (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen))
          (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))
      p0010 p0041
  have p0043 := @g_hwgenfn
  have p0044 := @g_fnfun (syn_cvv) (syn_chwgen)
  have p0045 := Nominal.mp p0043 p0044
  have p0046 := @g_vex f
  have p0047 := @g_vex r
  have p0048 := @g_opex (.cv f) (.cv r) p0046 p0047
  have p0050 := @g_fndm (syn_cvv) (syn_chwgen)
  have p0051 := Nominal.mp p0043 p0050
  have p0052 := @g_eleq2i (syn_cdm (syn_chwgen)) (syn_cvv) (syn_cop (.cv f) (.cv r)) p0051
  have p0053 :=
    @g_mpbir (.classMem (syn_cop (.cv f) (.cv r)) (syn_cdm (syn_chwgen)))
      (.classMem (syn_cop (.cv f) (.cv r)) (syn_cvv)) p0048 p0052
  have p0054 :=
    @g_pm3_2i (syn_wfun (syn_chwgen))
      (.classMem (syn_cop (.cv f) (.cv r)) (syn_cdm (syn_chwgen))) p0045 p0053
  have p0055 :=
    @g_fvimacnv (syn_cop (.cv f) (.cv r))
      (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))) (syn_chwgen)
  have p0056 := Nominal.mp p0054 p0055
  have p0057 :=
    @g_biimpri
      (.classMem (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
        (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))
      (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen))
          (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))
      p0056
  have p0058 :=
    @g_syl
      (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
          (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r))
      (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen))
          (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))
      (.classMem (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
        (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))
      p0042 p0057
  have p0060 := @g_hwgenval (.cv r) f p0047
  have p0061 :=
    @g_a1i
      (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
        (syn_cop (syn_cop (.cv r) (syn_cdm (.cv f)))
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))))
      (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
          (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r))
      p0060
  have p0062 :=
    @g_eleq1d
      (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
          (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r))
      (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
      (syn_cop (syn_cop (.cv r) (syn_cdm (.cv f)))
        (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))))
      (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))) p0061
  have p0063 :=
    @g_mpbid
      (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
          (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r))
      (.classMem (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
        (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))
      (.classMem (syn_cop (syn_cop (.cv r) (syn_cdm (.cv f)))
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))))
        (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))
      p0058 p0062
  have p0064 :=
    @g_opelxp (syn_cop (.cv r) (syn_cdm (.cv f)))
      (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
      (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))
  have p0065 :=
    @g_biimpi
      (.classMem (syn_cop (syn_cop (.cv r) (syn_cdm (.cv f)))
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))))
        (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))
      (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
        (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
            (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))
      p0064
  have p0066 :=
    @g_syl
      (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
          (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r))
      (.classMem (syn_cop (syn_cop (.cv r) (syn_cdm (.cv f)))
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))))
        (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))
      (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
        (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
            (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))
      p0063 p0065
  have p0067 :=
    @g_jca
      (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
          (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r))
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
        (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
            (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))
      p0035 p0066
  have p0068 :=
    @g_jca
      (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
          (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r))
      (.classMem (.cv r) (syn_cvv))
      (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa
          (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
          (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
              (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))
      p0017 p0067
  have p0069 :=
    @g_eximi
      (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
          (syn_cima (syn_ccnv (syn_chwgen))
            (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r))
      (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
            (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
      r p0068
  have p0070 :=
    (Nominal.biimpRefl (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
            (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))))
  have p0071 :=
    @g_biimpri
      (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
            (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
      (syn_wex r (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f)))
                (syn_crn (syn_chnwcutrel R D))) (.classMem
                (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))))
      p0070
  have p0072 :=
    @g_syl
      (syn_wex r (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
            (syn_cima (syn_ccnv (syn_chwgen))
              (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))
          (.cv r)))
      (syn_wex r (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f)))
                (syn_crn (syn_chnwcutrel R D))) (.classMem
                (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))))
      (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
            (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
      p0069 p0071
  have p0073 :=
    @g_syl (.classMem (.cv f) (syn_cwecutisogen R D S E))
      (syn_wex r (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv))
            (syn_cima (syn_ccnv (syn_chwgen))
              (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))
          (.cv r)))
      (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D)))
            (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
      p0005 p0072
  exact p0073


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part020`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wecutisogenfixedrev (x : Var) (y : Var) (D : Class) (R : Class)
    (S : Class) (f : Var) (E : Class) (r : Var) (_dv_D_f : f ∉ D.fv) (_dv_D_r : r ∉ D.fv)
    (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv) (_dv_E_f : f ∉ E.fv) (_dv_E_r : r ∉ E.fv)
    (dv_E_x : x ∉ E.fv) (dv_E_y : y ∉ E.fv) (_dv_R_f : f ∉ R.fv) (_dv_R_r : r ∉ R.fv)
    (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (_dv_S_f : f ∉ S.fv) (_dv_S_r : r ∉ S.fv)
    (dv_S_x : x ∉ S.fv) (dv_S_y : y ∉ S.fv) (_dv_f_r : f ≠ r) (dv_f_x : f ≠ x)
    (dv_f_y : f ≠ y) (_dv_r_x : r ≠ x) (_dv_r_y : r ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa
            (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa
              (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
        (.classMem (.cv f) (syn_cwecutiso R D S E))) :=
  by
  have dv_cache_0001 : y ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_y, not_false_eq_true])
  have dv_cache_0002 : x ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_x, not_false_eq_true])
  have dv_cache_0003 : y ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_E_y, not_false_eq_true])
  have dv_cache_0004 : x ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_E_x, not_false_eq_true])
  have dv_cache_0005 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_y, not_false_eq_true])
  have dv_cache_0006 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_x, not_false_eq_true])
  have dv_cache_0007 : y ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_S_y, not_false_eq_true])
  have dv_cache_0008 : x ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_S_x, not_false_eq_true])
  have dv_cache_0009 : f ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show f ≠ y from (by exact dv_f_y))
  have dv_cache_0010 : f ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show f ≠ x from (by exact dv_f_x))
  have dv_cache_0011 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show y ≠ x from (by exact Ne.symm dv_x_y))
  have p0000 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))
      (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa
          (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            (syn_chnwcutcode S E (.cv y)))))
  have p0001 := @g_simpl (.classMem (.cv x) D) (.classMem (.cv y) E)
  have p0002 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa
          (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (.classMem (.cv x) D) p0000
      p0001
  have p0004 := @g_simpr (.classMem (.cv x) D) (.classMem (.cv y) E)
  have p0005 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa
          (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (.classMem (.cv y) E) p0000
      p0004
  have p0006 :=
    @g_simpr (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))
      (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa
          (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            (syn_chnwcutcode S E (.cv y)))))
  have p0007 :=
    @g_simpl
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
        (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
            (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))
  have p0008 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa
          (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
      (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa
          (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            (syn_chnwcutcode S E (.cv y)))))
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      p0006 p0007
  have p0010 :=
    @g_simpr
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
        (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
            (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))
  have p0011 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa
          (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
      (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa
          (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            (syn_chnwcutcode S E (.cv y)))))
      (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
        (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
            (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))
      p0006 p0010
  have p0012 :=
    @g_simpl (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
      (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))
  have p0013 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa
          (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
      (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
        (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
            (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))
      (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) p0011
      p0012
  have p0014 := (Nominal.classEqRefl (syn_chnwcutcode R D (.cv x)))
  have p0015 :=
    @g_a1i
      (.classEq (syn_chnwcutcode R D (.cv x)) (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa
          (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
      p0014
  have p0016 :=
    @g_eqtrd
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa
          (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
      (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))
      (syn_cop (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0013 p0015
  have p0017 :=
    @g_opth (.cv r) (syn_cdm (.cv f))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
  have p0018 :=
    @g_sylib
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa
          (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
      (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (.classEq (.cv r) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
        (.classEq (syn_cdm (.cv f))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      p0016 p0017
  have p0019 :=
    @g_simpl
      (.classEq (.cv r) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (.classEq (syn_cdm (.cv f))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0020 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa
          (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
      (syn_wa (.classEq (.cv r) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
        (.classEq (syn_cdm (.cv f))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classEq (.cv r) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      p0018 p0019
  have p0021 :=
    @g_isoeq2 (syn_cdm (.cv f)) (syn_crn (.cv f)) (.cv r)
      (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.cv f)
  have p0022 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa
          (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
      (.classEq (.cv r) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wb (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wiso (.cv f) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
          (syn_crn (.cv f))))
      p0020 p0021
  have p0026 :=
    @g_simpr (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
      (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))
  have p0027 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa
          (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
      (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
        (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
            (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))
      (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))
      p0011 p0026
  have p0028 := (Nominal.classEqRefl (syn_chnwcutcode S E (.cv y)))
  have p0029 :=
    @g_a1i
      (.classEq (syn_chnwcutcode S E (.cv y)) (syn_cop (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa
          (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
      p0028
  have p0030 :=
    @g_eqtrd
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa
          (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
      (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
      (syn_chnwcutcode S E (.cv y))
      (syn_cop (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))
      p0027 p0029
  have p0031 :=
    @g_opth (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))
      (syn_cin S (syn_cxp
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
  have p0032 :=
    @g_sylib
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa
          (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
      (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))) (syn_cop (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (.classEq (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cin S
            (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))))
        (.classEq (syn_crn (.cv f))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      p0030 p0031
  have p0033 :=
    @g_simpl
      (.classEq (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))))
      (.classEq (syn_crn (.cv f))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))
  have p0034 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa
          (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
      (syn_wa (.classEq (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cin S
            (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))))
        (.classEq (syn_crn (.cv f))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))))
      p0032 p0033
  have p0035 :=
    @g_isoeq3 (syn_cdm (.cv f)) (syn_crn (.cv f))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
      (syn_cin S (syn_cxp
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (.cv f)
  have p0036 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa
          (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
      (.classEq (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))))
      (syn_wb (syn_wiso (.cv f) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
          (syn_crn (.cv f))) (syn_wiso (.cv f) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cdm (.cv f)) (syn_crn (.cv f))))
      p0034 p0035
  have p0037 :=
    @g_bitrd
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa
          (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
        (syn_crn (.cv f)))
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      p0022 p0036
  have p0048 :=
    @g_simpr
      (.classEq (.cv r) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (.classEq (syn_cdm (.cv f))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0049 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa
          (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
      (syn_wa (.classEq (.cv r) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
        (.classEq (syn_cdm (.cv f))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classEq (syn_cdm (.cv f))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0018 p0048
  have p0050 :=
    @g_isoeq4 (syn_cdm (.cv f)) (syn_crn (.cv f))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin S (syn_cxp
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (.cv f)
  have p0051 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa
          (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
      (.classEq (syn_cdm (.cv f))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wb (syn_wiso (.cv f) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wiso (.cv f) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_crn (.cv f))))
      p0049 p0050
  have p0052 :=
    @g_bitrd
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa
          (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_crn (.cv f)))
      p0037 p0051
  have p0063 :=
    @g_simpr
      (.classEq (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))))
      (.classEq (syn_crn (.cv f))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))
  have p0064 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa
          (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
      (syn_wa (.classEq (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cin S
            (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))))
        (.classEq (syn_crn (.cv f))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_crn (.cv f))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))
      p0032 p0063
  have p0065 :=
    @g_isoeq5 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_crn (.cv f))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin S (syn_cxp
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (.cv f)
  have p0066 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa
          (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
      (.classEq (syn_crn (.cv f))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))
      (syn_wb (syn_wiso (.cv f) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_crn (.cv f))) (syn_wiso (.cv f) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      p0064 p0065
  have p0067 :=
    @g_bitrd
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa
          (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_crn (.cv f)))
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))
      p0052 p0066
  have p0068 :=
    @g_mpbid
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa
          (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))
      p0008 p0067
  have p0069 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa
          (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
      (.classMem (.cv y) E)
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))
      p0005 p0068
  have p0070 :=
    @g_rspe
      (syn_wiso (.cv f) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))
      y E
  have p0071 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa
          (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
      (syn_wa (.classMem (.cv y) E) (syn_wiso (.cv f) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      (syn_wrex y E (syn_wiso (.cv f) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      p0069 p0070
  have p0072 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa
          (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
      (.classMem (.cv x) D)
      (syn_wrex y E (syn_wiso (.cv f) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      p0002 p0071
  have p0073 :=
    @g_rspe
      (syn_wrex y E (syn_wiso (.cv f) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
      x D
  have p0074 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa
          (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
      (syn_wa (.classMem (.cv x) D) (syn_wrex y E (syn_wiso (.cv f) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))))
      (syn_wrex x D (syn_wrex y E (syn_wiso (.cv f) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))))
      p0072 p0073
  have p0075 :=
    @g_elwecutiso x y D R S f E dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011
  have p0076 :=
    @g_biimpri (.classMem (.cv f) (syn_cwecutiso R D S E))
      (syn_wrex x D (syn_wrex y E (syn_wiso (.cv f) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))))
      p0075
  have p0077 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa
          (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa
            (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))))
      (syn_wrex x D (syn_wrex y E (syn_wiso (.cv f) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv y)))))))
      (.classMem (.cv f) (syn_cwecutiso R D S E)) p0074 p0076
  exact p0077


end NFChoice.DirectNominalPrf.WPPReplay

end
