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

/-- Checked nominal proof certificate identified upstream as `g_weincsegcutorwholendv`. -/
@[expose]
noncomputable def gWeincsegcutorwholendv (x : Var) (y : Var) (D : Class) (R : Class)
    (dv_D_y : y ∉ D.fv) (dv_R_y : y ∉ R.fv) (dv_x_y : x ≠ y)
    (hyp_weincsegcutorwholendv_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (.classMem (.cv x) D) (synWo (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))) D) (synWrex y D (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x))) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))) :=
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
      ((synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCsn (.cv x)))).fv :=
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
      ((synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCsn (.cv x)))).fv :=
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
      ((synWa (.classMem (.cv x) D) (.neg (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x))) D)))).fv :=
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
    @gOrc
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCsn (.cv x))) D)
      (synWrex y D (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
  have p0001 :=
    @gA1i
      (.imp (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x))) D) (synWo (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))) D) (synWrex y D (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x))) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))))
      (.classMem (.cv x) D) p0000
  have p0002 :=
    @gSimpl (.classMem (.cv x) D)
      (.neg (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x))) D))
  have p0003 := @gInss1 D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))
  have p0004 :=
    @gA1i
      (synWss (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) D)
      (.classMem (.cv x) D) p0003
  have p0005 := @gSnssi (.cv x) D
  have p0006 :=
    @gJca (.classMem (.cv x) D)
      (synWss (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) D)
      (synWss (synCsn (.cv x)) D) p0004 p0005
  have p0007 :=
    @gUnss (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCsn (.cv x)) D
  have p0008 :=
    @gSylib (.classMem (.cv x) D)
      (synWa (synWss
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) D)
        (synWss (synCsn (.cv x)) D))
      (synWss (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCsn (.cv x))) D)
      p0006 p0007
  have p0009 :=
    @gSyl
      (synWa (.classMem (.cv x) D) (.neg (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))) D)))
      (.classMem (.cv x) D)
      (synWss (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCsn (.cv x))) D)
      p0002 p0008
  have p0010 :=
    @gSimpr (.classMem (.cv x) D)
      (.neg (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x))) D))
  have p0011 :=
    @gJca
      (synWa (.classMem (.cv x) D) (.neg (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))) D)))
      (synWss (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCsn (.cv x))) D)
      (.neg (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x))) D))
      p0009 p0010
  have p0012 :=
    @gDfpss2
      (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCsn (.cv x)))
      D
  have p0013 :=
    @gSylibr
      (synWa (.classMem (.cv x) D) (.neg (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))) D)))
      (synWa (synWss (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x))) D) (.neg (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))) D)))
      (synWpss (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCsn (.cv x))) D)
      p0011 p0012
  have p0014 :=
    @gDfpss3
      (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCsn (.cv x)))
      D
  have p0015 :=
    @gSylib
      (synWa (.classMem (.cv x) D) (.neg (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))) D)))
      (synWpss (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCsn (.cv x))) D)
      (synWa (synWss (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x))) D) (.neg (synWss D (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))))
      p0013 p0014
  have p0016 :=
    @gSimpr
      (synWss (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCsn (.cv x))) D)
      (.neg (synWss D (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))))
  have p0017 :=
    @gSyl
      (synWa (.classMem (.cv x) D) (.neg (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))) D)))
      (synWa (synWss (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x))) D) (.neg (synWss D (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))))
      (.neg (synWss D (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))))
      p0015 p0016
  have p0018 :=
    @gNss z D
      (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCsn (.cv x)))
      dv_cache_0001 dv_cache_0002
  have p0019 :=
    @gSylib
      (synWa (.classMem (.cv x) D) (.neg (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))) D)))
      (.neg (synWss D (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))))
      (synWex z (synWa (.classMem (.cv z) D) (.neg (.classMem (.cv z) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))))))
      p0017 p0018
  have p0020 :=
    (Nominal.biimpRefl (synWrex z D (.neg (.classMem (.cv z) (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x)))))))
  have p0021 :=
    @gSylibr
      (synWa (.classMem (.cv x) D) (.neg (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))) D)))
      (synWex z (synWa (.classMem (.cv z) D) (.neg (.classMem (.cv z) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))))))
      (synWrex z D (.neg (.classMem (.cv z) (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))))
      p0019 p0020
  have p0022 := @gBrex R D (synCwe)
  have p0023 := Nominal.mp hyp_weincsegcutorwholendv_1 p0022
  have p0024 := @gSimpr (.classMem R (synCvv)) (.classMem D (synCvv))
  have p0025 := Nominal.mp p0023 p0024
  have p0028 := @gSimpl (.classMem R (synCvv)) (.classMem D (synCvv))
  have p0029 := Nominal.mp p0023 p0028
  have p0030 := @gIdex
  have p0031 := @gDifex R (synCid) p0029 p0030
  have p0032 := @gCnvex (synCdif R (synCid)) p0031
  have p0033 := @gSnex (.cv x)
  have p0034 := @gImaex (synCcnv (synCdif R (synCid))) (synCsn (.cv x)) p0032 p0033
  have p0035 :=
    @gInex D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))) p0025 p0034
  have p0037 :=
    @gUnex (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCsn (.cv x)) p0035 p0033
  have p0038 :=
    @gWedifleastssndv z y
      (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCsn (.cv x)))
      D R dv_cache_0002 dv_cache_0003 dv_cache_0001 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 hyp_weincsegcutorwholendv_1 p0037
  have p0039 :=
    @gSyl
      (synWa (.classMem (.cv x) D) (.neg (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))) D)))
      (synWrex z D (.neg (.classMem (.cv z) (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))))
      (synWrex y D (synWa (.neg (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x))))) (synWss (synCdif D (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))) (synCima R (synCsn (.cv y))))))
      p0021 p0038
  have p0040 :=
    @gSimpl
      (synWa (synWa (.classMem (.cv x) D) (.neg (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x))) D))) (.classMem (.cv y) D))
      (synWa (.neg (.classMem (.cv y) (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))) (synWss (synCdif D (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x)))) (synCima R (synCsn (.cv y)))))
  have p0041 :=
    @gSimpr
      (synWa (.classMem (.cv x) D) (.neg (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))) D)))
      (.classMem (.cv y) D)
  have p0042 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                  (synCsn (.cv x))) D))) (.classMem (.cv y) D)) (synWa (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x))))) (synWss (synCdif D (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))) (synCima R (synCsn (.cv y))))))
      (synWa (synWa (.classMem (.cv x) D) (.neg (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x))) D))) (.classMem (.cv y) D))
      (.classMem (.cv y) D) p0040 p0041
  have p0043 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv x) D) (.neg (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x))) D))) (.classMem (.cv y) D))
      (synWa (.neg (.classMem (.cv y) (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))) (synWss (synCdif D (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x)))) (synCima R (synCsn (.cv y)))))
  have p0044 :=
    @gSimpl
      (.neg (.classMem (.cv y) (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))))
      (synWss (synCdif D (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))) (synCima R (synCsn (.cv y))))
  have p0045 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                  (synCsn (.cv x))) D))) (.classMem (.cv y) D)) (synWa (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x))))) (synWss (synCdif D (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))) (synCima R (synCsn (.cv y))))))
      (synWa (.neg (.classMem (.cv y) (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))) (synWss (synCdif D (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x)))) (synCima R (synCsn (.cv y)))))
      (.neg (.classMem (.cv y) (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))))
      p0043 p0044
  have p0046 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                  (synCsn (.cv x))) D))) (.classMem (.cv y) D)) (synWa (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x))))) (synWss (synCdif D (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))) (synCima R (synCsn (.cv y))))))
      (.classMem (.cv y) D)
      (.neg (.classMem (.cv y) (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))))
      p0042 p0045
  have p0048 :=
    @gSimpr
      (.neg (.classMem (.cv y) (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))))
      (synWss (synCdif D (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))) (synCima R (synCsn (.cv y))))
  have p0049 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                  (synCsn (.cv x))) D))) (.classMem (.cv y) D)) (synWa (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x))))) (synWss (synCdif D (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))) (synCima R (synCsn (.cv y))))))
      (synWa (.neg (.classMem (.cv y) (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))) (synWss (synCdif D (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x)))) (synCima R (synCsn (.cv y)))))
      (synWss (synCdif D (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))) (synCima R (synCsn (.cv y))))
      p0043 p0048
  have p0050 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                  (synCsn (.cv x))) D))) (.classMem (.cv y) D)) (synWa (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x))))) (synWss (synCdif D (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))) (synCima R (synCsn (.cv y))))))
      (synWa (.classMem (.cv y) D) (.neg (.classMem (.cv y) (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))))
      (synWss (synCdif D (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))) (synCima R (synCsn (.cv y))))
      p0046 p0049
  have p0052 :=
    @gSimpl
      (synWa (.classMem (.cv x) D) (.neg (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))) D)))
      (.classMem (.cv y) D)
  have p0053 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                  (synCsn (.cv x))) D))) (.classMem (.cv y) D)) (synWa (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x))))) (synWss (synCdif D (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))) (synCima R (synCsn (.cv y))))))
      (synWa (synWa (.classMem (.cv x) D) (.neg (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x))) D))) (.classMem (.cv y) D))
      (synWa (.classMem (.cv x) D) (.neg (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))) D)))
      p0040 p0052
  have p0055 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                  (synCsn (.cv x))) D))) (.classMem (.cv y) D)) (synWa (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x))))) (synWss (synCdif D (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))) (synCima R (synCsn (.cv y))))))
      (synWa (.classMem (.cv x) D) (.neg (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))) D)))
      (.classMem (.cv x) D) p0053 p0002
  have p0059 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                  (synCsn (.cv x))) D))) (.classMem (.cv y) D)) (synWa (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x))))) (synWss (synCdif D (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))) (synCima R (synCsn (.cv y))))))
      (.classMem (.cv x) D) (.classMem (.cv y) D) p0055 p0042
  have p0063 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                  (synCsn (.cv x))) D))) (.classMem (.cv y) D)) (synWa (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x))))) (synWss (synCdif D (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))) (synCima R (synCsn (.cv y))))))
      (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (.neg (.classMem (.cv y) (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))))
      p0059 p0045
  have p0064 := @gWeincsegsscutndv x y D R dv_cache_0008 hyp_weincsegcutorwholendv_1
  have p0065 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                  (synCsn (.cv x))) D))) (.classMem (.cv y) D)) (synWa (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x))))) (synWss (synCdif D (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))) (synCima R (synCsn (.cv y))))))
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))))
      (synWss (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCsn (.cv x)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0063 p0064
  have p0066 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                  (synCsn (.cv x))) D))) (.classMem (.cv y) D)) (synWa (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x))))) (synWss (synCdif D (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))) (synCima R (synCsn (.cv y))))))
      (synWa (synWa (.classMem (.cv y) D) (.neg (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))))) (synWss (synCdif D (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x)))) (synCima R (synCsn (.cv y)))))
      (synWss (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCsn (.cv x)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0050 p0065
  have p0067 :=
    @gWedownexactcutndv y
      (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCsn (.cv x)))
      D R hyp_weincsegcutorwholendv_1
  have p0068 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                  (synCsn (.cv x))) D))) (.classMem (.cv y) D)) (synWa (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x))))) (synWss (synCdif D (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))) (synCima R (synCsn (.cv y))))))
      (synWa (synWa (synWa (.classMem (.cv y) D) (.neg (.classMem (.cv y) (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                  (synCsn (.cv x)))))) (synWss (synCdif D (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))) (synCima R (synCsn (.cv y))))) (synWss (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCsn (.cv x)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0066 p0067
  have p0069 :=
    @gEx
      (synWa (synWa (.classMem (.cv x) D) (.neg (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x))) D))) (.classMem (.cv y) D))
      (synWa (.neg (.classMem (.cv y) (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))) (synWss (synCdif D (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x)))) (synCima R (synCsn (.cv y)))))
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCsn (.cv x)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0068
  have p0070 :=
    @gReximdva
      (synWa (.classMem (.cv x) D) (.neg (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))) D)))
      (synWa (.neg (.classMem (.cv y) (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))) (synWss (synCdif D (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x)))) (synCima R (synCsn (.cv y)))))
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCsn (.cv x)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      y D dv_cache_0009 p0069
  have p0071 :=
    @gMpd
      (synWa (.classMem (.cv x) D) (.neg (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))) D)))
      (synWrex y D (synWa (.neg (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x))))) (synWss (synCdif D (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))) (synCima R (synCsn (.cv y))))))
      (synWrex y D (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0039 p0070
  have p0072 :=
    @gOlcd
      (synWa (.classMem (.cv x) D) (.neg (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))) D)))
      (synWrex y D (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCsn (.cv x))) D)
      p0071
  have p0073 :=
    @gEx (.classMem (.cv x) D)
      (.neg (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x))) D))
      (synWo (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x))) D) (synWrex y D (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      p0072
  have p0074 :=
    @gPm261d (.classMem (.cv x) D)
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCsn (.cv x))) D)
      (synWo (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x))) D) (synWrex y D (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      p0001 p0073
  exact p0074

/-- Checked nominal proof certificate identified upstream as `g_elwecutisoclterminalndv`. -/
@[expose]
noncomputable def gElwecutisoclterminalndv (x : Var) (u : Var) (D : Class) (R : Class)
    (S : Class) (E : Class) (K : Class) (dv_D_u : u ∉ D.fv) (dv_D_x : x ∉ D.fv)
    (dv_E_u : u ∉ E.fv) (dv_E_x : x ∉ E.fv) (dv_K_u : u ∉ K.fv) (dv_K_x : x ∉ K.fv)
    (dv_R_u : u ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_S_u : u ∉ S.fv) (dv_S_x : x ∉ S.fv)
    (dv_u_x : u ≠ x) :
    Nominal.NPrf
      (.imp (.classMem K (synCvv)) (synWb (.classMem K (synCwecutiso R D S E)) (synWrex x D
            (synWrex u E (synWiso K (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
                (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))))) :=
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
      ((synWb (.classMem K (synCwecutiso R D S E)) (synWrex x D (synWrex u E (synWiso K
                (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
                (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin E (synCima (synCcnv (synCdif S (synCid)))
                    (synCsn (.cv u))))))))).fv :=
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
  have p0000 := @gId (.classEq (.cv h) K)
  have p0001 := @gEleq1d (.classEq (.cv h) K) (.cv h) K (synCwecutiso R D S E) p0000
  have p0002 :=
    @gIsoeq1 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      K (.cv h)
  have p0003 :=
    @gRexbidv (.classEq (.cv h) K)
      (synWiso (.cv h) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWiso K (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      u E dv_cache_0001 p0002
  have p0004 :=
    @gRexbidv (.classEq (.cv h) K)
      (synWrex u E (synWiso (.cv h) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWrex u E (synWiso K (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      x D dv_cache_0002 p0003
  have p0005 :=
    @gBibi12d (.classEq (.cv h) K) (.classMem (.cv h) (synCwecutiso R D S E))
      (.classMem K (synCwecutiso R D S E))
      (synWrex x D (synWrex u E (synWiso (.cv h) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))))
      (synWrex x D (synWrex u E (synWiso K (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))))
      p0001 p0004
  have p0006 :=
    @gElwecutiso x u D R S h E dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013
  have p0007 :=
    @gVtoclg
      (synWb (.classMem (.cv h) (synCwecutiso R D S E)) (synWrex x D (synWrex u E
            (synWiso (.cv h) (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))))
      (synWb (.classMem K (synCwecutiso R D S E)) (synWrex x D (synWrex u E (synWiso K
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))))
      h K (synCvv) dv_cache_0014 dv_cache_0015 p0005 p0006
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

/-- Checked nominal proof certificate identified upstream as `g_wecutisouniondmcutorwholendv`. -/
@[expose]
noncomputable def gWecutisouniondmcutorwholendv (y : Var) (D : Class) (R : Class)
    (S : Class) (E : Class) (dv_D_y : y ∉ D.fv) (dv_E_y : y ∉ E.fv) (dv_R_y : y ∉ R.fv)
    (dv_S_y : y ∉ S.fv)
    (hyp_wecutisouniondmcutorwholendv_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_wecutisouniondmcutorwholendv_2 :
      Nominal.NPrf (.classMem (synCuni (synCwecutiso R D S E)) (synCvv))) :
    Nominal.NPrf
      (synWo (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D) (synWrex y D
          (.classEq (synCdm (synCuni (synCwecutiso R D S E))) (synCin D
              (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))) :=
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
  have dv_cache_0002 : x ∉ ((synCdm (synCuni (synCwecutiso R D S E)))).fv :=
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
  have dv_cache_0003 : y ∉ ((synCdm (synCuni (synCwecutiso R D S E)))).fv :=
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
    y ∉ ((Wff.neg (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D))).fv :=
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
    @gOrc (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)
      (synWrex y D (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
  have p0001 := @gWecutisouniondmrnss D R S E
  have p0002 :=
    @gSimpl (synWss (synCdm (synCuni (synCwecutiso R D S E))) D)
      (synWss (synCrn (synCuni (synCwecutiso R D S E))) E)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @gA1i (synWss (synCdm (synCuni (synCwecutiso R D S E))) D)
      (.neg (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)) p0003
  have p0005 := @gId (.neg (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D))
  have p0006 :=
    @gJca (.neg (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D))
      (synWss (synCdm (synCuni (synCwecutiso R D S E))) D)
      (.neg (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)) p0004 p0005
  have p0007 := @gDfpss2 (synCdm (synCuni (synCwecutiso R D S E))) D
  have p0008 :=
    @gSylibr (.neg (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D))
      (synWa (synWss (synCdm (synCuni (synCwecutiso R D S E))) D)
        (.neg (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)))
      (synWpss (synCdm (synCuni (synCwecutiso R D S E))) D) p0006 p0007
  have p0009 := @gDfpss3 (synCdm (synCuni (synCwecutiso R D S E))) D
  have p0010 :=
    @gSylib (.neg (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D))
      (synWpss (synCdm (synCuni (synCwecutiso R D S E))) D)
      (synWa (synWss (synCdm (synCuni (synCwecutiso R D S E))) D)
        (.neg (synWss D (synCdm (synCuni (synCwecutiso R D S E))))))
      p0008 p0009
  have p0011 :=
    @gSimpr (synWss (synCdm (synCuni (synCwecutiso R D S E))) D)
      (.neg (synWss D (synCdm (synCuni (synCwecutiso R D S E)))))
  have p0012 :=
    @gSyl (.neg (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D))
      (synWa (synWss (synCdm (synCuni (synCwecutiso R D S E))) D)
        (.neg (synWss D (synCdm (synCuni (synCwecutiso R D S E))))))
      (.neg (synWss D (synCdm (synCuni (synCwecutiso R D S E))))) p0010 p0011
  have p0013 :=
    @gNss x D (synCdm (synCuni (synCwecutiso R D S E))) dv_cache_0001 dv_cache_0002
  have p0014 :=
    @gSylib (.neg (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D))
      (.neg (synWss D (synCdm (synCuni (synCwecutiso R D S E)))))
      (synWex x (synWa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E)))))))
      p0012 p0013
  have p0015 :=
    (Nominal.biimpRefl (synWrex x D
        (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E)))))))
  have p0016 :=
    @gSylibr (.neg (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D))
      (synWex x (synWa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E)))))))
      (synWrex x D (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
      p0014 p0015
  have p0017 :=
    @gDmex (synCuni (synCwecutiso R D S E)) hyp_wecutisouniondmcutorwholendv_2
  have p0018 :=
    @gWedifleastssndv x y (synCdm (synCuni (synCwecutiso R D S E))) D R dv_cache_0002
      dv_cache_0003 dv_cache_0001 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      hyp_wecutisouniondmcutorwholendv_1 p0017
  have p0019 :=
    @gSyl (.neg (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D))
      (synWrex x D (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
      (synWrex y D
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
          (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
            (synCima R (synCsn (.cv y))))))
      p0016 p0018
  have p0020 := @gWecutisouniondmexactcutndv y D R S E hyp_wecutisouniondmcutorwholendv_1
  have p0021 :=
    @gExp31 (.classMem (.cv y) D)
      (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
        (synCima R (synCsn (.cv y))))
      (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0020
  have p0022 :=
    @gImp3a (.classMem (.cv y) D)
      (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
        (synCima R (synCsn (.cv y))))
      (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0021
  have p0023 :=
    @gA1i
      (.imp (.classMem (.cv y) D) (.imp
          (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
            (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
              (synCima R (synCsn (.cv y)))))
          (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      (.neg (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)) p0022
  have p0024 :=
    @gImp (.neg (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D))
      (.classMem (.cv y) D)
      (.imp (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
          (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
            (synCima R (synCsn (.cv y)))))
        (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0023
  have p0025 :=
    @gReximdva (.neg (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D))
      (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
        (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
          (synCima R (synCsn (.cv y)))))
      (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      y D dv_cache_0008 p0024
  have p0026 :=
    @gMpd (.neg (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D))
      (synWrex y D
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
          (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
            (synCima R (synCsn (.cv y))))))
      (synWrex y D (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0019 p0025
  have p0027 :=
    @gOlcd (.neg (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D))
      (synWrex y D (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D) p0026
  have p0028 :=
    @gPm261i (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)
      (synWo (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D) (synWrex y D
          (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      p0000 p0027
  exact p0028

/-- Checked nominal proof certificate identified upstream as `g_wecutisounionrncutorwholendv`. -/
@[expose]
noncomputable def gWecutisounionrncutorwholendv (u : Var) (D : Class) (R : Class)
    (S : Class) (E : Class) (dv_D_u : u ∉ D.fv) (dv_E_u : u ∉ E.fv) (dv_R_u : u ∉ R.fv)
    (dv_S_u : u ∉ S.fv)
    (hyp_wecutisounionrncutorwholendv_1 : Nominal.NPrf (synWbr S (synCwe) E))
    (hyp_wecutisounionrncutorwholendv_2 :
      Nominal.NPrf (.classMem (synCuni (synCwecutiso R D S E)) (synCvv))) :
    Nominal.NPrf
      (synWo (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E) (synWrex u E
          (.classEq (synCrn (synCuni (synCwecutiso R D S E))) (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))) :=
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
  have dv_cache_0002 : x ∉ ((synCrn (synCuni (synCwecutiso R D S E)))).fv :=
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
  have dv_cache_0003 : u ∉ ((synCrn (synCuni (synCwecutiso R D S E)))).fv :=
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
    u ∉ ((Wff.neg (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E))).fv :=
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
    @gOrc (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E)
      (synWrex u E (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
  have p0001 := @gWecutisouniondmrnss D R S E
  have p0002 :=
    @gSimpr (synWss (synCdm (synCuni (synCwecutiso R D S E))) D)
      (synWss (synCrn (synCuni (synCwecutiso R D S E))) E)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @gA1i (synWss (synCrn (synCuni (synCwecutiso R D S E))) E)
      (.neg (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E)) p0003
  have p0005 := @gId (.neg (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E))
  have p0006 :=
    @gJca (.neg (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E))
      (synWss (synCrn (synCuni (synCwecutiso R D S E))) E)
      (.neg (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E)) p0004 p0005
  have p0007 := @gDfpss2 (synCrn (synCuni (synCwecutiso R D S E))) E
  have p0008 :=
    @gSylibr (.neg (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E))
      (synWa (synWss (synCrn (synCuni (synCwecutiso R D S E))) E)
        (.neg (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E)))
      (synWpss (synCrn (synCuni (synCwecutiso R D S E))) E) p0006 p0007
  have p0009 := @gDfpss3 (synCrn (synCuni (synCwecutiso R D S E))) E
  have p0010 :=
    @gSylib (.neg (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E))
      (synWpss (synCrn (synCuni (synCwecutiso R D S E))) E)
      (synWa (synWss (synCrn (synCuni (synCwecutiso R D S E))) E)
        (.neg (synWss E (synCrn (synCuni (synCwecutiso R D S E))))))
      p0008 p0009
  have p0011 :=
    @gSimpr (synWss (synCrn (synCuni (synCwecutiso R D S E))) E)
      (.neg (synWss E (synCrn (synCuni (synCwecutiso R D S E)))))
  have p0012 :=
    @gSyl (.neg (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E))
      (synWa (synWss (synCrn (synCuni (synCwecutiso R D S E))) E)
        (.neg (synWss E (synCrn (synCuni (synCwecutiso R D S E))))))
      (.neg (synWss E (synCrn (synCuni (synCwecutiso R D S E))))) p0010 p0011
  have p0013 :=
    @gNss x E (synCrn (synCuni (synCwecutiso R D S E))) dv_cache_0001 dv_cache_0002
  have p0014 :=
    @gSylib (.neg (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E))
      (.neg (synWss E (synCrn (synCuni (synCwecutiso R D S E)))))
      (synWex x (synWa (.classMem (.cv x) E)
          (.neg (.classMem (.cv x) (synCrn (synCuni (synCwecutiso R D S E)))))))
      p0012 p0013
  have p0015 :=
    (Nominal.biimpRefl (synWrex x E
        (.neg (.classMem (.cv x) (synCrn (synCuni (synCwecutiso R D S E)))))))
  have p0016 :=
    @gSylibr (.neg (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E))
      (synWex x (synWa (.classMem (.cv x) E)
          (.neg (.classMem (.cv x) (synCrn (synCuni (synCwecutiso R D S E)))))))
      (synWrex x E (.neg (.classMem (.cv x) (synCrn (synCuni (synCwecutiso R D S E))))))
      p0014 p0015
  have p0017 :=
    @gRnex (synCuni (synCwecutiso R D S E)) hyp_wecutisounionrncutorwholendv_2
  have p0018 :=
    @gWedifleastssndv x u (synCrn (synCuni (synCwecutiso R D S E))) E S dv_cache_0002
      dv_cache_0003 dv_cache_0001 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      hyp_wecutisounionrncutorwholendv_1 p0017
  have p0019 :=
    @gSyl (.neg (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E))
      (synWrex x E (.neg (.classMem (.cv x) (synCrn (synCuni (synCwecutiso R D S E))))))
      (synWrex u E
        (synWa (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E)))))
          (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
            (synCima S (synCsn (.cv u))))))
      p0016 p0018
  have p0020 := @gWecutisounionrnexactcutndv u D R S E hyp_wecutisounionrncutorwholendv_1
  have p0021 :=
    @gExp31 (.classMem (.cv u) E)
      (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E)))))
      (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
        (synCima S (synCsn (.cv u))))
      (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      p0020
  have p0022 :=
    @gImp3a (.classMem (.cv u) E)
      (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E)))))
      (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
        (synCima S (synCsn (.cv u))))
      (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      p0021
  have p0023 :=
    @gA1i
      (.imp (.classMem (.cv u) E) (.imp
          (synWa (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E)))))
            (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
              (synCima S (synCsn (.cv u)))))
          (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))))
      (.neg (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E)) p0022
  have p0024 :=
    @gImp (.neg (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E))
      (.classMem (.cv u) E)
      (.imp (synWa (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E)))))
          (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
            (synCima S (synCsn (.cv u)))))
        (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      p0023
  have p0025 :=
    @gReximdva (.neg (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E))
      (synWa (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E)))))
        (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
          (synCima S (synCsn (.cv u)))))
      (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      u E dv_cache_0008 p0024
  have p0026 :=
    @gMpd (.neg (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E))
      (synWrex u E
        (synWa (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E)))))
          (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
            (synCima S (synCsn (.cv u))))))
      (synWrex u E (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      p0019 p0025
  have p0027 :=
    @gOlcd (.neg (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E))
      (synWrex u E (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E) p0026
  have p0028 :=
    @gPm261i (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E)
      (synWo (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E) (synWrex u E
          (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))))
      p0000 p0027
  exact p0028

/-- Checked nominal proof certificate identified upstream as `g_wecutisogencodeparts`. -/
@[expose]
noncomputable def gWecutisogencodeparts (x : Var) (D : Class) (R : Class)
    (hyp_wecutisogencodeparts_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (.classMem (.cv x) D) (synWa
          (.classEq (synCfv (synC1st) (synChnwcutcode R D (.cv x))) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
          (.classEq (synCfv (synC2nd) (synChnwcutcode R D (.cv x))) (synCin D
              (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))) :=
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
  have dv_cache_0001 : u ∉ ((synChnwcutcode R D (.cv x))).fv := by
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
      ((Wff.imp (.classMem (synChnwcutcode R D (.cv x)) (synChwcn D))
          (.classEq (synChnwcutcode R D (.cv x))
            (synCop (synCfv (synC1st) (synChnwcutcode R D (.cv x)))
              (synCfv (synC2nd) (synChnwcutcode R D (.cv x))))))).fv :=
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
  have p0000 := @gHnwcutcodecnndv x D R hyp_wecutisogencodeparts_1
  have p0002 := @gElex (synChnwcutcode R D (.cv x)) (synChwcn D)
  have p0003 :=
    @gSyl (.classMem (.cv x) D) (.classMem (synChnwcutcode R D (.cv x)) (synChwcn D))
      (.classMem (synChnwcutcode R D (.cv x)) (synCvv)) p0000 p0002
  have p0004 := @gId (.classEq (.cv u) (synChnwcutcode R D (.cv x)))
  have p0005 :=
    @gEleq1d (.classEq (.cv u) (synChnwcutcode R D (.cv x))) (.cv u)
      (synChnwcutcode R D (.cv x)) (synChwcn D) p0004
  have p0008 :=
    @gFveq2d (.classEq (.cv u) (synChnwcutcode R D (.cv x))) (.cv u)
      (synChnwcutcode R D (.cv x)) (synC1st) p0004
  have p0010 :=
    @gFveq2d (.classEq (.cv u) (synChnwcutcode R D (.cv x))) (.cv u)
      (synChnwcutcode R D (.cv x)) (synC2nd) p0004
  have p0011 :=
    @gOpeq12d (.classEq (.cv u) (synChnwcutcode R D (.cv x)))
      (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (synChnwcutcode R D (.cv x)))
      (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (synChnwcutcode R D (.cv x)))
      p0008 p0010
  have p0012 :=
    @gEqeq12d (.classEq (.cv u) (synChnwcutcode R D (.cv x))) (.cv u)
      (synChnwcutcode R D (.cv x))
      (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))
      (synCop (synCfv (synC1st) (synChnwcutcode R D (.cv x)))
        (synCfv (synC2nd) (synChnwcutcode R D (.cv x))))
      p0004 p0011
  have p0013 :=
    @gImbi12d (.classEq (.cv u) (synChnwcutcode R D (.cv x)))
      (.classMem (.cv u) (synChwcn D))
      (.classMem (synChnwcutcode R D (.cv x)) (synChwcn D))
      (.classEq (.cv u) (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))))
      (.classEq (synChnwcutcode R D (.cv x))
        (synCop (synCfv (synC1st) (synChnwcutcode R D (.cv x)))
          (synCfv (synC2nd) (synChnwcutcode R D (.cv x)))))
      p0005 p0012
  have p0014 := @gHwcnpair u D
  have p0015 :=
    @gVtoclg
      (.imp (.classMem (.cv u) (synChwcn D)) (.classEq (.cv u)
          (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
      (.imp (.classMem (synChnwcutcode R D (.cv x)) (synChwcn D))
        (.classEq (synChnwcutcode R D (.cv x))
          (synCop (synCfv (synC1st) (synChnwcutcode R D (.cv x)))
            (synCfv (synC2nd) (synChnwcutcode R D (.cv x))))))
      u (synChnwcutcode R D (.cv x)) (synCvv) dv_cache_0001 dv_cache_0002 p0013 p0014
  have p0016 :=
    @gSyl (.classMem (.cv x) D) (.classMem (synChnwcutcode R D (.cv x)) (synCvv))
      (.imp (.classMem (synChnwcutcode R D (.cv x)) (synChwcn D))
        (.classEq (synChnwcutcode R D (.cv x))
          (synCop (synCfv (synC1st) (synChnwcutcode R D (.cv x)))
            (synCfv (synC2nd) (synChnwcutcode R D (.cv x))))))
      p0003 p0015
  have p0017 :=
    @gMpd (.classMem (.cv x) D) (.classMem (synChnwcutcode R D (.cv x)) (synChwcn D))
      (.classEq (synChnwcutcode R D (.cv x))
        (synCop (synCfv (synC1st) (synChnwcutcode R D (.cv x)))
          (synCfv (synC2nd) (synChnwcutcode R D (.cv x)))))
      p0000 p0016
  have p0018 :=
    @gEqcomd (.classMem (.cv x) D) (synChnwcutcode R D (.cv x))
      (synCop (synCfv (synC1st) (synChnwcutcode R D (.cv x)))
        (synCfv (synC2nd) (synChnwcutcode R D (.cv x))))
      p0017
  have p0019 := (Nominal.classEqRefl (synChnwcutcode R D (.cv x)))
  have p0020 :=
    @gA1i
      (.classEq (synChnwcutcode R D (.cv x)) (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classMem (.cv x) D) p0019
  have p0021 :=
    @gEqtrd (.classMem (.cv x) D)
      (synCop (synCfv (synC1st) (synChnwcutcode R D (.cv x)))
        (synCfv (synC2nd) (synChnwcutcode R D (.cv x))))
      (synChnwcutcode R D (.cv x))
      (synCop (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0018 p0020
  have p0022 :=
    @gOpth (synCfv (synC1st) (synChnwcutcode R D (.cv x)))
      (synCfv (synC2nd) (synChnwcutcode R D (.cv x)))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
  have p0023 :=
    @gSylib (.classMem (.cv x) D)
      (.classEq (synCop (synCfv (synC1st) (synChnwcutcode R D (.cv x)))
          (synCfv (synC2nd) (synChnwcutcode R D (.cv x)))) (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWa (.classEq (synCfv (synC1st) (synChnwcutcode R D (.cv x))) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
        (.classEq (synCfv (synC2nd) (synChnwcutcode R D (.cv x)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
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

/-- Checked nominal proof certificate identified upstream as `g_wecutisogenrawcl`. -/
@[expose]
noncomputable def gWecutisogenrawcl (A : Class) (B : Class) (C : Class) (f : Var)
    (r : Var) (dv_A_f : f ∉ A.fv) (dv_A_r : r ∉ A.fv) (_dv_B_f : f ∉ B.fv)
    (dv_B_r : r ∉ B.fv) (_dv_C_f : f ∉ C.fv) (dv_C_r : r ∉ C.fv) (dv_f_r : f ≠ r) :
    Nominal.NPrf
      (.imp (synWa (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) C)
            (synCfv (synC2nd) B) (synCfv (synC2nd) C))) (synWrex r (synCvv) (synWa
            (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) C))))) :=
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
      ((Wff.imp (synWa (synWa (.classMem B (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
              (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)))) (synWrex r (synCvv)
            (synWa (synWiso (.cv f) (.cv r)
                (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
                (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
                (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                    (synCrn (.cv f))) (.cv v))))))).fv :=
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
      ((Wff.imp (.classMem B (synCvv)) (.imp
            (synWa (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
              (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) C)
                (synCfv (synC2nd) B) (synCfv (synC2nd) C))) (synWrex r (synCvv) (synWa
                (synWiso (.cv f) (.cv r)
                  (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCdm (.cv f)) (synCrn (.cv f)))
                (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B) (.classEq
                    (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                      (synCrn (.cv f))) C))))))).fv :=
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
    @gId
      (synWa (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) C)
          (synCfv (synC2nd) B) (synCfv (synC2nd) C)))
  have p0001 :=
    @gSimpl (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
      (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) C)
        (synCfv (synC2nd) B) (synCfv (synC2nd) C))
  have p0002 := @gSimpl (.classMem B (synChwcn A)) (.classMem C (synChwcn A))
  have p0003 :=
    @gSyl
      (synWa (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) C)
          (synCfv (synC2nd) B) (synCfv (synC2nd) C)))
      (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
      (.classMem B (synChwcn A)) p0001 p0002
  have p0004 := @gElex B (synChwcn A)
  have p0005 :=
    @gSyl
      (synWa (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) C)
          (synCfv (synC2nd) B) (synCfv (synC2nd) C)))
      (.classMem B (synChwcn A)) (.classMem B (synCvv)) p0003 p0004
  have p0007 := @gSimpr (.classMem B (synChwcn A)) (.classMem C (synChwcn A))
  have p0008 :=
    @gSyl
      (synWa (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) C)
          (synCfv (synC2nd) B) (synCfv (synC2nd) C)))
      (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
      (.classMem C (synChwcn A)) p0001 p0007
  have p0009 := @gElex C (synChwcn A)
  have p0010 :=
    @gSyl
      (synWa (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) C)
          (synCfv (synC2nd) B) (synCfv (synC2nd) C)))
      (.classMem C (synChwcn A)) (.classMem C (synCvv)) p0008 p0009
  have p0011 := @gBiid (.classMem B (synChwcn A))
  have p0012 :=
    @gA1i (synWb (.classMem B (synChwcn A)) (.classMem B (synChwcn A)))
      (.classEq (.cv v) C) p0011
  have p0013 := @gId (.classEq (.cv v) C)
  have p0014 := @gEleq1d (.classEq (.cv v) C) (.cv v) C (synChwcn A) p0013
  have p0015 :=
    @gAnbi12d (.classEq (.cv v) C) (.classMem B (synChwcn A))
      (.classMem B (synChwcn A)) (.classMem (.cv v) (synChwcn A))
      (.classMem C (synChwcn A)) p0012 p0014
  have p0017 := @gFveq2d (.classEq (.cv v) C) (.cv v) C (synC1st) p0013
  have p0018 :=
    @gIsoeq3 (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)) (synCfv (synC1st) B)
      (synCfv (synC1st) (.cv v)) (synCfv (synC1st) C) (.cv f)
  have p0019 :=
    @gSyl (.classEq (.cv v) C)
      (.classEq (synCfv (synC1st) (.cv v)) (synCfv (synC1st) C))
      (synWb (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)))
        (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) C)
          (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v))))
      p0017 p0018
  have p0021 := @gFveq2d (.classEq (.cv v) C) (.cv v) C (synC2nd) p0013
  have p0022 :=
    @gIsoeq5 (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) C)
      (synCfv (synC1st) B) (synCfv (synC1st) C) (.cv f)
  have p0023 :=
    @gSyl (.classEq (.cv v) C)
      (.classEq (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) C))
      (synWb (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) C)
          (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)))
        (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) C)
          (synCfv (synC2nd) B) (synCfv (synC2nd) C)))
      p0021 p0022
  have p0024 :=
    @gBitrd (.classEq (.cv v) C)
      (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)))
      (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) C)
        (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)))
      (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) C)
        (synCfv (synC2nd) B) (synCfv (synC2nd) C))
      p0019 p0023
  have p0025 :=
    @gAnbi12d (.classEq (.cv v) C)
      (synWa (.classMem B (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
      (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)))
      (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) C)
        (synCfv (synC2nd) B) (synCfv (synC2nd) C))
      p0015 p0024
  have p0026 :=
    @gBiid
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
  have p0027 :=
    @gA1i
      (synWb (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f)))
        (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f))))
      (.classEq (.cv v) C) p0026
  have p0028 := @gBiid (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
  have p0029 :=
    @gA1i
      (synWb (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
        (.classEq (synCop (.cv r) (synCdm (.cv f))) B))
      (.classEq (.cv v) C) p0028
  have p0031 :=
    @gEqeq2d (.classEq (.cv v) C) (.cv v) C
      (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
      p0013
  have p0032 :=
    @gAnbi12d (.classEq (.cv v) C) (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
      (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
      (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCrn (.cv f))) (.cv v))
      (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCrn (.cv f))) C)
      p0029 p0031
  have p0033 :=
    @gAnbi12d (.classEq (.cv v) C)
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B) (.classEq
          (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
          (.cv v)))
      (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B) (.classEq
          (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
          C))
      p0027 p0032
  have p0034 :=
    @gRexbidv (.classEq (.cv v) C)
      (synWa (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f)))
        (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            (.cv v))))
      (synWa (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f)))
        (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            C)))
      r (synCvv) dv_cache_0001 p0033
  have p0035 :=
    @gImbi12d (.classEq (.cv v) C)
      (synWa (synWa (.classMem B (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v))))
      (synWa (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) C)
          (synCfv (synC2nd) B) (synCfv (synC2nd) C)))
      (synWrex r (synCvv) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (synWrex r (synCvv) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) C))))
      p0025 p0034
  have p0036 :=
    @gImbi2d (.classEq (.cv v) C)
      (.imp (synWa (synWa (.classMem B (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)))) (synWrex r (synCvv) (synWa
            (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) (.cv v))))))
      (.imp (synWa (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) C)
            (synCfv (synC2nd) B) (synCfv (synC2nd) C))) (synWrex r (synCvv) (synWa
            (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) C)))))
      (.classMem B (synCvv)) p0035
  have p0037 := @gId (.classEq (.cv u) B)
  have p0038 := @gEleq1d (.classEq (.cv u) B) (.cv u) B (synChwcn A) p0037
  have p0039 := @gBiid (.classMem (.cv v) (synChwcn A))
  have p0040 :=
    @gA1i (synWb (.classMem (.cv v) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classEq (.cv u) B) p0039
  have p0041 :=
    @gAnbi12d (.classEq (.cv u) B) (.classMem (.cv u) (synChwcn A))
      (.classMem B (synChwcn A)) (.classMem (.cv v) (synChwcn A))
      (.classMem (.cv v) (synChwcn A)) p0038 p0040
  have p0043 := @gFveq2d (.classEq (.cv u) B) (.cv u) B (synC1st) p0037
  have p0044 :=
    @gIsoeq2 (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))
      (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) B)
      (.cv f)
  have p0045 :=
    @gSyl (.classEq (.cv u) B)
      (.classEq (synCfv (synC1st) (.cv u)) (synCfv (synC1st) B))
      (synWb (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
        (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      p0043 p0044
  have p0047 := @gFveq2d (.classEq (.cv u) B) (.cv u) B (synC2nd) p0037
  have p0048 :=
    @gIsoeq4 (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))
      (synCfv (synC2nd) B) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v)) (.cv f)
  have p0049 :=
    @gSyl (.classEq (.cv u) B)
      (.classEq (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) B))
      (synWb (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
        (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v))))
      p0047 p0048
  have p0050 :=
    @gBitrd (.classEq (.cv u) B)
      (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)))
      p0045 p0049
  have p0051 :=
    @gAnbi12d (.classEq (.cv u) B)
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWa (.classMem B (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)))
      p0041 p0050
  have p0053 :=
    @gA1i
      (synWb (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f)))
        (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f))))
      (.classEq (.cv u) B) p0026
  have p0055 :=
    @gEqeq2d (.classEq (.cv u) B) (.cv u) B (synCop (.cv r) (synCdm (.cv f))) p0037
  have p0056 :=
    @gBiid
      (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCrn (.cv f))) (.cv v))
  have p0057 :=
    @gA1i
      (synWb (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
            (synCrn (.cv f))) (.cv v)) (.classEq
          (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
          (.cv v)))
      (.classEq (.cv u) B) p0056
  have p0058 :=
    @gAnbi12d (.classEq (.cv u) B) (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
      (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
      (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCrn (.cv f))) (.cv v))
      (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCrn (.cv f))) (.cv v))
      p0055 p0057
  have p0059 :=
    @gAnbi12d (.classEq (.cv u) B)
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
          (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
          (.cv v)))
      (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B) (.classEq
          (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
          (.cv v)))
      p0053 p0058
  have p0060 :=
    @gRexbidv (.classEq (.cv u) B)
      (synWa (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f)))
        (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            (.cv v))))
      (synWa (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f)))
        (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            (.cv v))))
      r (synCvv) dv_cache_0002 p0059
  have p0061 :=
    @gImbi12d (.classEq (.cv u) B)
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      (synWa (synWa (.classMem B (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v))))
      (synWrex r (synCvv) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (synWrex r (synCvv) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      p0051 p0060
  have p0062 :=
    @gHwnisorawgeni v u A f r dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0063 :=
    @gVtoclg
      (.imp (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))) (synWrex r (synCvv)
          (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) (.cv v))))))
      (.imp (synWa (synWa (.classMem B (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)))) (synWrex r (synCvv) (synWa
            (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) (.cv v))))))
      u B (synCvv) dv_cache_0011 dv_cache_0012 p0061 p0062
  have p0064 :=
    @gVtoclg
      (.imp (.classMem B (synCvv)) (.imp
          (synWa (synWa (.classMem B (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
              (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)))) (synWrex r (synCvv)
            (synWa (synWiso (.cv f) (.cv r)
                (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
                (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
                (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                    (synCrn (.cv f))) (.cv v)))))))
      (.imp (.classMem B (synCvv)) (.imp
          (synWa (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
            (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) C)
              (synCfv (synC2nd) B) (synCfv (synC2nd) C))) (synWrex r (synCvv) (synWa
              (synWiso (.cv f) (.cv r)
                (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
                (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
                (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                    (synCrn (.cv f))) C))))))
      v C (synCvv) dv_cache_0013 dv_cache_0014 p0036 p0063
  have p0065 :=
    @gSyl
      (synWa (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) C)
          (synCfv (synC2nd) B) (synCfv (synC2nd) C)))
      (.classMem C (synCvv))
      (.imp (.classMem B (synCvv)) (.imp
          (synWa (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
            (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) C)
              (synCfv (synC2nd) B) (synCfv (synC2nd) C))) (synWrex r (synCvv) (synWa
              (synWiso (.cv f) (.cv r)
                (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
                (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
                (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                    (synCrn (.cv f))) C))))))
      p0010 p0064
  have p0066 :=
    @gMpd
      (synWa (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) C)
          (synCfv (synC2nd) B) (synCfv (synC2nd) C)))
      (.classMem B (synCvv))
      (.imp (synWa (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) C)
            (synCfv (synC2nd) B) (synCfv (synC2nd) C))) (synWrex r (synCvv) (synWa
            (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) C)))))
      p0005 p0065
  have p0067 :=
    @gMpd
      (synWa (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) C)
          (synCfv (synC2nd) B) (synCfv (synC2nd) C)))
      (synWa (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) B) (synCfv (synC1st) C)
          (synCfv (synC2nd) B) (synCfv (synC2nd) C)))
      (synWrex r (synCvv) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) C))))
      p0000 p0066
  exact p0067

/-- Checked nominal proof certificate identified upstream as `g_wecutisogencodeinran`. -/
@[expose]
noncomputable def gWecutisogencodeinran (x : Var) (D : Class) (R : Class)
    (hyp_wecutisogencodeinran_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (.classMem (.cv x) D)
        (.classMem (synChnwcutcode R D (.cv x)) (synCrn (synChnwcutrel R D)))) :=
  by
  have p0000 := @gHnwcutrelfn D R hyp_wecutisogencodeinran_1
  have p0001 :=
    @gA1i (synWfn (synChnwcutrel R D) (synCpw1 D)) (.classMem (.cv x) D) p0000
  have p0002 := @gSnelpw1 (.cv x) D
  have p0003 :=
    @gBiimpri (.classMem (synCsn (.cv x)) (synCpw1 D)) (.classMem (.cv x) D) p0002
  have p0004 :=
    @gJca (.classMem (.cv x) D) (synWfn (synChnwcutrel R D) (synCpw1 D))
      (.classMem (synCsn (.cv x)) (synCpw1 D)) p0001 p0003
  have p0005 := @gFnfvelrn (synCpw1 D) (synCsn (.cv x)) (synChnwcutrel R D)
  have p0006 :=
    @gSyl (.classMem (.cv x) D)
      (synWa (synWfn (synChnwcutrel R D) (synCpw1 D))
        (.classMem (synCsn (.cv x)) (synCpw1 D)))
      (.classMem (synCfv (synChnwcutrel R D) (synCsn (.cv x)))
        (synCrn (synChnwcutrel R D)))
      p0004 p0005
  have p0007 := @gHnwcutrelvalcld (.cv x) D R hyp_wecutisogencodeinran_1
  have p0008 :=
    @gEleq1d (.classMem (.cv x) D) (synCfv (synChnwcutrel R D) (synCsn (.cv x)))
      (synChnwcutcode R D (.cv x)) (synCrn (synChnwcutrel R D)) p0007
  have p0009 :=
    @gMpbid (.classMem (.cv x) D)
      (.classMem (synCfv (synChnwcutrel R D) (synCsn (.cv x)))
        (synCrn (synChnwcutrel R D)))
      (.classMem (synChnwcutcode R D (.cv x)) (synCrn (synChnwcutrel R D))) p0006 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_wecutisogenrangedecode`. -/
@[expose]
noncomputable def gWecutisogenrangedecode (x : Var) (B : Class) (D : Class) (R : Class)
    (dv_B_x : x ∉ B.fv) (dv_D_x : x ∉ D.fv) (dv_R_x : x ∉ R.fv)
    (hyp_wecutisogenrangedecode_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (.classMem B (synCrn (synChnwcutrel R D)))
        (synWrex x D (.classEq B (synChnwcutcode R D (.cv x))))) :=
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
  have dv_cache_0001 : u ∉ ((synCpw1 D)).fv := by
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
  have dv_cache_0003 : u ∉ ((synChnwcutrel R D)).fv :=
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
      ((synWa (.classMem (.cv u) (synCpw1 D))
          (.classEq (synCfv (synChnwcutrel R D) (.cv u)) B))).fv :=
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
    u ∉ ((synWrex x D (.classEq B (synChnwcutcode R D (.cv x))))).fv :=
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
  have p0000 := @gHnwcutrelfn D R hyp_wecutisogenrangedecode_1
  have p0001 :=
    @gFvelrnb u (synCpw1 D) B (synChnwcutrel R D) dv_cache_0001 dv_cache_0002
      dv_cache_0003
  have p0002 := Nominal.mp p0000 p0001
  have p0003 :=
    @gBiimpi (.classMem B (synCrn (synChnwcutrel R D)))
      (synWrex u (synCpw1 D) (.classEq (synCfv (synChnwcutrel R D) (.cv u)) B)) p0002
  have p0004 :=
    @gSimpl (.classMem (.cv u) (synCpw1 D))
      (.classEq (synCfv (synChnwcutrel R D) (.cv u)) B)
  have p0005 := @gElpw1 x (.cv u) D dv_cache_0004 dv_cache_0005
  have p0006 :=
    @gBiimpi (.classMem (.cv u) (synCpw1 D))
      (synWrex x D (.classEq (.cv u) (synCsn (.cv x)))) p0005
  have p0007 :=
    @gSyl
      (synWa (.classMem (.cv u) (synCpw1 D))
        (.classEq (synCfv (synChnwcutrel R D) (.cv u)) B))
      (.classMem (.cv u) (synCpw1 D)) (synWrex x D (.classEq (.cv u) (synCsn (.cv x))))
      p0004 p0006
  have p0008 :=
    @gSimpl
      (synWa (synWa (.classMem (.cv u) (synCpw1 D))
          (.classEq (synCfv (synChnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D))
      (.classEq (.cv u) (synCsn (.cv x)))
  have p0009 :=
    @gSimpl
      (synWa (.classMem (.cv u) (synCpw1 D))
        (.classEq (synCfv (synChnwcutrel R D) (.cv u)) B))
      (.classMem (.cv x) D)
  have p0010 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv u) (synCpw1 D))
            (.classEq (synCfv (synChnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D))
        (.classEq (.cv u) (synCsn (.cv x))))
      (synWa (synWa (.classMem (.cv u) (synCpw1 D))
          (.classEq (synCfv (synChnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D))
      (synWa (.classMem (.cv u) (synCpw1 D))
        (.classEq (synCfv (synChnwcutrel R D) (.cv u)) B))
      p0008 p0009
  have p0011 :=
    @gSimpr (.classMem (.cv u) (synCpw1 D))
      (.classEq (synCfv (synChnwcutrel R D) (.cv u)) B)
  have p0012 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv u) (synCpw1 D))
            (.classEq (synCfv (synChnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D))
        (.classEq (.cv u) (synCsn (.cv x))))
      (synWa (.classMem (.cv u) (synCpw1 D))
        (.classEq (synCfv (synChnwcutrel R D) (.cv u)) B))
      (.classEq (synCfv (synChnwcutrel R D) (.cv u)) B) p0010 p0011
  have p0013 :=
    @gEqcomd
      (synWa (synWa (synWa (.classMem (.cv u) (synCpw1 D))
            (.classEq (synCfv (synChnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D))
        (.classEq (.cv u) (synCsn (.cv x))))
      (synCfv (synChnwcutrel R D) (.cv u)) B p0012
  have p0014 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv u) (synCpw1 D))
          (.classEq (synCfv (synChnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D))
      (.classEq (.cv u) (synCsn (.cv x)))
  have p0015 := @gId (.classEq (.cv u) (synCsn (.cv x)))
  have p0016 :=
    @gFveq2d (.classEq (.cv u) (synCsn (.cv x))) (.cv u) (synCsn (.cv x))
      (synChnwcutrel R D) p0015
  have p0017 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv u) (synCpw1 D))
            (.classEq (synCfv (synChnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D))
        (.classEq (.cv u) (synCsn (.cv x))))
      (.classEq (.cv u) (synCsn (.cv x)))
      (.classEq (synCfv (synChnwcutrel R D) (.cv u))
        (synCfv (synChnwcutrel R D) (synCsn (.cv x))))
      p0014 p0016
  have p0018 :=
    @gEqtrd
      (synWa (synWa (synWa (.classMem (.cv u) (synCpw1 D))
            (.classEq (synCfv (synChnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D))
        (.classEq (.cv u) (synCsn (.cv x))))
      B (synCfv (synChnwcutrel R D) (.cv u))
      (synCfv (synChnwcutrel R D) (synCsn (.cv x))) p0013 p0017
  have p0020 :=
    @gSimpr
      (synWa (.classMem (.cv u) (synCpw1 D))
        (.classEq (synCfv (synChnwcutrel R D) (.cv u)) B))
      (.classMem (.cv x) D)
  have p0021 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv u) (synCpw1 D))
            (.classEq (synCfv (synChnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D))
        (.classEq (.cv u) (synCsn (.cv x))))
      (synWa (synWa (.classMem (.cv u) (synCpw1 D))
          (.classEq (synCfv (synChnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D))
      (.classMem (.cv x) D) p0008 p0020
  have p0022 := @gHnwcutrelvalcld (.cv x) D R hyp_wecutisogenrangedecode_1
  have p0023 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv u) (synCpw1 D))
            (.classEq (synCfv (synChnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D))
        (.classEq (.cv u) (synCsn (.cv x))))
      (.classMem (.cv x) D)
      (.classEq (synCfv (synChnwcutrel R D) (synCsn (.cv x))) (synChnwcutcode R D (.cv x)))
      p0021 p0022
  have p0024 :=
    @gEqtrd
      (synWa (synWa (synWa (.classMem (.cv u) (synCpw1 D))
            (.classEq (synCfv (synChnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D))
        (.classEq (.cv u) (synCsn (.cv x))))
      B (synCfv (synChnwcutrel R D) (synCsn (.cv x))) (synChnwcutcode R D (.cv x))
      p0018 p0023
  have p0025 :=
    @gEx
      (synWa (synWa (.classMem (.cv u) (synCpw1 D))
          (.classEq (synCfv (synChnwcutrel R D) (.cv u)) B)) (.classMem (.cv x) D))
      (.classEq (.cv u) (synCsn (.cv x))) (.classEq B (synChnwcutcode R D (.cv x)))
      p0024
  have p0026 :=
    @gReximdva
      (synWa (.classMem (.cv u) (synCpw1 D))
        (.classEq (synCfv (synChnwcutrel R D) (.cv u)) B))
      (.classEq (.cv u) (synCsn (.cv x))) (.classEq B (synChnwcutcode R D (.cv x))) x D
      dv_cache_0006 p0025
  have p0027 :=
    @gMpd
      (synWa (.classMem (.cv u) (synCpw1 D))
        (.classEq (synCfv (synChnwcutrel R D) (.cv u)) B))
      (synWrex x D (.classEq (.cv u) (synCsn (.cv x))))
      (synWrex x D (.classEq B (synChnwcutcode R D (.cv x)))) p0007 p0026
  have p0028 :=
    @gRexlimiva (.classEq (synCfv (synChnwcutrel R D) (.cv u)) B)
      (synWrex x D (.classEq B (synChnwcutcode R D (.cv x)))) u (synCpw1 D)
      dv_cache_0007 p0027
  have p0029 :=
    @gSyl (.classMem B (synCrn (synChnwcutrel R D)))
      (synWrex u (synCpw1 D) (.classEq (synCfv (synChnwcutrel R D) (.cv u)) B))
      (synWrex x D (.classEq B (synChnwcutcode R D (.cv x)))) p0003 p0028
  exact p0029

/-- Checked nominal proof certificate identified upstream as `g_wecutisogencodeambient`. -/
@[expose]
noncomputable def gWecutisogencodeambient (x : Var) (D : Class) (R : Class)
    (hyp_wecutisogencodeambient_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (.classMem (.cv x) D)
        (.classMem (synChnwcutcode R D (.cv x)) (synChwcn (synCvv)))) :=
  by
  have p0000 := @gHnwcutcodecnndv x D R hyp_wecutisogencodeambient_1
  have p0001 := @gSsv D
  have p0002 := @gHwcnssbase (synCvv) D p0001
  have p0003 :=
    @gSseli (synChwcn D) (synChwcn (synCvv)) (synChnwcutcode R D (.cv x)) p0002
  have p0004 :=
    @gSyl (.classMem (.cv x) D) (.classMem (synChnwcutcode R D (.cv x)) (synChwcn D))
      (.classMem (synChnwcutcode R D (.cv x)) (synChwcn (synCvv))) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_wecutisogennormbij`. -/
@[expose]
noncomputable def gWecutisogennormbij (f : Var) (r : Var) :
    Nominal.NPrf
      (.imp (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f))) (.classMem (.cv f) (synChwbij))) :=
  by
  have p0000 := @gHwtrnisob f r
  have p0001 :=
    @gBiimpri (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      p0000
  have p0002 := @gHwbijf1o f
  have p0003 :=
    @gBiimpri (.classMem (.cv f) (synChwbij))
      (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f))) p0002
  have p0004 :=
    @gSyl
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (.classMem (.cv f) (synChwbij)) p0001 p0003
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

/-- Checked nominal proof certificate identified upstream as `g_wecutisogenrawmem`. -/
@[expose]
noncomputable def gWecutisogenrawmem (B : Class) (C : Class) (D : Class) (R : Class)
    (S : Class) (f : Var) (E : Class) (r : Var) :
    Nominal.NPrf
      (.imp (synWa (synWa (.classMem B (synCrn (synChnwcutrel R D)))
            (.classMem C (synCrn (synChnwcutrel S E)))) (synWa (.classMem (.cv r) (synCvv))
            (synWa (synWiso (.cv f) (.cv r)
                (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
                (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
                (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                    (synCrn (.cv f))) C))))) (.classMem (.cv f) (synCwecutisogen R D S E))) :=
  by
  have p0000 :=
    @gSimpr
      (synWa (.classMem B (synCrn (synChnwcutrel R D)))
        (.classMem C (synCrn (synChnwcutrel S E))))
      (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) C))))
  have p0001 :=
    @gSimpr (.classMem (.cv r) (synCvv))
      (synWa (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f)))
        (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            C)))
  have p0002 :=
    @gSyl
      (synWa (synWa (.classMem B (synCrn (synChnwcutrel R D)))
          (.classMem C (synCrn (synChnwcutrel S E)))) (synWa (.classMem (.cv r) (synCvv))
          (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) C)))))
      (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) C))))
      (synWa (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f)))
        (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            C)))
      p0000 p0001
  have p0003 :=
    @gSimpl
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B) (.classEq
          (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
          C))
  have p0004 :=
    @gSyl
      (synWa (synWa (.classMem B (synCrn (synChnwcutrel R D)))
          (.classMem C (synCrn (synChnwcutrel S E)))) (synWa (.classMem (.cv r) (synCvv))
          (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) C)))))
      (synWa (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f)))
        (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            C)))
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      p0002 p0003
  have p0005 := @gWecutisogennormbij f r
  have p0006 :=
    @gSyl
      (synWa (synWa (.classMem B (synCrn (synChnwcutrel R D)))
          (.classMem C (synCrn (synChnwcutrel S E)))) (synWa (.classMem (.cv r) (synCvv))
          (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) C)))))
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      (.classMem (.cv f) (synChwbij)) p0004 p0005
  have p0008 :=
    @gSimpl (.classMem (.cv r) (synCvv))
      (synWa (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f)))
        (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            C)))
  have p0009 :=
    @gSyl
      (synWa (synWa (.classMem B (synCrn (synChnwcutrel R D)))
          (.classMem C (synCrn (synChnwcutrel S E)))) (synWa (.classMem (.cv r) (synCvv))
          (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) C)))))
      (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) C))))
      (.classMem (.cv r) (synCvv)) p0000 p0008
  have p0010 :=
    @gJca
      (synWa (synWa (.classMem B (synCrn (synChnwcutrel R D)))
          (.classMem C (synCrn (synChnwcutrel S E)))) (synWa (.classMem (.cv r) (synCvv))
          (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) C)))))
      (.classMem (.cv f) (synChwbij)) (.classMem (.cv r) (synCvv)) p0006 p0009
  have p0011 := @gOpelxp (.cv f) (.cv r) (synChwbij) (synCvv)
  have p0012 :=
    @gBiimpri (.classMem (synCop (.cv f) (.cv r)) (synCxp (synChwbij) (synCvv)))
      (synWa (.classMem (.cv f) (synChwbij)) (.classMem (.cv r) (synCvv))) p0011
  have p0013 :=
    @gSyl
      (synWa (synWa (.classMem B (synCrn (synChnwcutrel R D)))
          (.classMem C (synCrn (synChnwcutrel S E)))) (synWa (.classMem (.cv r) (synCvv))
          (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) C)))))
      (synWa (.classMem (.cv f) (synChwbij)) (.classMem (.cv r) (synCvv)))
      (.classMem (synCop (.cv f) (.cv r)) (synCxp (synChwbij) (synCvv))) p0010 p0012
  have p0014 :=
    @gSimpl
      (synWa (.classMem B (synCrn (synChnwcutrel R D)))
        (.classMem C (synCrn (synChnwcutrel S E))))
      (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) C))))
  have p0015 :=
    @gSimpl (.classMem B (synCrn (synChnwcutrel R D)))
      (.classMem C (synCrn (synChnwcutrel S E)))
  have p0016 :=
    @gSyl
      (synWa (synWa (.classMem B (synCrn (synChnwcutrel R D)))
          (.classMem C (synCrn (synChnwcutrel S E)))) (synWa (.classMem (.cv r) (synCvv))
          (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) C)))))
      (synWa (.classMem B (synCrn (synChnwcutrel R D)))
        (.classMem C (synCrn (synChnwcutrel S E))))
      (.classMem B (synCrn (synChnwcutrel R D))) p0014 p0015
  have p0018 :=
    @gSimpr (.classMem B (synCrn (synChnwcutrel R D)))
      (.classMem C (synCrn (synChnwcutrel S E)))
  have p0019 :=
    @gSyl
      (synWa (synWa (.classMem B (synCrn (synChnwcutrel R D)))
          (.classMem C (synCrn (synChnwcutrel S E)))) (synWa (.classMem (.cv r) (synCvv))
          (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) C)))))
      (synWa (.classMem B (synCrn (synChnwcutrel R D)))
        (.classMem C (synCrn (synChnwcutrel S E))))
      (.classMem C (synCrn (synChnwcutrel S E))) p0014 p0018
  have p0020 :=
    @gJca
      (synWa (synWa (.classMem B (synCrn (synChnwcutrel R D)))
          (.classMem C (synCrn (synChnwcutrel S E)))) (synWa (.classMem (.cv r) (synCvv))
          (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) C)))))
      (.classMem B (synCrn (synChnwcutrel R D)))
      (.classMem C (synCrn (synChnwcutrel S E))) p0016 p0019
  have p0021 :=
    @gOpelxp B C (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))
  have p0022 :=
    @gBiimpri
      (.classMem (synCop B C)
        (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))
      (synWa (.classMem B (synCrn (synChnwcutrel R D)))
        (.classMem C (synCrn (synChnwcutrel S E))))
      p0021
  have p0023 :=
    @gSyl
      (synWa (synWa (.classMem B (synCrn (synChnwcutrel R D)))
          (.classMem C (synCrn (synChnwcutrel S E)))) (synWa (.classMem (.cv r) (synCvv))
          (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) C)))))
      (synWa (.classMem B (synCrn (synChnwcutrel R D)))
        (.classMem C (synCrn (synChnwcutrel S E))))
      (.classMem (synCop B C)
        (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))
      p0020 p0022
  have p0024 := @gVex r
  have p0025 := @gHwgenval (.cv r) f p0024
  have p0026 :=
    @gA1i
      (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
        (synCop (synCop (.cv r) (synCdm (.cv f)))
          (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))))
      (synWa (synWa (.classMem B (synCrn (synChnwcutrel R D)))
          (.classMem C (synCrn (synChnwcutrel S E)))) (synWa (.classMem (.cv r) (synCvv))
          (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) C)))))
      p0025
  have p0030 :=
    @gSimpr
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B) (.classEq
          (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
          C))
  have p0031 :=
    @gSyl
      (synWa (synWa (.classMem B (synCrn (synChnwcutrel R D)))
          (.classMem C (synCrn (synChnwcutrel S E)))) (synWa (.classMem (.cv r) (synCvv))
          (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) C)))))
      (synWa (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f)))
        (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            C)))
      (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B) (.classEq
          (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
          C))
      p0002 p0030
  have p0032 :=
    @gSimpl (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
      (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCrn (.cv f))) C)
  have p0033 :=
    @gSyl
      (synWa (synWa (.classMem B (synCrn (synChnwcutrel R D)))
          (.classMem C (synCrn (synChnwcutrel S E)))) (synWa (.classMem (.cv r) (synCvv))
          (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) C)))))
      (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B) (.classEq
          (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
          C))
      (.classEq (synCop (.cv r) (synCdm (.cv f))) B) p0031 p0032
  have p0039 :=
    @gSimpr (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
      (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCrn (.cv f))) C)
  have p0040 :=
    @gSyl
      (synWa (synWa (.classMem B (synCrn (synChnwcutrel R D)))
          (.classMem C (synCrn (synChnwcutrel S E)))) (synWa (.classMem (.cv r) (synCvv))
          (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) C)))))
      (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B) (.classEq
          (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
          C))
      (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCrn (.cv f))) C)
      p0031 p0039
  have p0041 :=
    @gOpeq12d
      (synWa (synWa (.classMem B (synCrn (synChnwcutrel R D)))
          (.classMem C (synCrn (synChnwcutrel S E)))) (synWa (.classMem (.cv r) (synCvv))
          (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) C)))))
      (synCop (.cv r) (synCdm (.cv f))) B
      (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
      C p0033 p0040
  have p0042 :=
    @gEqtrd
      (synWa (synWa (.classMem B (synCrn (synChnwcutrel R D)))
          (.classMem C (synCrn (synChnwcutrel S E)))) (synWa (.classMem (.cv r) (synCvv))
          (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) C)))))
      (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
      (synCop (synCop (.cv r) (synCdm (.cv f)))
        (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f))))
      (synCop B C) p0026 p0041
  have p0043 :=
    @gEleq1d
      (synWa (synWa (.classMem B (synCrn (synChnwcutrel R D)))
          (.classMem C (synCrn (synChnwcutrel S E)))) (synWa (.classMem (.cv r) (synCvv))
          (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) C)))))
      (synCfv (synChwgen) (synCop (.cv f) (.cv r))) (synCop B C)
      (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))) p0042
  have p0044 :=
    @gMpbird
      (synWa (synWa (.classMem B (synCrn (synChnwcutrel R D)))
          (.classMem C (synCrn (synChnwcutrel S E)))) (synWa (.classMem (.cv r) (synCvv))
          (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) C)))))
      (.classMem (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
        (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))
      (.classMem (synCop B C)
        (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))
      p0023 p0043
  have p0045 := @gHwgenfn
  have p0046 := @gFnfun (synCvv) (synChwgen)
  have p0047 := Nominal.mp p0045 p0046
  have p0048 := @gVex f
  have p0050 := @gOpex (.cv f) (.cv r) p0048 p0024
  have p0052 := @gFndm (synCvv) (synChwgen)
  have p0053 := Nominal.mp p0045 p0052
  have p0054 := @gEleq2i (synCdm (synChwgen)) (synCvv) (synCop (.cv f) (.cv r)) p0053
  have p0055 :=
    @gMpbir (.classMem (synCop (.cv f) (.cv r)) (synCdm (synChwgen)))
      (.classMem (synCop (.cv f) (.cv r)) (synCvv)) p0050 p0054
  have p0056 :=
    @gPm32i (synWfun (synChwgen))
      (.classMem (synCop (.cv f) (.cv r)) (synCdm (synChwgen))) p0047 p0055
  have p0057 :=
    @gFvimacnv (synCop (.cv f) (.cv r))
      (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))) (synChwgen)
  have p0058 := Nominal.mp p0056 p0057
  have p0059 :=
    @gA1i
      (synWb (.classMem (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
          (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))
        (.classMem (synCop (.cv f) (.cv r)) (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))))
      (synWa (synWa (.classMem B (synCrn (synChnwcutrel R D)))
          (.classMem C (synCrn (synChnwcutrel S E)))) (synWa (.classMem (.cv r) (synCvv))
          (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) C)))))
      p0058
  have p0060 :=
    @gMpbid
      (synWa (synWa (.classMem B (synCrn (synChnwcutrel R D)))
          (.classMem C (synCrn (synChnwcutrel S E)))) (synWa (.classMem (.cv r) (synCvv))
          (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) C)))))
      (.classMem (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
        (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))
      (.classMem (synCop (.cv f) (.cv r)) (synCima (synCcnv (synChwgen))
          (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E)))))
      p0044 p0059
  have p0061 :=
    @gJca
      (synWa (synWa (.classMem B (synCrn (synChnwcutrel R D)))
          (.classMem C (synCrn (synChnwcutrel S E)))) (synWa (.classMem (.cv r) (synCvv))
          (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) C)))))
      (.classMem (synCop (.cv f) (.cv r)) (synCxp (synChwbij) (synCvv)))
      (.classMem (synCop (.cv f) (.cv r)) (synCima (synCcnv (synChwgen))
          (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E)))))
      p0013 p0060
  have p0062 :=
    @gElin (synCop (.cv f) (.cv r)) (synCxp (synChwbij) (synCvv))
      (synCima (synCcnv (synChwgen))
        (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))
  have p0063 :=
    @gBiimpri
      (.classMem (synCop (.cv f) (.cv r)) (synCin (synCxp (synChwbij) (synCvv))
          (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))))
      (synWa (.classMem (synCop (.cv f) (.cv r)) (synCxp (synChwbij) (synCvv)))
        (.classMem (synCop (.cv f) (.cv r)) (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))))
      p0062
  have p0064 :=
    @gSyl
      (synWa (synWa (.classMem B (synCrn (synChnwcutrel R D)))
          (.classMem C (synCrn (synChnwcutrel S E)))) (synWa (.classMem (.cv r) (synCvv))
          (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) C)))))
      (synWa (.classMem (synCop (.cv f) (.cv r)) (synCxp (synChwbij) (synCvv)))
        (.classMem (synCop (.cv f) (.cv r)) (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))))
      (.classMem (synCop (.cv f) (.cv r)) (synCin (synCxp (synChwbij) (synCvv))
          (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))))
      p0061 p0063
  have p0065 :=
    (Nominal.biimpRefl (synWbr (.cv f) (synCin (synCxp (synChwbij) (synCvv))
          (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))) (.cv r)))
  have p0066 :=
    @gBiimpri
      (synWbr (.cv f) (synCin (synCxp (synChwbij) (synCvv))
          (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))) (.cv r))
      (.classMem (synCop (.cv f) (.cv r)) (synCin (synCxp (synChwbij) (synCvv))
          (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))))
      p0065
  have p0067 :=
    @gSyl
      (synWa (synWa (.classMem B (synCrn (synChnwcutrel R D)))
          (.classMem C (synCrn (synChnwcutrel S E)))) (synWa (.classMem (.cv r) (synCvv))
          (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) C)))))
      (.classMem (synCop (.cv f) (.cv r)) (synCin (synCxp (synChwbij) (synCvv))
          (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))))
      (synWbr (.cv f) (synCin (synCxp (synChwbij) (synCvv))
          (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))) (.cv r))
      p0064 p0066
  have p0068 :=
    @gBreldm (.cv f) (.cv r)
      (synCin (synCxp (synChwbij) (synCvv)) (synCima (synCcnv (synChwgen))
          (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E)))))
  have p0069 :=
    @gSyl
      (synWa (synWa (.classMem B (synCrn (synChnwcutrel R D)))
          (.classMem C (synCrn (synChnwcutrel S E)))) (synWa (.classMem (.cv r) (synCvv))
          (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) C)))))
      (synWbr (.cv f) (synCin (synCxp (synChwbij) (synCvv))
          (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))) (.cv r))
      (.classMem (.cv f) (synCdm (synCin (synCxp (synChwbij) (synCvv))
            (synCima (synCcnv (synChwgen))
              (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E)))))))
      p0067 p0068
  have p0070 := (Nominal.classEqRefl (synCwecutisogen R D S E))
  have p0071 :=
    @gEleq2i (synCwecutisogen R D S E)
      (synCdm (synCin (synCxp (synChwbij) (synCvv)) (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))))
      (.cv f) p0070
  have p0072 :=
    @gA1i
      (synWb (.classMem (.cv f) (synCwecutisogen R D S E)) (.classMem (.cv f) (synCdm
            (synCin (synCxp (synChwbij) (synCvv)) (synCima (synCcnv (synChwgen))
                (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))))))
      (synWa (synWa (.classMem B (synCrn (synChnwcutrel R D)))
          (.classMem C (synCrn (synChnwcutrel S E)))) (synWa (.classMem (.cv r) (synCvv))
          (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) C)))))
      p0071
  have p0073 :=
    @gMpbird
      (synWa (synWa (.classMem B (synCrn (synChnwcutrel R D)))
          (.classMem C (synCrn (synChnwcutrel S E)))) (synWa (.classMem (.cv r) (synCvv))
          (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) B)
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) C)))))
      (.classMem (.cv f) (synCwecutisogen R D S E))
      (.classMem (.cv f) (synCdm (synCin (synCxp (synChwbij) (synCvv))
            (synCima (synCcnv (synChwgen))
              (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E)))))))
      p0069 p0072
  exact p0073

/-- Checked nominal proof certificate identified upstream as `g_wecutisogenrawout`. -/
@[expose]
noncomputable def gWecutisogenrawout (D : Class) (R : Class) (S : Class) (f : Var)
    (E : Class) (r : Var) (dv_D_r : r ∉ D.fv) (dv_E_r : r ∉ E.fv) (dv_R_r : r ∉ R.fv)
    (dv_S_r : r ∉ S.fv) (dv_f_r : f ≠ r) :
    Nominal.NPrf
      (.imp (.classMem (.cv f) (synCwecutisogen R D S E)) (synWrex r (synCvv) (synWa
            (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classMem (synCop (.cv r) (synCdm (.cv f)))
                (synCrn (synChnwcutrel R D))) (.classMem
                (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))) :=
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
      ((synCin (synCxp (synChwbij) (synCvv)) (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E)))))).fv :=
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
  have p0000 := (Nominal.classEqRefl (synCwecutisogen R D S E))
  have p0001 :=
    @gEleq2i (synCwecutisogen R D S E)
      (synCdm (synCin (synCxp (synChwbij) (synCvv)) (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))))
      (.cv f) p0000
  have p0002 :=
    @gBiimpi (.classMem (.cv f) (synCwecutisogen R D S E))
      (.classMem (.cv f) (synCdm (synCin (synCxp (synChwbij) (synCvv))
            (synCima (synCcnv (synChwgen))
              (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E)))))))
      p0001
  have p0003 :=
    @gEldm r (.cv f)
      (synCin (synCxp (synChwbij) (synCvv)) (synCima (synCcnv (synChwgen))
          (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E)))))
      dv_cache_0001 dv_cache_0002
  have p0004 :=
    @gBiimpi
      (.classMem (.cv f) (synCdm (synCin (synCxp (synChwbij) (synCvv))
            (synCima (synCcnv (synChwgen))
              (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E)))))))
      (synWex r (synWbr (.cv f) (synCin (synCxp (synChwbij) (synCvv))
            (synCima (synCcnv (synChwgen))
              (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E)))))
          (.cv r)))
      p0003
  have p0005 :=
    @gSyl (.classMem (.cv f) (synCwecutisogen R D S E))
      (.classMem (.cv f) (synCdm (synCin (synCxp (synChwbij) (synCvv))
            (synCima (synCcnv (synChwgen))
              (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E)))))))
      (synWex r (synWbr (.cv f) (synCin (synCxp (synChwbij) (synCvv))
            (synCima (synCcnv (synChwgen))
              (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E)))))
          (.cv r)))
      p0002 p0004
  have p0006 :=
    (Nominal.biimpRefl (synWbr (.cv f) (synCin (synCxp (synChwbij) (synCvv))
          (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))) (.cv r)))
  have p0007 :=
    @gBiimpi
      (synWbr (.cv f) (synCin (synCxp (synChwbij) (synCvv))
          (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))) (.cv r))
      (.classMem (synCop (.cv f) (.cv r)) (synCin (synCxp (synChwbij) (synCvv))
          (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))))
      p0006
  have p0008 :=
    @gElin (synCop (.cv f) (.cv r)) (synCxp (synChwbij) (synCvv))
      (synCima (synCcnv (synChwgen))
        (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))
  have p0009 :=
    @gBiimpi
      (.classMem (synCop (.cv f) (.cv r)) (synCin (synCxp (synChwbij) (synCvv))
          (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))))
      (synWa (.classMem (synCop (.cv f) (.cv r)) (synCxp (synChwbij) (synCvv)))
        (.classMem (synCop (.cv f) (.cv r)) (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))))
      p0008
  have p0010 :=
    @gSyl
      (synWbr (.cv f) (synCin (synCxp (synChwbij) (synCvv))
          (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))) (.cv r))
      (.classMem (synCop (.cv f) (.cv r)) (synCin (synCxp (synChwbij) (synCvv))
          (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))))
      (synWa (.classMem (synCop (.cv f) (.cv r)) (synCxp (synChwbij) (synCvv)))
        (.classMem (synCop (.cv f) (.cv r)) (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))))
      p0007 p0009
  have p0011 :=
    @gSimpl (.classMem (synCop (.cv f) (.cv r)) (synCxp (synChwbij) (synCvv)))
      (.classMem (synCop (.cv f) (.cv r)) (synCima (synCcnv (synChwgen))
          (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E)))))
  have p0012 :=
    @gSyl
      (synWbr (.cv f) (synCin (synCxp (synChwbij) (synCvv))
          (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))) (.cv r))
      (synWa (.classMem (synCop (.cv f) (.cv r)) (synCxp (synChwbij) (synCvv)))
        (.classMem (synCop (.cv f) (.cv r)) (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))))
      (.classMem (synCop (.cv f) (.cv r)) (synCxp (synChwbij) (synCvv))) p0010 p0011
  have p0013 := @gOpelxp (.cv f) (.cv r) (synChwbij) (synCvv)
  have p0014 :=
    @gBiimpi (.classMem (synCop (.cv f) (.cv r)) (synCxp (synChwbij) (synCvv)))
      (synWa (.classMem (.cv f) (synChwbij)) (.classMem (.cv r) (synCvv))) p0013
  have p0015 :=
    @gSyl
      (synWbr (.cv f) (synCin (synCxp (synChwbij) (synCvv))
          (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))) (.cv r))
      (.classMem (synCop (.cv f) (.cv r)) (synCxp (synChwbij) (synCvv)))
      (synWa (.classMem (.cv f) (synChwbij)) (.classMem (.cv r) (synCvv))) p0012 p0014
  have p0016 := @gSimpr (.classMem (.cv f) (synChwbij)) (.classMem (.cv r) (synCvv))
  have p0017 :=
    @gSyl
      (synWbr (.cv f) (synCin (synCxp (synChwbij) (synCvv))
          (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))) (.cv r))
      (synWa (.classMem (.cv f) (synChwbij)) (.classMem (.cv r) (synCvv)))
      (.classMem (.cv r) (synCvv)) p0015 p0016
  have p0028 := @gSimpl (.classMem (.cv f) (synChwbij)) (.classMem (.cv r) (synCvv))
  have p0029 :=
    @gSyl
      (synWbr (.cv f) (synCin (synCxp (synChwbij) (synCvv))
          (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))) (.cv r))
      (synWa (.classMem (.cv f) (synChwbij)) (.classMem (.cv r) (synCvv)))
      (.classMem (.cv f) (synChwbij)) p0015 p0028
  have p0030 := @gHwbijf1o f
  have p0031 :=
    @gBiimpi (.classMem (.cv f) (synChwbij))
      (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f))) p0030
  have p0032 := @gHwtrnisob f r
  have p0033 :=
    @gBiimpi (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      p0032
  have p0034 :=
    @gSyl (.classMem (.cv f) (synChwbij))
      (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      p0031 p0033
  have p0035 :=
    @gSyl
      (synWbr (.cv f) (synCin (synCxp (synChwbij) (synCvv))
          (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))) (.cv r))
      (.classMem (.cv f) (synChwbij))
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      p0029 p0034
  have p0041 :=
    @gSimpr (.classMem (synCop (.cv f) (.cv r)) (synCxp (synChwbij) (synCvv)))
      (.classMem (synCop (.cv f) (.cv r)) (synCima (synCcnv (synChwgen))
          (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E)))))
  have p0042 :=
    @gSyl
      (synWbr (.cv f) (synCin (synCxp (synChwbij) (synCvv))
          (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))) (.cv r))
      (synWa (.classMem (synCop (.cv f) (.cv r)) (synCxp (synChwbij) (synCvv)))
        (.classMem (synCop (.cv f) (.cv r)) (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))))
      (.classMem (synCop (.cv f) (.cv r)) (synCima (synCcnv (synChwgen))
          (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E)))))
      p0010 p0041
  have p0043 := @gHwgenfn
  have p0044 := @gFnfun (synCvv) (synChwgen)
  have p0045 := Nominal.mp p0043 p0044
  have p0046 := @gVex f
  have p0047 := @gVex r
  have p0048 := @gOpex (.cv f) (.cv r) p0046 p0047
  have p0050 := @gFndm (synCvv) (synChwgen)
  have p0051 := Nominal.mp p0043 p0050
  have p0052 := @gEleq2i (synCdm (synChwgen)) (synCvv) (synCop (.cv f) (.cv r)) p0051
  have p0053 :=
    @gMpbir (.classMem (synCop (.cv f) (.cv r)) (synCdm (synChwgen)))
      (.classMem (synCop (.cv f) (.cv r)) (synCvv)) p0048 p0052
  have p0054 :=
    @gPm32i (synWfun (synChwgen))
      (.classMem (synCop (.cv f) (.cv r)) (synCdm (synChwgen))) p0045 p0053
  have p0055 :=
    @gFvimacnv (synCop (.cv f) (.cv r))
      (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))) (synChwgen)
  have p0056 := Nominal.mp p0054 p0055
  have p0057 :=
    @gBiimpri
      (.classMem (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
        (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))
      (.classMem (synCop (.cv f) (.cv r)) (synCima (synCcnv (synChwgen))
          (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E)))))
      p0056
  have p0058 :=
    @gSyl
      (synWbr (.cv f) (synCin (synCxp (synChwbij) (synCvv))
          (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))) (.cv r))
      (.classMem (synCop (.cv f) (.cv r)) (synCima (synCcnv (synChwgen))
          (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E)))))
      (.classMem (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
        (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))
      p0042 p0057
  have p0060 := @gHwgenval (.cv r) f p0047
  have p0061 :=
    @gA1i
      (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
        (synCop (synCop (.cv r) (synCdm (.cv f)))
          (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))))
      (synWbr (.cv f) (synCin (synCxp (synChwbij) (synCvv))
          (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))) (.cv r))
      p0060
  have p0062 :=
    @gEleq1d
      (synWbr (.cv f) (synCin (synCxp (synChwbij) (synCvv))
          (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))) (.cv r))
      (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
      (synCop (synCop (.cv r) (synCdm (.cv f)))
        (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f))))
      (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))) p0061
  have p0063 :=
    @gMpbid
      (synWbr (.cv f) (synCin (synCxp (synChwbij) (synCvv))
          (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))) (.cv r))
      (.classMem (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
        (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))
      (.classMem (synCop (synCop (.cv r) (synCdm (.cv f)))
          (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f))))
        (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))
      p0058 p0062
  have p0064 :=
    @gOpelxp (synCop (.cv r) (synCdm (.cv f)))
      (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
      (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))
  have p0065 :=
    @gBiimpi
      (.classMem (synCop (synCop (.cv r) (synCdm (.cv f)))
          (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f))))
        (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))
      (synWa (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
        (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
            (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))
      p0064
  have p0066 :=
    @gSyl
      (synWbr (.cv f) (synCin (synCxp (synChwbij) (synCvv))
          (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))) (.cv r))
      (.classMem (synCop (synCop (.cv r) (synCdm (.cv f)))
          (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f))))
        (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))
      (synWa (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
        (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
            (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))
      p0063 p0065
  have p0067 :=
    @gJca
      (synWbr (.cv f) (synCin (synCxp (synChwbij) (synCvv))
          (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))) (.cv r))
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      (synWa (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
        (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
            (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))
      p0035 p0066
  have p0068 :=
    @gJca
      (synWbr (.cv f) (synCin (synCxp (synChwbij) (synCvv))
          (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))) (.cv r))
      (.classMem (.cv r) (synCvv))
      (synWa (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f))) (synWa
          (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
          (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
              (synCrn (.cv f))) (synCrn (synChnwcutrel S E)))))
      p0017 p0067
  have p0069 :=
    @gEximi
      (synWbr (.cv f) (synCin (synCxp (synChwbij) (synCvv))
          (synCima (synCcnv (synChwgen))
            (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))) (.cv r))
      (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
            (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
      r p0068
  have p0070 :=
    (Nominal.biimpRefl (synWrex r (synCvv) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
            (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synCrn (synChnwcutrel S E)))))))
  have p0071 :=
    @gBiimpri
      (synWrex r (synCvv) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
            (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
      (synWex r (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classMem (synCop (.cv r) (synCdm (.cv f)))
                (synCrn (synChnwcutrel R D))) (.classMem
                (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) (synCrn (synChnwcutrel S E)))))))
      p0070
  have p0072 :=
    @gSyl
      (synWex r (synWbr (.cv f) (synCin (synCxp (synChwbij) (synCvv))
            (synCima (synCcnv (synChwgen))
              (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E)))))
          (.cv r)))
      (synWex r (synWa (.classMem (.cv r) (synCvv)) (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classMem (synCop (.cv r) (synCdm (.cv f)))
                (synCrn (synChnwcutrel R D))) (.classMem
                (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) (synCrn (synChnwcutrel S E)))))))
      (synWrex r (synCvv) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
            (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
      p0069 p0071
  have p0073 :=
    @gSyl (.classMem (.cv f) (synCwecutisogen R D S E))
      (synWex r (synWbr (.cv f) (synCin (synCxp (synChwbij) (synCvv))
            (synCima (synCcnv (synChwgen))
              (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E)))))
          (.cv r)))
      (synWrex r (synCvv) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classMem (synCop (.cv r) (synCdm (.cv f))) (synCrn (synChnwcutrel R D)))
            (.classMem (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synCrn (synChnwcutrel S E))))))
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

/-- Checked nominal proof certificate identified upstream as `g_wecutisogenfixedrev`. -/
@[expose]
noncomputable def gWecutisogenfixedrev (x : Var) (y : Var) (D : Class) (R : Class)
    (S : Class) (f : Var) (E : Class) (r : Var) (_dv_D_f : f ∉ D.fv) (_dv_D_r : r ∉ D.fv)
    (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv) (_dv_E_f : f ∉ E.fv) (_dv_E_r : r ∉ E.fv)
    (dv_E_x : x ∉ E.fv) (dv_E_y : y ∉ E.fv) (_dv_R_f : f ∉ R.fv) (_dv_R_r : r ∉ R.fv)
    (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (_dv_S_f : f ∉ S.fv) (_dv_S_r : r ∉ S.fv)
    (dv_S_x : x ∉ S.fv) (dv_S_y : y ∉ S.fv) (_dv_f_r : f ≠ r) (dv_f_x : f ≠ x)
    (dv_f_y : f ≠ y) (_dv_r_x : r ≠ x) (_dv_r_y : r ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWa
            (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa
              (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
        (.classMem (.cv f) (synCwecutiso R D S E))) :=
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
    @gSimpl (synWa (.classMem (.cv x) D) (.classMem (.cv y) E))
      (synWa (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f))) (synWa
          (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x))) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            (synChnwcutcode S E (.cv y)))))
  have p0001 := @gSimpl (.classMem (.cv x) D) (.classMem (.cv y) E)
  have p0002 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWa
          (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
      (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (.classMem (.cv x) D) p0000
      p0001
  have p0004 := @gSimpr (.classMem (.cv x) D) (.classMem (.cv y) E)
  have p0005 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWa
          (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
      (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (.classMem (.cv y) E) p0000
      p0004
  have p0006 :=
    @gSimpr (synWa (.classMem (.cv x) D) (.classMem (.cv y) E))
      (synWa (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f))) (synWa
          (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x))) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            (synChnwcutcode S E (.cv y)))))
  have p0007 :=
    @gSimpl
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
        (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
            (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))
  have p0008 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWa
          (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
      (synWa (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f))) (synWa
          (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x))) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            (synChnwcutcode S E (.cv y)))))
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      p0006 p0007
  have p0010 :=
    @gSimpr
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
        (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
            (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))
  have p0011 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWa
          (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
      (synWa (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f))) (synWa
          (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x))) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            (synChnwcutcode S E (.cv y)))))
      (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
        (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
            (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))
      p0006 p0010
  have p0012 :=
    @gSimpl (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
      (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCrn (.cv f))) (synChnwcutcode S E (.cv y)))
  have p0013 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWa
          (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
      (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
        (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
            (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))
      (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x))) p0011
      p0012
  have p0014 := (Nominal.classEqRefl (synChnwcutcode R D (.cv x)))
  have p0015 :=
    @gA1i
      (.classEq (synChnwcutcode R D (.cv x)) (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWa
          (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
      p0014
  have p0016 :=
    @gEqtrd
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWa
          (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
      (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x))
      (synCop (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0013 p0015
  have p0017 :=
    @gOpth (.cv r) (synCdm (.cv f))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
  have p0018 :=
    @gSylib
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWa
          (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
      (.classEq (synCop (.cv r) (synCdm (.cv f))) (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWa (.classEq (.cv r) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
        (.classEq (synCdm (.cv f))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      p0016 p0017
  have p0019 :=
    @gSimpl
      (.classEq (.cv r) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (.classEq (synCdm (.cv f))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  have p0020 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWa
          (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
      (synWa (.classEq (.cv r) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
        (.classEq (synCdm (.cv f))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classEq (.cv r) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      p0018 p0019
  have p0021 :=
    @gIsoeq2 (synCdm (.cv f)) (synCrn (.cv f)) (.cv r)
      (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.cv f)
  have p0022 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWa
          (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
      (.classEq (.cv r) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (synWb (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f))) (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
          (synCrn (.cv f))))
      p0020 p0021
  have p0026 :=
    @gSimpr (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
      (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCrn (.cv f))) (synChnwcutcode S E (.cv y)))
  have p0027 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWa
          (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
      (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
        (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
            (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))
      (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCrn (.cv f))) (synChnwcutcode S E (.cv y)))
      p0011 p0026
  have p0028 := (Nominal.classEqRefl (synChnwcutcode S E (.cv y)))
  have p0029 :=
    @gA1i
      (.classEq (synChnwcutcode S E (.cv y)) (synCop (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWa
          (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
      p0028
  have p0030 :=
    @gEqtrd
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWa
          (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
      (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
      (synChnwcutcode S E (.cv y))
      (synCop (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))
      p0027 p0029
  have p0031 :=
    @gOpth (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f))
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
  have p0032 :=
    @gSylib
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWa
          (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
      (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCrn (.cv f))) (synCop (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (synWa (.classEq (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCin S
            (synCxp (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))))
        (.classEq (synCrn (.cv f))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      p0030 p0031
  have p0033 :=
    @gSimpl
      (.classEq (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))))
      (.classEq (synCrn (.cv f))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))
  have p0034 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWa
          (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
      (synWa (.classEq (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCin S
            (synCxp (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))))
        (.classEq (synCrn (.cv f))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (.classEq (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))))
      p0032 p0033
  have p0035 :=
    @gIsoeq3 (synCdm (.cv f)) (synCrn (.cv f))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (.cv f)
  have p0036 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWa
          (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
      (.classEq (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))))
      (synWb (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
          (synCrn (.cv f))) (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCdm (.cv f)) (synCrn (.cv f))))
      p0034 p0035
  have p0037 :=
    @gBitrd
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWa
          (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
        (synCrn (.cv f)))
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
        (synCdm (.cv f)) (synCrn (.cv f)))
      p0022 p0036
  have p0048 :=
    @gSimpr
      (.classEq (.cv r) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (.classEq (synCdm (.cv f))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  have p0049 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWa
          (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
      (synWa (.classEq (.cv r) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
        (.classEq (synCdm (.cv f))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classEq (synCdm (.cv f))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0018 p0048
  have p0050 :=
    @gIsoeq4 (synCdm (.cv f)) (synCrn (.cv f))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (.cv f)
  have p0051 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWa
          (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
      (.classEq (synCdm (.cv f))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWb (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCdm (.cv f)) (synCrn (.cv f))) (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCrn (.cv f))))
      p0049 p0050
  have p0052 :=
    @gBitrd
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWa
          (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
        (synCdm (.cv f)) (synCrn (.cv f)))
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCrn (.cv f)))
      p0037 p0051
  have p0063 :=
    @gSimpr
      (.classEq (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))))
      (.classEq (synCrn (.cv f))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))
  have p0064 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWa
          (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
      (synWa (.classEq (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCin S
            (synCxp (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))))
        (.classEq (synCrn (.cv f))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (.classEq (synCrn (.cv f))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))
      p0032 p0063
  have p0065 :=
    @gIsoeq5 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCrn (.cv f))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (.cv f)
  have p0066 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWa
          (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
      (.classEq (synCrn (.cv f))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))
      (synWb (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCrn (.cv f))) (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      p0064 p0065
  have p0067 :=
    @gBitrd
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWa
          (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCrn (.cv f)))
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))
      p0052 p0066
  have p0068 :=
    @gMpbid
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWa
          (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))
      p0008 p0067
  have p0069 :=
    @gJca
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWa
          (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
      (.classMem (.cv y) E)
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))
      p0005 p0068
  have p0070 :=
    @gRspe
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))
      y E
  have p0071 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWa
          (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
      (synWa (.classMem (.cv y) E) (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      (synWrex y E (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      p0069 p0070
  have p0072 :=
    @gJca
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWa
          (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
      (.classMem (.cv x) D)
      (synWrex y E (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      p0002 p0071
  have p0073 :=
    @gRspe
      (synWrex y E (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
      x D
  have p0074 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWa
          (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
      (synWa (.classMem (.cv x) D) (synWrex y E (synWiso (.cv f) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))))
      (synWrex x D (synWrex y E (synWiso (.cv f) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))))
      p0072 p0073
  have p0075 :=
    @gElwecutiso x y D R S f E dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011
  have p0076 :=
    @gBiimpri (.classMem (.cv f) (synCwecutiso R D S E))
      (synWrex x D (synWrex y E (synWiso (.cv f) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))))
      p0075
  have p0077 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (synWa
          (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa
            (.classEq (synCop (.cv r) (synCdm (.cv f))) (synChnwcutcode R D (.cv x)))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (synChnwcutcode S E (.cv y))))))
      (synWrex x D (synWrex y E (synWiso (.cv f) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv y)))))))
      (.classMem (.cv f) (synCwecutiso R D S E)) p0074 p0076
  exact p0077


end NFChoice.DirectNominalPrf.WPPReplay

end
