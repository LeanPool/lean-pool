/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk014Compact001Block009

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk014Compact001Part047`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_strictsegcut`. -/
@[expose]
noncomputable def gStrictsegcut (x : Var) (y : Var) (D : Class) (R : Class) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classEq (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) :=
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
  have dv_cache_0001 :
    z ∉
      ((synCin (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x))))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_D, fresh_z_not_R, fresh_z_ne_y, fresh_z_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 :
    z ∉ ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_D, fresh_z_not_R, fresh_z_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 :
    z ∉
      ((synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_R, fresh_z_not_D, fresh_z_ne_y, fresh_z_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @gElstrictseg x z
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
  have p0001 :=
    @gBiimpi
      (.classMem (.cv z) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      (synWa (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))) (synWa
          (synWbr (.cv z) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (.cv x)) (synWne (.cv z) (.cv x))))
      p0000
  have p0002 :=
    @gSimpld
      (.classMem (.cv z) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWa (synWbr (.cv z) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.cv x)) (synWne (.cv z) (.cv x)))
      p0001
  have p0003 := @gInss1 D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))
  have p0004 :=
    @gSseli (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) D
      (.cv z) p0003
  have p0005 :=
    @gSyl
      (.classMem (.cv z) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (.classMem (.cv z) D) p0002 p0004
  have p0008 :=
    @gSimprd
      (.classMem (.cv z) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWa (synWbr (.cv z) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.cv x)) (synWne (.cv z) (.cv x)))
      p0001
  have p0009 :=
    @gSimpld
      (.classMem (.cv z) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      (synWbr (.cv z) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.cv x))
      (synWne (.cv z) (.cv x)) p0008
  have p0010 :=
    @gBrin (.cv z) (.cv x) R
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
  have p0011 :=
    @gBiimpi
      (synWbr (.cv z) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.cv x))
      (synWa (synWbr (.cv z) R (.cv x)) (synWbr (.cv z) (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
          (.cv x)))
      p0010
  have p0012 :=
    @gSimpld
      (synWbr (.cv z) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.cv x))
      (synWbr (.cv z) R (.cv x))
      (synWbr (.cv z) (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))) (.cv x))
      p0011
  have p0013 :=
    @gSyl
      (.classMem (.cv z) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      (synWbr (.cv z) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.cv x))
      (synWbr (.cv z) R (.cv x)) p0009 p0012
  have p0017 :=
    @gSimprd
      (.classMem (.cv z) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      (synWbr (.cv z) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.cv x))
      (synWne (.cv z) (.cv x)) p0008
  have p0018 :=
    @gJca
      (.classMem (.cv z) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      (synWbr (.cv z) R (.cv x)) (synWne (.cv z) (.cv x)) p0013 p0017
  have p0019 :=
    @gJca
      (.classMem (.cv z) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      (.classMem (.cv z) D) (synWa (synWbr (.cv z) R (.cv x)) (synWne (.cv z) (.cv x)))
      p0005 p0018
  have p0020 := @gElstrictseg x z D R
  have p0021 :=
    @gBiimpri
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWa (.classMem (.cv z) D)
        (synWa (synWbr (.cv z) R (.cv x)) (synWne (.cv z) (.cv x))))
      p0020
  have p0022 :=
    @gSyl
      (.classMem (.cv z) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      (synWa (.classMem (.cv z) D)
        (synWa (synWbr (.cv z) R (.cv x)) (synWne (.cv z) (.cv x))))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0019 p0021
  have p0023 :=
    @gA1i
      (.imp (.classMem (.cv z) (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x))))) (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0022
  have p0024 :=
    @gSimpl
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  have p0025 :=
    @gSimpl (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
  have p0026 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) p0024 p0025
  have p0028 :=
    @gSimpr (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
  have p0029 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0024 p0028
  have p0030 :=
    @gSimpr
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  have p0032 :=
    @gBiimpi
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWa (.classMem (.cv z) D)
        (synWa (synWbr (.cv z) R (.cv x)) (synWne (.cv z) (.cv x))))
      p0020
  have p0033 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWa (.classMem (.cv z) D)
        (synWa (synWbr (.cv z) R (.cv x)) (synWne (.cv z) (.cv x))))
      p0030 p0032
  have p0034 :=
    @gSimpld
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classMem (.cv z) D) (synWa (synWbr (.cv z) R (.cv x)) (synWne (.cv z) (.cv x)))
      p0033
  have p0035 :=
    @gJca
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (.classMem (.cv z) D) p0029 p0034
  have p0040 :=
    @gSimprd
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classMem (.cv z) D) (synWa (synWbr (.cv z) R (.cv x)) (synWne (.cv z) (.cv x)))
      p0033
  have p0041 :=
    @gSimpld
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWbr (.cv z) R (.cv x)) (synWne (.cv z) (.cv x)) p0040
  have p0042 :=
    @gN3jca
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D))
      (synWa (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
        (.classMem (.cv z) D))
      (synWbr (.cv z) R (.cv x)) p0026 p0035 p0041
  have p0043 := @gStrictsegdown y x z D R
  have p0044 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (synWa (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv x)))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0042 p0043
  have p0075 :=
    @gJca
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0044 p0029
  have p0076 :=
    @gBrinxp (.cv z) (.cv x)
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) R
  have p0077 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWa (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
        (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWb (synWbr (.cv z) R (.cv x)) (synWbr (.cv z) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.cv x)))
      p0075 p0076
  have p0078 :=
    @gBiimpd
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWbr (.cv z) R (.cv x))
      (synWbr (.cv z) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.cv x))
      p0077
  have p0079 :=
    @gMpd
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWbr (.cv z) R (.cv x))
      (synWbr (.cv z) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.cv x))
      p0041 p0078
  have p0085 :=
    @gSimprd
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWbr (.cv z) R (.cv x)) (synWne (.cv z) (.cv x)) p0040
  have p0086 :=
    @gJca
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWbr (.cv z) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.cv x))
      (synWne (.cv z) (.cv x)) p0079 p0085
  have p0087 :=
    @gJca
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWa (synWbr (.cv z) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.cv x)) (synWne (.cv z) (.cv x)))
      p0044 p0086
  have p0089 :=
    @gBiimpri
      (.classMem (.cv z) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      (synWa (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))) (synWa
          (synWbr (.cv z) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (.cv x)) (synWne (.cv z) (.cv x))))
      p0000
  have p0090 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWa (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))) (synWa
          (synWbr (.cv z) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (.cv x)) (synWne (.cv z) (.cv x))))
      (.classMem (.cv z) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      p0087 p0089
  have p0091 :=
    @gEx
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.classMem (.cv z) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      p0090
  have p0092 :=
    @gImpbid
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (.cv z) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0023 p0091
  have p0093 :=
    @gEqrdv
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      z
      (synCin (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0092
  exact p0093

/-- Checked nominal proof certificate identified upstream as `g_strictsegrestrnest`. -/
@[expose]
noncomputable def gStrictsegrestrnest (x : Var) (y : Var) (D : Class) (R : Class) :
    Nominal.NPrf
      (.imp (synWss (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))) (.classEq
          (synCin (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))) :=
  by
  have p0000 :=
    @gInass R
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  have p0001 :=
    @gA1i
      (.classEq (synCin (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin R (synCin (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      (synWss (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0000
  have p0002 :=
    @gId
      (synWss (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
  have p0004 :=
    @gJca
      (synWss (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWss (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWss (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0002 p0002
  have p0005 :=
    @gXpss12 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
  have p0006 :=
    @gSyl
      (synWss (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWa (synWss
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))) (synWss
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWss (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0004 p0005
  have p0007 :=
    @gDfss1
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
  have p0008 :=
    @gSylib
      (synWss (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWss (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classEq (synCin (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))) (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      p0006 p0007
  have p0009 :=
    @gIneq2d
      (synWss (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synCin (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))) (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      R p0008
  have p0010 :=
    @gEqtrd
      (synWss (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synCin (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin R (synCin (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))) (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      p0001 p0009
  exact p0010


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part048`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_strictsegltnoiso`. -/
@[expose]
noncomputable def gStrictsegltnoiso (x : Var) (y : Var) (D : Class) (R : Class)
    (H : Class) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.classMem H (synCvv))) (.neg (synWiso H (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ D.fv ∪ R.fv ∪ H.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have dv_cache_0001 :
    z ∉
      ((synCin (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x))))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_D, fresh_z_not_R, fresh_z_ne_y, fresh_z_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 :
    z ∉ ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_D, fresh_z_not_R, fresh_z_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 :
    z ∉
      ((synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_R, fresh_z_not_D, fresh_z_ne_y, fresh_z_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @gSimpr
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem H (synCvv)))
      (synWiso H (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
  have p0001 :=
    @gIsocnv (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      H
  have p0002 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWiso H (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWiso (synCcnv H) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0000 p0001
  have p0003 :=
    @gSimpl
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem H (synCvv)))
      (synWiso H (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
  have p0004 :=
    @gSimpl
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem H (synCvv))
  have p0005 :=
    @gElstrictseg x z
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
  have p0006 :=
    @gBiimpi
      (.classMem (.cv z) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      (synWa (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))) (synWa
          (synWbr (.cv z) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (.cv x)) (synWne (.cv z) (.cv x))))
      p0005
  have p0007 :=
    @gSimpld
      (.classMem (.cv z) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWa (synWbr (.cv z) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.cv x)) (synWne (.cv z) (.cv x)))
      p0006
  have p0008 := @gInss1 D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))
  have p0009 :=
    @gSseli (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) D
      (.cv z) p0008
  have p0010 :=
    @gSyl
      (.classMem (.cv z) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (.classMem (.cv z) D) p0007 p0009
  have p0013 :=
    @gSimprd
      (.classMem (.cv z) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWa (synWbr (.cv z) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.cv x)) (synWne (.cv z) (.cv x)))
      p0006
  have p0014 :=
    @gSimpld
      (.classMem (.cv z) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      (synWbr (.cv z) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.cv x))
      (synWne (.cv z) (.cv x)) p0013
  have p0015 :=
    @gBrin (.cv z) (.cv x) R
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
  have p0016 :=
    @gBiimpi
      (synWbr (.cv z) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.cv x))
      (synWa (synWbr (.cv z) R (.cv x)) (synWbr (.cv z) (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
          (.cv x)))
      p0015
  have p0017 :=
    @gSimpld
      (synWbr (.cv z) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.cv x))
      (synWbr (.cv z) R (.cv x))
      (synWbr (.cv z) (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))) (.cv x))
      p0016
  have p0018 :=
    @gSyl
      (.classMem (.cv z) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      (synWbr (.cv z) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.cv x))
      (synWbr (.cv z) R (.cv x)) p0014 p0017
  have p0022 :=
    @gSimprd
      (.classMem (.cv z) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      (synWbr (.cv z) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.cv x))
      (synWne (.cv z) (.cv x)) p0013
  have p0023 :=
    @gJca
      (.classMem (.cv z) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      (synWbr (.cv z) R (.cv x)) (synWne (.cv z) (.cv x)) p0018 p0022
  have p0024 :=
    @gJca
      (.classMem (.cv z) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      (.classMem (.cv z) D) (synWa (synWbr (.cv z) R (.cv x)) (synWne (.cv z) (.cv x)))
      p0010 p0023
  have p0025 := @gElstrictseg x z D R
  have p0026 :=
    @gBiimpri
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWa (.classMem (.cv z) D)
        (synWa (synWbr (.cv z) R (.cv x)) (synWne (.cv z) (.cv x))))
      p0025
  have p0027 :=
    @gSyl
      (.classMem (.cv z) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      (synWa (.classMem (.cv z) D)
        (synWa (synWbr (.cv z) R (.cv x)) (synWne (.cv z) (.cv x))))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0024 p0026
  have p0028 :=
    @gA1i
      (.imp (.classMem (.cv z) (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x))))) (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0027
  have p0029 :=
    @gSimpl
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  have p0030 :=
    @gSimpl (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
  have p0031 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) p0029 p0030
  have p0033 :=
    @gSimpr (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
  have p0034 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0029 p0033
  have p0035 :=
    @gSimpr
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  have p0037 :=
    @gBiimpi
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWa (.classMem (.cv z) D)
        (synWa (synWbr (.cv z) R (.cv x)) (synWne (.cv z) (.cv x))))
      p0025
  have p0038 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWa (.classMem (.cv z) D)
        (synWa (synWbr (.cv z) R (.cv x)) (synWne (.cv z) (.cv x))))
      p0035 p0037
  have p0039 :=
    @gSimpld
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classMem (.cv z) D) (synWa (synWbr (.cv z) R (.cv x)) (synWne (.cv z) (.cv x)))
      p0038
  have p0040 :=
    @gJca
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (.classMem (.cv z) D) p0034 p0039
  have p0045 :=
    @gSimprd
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classMem (.cv z) D) (synWa (synWbr (.cv z) R (.cv x)) (synWne (.cv z) (.cv x)))
      p0038
  have p0046 :=
    @gSimpld
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWbr (.cv z) R (.cv x)) (synWne (.cv z) (.cv x)) p0045
  have p0047 :=
    @gN3jca
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D))
      (synWa (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
        (.classMem (.cv z) D))
      (synWbr (.cv z) R (.cv x)) p0031 p0040 p0046
  have p0048 := @gStrictsegdown y x z D R
  have p0049 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (synWa (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv x)))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0047 p0048
  have p0080 :=
    @gJca
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0049 p0034
  have p0081 :=
    @gBrinxp (.cv z) (.cv x)
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) R
  have p0082 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWa (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
        (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWb (synWbr (.cv z) R (.cv x)) (synWbr (.cv z) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.cv x)))
      p0080 p0081
  have p0083 :=
    @gBiimpd
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWbr (.cv z) R (.cv x))
      (synWbr (.cv z) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.cv x))
      p0082
  have p0084 :=
    @gMpd
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWbr (.cv z) R (.cv x))
      (synWbr (.cv z) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.cv x))
      p0046 p0083
  have p0090 :=
    @gSimprd
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWbr (.cv z) R (.cv x)) (synWne (.cv z) (.cv x)) p0045
  have p0091 :=
    @gJca
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWbr (.cv z) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.cv x))
      (synWne (.cv z) (.cv x)) p0084 p0090
  have p0092 :=
    @gJca
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWa (synWbr (.cv z) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.cv x)) (synWne (.cv z) (.cv x)))
      p0049 p0091
  have p0094 :=
    @gBiimpri
      (.classMem (.cv z) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      (synWa (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))) (synWa
          (synWbr (.cv z) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (.cv x)) (synWne (.cv z) (.cv x))))
      p0005
  have p0095 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWa (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))) (synWa
          (synWbr (.cv z) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (.cv x)) (synWne (.cv z) (.cv x))))
      (.classMem (.cv z) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      p0092 p0094
  have p0096 :=
    @gEx
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.classMem (.cv z) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      p0095
  have p0097 :=
    @gImpbid
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (.cv z) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0028 p0096
  have p0098 :=
    @gEqrdv
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      z
      (synCin (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0097
  have p0099 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem H (synCvv)))
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classEq (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0004 p0098
  have p0196 :=
    @gXpeq12d
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem H (synCvv)))
      (synCin (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) p0099
      p0099
  have p0197 :=
    @gIneq2d
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem H (synCvv)))
      (synCxp (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0196
  have p0294 :=
    @gEqcomd
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem H (synCvv)))
      (synCin (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) p0099
  have p0295 :=
    @gInss1 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCima (synCcnv (synCdif (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCid))) (synCsn (.cv x)))
  have p0296 :=
    @gA1i
      (synWss (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem H (synCvv)))
      p0295
  have p0297 :=
    @gEqsstrd
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem H (synCvv)))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) p0294
      p0296
  have p0298 := @gStrictsegrestrnest x y D R
  have p0299 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem H (synCvv)))
      (synWss (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (.classEq (synCin (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      p0297 p0298
  have p0300 :=
    @gEqtrd
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem H (synCvv)))
      (synCin (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCxp (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x)))) (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x))))))
      (synCin (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      p0197 p0299
  have p0301 :=
    @gIsoeq3 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCin (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCid))) (synCsn (.cv x))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synCin (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCxp (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x)))) (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x))))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCcnv H)
  have p0302 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem H (synCvv)))
      (.classEq (synCin (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCxp (synCin
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x)))) (synCin
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x)))))) (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (synWb (synWiso (synCcnv H) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCxp (synCin
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                            (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                          (synCin D (synCima (synCcnv (synCdif R (synCid)))
                              (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x)))) (synCin
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                            (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                          (synCin D (synCima (synCcnv (synCdif R (synCid)))
                              (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x))))) (synWiso (synCcnv H) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x))))))
      p0300 p0301
  have p0399 :=
    @gIsoeq5 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCin (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCcnv H)
  have p0400 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem H (synCvv)))
      (.classEq (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWb (synWiso (synCcnv H) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x))))) (synWiso (synCcnv H) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      p0099 p0399
  have p0401 :=
    @gBitrd
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem H (synCvv)))
      (synWiso (synCcnv H) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCxp (synCin
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x)))) (synCin
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      (synWiso (synCcnv H) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      (synWiso (synCcnv H) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0302 p0400
  have p0402 :=
    @gBiimprd
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem H (synCvv)))
      (synWiso (synCcnv H) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCxp (synCin
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x)))) (synCin
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      (synWiso (synCcnv H) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0401
  have p0403 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem H (synCvv)))
      (.imp (synWiso (synCcnv H) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synWiso (synCcnv H) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCxp (synCin
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                            (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                          (synCin D (synCima (synCcnv (synCdif R (synCid)))
                              (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x)))) (synCin
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                            (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                          (synCin D (synCima (synCcnv (synCdif R (synCid)))
                              (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x))))))
      p0003 p0402
  have p0404 :=
    @gMpd
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWiso (synCcnv H) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWiso (synCcnv H) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCxp (synCin
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x)))) (synCin
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      p0002 p0403
  have p0408 := @gWestrsegndv y D R
  have p0409 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D))
      (synWbr (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCwe) (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0030 p0408
  have p0410 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem H (synCvv)))
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWbr (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCwe) (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0004 p0409
  have p0413 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem H (synCvv)))
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0004 p0033
  have p0414 :=
    @gJca
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem H (synCvv)))
      (synWbr (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCwe) (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0410 p0413
  have p0415 :=
    @gSimpr
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem H (synCvv))
  have p0416 := @gCnvexg H (synCvv)
  have p0417 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem H (synCvv)))
      (.classMem H (synCvv)) (.classMem (synCcnv H) (synCvv)) p0415 p0416
  have p0418 :=
    @gJca
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem H (synCvv)))
      (synWa (synWbr (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCwe) (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
        (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (synCcnv H) (synCvv)) p0414 p0417
  have p0419 :=
    @gStrictsegnoiso x
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synCcnv H)
  have p0420 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem H (synCvv)))
      (synWa (synWa (synWbr (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCwe)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
          (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (synCcnv H) (synCvv)))
      (.neg (synWiso (synCcnv H) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCxp (synCin
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                            (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                          (synCin D (synCima (synCcnv (synCdif R (synCid)))
                              (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x)))) (synCin
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                            (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                          (synCin D (synCima (synCcnv (synCdif R (synCid)))
                              (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x))))))
      p0418 p0419
  have p0421 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem H (synCvv)))
      (.neg (synWiso (synCcnv H) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCxp (synCin
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                            (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                          (synCin D (synCima (synCcnv (synCdif R (synCid)))
                              (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x)))) (synCin
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                            (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                          (synCin D (synCima (synCcnv (synCdif R (synCid)))
                              (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x))))))
      p0003 p0420
  have p0422 :=
    @gPm221dd
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D))
            (.classMem (.cv x)
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.classMem H (synCvv))) (synWiso H (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWiso (synCcnv H) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCxp (synCin
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x)))) (synCin
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      (.neg (synWiso H (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0404 p0421
  have p0423 :=
    @gPm201da
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem H (synCvv)))
      (synWiso H (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0422
  exact p0423


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part049`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_strictseghwnisono`. -/
@[expose]
noncomputable def gStrictseghwnisono (x : Var) (y : Var) (D : Class) (R : Class) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) (.neg
          (synWbr (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (synChwniso D) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) (synCin D
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
      ((synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_R, fresh_z_not_D, fresh_z_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 :
    z ∉
      ((synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_R, fresh_z_not_D, fresh_z_ne_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 :
    z ∉
      ((synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_R, fresh_z_not_D, fresh_z_ne_y, fresh_z_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @gSimpr
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWbr (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synChwniso D) (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
  have p0002 :=
    @gBrex
      (synCop (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synCop (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synChwniso D)
  have p0003 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWbr (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synChwniso D) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      (synWbr (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synChwniso D) (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (.classMem (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synCvv)) (.classMem (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
          (synCvv)))
      p0000 p0002
  have p0004 :=
    @gHwnisohwisocl D
      (synCop (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synCop (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
  have p0005 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWbr (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synChwniso D) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      (synWa (.classMem (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synCvv)) (.classMem (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
          (synCvv)))
      (.imp (synWbr (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synChwniso D) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWbr (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synChwiso D) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      p0003 p0004
  have p0006 :=
    @gMpd
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWbr (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synChwniso D) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      (synWbr (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synChwniso D) (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWbr (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synChwiso D) (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0000 p0005
  have p0010 :=
    @gHwisowitnesscl D
      (synCop (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synCop (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      z dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0011 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWbr (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synChwniso D) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      (synWa (.classMem (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synCvv)) (.classMem (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
          (synCvv)))
      (.imp (synWbr (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synChwiso D) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWex z (synWiso (.cv z) (synCfv (synC1st) (synCop (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCfv (synC1st) (synCop (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))))
      p0003 p0010
  have p0012 :=
    @gMpd
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWbr (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synChwniso D) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      (synWbr (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synChwiso D) (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWex z (synWiso (.cv z) (synCfv (synC1st) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCfv (synC1st) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))))
      p0006 p0011
  have p0013 :=
    @gSimpl
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWbr (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synChwniso D) (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
  have p0014 :=
    @gNfv
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      z dv_cache_0004
  have p0015 :=
    @gSimpl (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
  have p0016 := @gSimpl (synWbr R (synCwe) D) (.classMem (.cv y) D)
  have p0017 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (synWbr R (synCwe) D) p0015
      p0016
  have p0018 := @gBrex R D (synCwe)
  have p0019 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWbr R (synCwe) D) (synWa (.classMem R (synCvv)) (.classMem D (synCvv)))
      p0017 p0018
  have p0020 :=
    @gSimpld
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem R (synCvv)) (.classMem D (synCvv)) p0019
  have p0026 :=
    @gSimprd
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem R (synCvv)) (.classMem D (synCvv)) p0019
  have p0033 := @gIdex
  have p0034 :=
    @gA1i (.classMem (synCid) (synCvv))
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0033
  have p0035 :=
    @gJca
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem R (synCvv)) (.classMem (synCid) (synCvv)) p0020 p0034
  have p0036 := @gDifexg R (synCid) (synCvv) (synCvv)
  have p0037 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (.classMem R (synCvv)) (.classMem (synCid) (synCvv)))
      (.classMem (synCdif R (synCid)) (synCvv)) p0035 p0036
  have p0038 := @gCnvexg (synCdif R (synCid)) (synCvv)
  have p0039 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (synCdif R (synCid)) (synCvv))
      (.classMem (synCcnv (synCdif R (synCid))) (synCvv)) p0037 p0038
  have p0040 := @gSnex (.cv x)
  have p0041 :=
    @gA1i (.classMem (synCsn (.cv x)) (synCvv))
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0040
  have p0042 :=
    @gJca
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (synCcnv (synCdif R (synCid))) (synCvv))
      (.classMem (synCsn (.cv x)) (synCvv)) p0039 p0041
  have p0043 :=
    @gImaexg (synCcnv (synCdif R (synCid))) (synCsn (.cv x)) (synCvv) (synCvv)
  have p0044 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (.classMem (synCcnv (synCdif R (synCid))) (synCvv))
        (.classMem (synCsn (.cv x)) (synCvv)))
      (.classMem (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))) (synCvv))
      p0042 p0043
  have p0045 :=
    @gJca
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem D (synCvv))
      (.classMem (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))) (synCvv))
      p0026 p0044
  have p0046 :=
    @gInexg D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))) (synCvv)
      (synCvv)
  have p0047 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (.classMem D (synCvv))
        (.classMem (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))) (synCvv)))
      (.classMem (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCvv))
      p0045 p0046
  have p0075 :=
    @gJca
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCvv))
      (.classMem (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCvv))
      p0047 p0047
  have p0076 :=
    @gXpexg (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCvv)
      (synCvv)
  have p0077 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (.classMem
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCvv))
        (.classMem (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCvv)))
      (.classMem (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCvv))
      p0075 p0076
  have p0078 :=
    @gJca
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem R (synCvv))
      (.classMem (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCvv))
      p0020 p0077
  have p0079 :=
    @gInexg R
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synCvv) (synCvv)
  have p0080 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (.classMem R (synCvv)) (.classMem (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synCvv)))
      (.classMem (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCvv))
      p0078 p0079
  have p0108 :=
    @gJca
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCvv))
      (.classMem (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCvv))
      p0080 p0047
  have p0109 :=
    @gOpfvscl
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
  have p0110 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (.classMem (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCvv)) (.classMem
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCvv)))
      (synWa (.classEq (synCfv (synC1st) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
        (.classEq (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      p0108 p0109
  have p0111 :=
    @gSimpld
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classEq (synCfv (synC1st) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (.classEq (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0110
  have p0112 :=
    @gIsoeq2
      (synCfv (synC2nd) (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCfv (synC2nd) (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synCfv (synC1st) (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCfv (synC1st) (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.cv z)
  have p0113 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classEq (synCfv (synC1st) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (synWb (synWiso (.cv z) (synCfv (synC1st) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCfv (synC1st) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
        (synWiso (.cv z) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCfv (synC1st) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))))
      p0111 p0112
  have p0139 := @gSnex (.cv y)
  have p0140 :=
    @gA1i (.classMem (synCsn (.cv y)) (synCvv))
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0139
  have p0141 :=
    @gJca
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (synCcnv (synCdif R (synCid))) (synCvv))
      (.classMem (synCsn (.cv y)) (synCvv)) p0039 p0140
  have p0142 :=
    @gImaexg (synCcnv (synCdif R (synCid))) (synCsn (.cv y)) (synCvv) (synCvv)
  have p0143 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (.classMem (synCcnv (synCdif R (synCid))) (synCvv))
        (.classMem (synCsn (.cv y)) (synCvv)))
      (.classMem (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))) (synCvv))
      p0141 p0142
  have p0144 :=
    @gJca
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem D (synCvv))
      (.classMem (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))) (synCvv))
      p0026 p0143
  have p0145 :=
    @gInexg D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))) (synCvv)
      (synCvv)
  have p0146 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (.classMem D (synCvv))
        (.classMem (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))) (synCvv)))
      (.classMem (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCvv))
      p0144 p0145
  have p0174 :=
    @gJca
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCvv))
      (.classMem (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCvv))
      p0146 p0146
  have p0175 :=
    @gXpexg (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCvv)
      (synCvv)
  have p0176 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (.classMem
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCvv))
        (.classMem (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCvv)))
      (.classMem (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))) (synCvv))
      p0174 p0175
  have p0177 :=
    @gJca
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem R (synCvv))
      (.classMem (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))) (synCvv))
      p0020 p0176
  have p0178 :=
    @gInexg R
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synCvv) (synCvv)
  have p0179 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (.classMem R (synCvv)) (.classMem (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
          (synCvv)))
      (.classMem (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCvv))
      p0177 p0178
  have p0207 :=
    @gJca
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCvv))
      (.classMem (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCvv))
      p0179 p0146
  have p0208 :=
    @gOpfvscl
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
  have p0209 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (.classMem (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCvv)) (.classMem
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCvv)))
      (synWa (.classEq (synCfv (synC1st) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
        (.classEq (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0207 p0208
  have p0210 :=
    @gSimpld
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classEq (synCfv (synC1st) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      (.classEq (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0209
  have p0211 :=
    @gIsoeq3
      (synCfv (synC2nd) (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCfv (synC2nd) (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCfv (synC1st) (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.cv z)
  have p0212 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classEq (synCfv (synC1st) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      (synWb (synWiso (.cv z) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCfv (synC1st) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
        (synWiso (.cv z) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))))
      p0210 p0211
  have p0213 :=
    @gBitrd
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWiso (.cv z) (synCfv (synC1st) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCfv (synC1st) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      (synWiso (.cv z) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCfv (synC1st) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      (synWiso (.cv z) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      p0113 p0212
  have p0310 :=
    @gSimprd
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classEq (synCfv (synC1st) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (.classEq (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0110
  have p0311 :=
    @gIsoeq4
      (synCfv (synC2nd) (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCfv (synC2nd) (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.cv z)
  have p0312 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classEq (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWb (synWiso (.cv z) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
        (synWiso (.cv z) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))))
      p0310 p0311
  have p0313 :=
    @gBitrd
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWiso (.cv z) (synCfv (synC1st) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCfv (synC1st) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      (synWiso (.cv z) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      (synWiso (.cv z) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      p0213 p0312
  have p0410 :=
    @gSimprd
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classEq (synCfv (synC1st) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      (.classEq (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0209
  have p0411 :=
    @gIsoeq5 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCfv (synC2nd) (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.cv z)
  have p0412 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classEq (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWb (synWiso (.cv z) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
        (synWiso (.cv z) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0410 p0411
  have p0413 :=
    @gBitrd
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWiso (.cv z) (synCfv (synC1st) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCfv (synC1st) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      (synWiso (.cv z) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      (synWiso (.cv z) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0313 p0412
  have p0414 :=
    @gBiimpd
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWiso (.cv z) (synCfv (synC1st) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCfv (synC1st) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      (synWiso (.cv z) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0413
  have p0415 :=
    @gEximd
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWiso (.cv z) (synCfv (synC1st) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCfv (synC1st) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      (synWiso (.cv z) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      z p0014 p0414
  have p0416 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWbr (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synChwniso D) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.imp (synWex z (synWiso (.cv z) (synCfv (synC1st) (synCop (synCin R (synCxp
                    (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                    (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCfv (synC1st) (synCop (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))))
        (synWex z (synWiso (.cv z) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      p0013 p0415
  have p0417 :=
    @gMpd
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWbr (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synChwniso D) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      (synWex z (synWiso (.cv z) (synCfv (synC1st) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCfv (synC1st) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))))
      (synWex z (synWiso (.cv z) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0012 p0416
  have p0419 :=
    @gId
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
  have p0420 := @gVex z
  have p0421 :=
    @gA1i (.classMem (.cv z) (synCvv))
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0420
  have p0422 :=
    @gJca
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (.cv z) (synCvv)) p0419 p0421
  have p0423 := @gStrictsegltnoiso x y D R (.cv z)
  have p0424 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv z) (synCvv)))
      (.neg (synWiso (.cv z) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0422 p0423
  have p0425 :=
    @gNexdv
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWiso (.cv z) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      z dv_cache_0004 p0424
  have p0426 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWbr (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synChwniso D) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.neg (synWex z (synWiso (.cv z) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      p0013 p0425
  have p0427 :=
    @gPm221dd
      (synWa (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synWbr (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synChwniso D) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      (synWex z (synWiso (.cv z) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.neg (synWbr (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synChwniso D) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      p0417 p0426
  have p0428 :=
    @gPm201da
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWbr (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synChwniso D) (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0427
  exact p0428


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part050`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hnwcutcodeeq3`. -/
@[expose]
noncomputable def gHnwcutcodeeq3 (A : Class) (B : Class) (D : Class) (R : Class)
    (_dv_A_R : Disjoint A.fv R.fv) :
    Nominal.NPrf
      (.imp (.classEq A B) (.classEq (synChnwcutcode R D A) (synChnwcutcode R D B))) :=
  by
  have p0000 := (Nominal.classEqRefl (synChnwcutcode R D A))
  have p0001 :=
    @gA1i
      (.classEq (synChnwcutcode R D A) (synCop (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn A)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn A)))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn A)))))
      (.classEq A B) p0000
  have p0002 := @gSneq A B
  have p0003 :=
    @gImaeq2d (.classEq A B) (synCsn A) (synCsn B) (synCcnv (synCdif R (synCid)))
      p0002
  have p0004 :=
    @gIneq2d (.classEq A B) (synCima (synCcnv (synCdif R (synCid))) (synCsn A))
      (synCima (synCcnv (synCdif R (synCid))) (synCsn B)) D p0003
  have p0008 :=
    @gXpeq12d (.classEq A B)
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn A)))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn A)))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))) p0004 p0004
  have p0009 :=
    @gIneq2d (.classEq A B)
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn A)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn A))))
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))
      R p0008
  have p0013 :=
    @gOpeq12d (.classEq A B)
      (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn A)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn A)))))
      (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn A)))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))) p0009 p0004
  have p0014 :=
    @gEqtrd (.classEq A B) (synChnwcutcode R D A)
      (synCop (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn A)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn A)))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn A))))
      (synCop (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))
      p0001 p0013
  have p0015 := (Nominal.classEqRefl (synChnwcutcode R D B))
  have p0016 :=
    @gEqcomi (synChnwcutcode R D B)
      (synCop (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))
      p0015
  have p0017 :=
    @gA1i
      (.classEq (synCop (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))
        (synChnwcutcode R D B))
      (.classEq A B) p0016
  have p0018 :=
    @gEqtrd (.classEq A B) (synChnwcutcode R D A)
      (synCop (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))
      (synChnwcutcode R D B) p0014 p0017
  exact p0018

/-- Checked nominal proof certificate identified upstream as `g_elhwcncl`. -/
@[expose]
noncomputable def gElhwcncl (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (.classMem B (synCvv)) (synWb (.classMem B (synChwcn A))
          (synWa (.classMem B (synChwcodes A)) (synWss (synCfv (synC1st) B)
              (synCxp (synCfv (synC2nd) B) (synCfv (synC2nd) B)))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have dv_cache_0001 : u ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_B, not_false_eq_true])
  have dv_cache_0002 :
    u ∉
      ((synWb (.classMem B (synChwcn A)) (synWa (.classMem B (synChwcodes A))
            (synWss (synCfv (synC1st) B)
              (synCxp (synCfv (synC2nd) B) (synCfv (synC2nd) B)))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcodes,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          fresh_u_not_B, fresh_u_not_A, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @gEleq1 (.cv u) B (synChwcn A)
  have p0001 := @gEleq1 (.cv u) B (synChwcodes A)
  have p0002 := @gFveq2 (.cv u) B (synC1st)
  have p0003 := @gFveq2 (.cv u) B (synC2nd)
  have p0005 :=
    @gXpeq12d (.classEq (.cv u) B) (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) B)
      (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) B) p0003 p0003
  have p0006 :=
    @gSseq12d (.classEq (.cv u) B) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) B)
      (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))
      (synCxp (synCfv (synC2nd) B) (synCfv (synC2nd) B)) p0002 p0005
  have p0007 :=
    @gAnbi12d (.classEq (.cv u) B) (.classMem (.cv u) (synChwcodes A))
      (.classMem B (synChwcodes A))
      (synWss (synCfv (synC1st) (.cv u))
        (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      (synWss (synCfv (synC1st) B) (synCxp (synCfv (synC2nd) B) (synCfv (synC2nd) B)))
      p0001 p0006
  have p0008 :=
    @gBibi12d (.classEq (.cv u) B) (.classMem (.cv u) (synChwcn A))
      (.classMem B (synChwcn A))
      (synWa (.classMem (.cv u) (synChwcodes A)) (synWss (synCfv (synC1st) (.cv u))
          (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))))
      (synWa (.classMem B (synChwcodes A)) (synWss (synCfv (synC1st) B)
          (synCxp (synCfv (synC2nd) B) (synCfv (synC2nd) B))))
      p0000 p0007
  have p0009 := @gElhwcn u A
  have p0010 :=
    @gVtoclg
      (synWb (.classMem (.cv u) (synChwcn A)) (synWa (.classMem (.cv u) (synChwcodes A))
          (synWss (synCfv (synC1st) (.cv u))
            (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))))
      (synWb (.classMem B (synChwcn A)) (synWa (.classMem B (synChwcodes A))
          (synWss (synCfv (synC1st) B)
            (synCxp (synCfv (synC2nd) B) (synCfv (synC2nd) B)))))
      u B (synCvv) dv_cache_0001 dv_cache_0002 p0008 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_hwnisoclasselhnordcl`. -/
@[expose]
noncomputable def gHwnisoclasselhnordcl (A : Class) (B : Class)
    (hyp_hwnisoclasselhnordcl_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem B (synChwcn A))
        (.classMem (synCec B (synChwniso A)) (synChnord A))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have dv_cache_0001 : u ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
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
  have dv_cache_0003 :
    u ∉
      ((Wff.imp (.classMem B (synChwcn A))
          (.classMem (synCec B (synChwniso A)) (synChnord A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          fresh_u_not_B, fresh_u_not_A, or_false, not_false_eq_true])
  have p0000 := @gElex B (synChwcn A)
  have p0001 := @gEleq1 (.cv u) B (synChwcn A)
  have p0002 := @gEceq1 (.cv u) B (synChwniso A)
  have p0003 :=
    @gEleq1d (.classEq (.cv u) B) (synCec (.cv u) (synChwniso A))
      (synCec B (synChwniso A)) (synChnord A) p0002
  have p0004 :=
    @gImbi12d (.classEq (.cv u) B) (.classMem (.cv u) (synChwcn A))
      (.classMem B (synChwcn A))
      (.classMem (synCec (.cv u) (synChwniso A)) (synChnord A))
      (.classMem (synCec B (synChwniso A)) (synChnord A)) p0001 p0003
  have p0005 := @gHwnisoclasselhnord u A dv_cache_0001 hyp_hwnisoclasselhnordcl_1
  have p0006 :=
    @gVtoclg
      (.imp (.classMem (.cv u) (synChwcn A))
        (.classMem (synCec (.cv u) (synChwniso A)) (synChnord A)))
      (.imp (.classMem B (synChwcn A)) (.classMem (synCec B (synChwniso A)) (synChnord A)))
      u B (synCvv) dv_cache_0002 dv_cache_0003 p0004 p0005
  have p0007 :=
    @gMpcom (.classMem B (synCvv)) (.classMem B (synChwcn A))
      (.classMem (synCec B (synChwniso A)) (synChnord A)) p0000 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_pw12argcl`. -/
@[expose]
noncomputable def gPw12argcl (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (.classMem B (synCpw1 (synCpw1 C))) (synWa (.classMem (synCuni (synCuni B)) C)
          (.classEq B (synCsn (synCsn (synCuni (synCuni B))))))) :=
  by
  let proofSupport : Finset Var := B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (C).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
  have dv_cache_0002 : x ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0003 :
    x ∉
      ((Wff.imp (.classMem B (synCpw1 (synCpw1 C)))
          (synWa (.classMem (synCuni (synCuni B)) C)
            (.classEq B (synCsn (synCsn (synCuni (synCuni B)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          fresh_x_not_B, fresh_x_not_C, or_false, not_false_eq_true])
  have p0000 := @gElex B (synCpw1 (synCpw1 C))
  have p0001 := @gEleq1 (.cv x) B (synCpw1 (synCpw1 C))
  have p0002 := @gUnieq (.cv x) B
  have p0003 := @gUnieqd (.classEq (.cv x) B) (synCuni (.cv x)) (synCuni B) p0002
  have p0004 :=
    @gEleq1d (.classEq (.cv x) B) (synCuni (synCuni (.cv x))) (synCuni (synCuni B)) C
      p0003
  have p0005 := @gId (.classEq (.cv x) B)
  have p0008 :=
    @gSneqd (.classEq (.cv x) B) (synCuni (synCuni (.cv x))) (synCuni (synCuni B))
      p0003
  have p0009 :=
    @gSneqd (.classEq (.cv x) B) (synCsn (synCuni (synCuni (.cv x))))
      (synCsn (synCuni (synCuni B))) p0008
  have p0010 :=
    @gEqeq12d (.classEq (.cv x) B) (.cv x) B
      (synCsn (synCsn (synCuni (synCuni (.cv x)))))
      (synCsn (synCsn (synCuni (synCuni B)))) p0005 p0009
  have p0011 :=
    @gAnbi12d (.classEq (.cv x) B) (.classMem (synCuni (synCuni (.cv x))) C)
      (.classMem (synCuni (synCuni B)) C)
      (.classEq (.cv x) (synCsn (synCsn (synCuni (synCuni (.cv x))))))
      (.classEq B (synCsn (synCsn (synCuni (synCuni B))))) p0004 p0010
  have p0012 :=
    @gImbi12d (.classEq (.cv x) B) (.classMem (.cv x) (synCpw1 (synCpw1 C)))
      (.classMem B (synCpw1 (synCpw1 C)))
      (synWa (.classMem (synCuni (synCuni (.cv x))) C)
        (.classEq (.cv x) (synCsn (synCsn (synCuni (synCuni (.cv x)))))))
      (synWa (.classMem (synCuni (synCuni B)) C)
        (.classEq B (synCsn (synCsn (synCuni (synCuni B))))))
      p0001 p0011
  have p0013 := @gFdcolcodearg C x dv_cache_0001
  have p0014 :=
    @gVtoclg
      (.imp (.classMem (.cv x) (synCpw1 (synCpw1 C)))
        (synWa (.classMem (synCuni (synCuni (.cv x))) C)
          (.classEq (.cv x) (synCsn (synCsn (synCuni (synCuni (.cv x))))))))
      (.imp (.classMem B (synCpw1 (synCpw1 C))) (synWa (.classMem (synCuni (synCuni B)) C)
          (.classEq B (synCsn (synCsn (synCuni (synCuni B)))))))
      x B (synCvv) dv_cache_0002 dv_cache_0003 p0012 p0013
  have p0015 :=
    @gMpcom (.classMem B (synCvv)) (.classMem B (synCpw1 (synCpw1 C)))
      (synWa (.classMem (synCuni (synCuni B)) C)
        (.classEq B (synCsn (synCsn (synCuni (synCuni B))))))
      p0000 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_hnwcutcodecn`. -/
@[expose]
noncomputable def gHnwcutcodecn (x : Var) (D : Class) (R : Class)
    (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutcodecn_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (.classMem (.cv x) D) (.classMem (synChnwcutcode R D (.cv x)) (synChwcn D))) :=
  by
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have p0000 := @gA1i (synWbr R (synCwe) D) (.classMem (.cv x) D) hyp_hnwcutcodecn_1
  have p0001 := @gId (.classMem (.cv x) D)
  have p0002 :=
    @gJca (.classMem (.cv x) D) (synWbr R (synCwe) D) (.classMem (.cv x) D) p0000 p0001
  have p0003 := @gWestrseg x D R dv_cache_0001
  have p0004 :=
    @gSyl (.classMem (.cv x) D) (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D))
      (synWbr (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCwe) (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0002 p0003
  have p0005 :=
    (Nominal.biimpRefl (synWbr (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCwe) (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
  have p0006 :=
    @gBiimpi
      (synWbr (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCwe) (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.classMem (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCwe))
      p0005
  have p0007 :=
    @gSyl (.classMem (.cv x) D)
      (synWbr (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCwe) (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.classMem (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCwe))
      p0004 p0006
  have p0008 := @gBrex R D (synCwe)
  have p0009 :=
    @gSimpld (synWbr R (synCwe) D) (.classMem R (synCvv)) (.classMem D (synCvv))
      p0008
  have p0010 := Nominal.mp hyp_hnwcutcodecn_1 p0009
  have p0012 :=
    @gSimprd (synWbr R (synCwe) D) (.classMem R (synCvv)) (.classMem D (synCvv))
      p0008
  have p0013 := Nominal.mp hyp_hnwcutcodecn_1 p0012
  have p0017 := @gIdex
  have p0018 := @gDifex R (synCid) p0010 p0017
  have p0019 := @gCnvex (synCdif R (synCid)) p0018
  have p0020 := @gSnex (.cv x)
  have p0021 := @gImaex (synCcnv (synCdif R (synCid))) (synCsn (.cv x)) p0019 p0020
  have p0022 :=
    @gInex D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))) p0013 p0021
  have p0035 :=
    @gXpex (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) p0022
      p0022
  have p0036 :=
    @gInex R
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0010 p0035
  have p0037 := @gInss1 D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))
  have p0050 :=
    @gElpw (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) D
      p0022
  have p0051 :=
    @gMpbir
      (.classMem (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCpw D))
      (synWss (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) D)
      p0037 p0050
  have p0052 :=
    @gPm32i
      (.classMem (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCvv))
      (.classMem (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCpw D))
      p0036 p0051
  have p0053 :=
    @gOpelxp
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCvv)
      (synCpw D)
  have p0054 :=
    @gMpbir
      (.classMem (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synCxp (synCvv) (synCpw D)))
      (synWa (.classMem (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCvv)) (.classMem
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCpw D)))
      p0052 p0053
  have p0055 :=
    @gA1i
      (.classMem (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synCxp (synCvv) (synCpw D)))
      (.classMem (.cv x) D) p0054
  have p0056 :=
    @gJca (.classMem (.cv x) D)
      (.classMem (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCwe))
      (.classMem (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synCxp (synCvv) (synCpw D)))
      p0007 p0055
  have p0057 :=
    @gElin
      (synCop (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synCwe) (synCxp (synCvv) (synCpw D))
  have p0058 :=
    @gA1i
      (synWb (.classMem (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synCin (synCwe) (synCxp (synCvv) (synCpw D)))) (synWa (.classMem (synCop
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (synCwe)) (.classMem (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (synCxp (synCvv) (synCpw D)))))
      (.classMem (.cv x) D) p0057
  have p0059 :=
    @gMpbird (.classMem (.cv x) D)
      (.classMem (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synCin (synCwe) (synCxp (synCvv) (synCpw D))))
      (synWa (.classMem (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synCwe)) (.classMem (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synCxp (synCvv) (synCpw D))))
      p0056 p0058
  have p0060 := (Nominal.classEqRefl (synChwcodes D))
  have p0061 :=
    @gEleq2i (synChwcodes D) (synCin (synCwe) (synCxp (synCvv) (synCpw D)))
      (synCop (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0060
  have p0062 :=
    @gSylibr (.classMem (.cv x) D)
      (.classMem (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synCin (synCwe) (synCxp (synCvv) (synCpw D))))
      (.classMem (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synChwcodes D))
      p0059 p0061
  have p0063 :=
    @gInss2 R
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  have p0105 :=
    @gOpfv2nd
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) p0036
      p0022
  have p0148 :=
    @gPm32i
      (.classEq (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.classEq (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0105 p0105
  have p0149 :=
    @gXpeq12
      (synCfv (synC2nd) (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCfv (synC2nd) (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
  have p0150 := Nominal.mp p0148 p0149
  have p0151 :=
    @gEqcomi
      (synCxp (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0150
  have p0152 :=
    @gSseq2
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synCxp (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
  have p0153 := Nominal.mp p0151 p0152
  have p0154 :=
    @gMpbi
      (synWss (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWss (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCxp (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      p0063 p0153
  have p0196 :=
    @gOpfv1st
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) p0036
      p0022
  have p0197 :=
    @gSseq1
      (synCfv (synC1st) (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCxp (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
  have p0198 := Nominal.mp p0196 p0197
  have p0199 :=
    @gMpbir
      (synWss (synCfv (synC1st) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCxp (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      (synWss (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCxp (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      p0154 p0198
  have p0200 :=
    @gA1i
      (synWss (synCfv (synC1st) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCxp (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      (.classMem (.cv x) D) p0199
  have p0201 :=
    @gJca (.classMem (.cv x) D)
      (.classMem (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synChwcodes D))
      (synWss (synCfv (synC1st) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCxp (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      p0062 p0200
  have p0243 :=
    @gOpex
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) p0036
      p0022
  have p0244 :=
    @gElhwcncl D
      (synCop (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  have p0245 := Nominal.mp p0243 p0244
  have p0246 :=
    @gA1i
      (synWb (.classMem (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synChwcn D)) (synWa (.classMem (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (synChwcodes D)) (synWss (synCfv (synC1st) (synCop (synCin R (synCxp
                    (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                    (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCxp (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
              (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
                  (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))))
      (.classMem (.cv x) D) p0245
  have p0247 :=
    @gMpbird (.classMem (.cv x) D)
      (.classMem (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synChwcn D))
      (synWa (.classMem (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synChwcodes D)) (synWss (synCfv (synC1st) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCxp (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))
      p0201 p0246
  have p0248 := (Nominal.classEqRefl (synChnwcutcode R D (.cv x)))
  have p0249 :=
    @gEleq1i (synChnwcutcode R D (.cv x))
      (synCop (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synChwcn D) p0248
  have p0250 :=
    @gSylibr (.classMem (.cv x) D)
      (.classMem (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synChwcn D))
      (.classMem (synChnwcutcode R D (.cv x)) (synChwcn D)) p0247 p0249
  exact p0250

/-- Checked nominal proof certificate identified upstream as `g_hnwcutclassord`. -/
@[expose]
noncomputable def gHnwcutclassord (x : Var) (D : Class) (R : Class)
    (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutclassord_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (.classMem (.cv x) D)
        (.classMem (synCec (synChnwcutcode R D (.cv x)) (synChwniso D)) (synChnord D))) :=
  by
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have p0000 := @gHnwcutcodecn x D R dv_cache_0001 hyp_hnwcutclassord_1
  have p0001 := @gBrex R D (synCwe)
  have p0002 :=
    @gSimprd (synWbr R (synCwe) D) (.classMem R (synCvv)) (.classMem D (synCvv))
      p0001
  have p0003 := Nominal.mp hyp_hnwcutclassord_1 p0002
  have p0004 := @gHwnisoclasselhnordcl D (synChnwcutcode R D (.cv x)) p0003
  have p0005 :=
    @gSyl (.classMem (.cv x) D) (.classMem (synChnwcutcode R D (.cv x)) (synChwcn D))
      (.classMem (synCec (synChnwcutcode R D (.cv x)) (synChwniso D)) (synChnord D))
      p0000 p0004
  exact p0005


end NFChoice.DirectNominalPrf.WPPReplay

end
