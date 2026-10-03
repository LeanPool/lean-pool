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

@[expose]
noncomputable def g_strictsegcut (x : Var) (y : Var) (D : Class) (R : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classEq (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) :=
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
      ((syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x))))).fv :=
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
    z ∉ ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))).fv :=
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
      ((syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))).fv :=
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
    @g_elstrictseg x z
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
  have p0001 :=
    @g_biimpi
      (.classMem (.cv z) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_wa
          (syn_wbr (.cv z) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (.cv x)) (syn_wne (.cv z) (.cv x))))
      p0000
  have p0002 :=
    @g_simpld
      (.classMem (.cv z) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wa (syn_wbr (.cv z) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.cv x)) (syn_wne (.cv z) (.cv x)))
      p0001
  have p0003 := @g_inss1 D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))
  have p0004 :=
    @g_sseli (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) D
      (.cv z) p0003
  have p0005 :=
    @g_syl
      (.classMem (.cv z) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (.classMem (.cv z) D) p0002 p0004
  have p0008 :=
    @g_simprd
      (.classMem (.cv z) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wa (syn_wbr (.cv z) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.cv x)) (syn_wne (.cv z) (.cv x)))
      p0001
  have p0009 :=
    @g_simpld
      (.classMem (.cv z) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      (syn_wbr (.cv z) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.cv x))
      (syn_wne (.cv z) (.cv x)) p0008
  have p0010 :=
    @g_brin (.cv z) (.cv x) R
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0011 :=
    @g_biimpi
      (syn_wbr (.cv z) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.cv x))
      (syn_wa (syn_wbr (.cv z) R (.cv x)) (syn_wbr (.cv z) (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
          (.cv x)))
      p0010
  have p0012 :=
    @g_simpld
      (syn_wbr (.cv z) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.cv x))
      (syn_wbr (.cv z) R (.cv x))
      (syn_wbr (.cv z) (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (.cv x))
      p0011
  have p0013 :=
    @g_syl
      (.classMem (.cv z) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      (syn_wbr (.cv z) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.cv x))
      (syn_wbr (.cv z) R (.cv x)) p0009 p0012
  have p0017 :=
    @g_simprd
      (.classMem (.cv z) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      (syn_wbr (.cv z) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.cv x))
      (syn_wne (.cv z) (.cv x)) p0008
  have p0018 :=
    @g_jca
      (.classMem (.cv z) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x)) p0013 p0017
  have p0019 :=
    @g_jca
      (.classMem (.cv z) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      (.classMem (.cv z) D) (syn_wa (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x)))
      p0005 p0018
  have p0020 := @g_elstrictseg x z D R
  have p0021 :=
    @g_biimpri
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv z) D)
        (syn_wa (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x))))
      p0020
  have p0022 :=
    @g_syl
      (.classMem (.cv z) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv z) D)
        (syn_wa (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x))))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0019 p0021
  have p0023 :=
    @g_a1i
      (.imp (.classMem (.cv z) (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0022
  have p0024 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0025 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0026 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) p0024 p0025
  have p0028 :=
    @g_simpr (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0029 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0024 p0028
  have p0030 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0032 :=
    @g_biimpi
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv z) D)
        (syn_wa (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x))))
      p0020
  have p0033 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv z) D)
        (syn_wa (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x))))
      p0030 p0032
  have p0034 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classMem (.cv z) D) (syn_wa (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x)))
      p0033
  have p0035 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (.classMem (.cv z) D) p0029 p0034
  have p0040 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classMem (.cv z) D) (syn_wa (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x)))
      p0033
  have p0041 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x)) p0040
  have p0042 :=
    @g_n_3jca
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D))
      (syn_wa (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
        (.classMem (.cv z) D))
      (syn_wbr (.cv z) R (.cv x)) p0026 p0035 p0041
  have p0043 := @g_strictsegdown y x z D R
  have p0044 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wa (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
          (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv x)))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0042 p0043
  have p0075 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0044 p0029
  have p0076 :=
    @g_brinxp (.cv z) (.cv x)
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) R
  have p0077 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
        (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wb (syn_wbr (.cv z) R (.cv x)) (syn_wbr (.cv z) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.cv x)))
      p0075 p0076
  have p0078 :=
    @g_biimpd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wbr (.cv z) R (.cv x))
      (syn_wbr (.cv z) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.cv x))
      p0077
  have p0079 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wbr (.cv z) R (.cv x))
      (syn_wbr (.cv z) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.cv x))
      p0041 p0078
  have p0085 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x)) p0040
  have p0086 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wbr (.cv z) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.cv x))
      (syn_wne (.cv z) (.cv x)) p0079 p0085
  have p0087 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wa (syn_wbr (.cv z) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.cv x)) (syn_wne (.cv z) (.cv x)))
      p0044 p0086
  have p0089 :=
    @g_biimpri
      (.classMem (.cv z) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_wa
          (syn_wbr (.cv z) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (.cv x)) (syn_wne (.cv z) (.cv x))))
      p0000
  have p0090 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_wa
          (syn_wbr (.cv z) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (.cv x)) (syn_wne (.cv z) (.cv x))))
      (.classMem (.cv z) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      p0087 p0089
  have p0091 :=
    @g_ex
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (.classMem (.cv z) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      p0090
  have p0092 :=
    @g_impbid
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (.cv z) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0023 p0091
  have p0093 :=
    @g_eqrdv
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      z
      (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0092
  exact p0093

@[expose]
noncomputable def g_strictsegrestrnest (x : Var) (y : Var) (D : Class) (R : Class) :
    Nominal.NPrf
      (.imp (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (.classEq
          (syn_cin (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) :=
  by
  have p0000 :=
    @g_inass R
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0001 :=
    @g_a1i
      (.classEq (syn_cin (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin R (syn_cin (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0000
  have p0002 :=
    @g_id
      (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0004 :=
    @g_jca
      (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0002 p0002
  have p0005 :=
    @g_xpss12 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
  have p0006 :=
    @g_syl
      (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wa (syn_wss
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_wss
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wss (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0004 p0005
  have p0007 :=
    @g_dfss1
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0008 :=
    @g_sylib
      (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wss (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_cin (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      p0006 p0007
  have p0009 :=
    @g_ineq2d
      (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_cin (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      R p0008
  have p0010 :=
    @g_eqtrd
      (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_cin (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin R (syn_cin (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
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

@[expose]
noncomputable def g_strictsegltnoiso (x : Var) (y : Var) (D : Class) (R : Class)
    (H : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.classMem H (syn_cvv))) (.neg (syn_wiso H (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) :=
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
      ((syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x))))).fv :=
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
    z ∉ ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))).fv :=
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
      ((syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))).fv :=
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
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem H (syn_cvv)))
      (syn_wiso H (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0001 :=
    @g_isocnv (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      H
  have p0002 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wiso H (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wiso (syn_ccnv H) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0000 p0001
  have p0003 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem H (syn_cvv)))
      (syn_wiso H (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0004 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem H (syn_cvv))
  have p0005 :=
    @g_elstrictseg x z
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
  have p0006 :=
    @g_biimpi
      (.classMem (.cv z) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_wa
          (syn_wbr (.cv z) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (.cv x)) (syn_wne (.cv z) (.cv x))))
      p0005
  have p0007 :=
    @g_simpld
      (.classMem (.cv z) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wa (syn_wbr (.cv z) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.cv x)) (syn_wne (.cv z) (.cv x)))
      p0006
  have p0008 := @g_inss1 D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))
  have p0009 :=
    @g_sseli (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) D
      (.cv z) p0008
  have p0010 :=
    @g_syl
      (.classMem (.cv z) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (.classMem (.cv z) D) p0007 p0009
  have p0013 :=
    @g_simprd
      (.classMem (.cv z) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wa (syn_wbr (.cv z) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.cv x)) (syn_wne (.cv z) (.cv x)))
      p0006
  have p0014 :=
    @g_simpld
      (.classMem (.cv z) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      (syn_wbr (.cv z) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.cv x))
      (syn_wne (.cv z) (.cv x)) p0013
  have p0015 :=
    @g_brin (.cv z) (.cv x) R
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0016 :=
    @g_biimpi
      (syn_wbr (.cv z) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.cv x))
      (syn_wa (syn_wbr (.cv z) R (.cv x)) (syn_wbr (.cv z) (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
          (.cv x)))
      p0015
  have p0017 :=
    @g_simpld
      (syn_wbr (.cv z) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.cv x))
      (syn_wbr (.cv z) R (.cv x))
      (syn_wbr (.cv z) (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (.cv x))
      p0016
  have p0018 :=
    @g_syl
      (.classMem (.cv z) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      (syn_wbr (.cv z) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.cv x))
      (syn_wbr (.cv z) R (.cv x)) p0014 p0017
  have p0022 :=
    @g_simprd
      (.classMem (.cv z) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      (syn_wbr (.cv z) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.cv x))
      (syn_wne (.cv z) (.cv x)) p0013
  have p0023 :=
    @g_jca
      (.classMem (.cv z) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x)) p0018 p0022
  have p0024 :=
    @g_jca
      (.classMem (.cv z) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      (.classMem (.cv z) D) (syn_wa (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x)))
      p0010 p0023
  have p0025 := @g_elstrictseg x z D R
  have p0026 :=
    @g_biimpri
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv z) D)
        (syn_wa (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x))))
      p0025
  have p0027 :=
    @g_syl
      (.classMem (.cv z) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv z) D)
        (syn_wa (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x))))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0024 p0026
  have p0028 :=
    @g_a1i
      (.imp (.classMem (.cv z) (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0027
  have p0029 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0030 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0031 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) p0029 p0030
  have p0033 :=
    @g_simpr (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0034 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0029 p0033
  have p0035 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0037 :=
    @g_biimpi
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv z) D)
        (syn_wa (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x))))
      p0025
  have p0038 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv z) D)
        (syn_wa (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x))))
      p0035 p0037
  have p0039 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classMem (.cv z) D) (syn_wa (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x)))
      p0038
  have p0040 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (.classMem (.cv z) D) p0034 p0039
  have p0045 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classMem (.cv z) D) (syn_wa (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x)))
      p0038
  have p0046 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x)) p0045
  have p0047 :=
    @g_n_3jca
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D))
      (syn_wa (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
        (.classMem (.cv z) D))
      (syn_wbr (.cv z) R (.cv x)) p0031 p0040 p0046
  have p0048 := @g_strictsegdown y x z D R
  have p0049 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wa (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
          (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv x)))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0047 p0048
  have p0080 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0049 p0034
  have p0081 :=
    @g_brinxp (.cv z) (.cv x)
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) R
  have p0082 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
        (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wb (syn_wbr (.cv z) R (.cv x)) (syn_wbr (.cv z) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.cv x)))
      p0080 p0081
  have p0083 :=
    @g_biimpd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wbr (.cv z) R (.cv x))
      (syn_wbr (.cv z) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.cv x))
      p0082
  have p0084 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wbr (.cv z) R (.cv x))
      (syn_wbr (.cv z) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.cv x))
      p0046 p0083
  have p0090 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x)) p0045
  have p0091 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wbr (.cv z) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.cv x))
      (syn_wne (.cv z) (.cv x)) p0084 p0090
  have p0092 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wa (syn_wbr (.cv z) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.cv x)) (syn_wne (.cv z) (.cv x)))
      p0049 p0091
  have p0094 :=
    @g_biimpri
      (.classMem (.cv z) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_wa
          (syn_wbr (.cv z) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (.cv x)) (syn_wne (.cv z) (.cv x))))
      p0005
  have p0095 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_wa
          (syn_wbr (.cv z) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (.cv x)) (syn_wne (.cv z) (.cv x))))
      (.classMem (.cv z) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      p0092 p0094
  have p0096 :=
    @g_ex
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (.classMem (.cv z) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      p0095
  have p0097 :=
    @g_impbid
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (.cv z) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0028 p0096
  have p0098 :=
    @g_eqrdv
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      z
      (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0097
  have p0099 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem H (syn_cvv)))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0004 p0098
  have p0196 :=
    @g_xpeq12d
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem H (syn_cvv)))
      (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0099
      p0099
  have p0197 :=
    @g_ineq2d
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem H (syn_cvv)))
      (syn_cxp (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0196
  have p0294 :=
    @g_eqcomd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem H (syn_cvv)))
      (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0099
  have p0295 :=
    @g_inss1 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cid))) (syn_csn (.cv x)))
  have p0296 :=
    @g_a1i
      (syn_wss (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem H (syn_cvv)))
      p0295
  have p0297 :=
    @g_eqsstrd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem H (syn_cvv)))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) p0294
      p0296
  have p0298 := @g_strictsegrestrnest x y D R
  have p0299 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem H (syn_cvv)))
      (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (.classEq (syn_cin (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      p0297 p0298
  have p0300 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem H (syn_cvv)))
      (syn_cin (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cxp (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x)))) (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      p0197 p0299
  have p0301 :=
    @g_isoeq3 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cid))) (syn_csn (.cv x))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_cin (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cxp (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x)))) (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_ccnv H)
  have p0302 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem H (syn_cvv)))
      (.classEq (syn_cin (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cxp (syn_cin
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wb (syn_wiso (syn_ccnv H) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cxp (syn_cin
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                            (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                              (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                            (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                              (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x))))) (syn_wiso (syn_ccnv H) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x))))))
      p0300 p0301
  have p0399 :=
    @g_isoeq5 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_ccnv H)
  have p0400 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem H (syn_cvv)))
      (.classEq (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wb (syn_wiso (syn_ccnv H) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x))))) (syn_wiso (syn_ccnv H) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      p0099 p0399
  have p0401 :=
    @g_bitrd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem H (syn_cvv)))
      (syn_wiso (syn_ccnv H) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cxp (syn_cin
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      (syn_wiso (syn_ccnv H) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      (syn_wiso (syn_ccnv H) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0302 p0400
  have p0402 :=
    @g_biimprd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem H (syn_cvv)))
      (syn_wiso (syn_ccnv H) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cxp (syn_cin
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      (syn_wiso (syn_ccnv H) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0401
  have p0403 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem H (syn_cvv)))
      (.imp (syn_wiso (syn_ccnv H) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_wiso (syn_ccnv H) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cxp (syn_cin
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                            (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                              (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                            (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                              (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x))))))
      p0003 p0402
  have p0404 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wiso (syn_ccnv H) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wiso (syn_ccnv H) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cxp (syn_cin
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      p0002 p0403
  have p0408 := @g_westrsegndv y D R
  have p0409 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D))
      (syn_wbr (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cwe) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0030 p0408
  have p0410 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem H (syn_cvv)))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wbr (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cwe) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0004 p0409
  have p0413 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem H (syn_cvv)))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0004 p0033
  have p0414 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem H (syn_cvv)))
      (syn_wbr (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cwe) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0410 p0413
  have p0415 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem H (syn_cvv))
  have p0416 := @g_cnvexg H (syn_cvv)
  have p0417 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem H (syn_cvv)))
      (.classMem H (syn_cvv)) (.classMem (syn_ccnv H) (syn_cvv)) p0415 p0416
  have p0418 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem H (syn_cvv)))
      (syn_wa (syn_wbr (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cwe) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
        (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (syn_ccnv H) (syn_cvv)) p0414 p0417
  have p0419 :=
    @g_strictsegnoiso x
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_ccnv H)
  have p0420 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem H (syn_cvv)))
      (syn_wa (syn_wa (syn_wbr (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cwe)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
          (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (syn_ccnv H) (syn_cvv)))
      (.neg (syn_wiso (syn_ccnv H) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cxp (syn_cin
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                            (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                              (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                            (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                              (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x))))))
      p0418 p0419
  have p0421 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem H (syn_cvv)))
      (.neg (syn_wiso (syn_ccnv H) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cxp (syn_cin
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                            (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                              (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                            (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                              (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x))))))
      p0003 p0420
  have p0422 :=
    @g_pm2_21dd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D))
            (.classMem (.cv x)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wiso (syn_ccnv H) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cxp (syn_cin
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      (.neg (syn_wiso H (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0404 p0421
  have p0423 :=
    @g_pm2_01da
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem H (syn_cvv)))
      (syn_wiso H (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
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

@[expose]
noncomputable def g_strictseghwnisono (x : Var) (y : Var) (D : Class) (R : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.neg
          (syn_wbr (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D
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
      ((syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))).fv :=
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
      ((syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))).fv :=
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
      ((syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))).fv :=
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
    @g_simpr
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wbr (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
  have p0002 :=
    @g_brex
      (syn_cop (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_cop (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_chwniso D)
  have p0003 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wbr (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      (syn_wbr (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (.classMem (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_cvv)) (.classMem (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
          (syn_cvv)))
      p0000 p0002
  have p0004 :=
    @g_hwnisohwisocl D
      (syn_cop (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_cop (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0005 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wbr (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      (syn_wa (.classMem (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_cvv)) (.classMem (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
          (syn_cvv)))
      (.imp (syn_wbr (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wbr (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_chwiso D) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      p0003 p0004
  have p0006 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wbr (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      (syn_wbr (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wbr (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_chwiso D) (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0000 p0005
  have p0010 :=
    @g_hwisowitnesscl D
      (syn_cop (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_cop (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      z dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0011 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wbr (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      (syn_wa (.classMem (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_cvv)) (.classMem (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
          (syn_cvv)))
      (.imp (syn_wbr (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_chwiso D) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wex z (syn_wiso (.cv z) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))))
      p0003 p0010
  have p0012 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wbr (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      (syn_wbr (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_chwiso D) (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wex z (syn_wiso (.cv z) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))))
      p0006 p0011
  have p0013 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wbr (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
  have p0014 :=
    @g_nfv
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      z dv_cache_0004
  have p0015 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0016 := @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)
  have p0017 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wbr R (syn_cwe) D) p0015
      p0016
  have p0018 := @g_brex R D (syn_cwe)
  have p0019 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv)))
      p0017 p0018
  have p0020 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0019
  have p0026 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0019
  have p0033 := @g_idex
  have p0034 :=
    @g_a1i (.classMem (syn_cid) (syn_cvv))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0033
  have p0035 :=
    @g_jca
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem R (syn_cvv)) (.classMem (syn_cid) (syn_cvv)) p0020 p0034
  have p0036 := @g_difexg R (syn_cid) (syn_cvv) (syn_cvv)
  have p0037 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (.classMem R (syn_cvv)) (.classMem (syn_cid) (syn_cvv)))
      (.classMem (syn_cdif R (syn_cid)) (syn_cvv)) p0035 p0036
  have p0038 := @g_cnvexg (syn_cdif R (syn_cid)) (syn_cvv)
  have p0039 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (syn_cdif R (syn_cid)) (syn_cvv))
      (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) p0037 p0038
  have p0040 := @g_snex (.cv x)
  have p0041 :=
    @g_a1i (.classMem (syn_csn (.cv x)) (syn_cvv))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0040
  have p0042 :=
    @g_jca
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv))
      (.classMem (syn_csn (.cv x)) (syn_cvv)) p0039 p0041
  have p0043 :=
    @g_imaexg (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) (syn_cvv) (syn_cvv)
  have p0044 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv))
        (.classMem (syn_csn (.cv x)) (syn_cvv)))
      (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv))
      p0042 p0043
  have p0045 :=
    @g_jca
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem D (syn_cvv))
      (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv))
      p0026 p0044
  have p0046 :=
    @g_inexg D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv)
      (syn_cvv)
  have p0047 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (.classMem D (syn_cvv))
        (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv)))
      (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cvv))
      p0045 p0046
  have p0075 :=
    @g_jca
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cvv))
      (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cvv))
      p0047 p0047
  have p0076 :=
    @g_xpexg (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv)
      (syn_cvv)
  have p0077 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (.classMem
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv))
        (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cvv)))
      (.classMem (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cvv))
      p0075 p0076
  have p0078 :=
    @g_jca
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem R (syn_cvv))
      (.classMem (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cvv))
      p0020 p0077
  have p0079 :=
    @g_inexg R
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_cvv) (syn_cvv)
  have p0080 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (.classMem R (syn_cvv)) (.classMem (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_cvv)))
      (.classMem (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cvv))
      p0078 p0079
  have p0108 :=
    @g_jca
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cvv))
      (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cvv))
      p0080 p0047
  have p0109 :=
    @g_opfvscl
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
  have p0110 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (.classMem (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cvv)) (.classMem
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv)))
      (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
        (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      p0108 p0109
  have p0111 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0110
  have p0112 :=
    @g_isoeq2
      (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.cv z)
  have p0113 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wb (syn_wiso (.cv z) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
        (syn_wiso (.cv z) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))))
      p0111 p0112
  have p0139 := @g_snex (.cv y)
  have p0140 :=
    @g_a1i (.classMem (syn_csn (.cv y)) (syn_cvv))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0139
  have p0141 :=
    @g_jca
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv))
      (.classMem (syn_csn (.cv y)) (syn_cvv)) p0039 p0140
  have p0142 :=
    @g_imaexg (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)) (syn_cvv) (syn_cvv)
  have p0143 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv))
        (.classMem (syn_csn (.cv y)) (syn_cvv)))
      (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) (syn_cvv))
      p0141 p0142
  have p0144 :=
    @g_jca
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem D (syn_cvv))
      (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) (syn_cvv))
      p0026 p0143
  have p0145 :=
    @g_inexg D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) (syn_cvv)
      (syn_cvv)
  have p0146 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (.classMem D (syn_cvv))
        (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) (syn_cvv)))
      (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cvv))
      p0144 p0145
  have p0174 :=
    @g_jca
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cvv))
      (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cvv))
      p0146 p0146
  have p0175 :=
    @g_xpexg (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cvv)
      (syn_cvv)
  have p0176 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (.classMem
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cvv))
        (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cvv)))
      (.classMem (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_cvv))
      p0174 p0175
  have p0177 :=
    @g_jca
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem R (syn_cvv))
      (.classMem (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_cvv))
      p0020 p0176
  have p0178 :=
    @g_inexg R
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_cvv) (syn_cvv)
  have p0179 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (.classMem R (syn_cvv)) (.classMem (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
          (syn_cvv)))
      (.classMem (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cvv))
      p0177 p0178
  have p0207 :=
    @g_jca
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cvv))
      (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cvv))
      p0179 p0146
  have p0208 :=
    @g_opfvscl
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
  have p0209 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (.classMem (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cvv)) (.classMem
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cvv)))
      (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
        (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0207 p0208
  have p0210 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0209
  have p0211 :=
    @g_isoeq3
      (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.cv z)
  have p0212 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      (syn_wb (syn_wiso (.cv z) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
        (syn_wiso (.cv z) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))))
      p0210 p0211
  have p0213 :=
    @g_bitrd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wiso (.cv z) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      (syn_wiso (.cv z) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      (syn_wiso (.cv z) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      p0113 p0212
  have p0310 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0110
  have p0311 :=
    @g_isoeq4
      (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.cv z)
  have p0312 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wb (syn_wiso (.cv z) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
        (syn_wiso (.cv z) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))))
      p0310 p0311
  have p0313 :=
    @g_bitrd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wiso (.cv z) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      (syn_wiso (.cv z) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      (syn_wiso (.cv z) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      p0213 p0312
  have p0410 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0209
  have p0411 :=
    @g_isoeq5 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.cv z)
  have p0412 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wb (syn_wiso (.cv z) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
        (syn_wiso (.cv z) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0410 p0411
  have p0413 :=
    @g_bitrd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wiso (.cv z) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      (syn_wiso (.cv z) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      (syn_wiso (.cv z) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0313 p0412
  have p0414 :=
    @g_biimpd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wiso (.cv z) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      (syn_wiso (.cv z) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0413
  have p0415 :=
    @g_eximd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wiso (.cv z) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      (syn_wiso (.cv z) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      z p0014 p0414
  have p0416 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wbr (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.imp (syn_wex z (syn_wiso (.cv z) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))))
        (syn_wex z (syn_wiso (.cv z) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      p0013 p0415
  have p0417 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wbr (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      (syn_wex z (syn_wiso (.cv z) (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))))
      (syn_wex z (syn_wiso (.cv z) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0012 p0416
  have p0419 :=
    @g_id
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
  have p0420 := @g_vex z
  have p0421 :=
    @g_a1i (.classMem (.cv z) (syn_cvv))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0420
  have p0422 :=
    @g_jca
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (.cv z) (syn_cvv)) p0419 p0421
  have p0423 := @g_strictsegltnoiso x y D R (.cv z)
  have p0424 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv z) (syn_cvv)))
      (.neg (syn_wiso (.cv z) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0422 p0423
  have p0425 :=
    @g_nexdv
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wiso (.cv z) (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      z dv_cache_0004 p0424
  have p0426 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wbr (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.neg (syn_wex z (syn_wiso (.cv z) (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      p0013 p0425
  have p0427 :=
    @g_pm2_21dd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_wbr (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      (syn_wex z (syn_wiso (.cv z) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.neg (syn_wbr (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      p0417 p0426
  have p0428 :=
    @g_pm2_01da
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wbr (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
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

@[expose]
noncomputable def g_hnwcutcodeeq3 (A : Class) (B : Class) (D : Class) (R : Class)
    (_dv_A_R : Disjoint A.fv R.fv) :
    Nominal.NPrf
      (.imp (.classEq A B) (.classEq (syn_chnwcutcode R D A) (syn_chnwcutcode R D B))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chnwcutcode R D A))
  have p0001 :=
    @g_a1i
      (.classEq (syn_chnwcutcode R D A) (syn_cop (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A)))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A)))))
      (.classEq A B) p0000
  have p0002 := @g_sneq A B
  have p0003 :=
    @g_imaeq2d (.classEq A B) (syn_csn A) (syn_csn B) (syn_ccnv (syn_cdif R (syn_cid)))
      p0002
  have p0004 :=
    @g_ineq2d (.classEq A B) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A))
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)) D p0003
  have p0008 :=
    @g_xpeq12d (.classEq A B)
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A)))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A)))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) p0004 p0004
  have p0009 :=
    @g_ineq2d (.classEq A B)
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A))))
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))
      R p0008
  have p0013 :=
    @g_opeq12d (.classEq A B)
      (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A)))))
      (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A)))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) p0009 p0004
  have p0014 :=
    @g_eqtrd (.classEq A B) (syn_chnwcutcode R D A)
      (syn_cop (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A)))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A))))
      (syn_cop (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))
      p0001 p0013
  have p0015 := (Nominal.classEqRefl (syn_chnwcutcode R D B))
  have p0016 :=
    @g_eqcomi (syn_chnwcutcode R D B)
      (syn_cop (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))
      p0015
  have p0017 :=
    @g_a1i
      (.classEq (syn_cop (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))
        (syn_chnwcutcode R D B))
      (.classEq A B) p0016
  have p0018 :=
    @g_eqtrd (.classEq A B) (syn_chnwcutcode R D A)
      (syn_cop (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))
      (syn_chnwcutcode R D B) p0014 p0017
  exact p0018

@[expose]
noncomputable def g_elhwcncl (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (.classMem B (syn_cvv)) (syn_wb (.classMem B (syn_chwcn A))
          (syn_wa (.classMem B (syn_chwcodes A)) (syn_wss (syn_cfv (syn_c1st) B)
              (syn_cxp (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) B)))))) :=
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
      ((syn_wb (.classMem B (syn_chwcn A)) (syn_wa (.classMem B (syn_chwcodes A))
            (syn_wss (syn_cfv (syn_c1st) B)
              (syn_cxp (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) B)))))).fv :=
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
  have p0000 := @g_eleq1 (.cv u) B (syn_chwcn A)
  have p0001 := @g_eleq1 (.cv u) B (syn_chwcodes A)
  have p0002 := @g_fveq2 (.cv u) B (syn_c1st)
  have p0003 := @g_fveq2 (.cv u) B (syn_c2nd)
  have p0005 :=
    @g_xpeq12d (.classEq (.cv u) B) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) B)
      (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) B) p0003 p0003
  have p0006 :=
    @g_sseq12d (.classEq (.cv u) B) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) B)
      (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_cxp (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) B)) p0002 p0005
  have p0007 :=
    @g_anbi12d (.classEq (.cv u) B) (.classMem (.cv u) (syn_chwcodes A))
      (.classMem B (syn_chwcodes A))
      (syn_wss (syn_cfv (syn_c1st) (.cv u))
        (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wss (syn_cfv (syn_c1st) B) (syn_cxp (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) B)))
      p0001 p0006
  have p0008 :=
    @g_bibi12d (.classEq (.cv u) B) (.classMem (.cv u) (syn_chwcn A))
      (.classMem B (syn_chwcn A))
      (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (syn_wss (syn_cfv (syn_c1st) (.cv u))
          (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (.classMem B (syn_chwcodes A)) (syn_wss (syn_cfv (syn_c1st) B)
          (syn_cxp (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) B))))
      p0000 p0007
  have p0009 := @g_elhwcn u A
  have p0010 :=
    @g_vtoclg
      (syn_wb (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv u) (syn_chwcodes A))
          (syn_wss (syn_cfv (syn_c1st) (.cv u))
            (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wb (.classMem B (syn_chwcn A)) (syn_wa (.classMem B (syn_chwcodes A))
          (syn_wss (syn_cfv (syn_c1st) B)
            (syn_cxp (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) B)))))
      u B (syn_cvv) dv_cache_0001 dv_cache_0002 p0008 p0009
  exact p0010

@[expose]
noncomputable def g_hwnisoclasselhnordcl (A : Class) (B : Class)
    (hyp_hwnisoclasselhnordcl_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem B (syn_chwcn A))
        (.classMem (syn_cec B (syn_chwniso A)) (syn_chnord A))) :=
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
      ((Wff.imp (.classMem B (syn_chwcn A))
          (.classMem (syn_cec B (syn_chwniso A)) (syn_chnord A)))).fv :=
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
  have p0000 := @g_elex B (syn_chwcn A)
  have p0001 := @g_eleq1 (.cv u) B (syn_chwcn A)
  have p0002 := @g_eceq1 (.cv u) B (syn_chwniso A)
  have p0003 :=
    @g_eleq1d (.classEq (.cv u) B) (syn_cec (.cv u) (syn_chwniso A))
      (syn_cec B (syn_chwniso A)) (syn_chnord A) p0002
  have p0004 :=
    @g_imbi12d (.classEq (.cv u) B) (.classMem (.cv u) (syn_chwcn A))
      (.classMem B (syn_chwcn A))
      (.classMem (syn_cec (.cv u) (syn_chwniso A)) (syn_chnord A))
      (.classMem (syn_cec B (syn_chwniso A)) (syn_chnord A)) p0001 p0003
  have p0005 := @g_hwnisoclasselhnord u A dv_cache_0001 hyp_hwnisoclasselhnordcl_1
  have p0006 :=
    @g_vtoclg
      (.imp (.classMem (.cv u) (syn_chwcn A))
        (.classMem (syn_cec (.cv u) (syn_chwniso A)) (syn_chnord A)))
      (.imp (.classMem B (syn_chwcn A)) (.classMem (syn_cec B (syn_chwniso A)) (syn_chnord A)))
      u B (syn_cvv) dv_cache_0002 dv_cache_0003 p0004 p0005
  have p0007 :=
    @g_mpcom (.classMem B (syn_cvv)) (.classMem B (syn_chwcn A))
      (.classMem (syn_cec B (syn_chwniso A)) (syn_chnord A)) p0000 p0006
  exact p0007

@[expose]
noncomputable def g_pw12argcl (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (.classMem B (syn_cpw1 (syn_cpw1 C))) (syn_wa (.classMem (syn_cuni (syn_cuni B)) C)
          (.classEq B (syn_csn (syn_csn (syn_cuni (syn_cuni B))))))) :=
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
      ((Wff.imp (.classMem B (syn_cpw1 (syn_cpw1 C)))
          (syn_wa (.classMem (syn_cuni (syn_cuni B)) C)
            (.classEq B (syn_csn (syn_csn (syn_cuni (syn_cuni B)))))))).fv :=
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
  have p0000 := @g_elex B (syn_cpw1 (syn_cpw1 C))
  have p0001 := @g_eleq1 (.cv x) B (syn_cpw1 (syn_cpw1 C))
  have p0002 := @g_unieq (.cv x) B
  have p0003 := @g_unieqd (.classEq (.cv x) B) (syn_cuni (.cv x)) (syn_cuni B) p0002
  have p0004 :=
    @g_eleq1d (.classEq (.cv x) B) (syn_cuni (syn_cuni (.cv x))) (syn_cuni (syn_cuni B)) C
      p0003
  have p0005 := @g_id (.classEq (.cv x) B)
  have p0008 :=
    @g_sneqd (.classEq (.cv x) B) (syn_cuni (syn_cuni (.cv x))) (syn_cuni (syn_cuni B))
      p0003
  have p0009 :=
    @g_sneqd (.classEq (.cv x) B) (syn_csn (syn_cuni (syn_cuni (.cv x))))
      (syn_csn (syn_cuni (syn_cuni B))) p0008
  have p0010 :=
    @g_eqeq12d (.classEq (.cv x) B) (.cv x) B
      (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv x)))))
      (syn_csn (syn_csn (syn_cuni (syn_cuni B)))) p0005 p0009
  have p0011 :=
    @g_anbi12d (.classEq (.cv x) B) (.classMem (syn_cuni (syn_cuni (.cv x))) C)
      (.classMem (syn_cuni (syn_cuni B)) C)
      (.classEq (.cv x) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv x))))))
      (.classEq B (syn_csn (syn_csn (syn_cuni (syn_cuni B))))) p0004 p0010
  have p0012 :=
    @g_imbi12d (.classEq (.cv x) B) (.classMem (.cv x) (syn_cpw1 (syn_cpw1 C)))
      (.classMem B (syn_cpw1 (syn_cpw1 C)))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv x))) C)
        (.classEq (.cv x) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv x)))))))
      (syn_wa (.classMem (syn_cuni (syn_cuni B)) C)
        (.classEq B (syn_csn (syn_csn (syn_cuni (syn_cuni B))))))
      p0001 p0011
  have p0013 := @g_fdcolcodearg C x dv_cache_0001
  have p0014 :=
    @g_vtoclg
      (.imp (.classMem (.cv x) (syn_cpw1 (syn_cpw1 C)))
        (syn_wa (.classMem (syn_cuni (syn_cuni (.cv x))) C)
          (.classEq (.cv x) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv x))))))))
      (.imp (.classMem B (syn_cpw1 (syn_cpw1 C))) (syn_wa (.classMem (syn_cuni (syn_cuni B)) C)
          (.classEq B (syn_csn (syn_csn (syn_cuni (syn_cuni B)))))))
      x B (syn_cvv) dv_cache_0002 dv_cache_0003 p0012 p0013
  have p0015 :=
    @g_mpcom (.classMem B (syn_cvv)) (.classMem B (syn_cpw1 (syn_cpw1 C)))
      (syn_wa (.classMem (syn_cuni (syn_cuni B)) C)
        (.classEq B (syn_csn (syn_csn (syn_cuni (syn_cuni B))))))
      p0000 p0014
  exact p0015

@[expose]
noncomputable def g_hnwcutcodecn (x : Var) (D : Class) (R : Class)
    (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutcodecn_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (.classMem (.cv x) D) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D))) :=
  by
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have p0000 := @g_a1i (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D) hyp_hnwcutcodecn_1
  have p0001 := @g_id (.classMem (.cv x) D)
  have p0002 :=
    @g_jca (.classMem (.cv x) D) (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D) p0000 p0001
  have p0003 := @g_westrseg x D R dv_cache_0001
  have p0004 :=
    @g_syl (.classMem (.cv x) D) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D))
      (syn_wbr (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cwe) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0002 p0003
  have p0005 :=
    (Nominal.biimpRefl (syn_wbr (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cwe) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
  have p0006 :=
    @g_biimpi
      (syn_wbr (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cwe) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (.classMem (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cwe))
      p0005
  have p0007 :=
    @g_syl (.classMem (.cv x) D)
      (syn_wbr (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cwe) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (.classMem (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cwe))
      p0004 p0006
  have p0008 := @g_brex R D (syn_cwe)
  have p0009 :=
    @g_simpld (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
      p0008
  have p0010 := Nominal.mp hyp_hnwcutcodecn_1 p0009
  have p0012 :=
    @g_simprd (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
      p0008
  have p0013 := Nominal.mp hyp_hnwcutcodecn_1 p0012
  have p0017 := @g_idex
  have p0018 := @g_difex R (syn_cid) p0010 p0017
  have p0019 := @g_cnvex (syn_cdif R (syn_cid)) p0018
  have p0020 := @g_snex (.cv x)
  have p0021 := @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) p0019 p0020
  have p0022 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0013 p0021
  have p0035 :=
    @g_xpex (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0022
      p0022
  have p0036 :=
    @g_inex R
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0010 p0035
  have p0037 := @g_inss1 D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0050 :=
    @g_elpw (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) D
      p0022
  have p0051 :=
    @g_mpbir
      (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cpw D))
      (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) D)
      p0037 p0050
  have p0052 :=
    @g_pm3_2i
      (.classMem (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cvv))
      (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cpw D))
      p0036 p0051
  have p0053 :=
    @g_opelxp
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv)
      (syn_cpw D)
  have p0054 :=
    @g_mpbir
      (.classMem (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_cxp (syn_cvv) (syn_cpw D)))
      (syn_wa (.classMem (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cvv)) (.classMem
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cpw D)))
      p0052 p0053
  have p0055 :=
    @g_a1i
      (.classMem (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_cxp (syn_cvv) (syn_cpw D)))
      (.classMem (.cv x) D) p0054
  have p0056 :=
    @g_jca (.classMem (.cv x) D)
      (.classMem (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cwe))
      (.classMem (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_cxp (syn_cvv) (syn_cpw D)))
      p0007 p0055
  have p0057 :=
    @g_elin
      (syn_cop (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw D))
  have p0058 :=
    @g_a1i
      (syn_wb (.classMem (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw D)))) (syn_wa (.classMem (syn_cop
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (syn_cwe)) (.classMem (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (syn_cxp (syn_cvv) (syn_cpw D)))))
      (.classMem (.cv x) D) p0057
  have p0059 :=
    @g_mpbird (.classMem (.cv x) D)
      (.classMem (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw D))))
      (syn_wa (.classMem (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_cwe)) (.classMem (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_cxp (syn_cvv) (syn_cpw D))))
      p0056 p0058
  have p0060 := (Nominal.classEqRefl (syn_chwcodes D))
  have p0061 :=
    @g_eleq2i (syn_chwcodes D) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw D)))
      (syn_cop (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0060
  have p0062 :=
    @g_sylibr (.classMem (.cv x) D)
      (.classMem (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw D))))
      (.classMem (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_chwcodes D))
      p0059 p0061
  have p0063 :=
    @g_inss2 R
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0105 :=
    @g_opfv2nd
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0036
      p0022
  have p0148 :=
    @g_pm3_2i
      (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0105 p0105
  have p0149 :=
    @g_xpeq12
      (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
  have p0150 := Nominal.mp p0148 p0149
  have p0151 :=
    @g_eqcomi
      (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0150
  have p0152 :=
    @g_sseq2
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
  have p0153 := Nominal.mp p0151 p0152
  have p0154 :=
    @g_mpbi
      (syn_wss (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wss (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      p0063 p0153
  have p0196 :=
    @g_opfv1st
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0036
      p0022
  have p0197 :=
    @g_sseq1
      (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
  have p0198 := Nominal.mp p0196 p0197
  have p0199 :=
    @g_mpbir
      (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      (syn_wss (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      p0154 p0198
  have p0200 :=
    @g_a1i
      (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      (.classMem (.cv x) D) p0199
  have p0201 :=
    @g_jca (.classMem (.cv x) D)
      (.classMem (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_chwcodes D))
      (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      p0062 p0200
  have p0243 :=
    @g_opex
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0036
      p0022
  have p0244 :=
    @g_elhwcncl D
      (syn_cop (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0245 := Nominal.mp p0243 p0244
  have p0246 :=
    @g_a1i
      (syn_wb (.classMem (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_chwcn D)) (syn_wa (.classMem (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (syn_chwcodes D)) (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
              (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                  (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))))
      (.classMem (.cv x) D) p0245
  have p0247 :=
    @g_mpbird (.classMem (.cv x) D)
      (.classMem (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_chwcn D))
      (syn_wa (.classMem (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_chwcodes D)) (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))))
      p0201 p0246
  have p0248 := (Nominal.classEqRefl (syn_chnwcutcode R D (.cv x)))
  have p0249 :=
    @g_eleq1i (syn_chnwcutcode R D (.cv x))
      (syn_cop (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_chwcn D) p0248
  have p0250 :=
    @g_sylibr (.classMem (.cv x) D)
      (.classMem (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_chwcn D))
      (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D)) p0247 p0249
  exact p0250

@[expose]
noncomputable def g_hnwcutclassord (x : Var) (D : Class) (R : Class)
    (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutclassord_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (.classMem (.cv x) D)
        (.classMem (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_chnord D))) :=
  by
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have p0000 := @g_hnwcutcodecn x D R dv_cache_0001 hyp_hnwcutclassord_1
  have p0001 := @g_brex R D (syn_cwe)
  have p0002 :=
    @g_simprd (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
      p0001
  have p0003 := Nominal.mp hyp_hnwcutclassord_1 p0002
  have p0004 := @g_hwnisoclasselhnordcl D (syn_chnwcutcode R D (.cv x)) p0003
  have p0005 :=
    @g_syl (.classMem (.cv x) D) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D))
      (.classMem (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_chnord D))
      p0000 p0004
  exact p0005


end NFChoice.DirectNominalPrf.WPPReplay

end
