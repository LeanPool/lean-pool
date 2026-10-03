/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk015Compact001Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk015Compact001Part007`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_brlnqordkern (C : Class) (R : Class) (X : Class) (Y : Class)
    (_dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem R (syn_cvv)) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))) (syn_wb
          (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqord R C) (syn_cec Y (syn_clnker R)))
          (syn_wbr X R Y))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_clnqord R C))
  have p0001 :=
    @g_breqi (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)) (syn_clnqord R C)
      (syn_cin (syn_clnqrel R) (syn_cxp (syn_clnquo R C) (syn_clnquo R C))) p0000
  have p0002 :=
    @g_brin (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)) (syn_clnqrel R)
      (syn_cxp (syn_clnquo R C) (syn_clnquo R C))
  have p0003 :=
    @g_bitri
      (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqord R C) (syn_cec Y (syn_clnker R)))
      (syn_wbr (syn_cec X (syn_clnker R))
        (syn_cin (syn_clnqrel R) (syn_cxp (syn_clnquo R C) (syn_clnquo R C)))
        (syn_cec Y (syn_clnker R)))
      (syn_wa (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqrel R) (syn_cec Y (syn_clnker R)))
        (syn_wbr (syn_cec X (syn_clnker R)) (syn_cxp (syn_clnquo R C) (syn_clnquo R C))
          (syn_cec Y (syn_clnker R))))
      p0001 p0002
  have p0004 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqord R C) (syn_cec Y (syn_clnker R)))
        (syn_wa (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqrel R) (syn_cec Y (syn_clnker R)))
          (syn_wbr (syn_cec X (syn_clnker R)) (syn_cxp (syn_clnquo R C) (syn_clnquo R C))
            (syn_cec Y (syn_clnker R)))))
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))))
      p0003
  have p0005 :=
    @g_simpl (.classMem R (syn_cvv))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
  have p0006 := @g_lnkerexg R
  have p0007 :=
    @g_syl
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))))
      (.classMem R (syn_cvv)) (.classMem (syn_clnker R) (syn_cvv)) p0005 p0006
  have p0008 :=
    @g_simpr (.classMem R (syn_cvv))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
  have p0009 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wss R (syn_cxp C C)))
      (syn_wa (.classMem X C) (.classMem Y C))
  have p0010 :=
    @g_syl
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (.classMem X C) (.classMem Y C)) p0008 p0009
  have p0011 := @g_simpl (.classMem X C) (.classMem Y C)
  have p0012 :=
    @g_syl
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))))
      (syn_wa (.classMem X C) (.classMem Y C)) (.classMem X C) p0010 p0011
  have p0013 :=
    @g_jca
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))))
      (.classMem (syn_clnker R) (syn_cvv)) (.classMem X C) p0007 p0012
  have p0014 := @g_ecelqsg C X (syn_clnker R) (syn_cvv)
  have p0015 :=
    @g_syl
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))))
      (syn_wa (.classMem (syn_clnker R) (syn_cvv)) (.classMem X C))
      (.classMem (syn_cec X (syn_clnker R)) (syn_cqs C (syn_clnker R))) p0013 p0014
  have p0016 := (Nominal.classEqRefl (syn_clnquo R C))
  have p0017 :=
    @g_syl6eleqr
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))))
      (syn_cec X (syn_clnker R)) (syn_cqs C (syn_clnker R)) (syn_clnquo R C) p0015 p0016
  have p0024 := @g_simpr (.classMem X C) (.classMem Y C)
  have p0025 :=
    @g_syl
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))))
      (syn_wa (.classMem X C) (.classMem Y C)) (.classMem Y C) p0010 p0024
  have p0026 :=
    @g_jca
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))))
      (.classMem (syn_clnker R) (syn_cvv)) (.classMem Y C) p0007 p0025
  have p0027 := @g_ecelqsg C Y (syn_clnker R) (syn_cvv)
  have p0028 :=
    @g_syl
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))))
      (syn_wa (.classMem (syn_clnker R) (syn_cvv)) (.classMem Y C))
      (.classMem (syn_cec Y (syn_clnker R)) (syn_cqs C (syn_clnker R))) p0026 p0027
  have p0030 :=
    @g_syl6eleqr
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))))
      (syn_cec Y (syn_clnker R)) (syn_cqs C (syn_clnker R)) (syn_clnquo R C) p0028 p0016
  have p0031 :=
    @g_jca
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))))
      (.classMem (syn_cec X (syn_clnker R)) (syn_clnquo R C))
      (.classMem (syn_cec Y (syn_clnker R)) (syn_clnquo R C)) p0017 p0030
  have p0032 :=
    @g_brxp (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)) (syn_clnquo R C)
      (syn_clnquo R C)
  have p0033 :=
    @g_sylibr
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))))
      (syn_wa (.classMem (syn_cec X (syn_clnker R)) (syn_clnquo R C))
        (.classMem (syn_cec Y (syn_clnker R)) (syn_clnquo R C)))
      (syn_wbr (syn_cec X (syn_clnker R)) (syn_cxp (syn_clnquo R C) (syn_clnquo R C))
        (syn_cec Y (syn_clnker R)))
      p0031 p0032
  have p0034 :=
    @g_biantrud
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))))
      (syn_wbr (syn_cec X (syn_clnker R)) (syn_cxp (syn_clnquo R C) (syn_clnquo R C))
        (syn_cec Y (syn_clnker R)))
      (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqrel R) (syn_cec Y (syn_clnker R)))
      p0033
  have p0035 :=
    @g_bitr4d
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))))
      (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqord R C) (syn_cec Y (syn_clnker R)))
      (syn_wa (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqrel R) (syn_cec Y (syn_clnker R)))
        (syn_wbr (syn_cec X (syn_clnker R)) (syn_cxp (syn_clnquo R C) (syn_clnquo R C))
          (syn_cec Y (syn_clnker R))))
      (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqrel R) (syn_cec Y (syn_clnker R)))
      p0004 p0034
  have p0036 := @g_brlnqrelkern C R X Y
  have p0037 :=
    @g_bitrd
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))))
      (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqord R C) (syn_cec Y (syn_clnker R)))
      (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqrel R) (syn_cec Y (syn_clnker R)))
      (syn_wbr X R Y) p0035 p0036
  exact p0037

@[expose]
noncomputable def g_lnqordref (C : Class) (R : Class) (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wbr (syn_clnqord R C) (syn_cref) (syn_clnquo R C))) :=
  by
  let proofSupport : Finset Var := C.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_x_ne_u : x ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_x : u ≠ x := Ne.symm fresh_x_ne_u
  have dv_cache_0001 : Disjoint (C).fv (R).fv := by
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0002 : Disjoint (C).fv ((Class.cv x)).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (C).fv ((Class.cv x)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((C).fv) (({ x } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show x ∉ (C).fv from (by exact fresh_x_not_C))))))
  have dv_cache_0003 : u ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_C, not_false_eq_true])
  have dv_cache_0004 : Disjoint ((Class.cv x)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint ((Class.cv x)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ x } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show x ∉ (R).fv from (by exact fresh_x_not_R))))))
  have dv_cache_0005 : u ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_x, not_false_eq_true])
  have dv_cache_0006 : u ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_R, not_false_eq_true])
  have dv_cache_0007 : u ∉ ((syn_wbr (.cv x) (syn_clnqord R C) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_x, fresh_u_not_C, fresh_u_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0008 :
    u ∉
      ((syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (.classMem (.cv x) (syn_clnquo R C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo, Finset.mem_union,
          Finset.mem_singleton, fresh_u_not_R, fresh_u_not_C, fresh_u_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((syn_clnquo R C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo,
          Finset.mem_union, fresh_x_not_C, fresh_x_not_R, or_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((syn_clnqord R C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          Finset.mem_union, fresh_x_not_C, fresh_x_not_R, or_false, not_false_eq_true])
  have dv_cache_0011 :
    x ∉
      ((syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_x_not_R, fresh_x_not_C, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 :=
    @g_simpl (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0001 := @g_lnqordexg C R dv_cache_0001
  have p0002 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (.classMem (syn_clnqord R C) (syn_cvv)) p0000 p0001
  have p0004 := @g_lnquoexg C R dv_cache_0001
  have p0005 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (.classMem (syn_clnquo R C) (syn_cvv)) p0000 p0004
  have p0006 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (.classMem (.cv x) (syn_clnquo R C))
  have p0007 := @g_vex x
  have p0008 :=
    @g_ellnquo u C (.cv x) R dv_cache_0002 dv_cache_0001 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 p0007
  have p0009 :=
    @g_biimpi (.classMem (.cv x) (syn_clnquo R C))
      (syn_wrex u C (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))) p0008
  have p0010 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (.classMem (.cv x) (syn_clnquo R C)))
      (.classMem (.cv x) (syn_clnquo R C))
      (syn_wrex u C (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))) p0006 p0009
  have p0011 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (.classMem (.cv x) (syn_clnquo R C)))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0012 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (.classMem (.cv x) (syn_clnquo R C))
  have p0013 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (.classMem (.cv x) (syn_clnquo R C)))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0011 p0012
  have p0014 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0015 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wss R (syn_cxp C C))
  have p0016 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      p0014 p0015
  have p0017 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wbr R (syn_cconnex) C)
  have p0018 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0016 p0017
  have p0019 := @g_simpl (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)
  have p0020 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wbr R (syn_cref) C) p0018 p0019
  have p0021 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wbr R (syn_cref) C) p0013 p0020
  have p0022 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (.classMem (.cv x) (syn_clnquo R C)))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0023 :=
    @g_simpl (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
  have p0024 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
      (.classMem (.cv u) C) p0022 p0023
  have p0025 :=
    @g_refd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      C R (.cv u) p0021 p0024
  have p0027 :=
    @g_simpr (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
  have p0028 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) p0022 p0027
  have p0032 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) p0028 p0028
  have p0033 :=
    @g_breq12 (.cv x) (syn_cec (.cv u) (syn_clnker R)) (.cv x)
      (syn_cec (.cv u) (syn_clnker R)) (syn_clnqord R C)
  have p0034 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
        (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
      (syn_wb (syn_wbr (.cv x) (syn_clnqord R C) (.cv x))
        (syn_wbr (syn_cec (.cv u) (syn_clnker R)) (syn_clnqord R C)
          (syn_cec (.cv u) (syn_clnker R))))
      p0032 p0033
  have p0039 := @g_simpl (.classMem R (syn_cvv)) (.classMem C (syn_cvv))
  have p0040 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (.classMem R (syn_cvv))
      p0000 p0039
  have p0041 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (.classMem R (syn_cvv)) p0013 p0040
  have p0050 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0013 p0018
  have p0055 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wss R (syn_cxp C C))
  have p0056 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
      (syn_wss R (syn_cxp C C)) p0014 p0055
  have p0057 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wss R (syn_cxp C C)) p0013 p0056
  have p0058 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wss R (syn_cxp C C)) p0050 p0057
  have p0065 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (.classMem (.cv u) C) (.classMem (.cv u) C) p0024 p0024
  have p0066 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wss R (syn_cxp C C)))
      (syn_wa (.classMem (.cv u) C) (.classMem (.cv u) C)) p0058 p0065
  have p0067 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (.classMem R (syn_cvv))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem (.cv u) C) (.classMem (.cv u) C)))
      p0041 p0066
  have p0068 := @g_brlnqordkern C R (.cv u) (.cv u) dv_cache_0001
  have p0069 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem (.cv u) C) (.classMem (.cv u) C))))
      (syn_wb (syn_wbr (syn_cec (.cv u) (syn_clnker R)) (syn_clnqord R C)
          (syn_cec (.cv u) (syn_clnker R))) (syn_wbr (.cv u) R (.cv u)))
      p0067 p0068
  have p0070 :=
    @g_bitrd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wbr (.cv x) (syn_clnqord R C) (.cv x))
      (syn_wbr (syn_cec (.cv u) (syn_clnker R)) (syn_clnqord R C)
        (syn_cec (.cv u) (syn_clnker R)))
      (syn_wbr (.cv u) R (.cv u)) p0034 p0069
  have p0071 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (.classMem (.cv x) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wbr (.cv x) (syn_clnqord R C) (.cv x)) (syn_wbr (.cv u) R (.cv u)) p0025 p0070
  have p0072 :=
    @g_rexlimddv
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (.classMem (.cv x) (syn_clnquo R C)))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
      (syn_wbr (.cv x) (syn_clnqord R C) (.cv x)) u C dv_cache_0007 dv_cache_0008 p0010
      p0071
  have p0073 :=
    @g_refrd
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      x (syn_clnquo R C) (syn_clnqord R C) (syn_cvv) (syn_cvv) dv_cache_0009 dv_cache_0010
      dv_cache_0011 p0002 p0005 p0072
  exact p0073


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part008`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_lnqordtrans (C : Class) (R : Class) (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wbr (syn_clnqord R C) (syn_ctrans) (syn_clnquo R C))) :=
  by
  let proofSupport : Finset Var := C.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let u : Var := freshVar proofSupport 3
  let v : Var := freshVar proofSupport 4
  let w : Var := freshVar proofSupport 5
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_v_not_C : v ∉ C.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (h))
  have fresh_v_not_R : v ∉ R.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_w_not_C : w ∉ C.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (h))
  have fresh_w_not_R : w ∉ R.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_u : x ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_u_ne_x : u ≠ x := Ne.symm fresh_x_ne_u
  have fresh_x_ne_v : x ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_v_ne_x : v ≠ x := Ne.symm fresh_x_ne_v
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_u : y ≠ u :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_u_ne_y : u ≠ y := Ne.symm fresh_y_ne_u
  have fresh_y_ne_v : y ≠ v :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_v_ne_y : v ≠ y := Ne.symm fresh_y_ne_v
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_z_ne_u : z ≠ u :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_u_ne_z : u ≠ z := Ne.symm fresh_z_ne_u
  have fresh_z_ne_v : z ≠ v :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_v_ne_z : v ≠ z := Ne.symm fresh_z_ne_v
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_u_ne_v : u ≠ v :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_v_ne_u : v ≠ u := Ne.symm fresh_u_ne_v
  have fresh_u_ne_w : u ≠ w :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_w_ne_u : w ≠ u := Ne.symm fresh_u_ne_w
  have fresh_v_ne_w : v ≠ w :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_w_ne_v : w ≠ v := Ne.symm fresh_v_ne_w
  have dv_cache_0001 : Disjoint (C).fv (R).fv := by
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0002 : Disjoint (C).fv ((Class.cv x)).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (C).fv ((Class.cv x)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((C).fv) (({ x } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show x ∉ (C).fv from (by exact fresh_x_not_C))))))
  have dv_cache_0003 : u ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_C, not_false_eq_true])
  have dv_cache_0004 : Disjoint ((Class.cv x)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint ((Class.cv x)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ x } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show x ∉ (R).fv from (by exact fresh_x_not_R))))))
  have dv_cache_0005 : u ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_x, not_false_eq_true])
  have dv_cache_0006 : u ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_R, not_false_eq_true])
  have dv_cache_0007 : Disjoint (C).fv ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint (C).fv ((Class.cv y)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((C).fv) (({ y } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show y ∉ (C).fv from (by exact fresh_y_not_C))))))
  have dv_cache_0008 : v ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_C, not_false_eq_true])
  have dv_cache_0009 : Disjoint ((Class.cv y)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (show Disjoint ((Class.cv y)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ y } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show y ∉ (R).fv from (by exact fresh_y_not_R))))))
  have dv_cache_0010 : v ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_v_ne_y, not_false_eq_true])
  have dv_cache_0011 : v ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_R, not_false_eq_true])
  have dv_cache_0012 : Disjoint (C).fv ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (show Disjoint (C).fv ((Class.cv z)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((C).fv) (({ z } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show z ∉ (C).fv from (by exact fresh_z_not_C))))))
  have dv_cache_0013 : w ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_C, not_false_eq_true])
  have dv_cache_0014 : Disjoint ((Class.cv z)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (show Disjoint ((Class.cv z)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ z } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show z ∉ (R).fv from (by exact fresh_z_not_R))))))
  have dv_cache_0015 : w ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_z, not_false_eq_true])
  have dv_cache_0016 : w ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_R, not_false_eq_true])
  have dv_cache_0017 : w ∉ ((syn_wbr (.cv x) (syn_clnqord R C) (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_z, fresh_w_not_C, fresh_w_not_R,
          or_false, not_false_eq_true])
  have dv_cache_0018 :
    w ∉
      ((syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
                (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C)
            (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_not_C, fresh_w_not_R,
          fresh_w_ne_z, fresh_w_ne_u, fresh_w_ne_v, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0019 : v ∉ ((syn_wbr (.cv x) (syn_clnqord R C) (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_x, fresh_v_ne_z, fresh_v_not_C, fresh_v_not_R,
          or_false, not_false_eq_true])
  have dv_cache_0020 :
    v ∉
      ((syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
              (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_x, fresh_v_ne_y, fresh_v_not_C, fresh_v_not_R,
          fresh_v_ne_z, fresh_v_ne_u, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0021 : u ∉ ((syn_wbr (.cv x) (syn_clnqord R C) (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_x, fresh_u_ne_z, fresh_u_not_C, fresh_u_not_R,
          or_false, not_false_eq_true])
  have dv_cache_0022 :
    u ∉
      ((syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
            (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv z))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_x, fresh_u_ne_y, fresh_u_not_C, fresh_u_not_R,
          fresh_u_ne_z, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0023 : x ∉ ((syn_clnquo R C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo,
          Finset.mem_union, fresh_x_not_C, fresh_x_not_R, or_false, not_false_eq_true])
  have dv_cache_0024 : y ∉ ((syn_clnquo R C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo,
          Finset.mem_union, fresh_y_not_C, fresh_y_not_R, or_false, not_false_eq_true])
  have dv_cache_0025 : z ∉ ((syn_clnquo R C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo,
          Finset.mem_union, fresh_z_not_C, fresh_z_not_R, or_false, not_false_eq_true])
  have dv_cache_0026 : x ∉ ((syn_clnqord R C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          Finset.mem_union, fresh_x_not_C, fresh_x_not_R, or_false, not_false_eq_true])
  have dv_cache_0027 : y ∉ ((syn_clnqord R C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          Finset.mem_union, fresh_y_not_C, fresh_y_not_R, or_false, not_false_eq_true])
  have dv_cache_0028 : z ∉ ((syn_clnqord R C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          Finset.mem_union, fresh_z_not_C, fresh_z_not_R, or_false, not_false_eq_true])
  have dv_cache_0029 :
    x ∉
      ((syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_x_not_R, fresh_x_not_C, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0030 :
    y ∉
      ((syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_y_not_R, fresh_y_not_C, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0031 :
    z ∉
      ((syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_z_not_R, fresh_z_not_C, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0032 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0033 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0034 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    @g_simpl (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0001 := @g_lnqordexg C R dv_cache_0001
  have p0002 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (.classMem (syn_clnqord R C) (syn_cvv)) p0000 p0001
  have p0004 := @g_lnquoexg C R dv_cache_0001
  have p0005 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (.classMem (syn_clnquo R C) (syn_cvv)) p0000 p0004
  have p0006 :=
    @g_simp2
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_w3a (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
        (.classMem (.cv z) (syn_clnquo R C)))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))
  have p0007 :=
    @g_simp1 (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
      (.classMem (.cv z) (syn_clnquo R C))
  have p0008 :=
    @g_syl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_w3a (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
          (.classMem (.cv z) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv z))))
      (syn_w3a (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
        (.classMem (.cv z) (syn_clnquo R C)))
      (.classMem (.cv x) (syn_clnquo R C)) p0006 p0007
  have p0009 := @g_vex x
  have p0010 :=
    @g_ellnquo u C (.cv x) R dv_cache_0002 dv_cache_0001 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 p0009
  have p0011 :=
    @g_biimpi (.classMem (.cv x) (syn_clnquo R C))
      (syn_wrex u C (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))) p0010
  have p0012 :=
    @g_syl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_w3a (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
          (.classMem (.cv z) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv z))))
      (.classMem (.cv x) (syn_clnquo R C))
      (syn_wrex u C (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))) p0008 p0011
  have p0013 :=
    @g_simpl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_w3a (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
          (.classMem (.cv z) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv z))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0015 :=
    @g_simp2 (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
      (.classMem (.cv z) (syn_clnquo R C))
  have p0016 :=
    @g_syl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_w3a (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
          (.classMem (.cv z) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv z))))
      (syn_w3a (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
        (.classMem (.cv z) (syn_clnquo R C)))
      (.classMem (.cv y) (syn_clnquo R C)) p0006 p0015
  have p0017 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
            (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_w3a (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
          (.classMem (.cv z) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv z))))
      (.classMem (.cv y) (syn_clnquo R C)) p0013 p0016
  have p0018 := @g_vex y
  have p0019 :=
    @g_ellnquo v C (.cv y) R dv_cache_0007 dv_cache_0001 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 p0018
  have p0020 :=
    @g_biimpi (.classMem (.cv y) (syn_clnquo R C))
      (syn_wrex v C (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))) p0019
  have p0021 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
            (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (.classMem (.cv y) (syn_clnquo R C))
      (syn_wrex v C (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))) p0017 p0020
  have p0022 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
            (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0024 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
              (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
            (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_w3a (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
          (.classMem (.cv z) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv z))))
      p0022 p0013
  have p0026 :=
    @g_simp3 (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
      (.classMem (.cv z) (syn_clnquo R C))
  have p0027 :=
    @g_syl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_w3a (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
          (.classMem (.cv z) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv z))))
      (syn_w3a (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
        (.classMem (.cv z) (syn_clnquo R C)))
      (.classMem (.cv z) (syn_clnquo R C)) p0006 p0026
  have p0028 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
              (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_w3a (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
          (.classMem (.cv z) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv z))))
      (.classMem (.cv z) (syn_clnquo R C)) p0024 p0027
  have p0029 := @g_vex z
  have p0030 :=
    @g_ellnquo w C (.cv z) R dv_cache_0012 dv_cache_0001 dv_cache_0013 dv_cache_0014
      dv_cache_0015 dv_cache_0016 p0029
  have p0031 :=
    @g_biimpi (.classMem (.cv z) (syn_clnquo R C))
      (syn_wrex w C (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))) p0030
  have p0032 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
              (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv z) (syn_clnquo R C))
      (syn_wrex w C (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))) p0028 p0031
  have p0033 :=
    @g_simpl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
              (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R))))
  have p0036 :=
    @g_simp1
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_w3a (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
        (.classMem (.cv z) (syn_clnquo R C)))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))
  have p0037 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
            (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_w3a (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
          (.classMem (.cv z) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv z))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0013 p0036
  have p0038 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
              (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
            (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0022 p0037
  have p0039 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
              (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0033 p0038
  have p0040 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0041 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wss R (syn_cxp C C))
  have p0042 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      p0040 p0041
  have p0043 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wbr R (syn_cconnex) C)
  have p0044 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0042 p0043
  have p0045 := @g_simpr (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)
  have p0046 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wbr R (syn_ctrans) C) p0044 p0045
  have p0047 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wbr R (syn_ctrans) C) p0039 p0046
  have p0050 :=
    @g_simpr
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_w3a (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
          (.classMem (.cv z) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv z))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0051 :=
    @g_simpl (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
  have p0052 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
            (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
      (.classMem (.cv u) C) p0050 p0051
  have p0053 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
              (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
            (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (.classMem (.cv u) C) p0022 p0052
  have p0054 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
              (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv u) C) p0033 p0053
  have p0056 :=
    @g_simpr
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
            (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0057 :=
    @g_simpl (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
  have p0058 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
              (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
      (.classMem (.cv v) C) p0056 p0057
  have p0059 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
              (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv v) C) p0033 p0058
  have p0060 :=
    @g_simpr
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
              (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R))))
  have p0061 :=
    @g_simpl (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))
  have p0062 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R))))
      (.classMem (.cv w) C) p0060 p0061
  have p0067 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
              (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_w3a (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
          (.classMem (.cv z) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv z))))
      p0033 p0024
  have p0068 :=
    @g_simp3
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_w3a (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
        (.classMem (.cv z) (syn_clnquo R C)))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))
  have p0069 :=
    @g_simpl (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
      (syn_wbr (.cv y) (syn_clnqord R C) (.cv z))
  have p0070 :=
    @g_syl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_w3a (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
          (.classMem (.cv z) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv z))))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))
      (syn_wbr (.cv x) (syn_clnqord R C) (.cv y)) p0068 p0069
  have p0071 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_w3a (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
          (.classMem (.cv z) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv z))))
      (syn_wbr (.cv x) (syn_clnqord R C) (.cv y)) p0067 p0070
  have p0075 :=
    @g_simpr (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
  have p0076 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
            (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) p0050 p0075
  have p0077 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
              (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
            (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) p0022 p0076
  have p0078 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
              (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) p0033 p0077
  have p0081 :=
    @g_simpr (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
  have p0082 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
              (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
      (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))) p0056 p0081
  have p0083 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
              (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))) p0033 p0082
  have p0084 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
      (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))) p0078 p0083
  have p0085 :=
    @g_breq12 (.cv x) (syn_cec (.cv u) (syn_clnker R)) (.cv y)
      (syn_cec (.cv v) (syn_clnker R)) (syn_clnqord R C)
  have p0086 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wa (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
        (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
      (syn_wb (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (syn_cec (.cv u) (syn_clnker R)) (syn_clnqord R C)
          (syn_cec (.cv v) (syn_clnker R))))
      p0084 p0085
  have p0095 := @g_simpl (.classMem R (syn_cvv)) (.classMem C (syn_cvv))
  have p0096 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (.classMem R (syn_cvv))
      p0000 p0095
  have p0097 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (.classMem R (syn_cvv)) p0039 p0096
  have p0110 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0039 p0044
  have p0119 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wss R (syn_cxp C C))
  have p0120 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
      (syn_wss R (syn_cxp C C)) p0040 p0119
  have p0121 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wss R (syn_cxp C C)) p0039 p0120
  have p0122 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wss R (syn_cxp C C)) p0110 p0121
  have p0135 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (.classMem (.cv u) C) (.classMem (.cv v) C) p0054 p0059
  have p0136 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wss R (syn_cxp C C)))
      (syn_wa (.classMem (.cv u) C) (.classMem (.cv v) C)) p0122 p0135
  have p0137 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (.classMem R (syn_cvv))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem (.cv u) C) (.classMem (.cv v) C)))
      p0097 p0136
  have p0138 := @g_brlnqordkern C R (.cv u) (.cv v) dv_cache_0001
  have p0139 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem (.cv u) C) (.classMem (.cv v) C))))
      (syn_wb (syn_wbr (syn_cec (.cv u) (syn_clnker R)) (syn_clnqord R C)
          (syn_cec (.cv v) (syn_clnker R))) (syn_wbr (.cv u) R (.cv v)))
      p0137 p0138
  have p0140 :=
    @g_bitrd
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
      (syn_wbr (syn_cec (.cv u) (syn_clnker R)) (syn_clnqord R C)
        (syn_cec (.cv v) (syn_clnker R)))
      (syn_wbr (.cv u) R (.cv v)) p0086 p0139
  have p0141 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wbr (.cv x) (syn_clnqord R C) (.cv y)) (syn_wbr (.cv u) R (.cv v)) p0071 p0140
  have p0148 :=
    @g_simpr (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
      (syn_wbr (.cv y) (syn_clnqord R C) (.cv z))
  have p0149 :=
    @g_syl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_w3a (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
          (.classMem (.cv z) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv z))))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))
      (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)) p0068 p0148
  have p0150 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_w3a (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
          (.classMem (.cv z) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv z))))
      (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)) p0067 p0149
  have p0157 :=
    @g_simpr (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))
  have p0158 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R))))
      (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R))) p0060 p0157
  have p0159 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
      (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R))) p0083 p0158
  have p0160 :=
    @g_breq12 (.cv y) (syn_cec (.cv v) (syn_clnker R)) (.cv z)
      (syn_cec (.cv w) (syn_clnker R)) (syn_clnqord R C)
  have p0161 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wa (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
        (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R))))
      (syn_wb (syn_wbr (.cv y) (syn_clnqord R C) (.cv z))
        (syn_wbr (syn_cec (.cv v) (syn_clnker R)) (syn_clnqord R C)
          (syn_cec (.cv w) (syn_clnker R))))
      p0159 p0160
  have p0206 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (.classMem (.cv v) C) (.classMem (.cv w) C) p0059 p0062
  have p0207 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wss R (syn_cxp C C)))
      (syn_wa (.classMem (.cv v) C) (.classMem (.cv w) C)) p0122 p0206
  have p0208 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (.classMem R (syn_cvv))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem (.cv v) C) (.classMem (.cv w) C)))
      p0097 p0207
  have p0209 := @g_brlnqordkern C R (.cv v) (.cv w) dv_cache_0001
  have p0210 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem (.cv v) C) (.classMem (.cv w) C))))
      (syn_wb (syn_wbr (syn_cec (.cv v) (syn_clnker R)) (syn_clnqord R C)
          (syn_cec (.cv w) (syn_clnker R))) (syn_wbr (.cv v) R (.cv w)))
      p0208 p0209
  have p0211 :=
    @g_bitrd
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wbr (.cv y) (syn_clnqord R C) (.cv z))
      (syn_wbr (syn_cec (.cv v) (syn_clnker R)) (syn_clnqord R C)
        (syn_cec (.cv w) (syn_clnker R)))
      (syn_wbr (.cv v) R (.cv w)) p0161 p0210
  have p0212 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)) (syn_wbr (.cv v) R (.cv w)) p0150 p0211
  have p0213 :=
    @g_trd
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      C R (.cv u) (.cv v) (.cv w) p0047 p0054 p0059 p0062 p0141 p0212
  have p0224 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
      (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R))) p0078 p0158
  have p0225 :=
    @g_breq12 (.cv x) (syn_cec (.cv u) (syn_clnker R)) (.cv z)
      (syn_cec (.cv w) (syn_clnker R)) (syn_clnqord R C)
  have p0226 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wa (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
        (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R))))
      (syn_wb (syn_wbr (.cv x) (syn_clnqord R C) (.cv z))
        (syn_wbr (syn_cec (.cv u) (syn_clnker R)) (syn_clnqord R C)
          (syn_cec (.cv w) (syn_clnker R))))
      p0224 p0225
  have p0273 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (.classMem (.cv u) C) (.classMem (.cv w) C) p0054 p0062
  have p0274 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wss R (syn_cxp C C)))
      (syn_wa (.classMem (.cv u) C) (.classMem (.cv w) C)) p0122 p0273
  have p0275 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (.classMem R (syn_cvv))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem (.cv u) C) (.classMem (.cv w) C)))
      p0097 p0274
  have p0276 := @g_brlnqordkern C R (.cv u) (.cv w) dv_cache_0001
  have p0277 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem (.cv u) C) (.classMem (.cv w) C))))
      (syn_wb (syn_wbr (syn_cec (.cv u) (syn_clnker R)) (syn_clnqord R C)
          (syn_cec (.cv w) (syn_clnker R))) (syn_wbr (.cv u) R (.cv w)))
      p0275 p0276
  have p0278 :=
    @g_bitrd
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wbr (.cv x) (syn_clnqord R C) (.cv z))
      (syn_wbr (syn_cec (.cv u) (syn_clnker R)) (syn_clnqord R C)
        (syn_cec (.cv w) (syn_clnker R)))
      (syn_wbr (.cv u) R (.cv w)) p0226 p0277
  have p0279 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
                (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wbr (.cv x) (syn_clnqord R C) (.cv z)) (syn_wbr (.cv u) R (.cv w)) p0213 p0278
  have p0280 :=
    @g_rexlimddv
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
              (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classEq (.cv z) (syn_cec (.cv w) (syn_clnker R)))
      (syn_wbr (.cv x) (syn_clnqord R C) (.cv z)) w C dv_cache_0017 dv_cache_0018 p0032
      p0279
  have p0281 :=
    @g_rexlimddv
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_w3a (.classMem (.cv x) (syn_clnquo R C))
            (.classMem (.cv y) (syn_clnquo R C)) (.classMem (.cv z) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
      (syn_wbr (.cv x) (syn_clnqord R C) (.cv z)) v C dv_cache_0019 dv_cache_0020 p0021
      p0280
  have p0282 :=
    @g_rexlimddv
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_w3a (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
          (.classMem (.cv z) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv z))))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
      (syn_wbr (.cv x) (syn_clnqord R C) (.cv z)) u C dv_cache_0021 dv_cache_0022 p0012
      p0281
  have p0283 :=
    @g_trrd
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      x y z (syn_clnquo R C) (syn_clnqord R C) (syn_cvv) (syn_cvv) dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 p0002 p0005
      p0282
  exact p0283


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part009`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_lnqordconnex (C : Class) (R : Class) (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wbr (syn_clnqord R C) (syn_cconnex) (syn_clnquo R C))) :=
  by
  let proofSupport : Finset Var := C.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let u : Var := freshVar proofSupport 2
  let v : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_v_not_C : v ∉ C.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (h))
  have fresh_v_not_R : v ∉ R.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_u : x ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_u_ne_x : u ≠ x := Ne.symm fresh_x_ne_u
  have fresh_x_ne_v : x ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_v_ne_x : v ≠ x := Ne.symm fresh_x_ne_v
  have fresh_y_ne_u : y ≠ u :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_u_ne_y : u ≠ y := Ne.symm fresh_y_ne_u
  have fresh_y_ne_v : y ≠ v :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_v_ne_y : v ≠ y := Ne.symm fresh_y_ne_v
  have fresh_u_ne_v : u ≠ v :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_v_ne_u : v ≠ u := Ne.symm fresh_u_ne_v
  have dv_cache_0001 : Disjoint (C).fv (R).fv := by
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0002 : Disjoint (C).fv ((Class.cv x)).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (C).fv ((Class.cv x)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((C).fv) (({ x } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show x ∉ (C).fv from (by exact fresh_x_not_C))))))
  have dv_cache_0003 : u ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_C, not_false_eq_true])
  have dv_cache_0004 : Disjoint ((Class.cv x)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint ((Class.cv x)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ x } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show x ∉ (R).fv from (by exact fresh_x_not_R))))))
  have dv_cache_0005 : u ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_x, not_false_eq_true])
  have dv_cache_0006 : u ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_R, not_false_eq_true])
  have dv_cache_0007 : Disjoint (C).fv ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint (C).fv ((Class.cv y)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((C).fv) (({ y } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show y ∉ (C).fv from (by exact fresh_y_not_C))))))
  have dv_cache_0008 : v ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_C, not_false_eq_true])
  have dv_cache_0009 : Disjoint ((Class.cv y)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (show Disjoint ((Class.cv y)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ y } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show y ∉ (R).fv from (by exact fresh_y_not_R))))))
  have dv_cache_0010 : v ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_v_ne_y, not_false_eq_true])
  have dv_cache_0011 : v ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_R, not_false_eq_true])
  have dv_cache_0012 :
    v ∉
      ((syn_wo (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_x, fresh_v_ne_y, fresh_v_not_C, fresh_v_not_R,
          or_false, not_false_eq_true])
  have dv_cache_0013 :
    v ∉
      ((syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_y, fresh_v_not_C, fresh_v_not_R, fresh_v_ne_x,
          fresh_v_ne_u, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0014 :
    u ∉
      ((syn_wo (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_x, fresh_u_ne_y, fresh_u_not_C, fresh_u_not_R,
          or_false, not_false_eq_true])
  have dv_cache_0015 :
    u ∉
      ((syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_y, fresh_u_not_C, fresh_u_not_R, fresh_u_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0016 : x ∉ ((syn_clnquo R C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo,
          Finset.mem_union, fresh_x_not_C, fresh_x_not_R, or_false, not_false_eq_true])
  have dv_cache_0017 : y ∉ ((syn_clnquo R C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo,
          Finset.mem_union, fresh_y_not_C, fresh_y_not_R, or_false, not_false_eq_true])
  have dv_cache_0018 : x ∉ ((syn_clnqord R C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          Finset.mem_union, fresh_x_not_C, fresh_x_not_R, or_false, not_false_eq_true])
  have dv_cache_0019 : y ∉ ((syn_clnqord R C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          Finset.mem_union, fresh_y_not_C, fresh_y_not_R, or_false, not_false_eq_true])
  have dv_cache_0020 :
    x ∉
      ((syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_x_not_R, fresh_x_not_C, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0021 :
    y ∉
      ((syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_y_not_R, fresh_y_not_C, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0022 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_simpl (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0001 := @g_lnqordexg C R dv_cache_0001
  have p0002 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (.classMem (syn_clnqord R C) (syn_cvv)) p0000 p0001
  have p0004 := @g_lnquoexg C R dv_cache_0001
  have p0005 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (.classMem (syn_clnquo R C) (syn_cvv)) p0000 p0004
  have p0006 :=
    @g_simp2
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
  have p0007 := @g_vex x
  have p0008 :=
    @g_ellnquo u C (.cv x) R dv_cache_0002 dv_cache_0001 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 p0007
  have p0009 :=
    @g_biimpi (.classMem (.cv x) (syn_clnquo R C))
      (syn_wrex u C (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))) p0008
  have p0010 :=
    @g_syl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (.classMem (.cv x) (syn_clnquo R C))
      (syn_wrex u C (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))) p0006 p0009
  have p0011 :=
    @g_simpl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0012 :=
    @g_simp3
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
  have p0013 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (.classMem (.cv y) (syn_clnquo R C)) p0011 p0012
  have p0014 := @g_vex y
  have p0015 :=
    @g_ellnquo v C (.cv y) R dv_cache_0007 dv_cache_0001 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 p0014
  have p0016 :=
    @g_biimpi (.classMem (.cv y) (syn_clnquo R C))
      (syn_wrex v C (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))) p0015
  have p0017 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (.classMem (.cv y) (syn_clnquo R C))
      (syn_wrex v C (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))) p0013 p0016
  have p0018 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0020 :=
    @g_simp1
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
  have p0021 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0011 p0020
  have p0022 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
        (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0018 p0021
  have p0023 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0024 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wss R (syn_cxp C C))
  have p0025 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      p0023 p0024
  have p0026 :=
    @g_simpr (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wbr R (syn_cconnex) C)
  have p0027 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wbr R (syn_cconnex) C) p0025 p0026
  have p0028 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
        (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wbr R (syn_cconnex) C) p0022 p0027
  have p0030 :=
    @g_simpr
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0031 :=
    @g_simpl (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
  have p0032 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
      (.classMem (.cv u) C) p0030 p0031
  have p0033 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
        (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (.classMem (.cv u) C) p0018 p0032
  have p0034 :=
    @g_simpr
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0035 :=
    @g_simpl (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
  have p0036 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
        (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
      (.classMem (.cv v) C) p0034 p0035
  have p0037 :=
    @g_connexd
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
        (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      C R (.cv u) (.cv v) p0028 p0033 p0036
  have p0040 :=
    @g_simpr (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
  have p0041 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) p0030 p0040
  have p0042 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
        (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) p0018 p0041
  have p0044 :=
    @g_simpr (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
  have p0045 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
        (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
      (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))) p0034 p0044
  have p0046 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
        (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
      (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))) p0042 p0045
  have p0047 :=
    @g_breq12 (.cv x) (syn_cec (.cv u) (syn_clnker R)) (.cv y)
      (syn_cec (.cv v) (syn_clnker R)) (syn_clnqord R C)
  have p0048 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
        (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
        (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
      (syn_wb (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (syn_cec (.cv u) (syn_clnker R)) (syn_clnqord R C)
          (syn_cec (.cv v) (syn_clnker R))))
      p0046 p0047
  have p0055 := @g_simpl (.classMem R (syn_cvv)) (.classMem C (syn_cvv))
  have p0056 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (.classMem R (syn_cvv))
      p0000 p0055
  have p0057 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
        (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (.classMem R (syn_cvv)) p0022 p0056
  have p0066 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wbr R (syn_cconnex) C)
  have p0067 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0025 p0066
  have p0068 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
        (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0022 p0067
  have p0075 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wss R (syn_cxp C C))
  have p0076 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
      (syn_wss R (syn_cxp C C)) p0023 p0075
  have p0077 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
        (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wss R (syn_cxp C C)) p0022 p0076
  have p0078 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
        (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wss R (syn_cxp C C)) p0068 p0077
  have p0087 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
        (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv u) C) (.classMem (.cv v) C) p0033 p0036
  have p0088 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
        (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wss R (syn_cxp C C)))
      (syn_wa (.classMem (.cv u) C) (.classMem (.cv v) C)) p0078 p0087
  have p0089 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
        (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem R (syn_cvv))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem (.cv u) C) (.classMem (.cv v) C)))
      p0057 p0088
  have p0090 := @g_brlnqordkern C R (.cv u) (.cv v) dv_cache_0001
  have p0091 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
        (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem (.cv u) C) (.classMem (.cv v) C))))
      (syn_wb (syn_wbr (syn_cec (.cv u) (syn_clnker R)) (syn_clnqord R C)
          (syn_cec (.cv v) (syn_clnker R))) (syn_wbr (.cv u) R (.cv v)))
      p0089 p0090
  have p0092 :=
    @g_bitrd
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
        (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
      (syn_wbr (syn_cec (.cv u) (syn_clnker R)) (syn_clnqord R C)
        (syn_cec (.cv v) (syn_clnker R)))
      (syn_wbr (.cv u) R (.cv v)) p0048 p0091
  have p0101 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
        (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) p0045 p0042
  have p0102 :=
    @g_breq12 (.cv y) (syn_cec (.cv v) (syn_clnker R)) (.cv x)
      (syn_cec (.cv u) (syn_clnker R)) (syn_clnqord R C)
  have p0103 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
        (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
        (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
      (syn_wb (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))
        (syn_wbr (syn_cec (.cv v) (syn_clnker R)) (syn_clnqord R C)
          (syn_cec (.cv u) (syn_clnker R))))
      p0101 p0102
  have p0142 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
        (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv v) C) (.classMem (.cv u) C) p0036 p0033
  have p0143 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
        (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wss R (syn_cxp C C)))
      (syn_wa (.classMem (.cv v) C) (.classMem (.cv u) C)) p0078 p0142
  have p0144 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
        (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem R (syn_cvv))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem (.cv v) C) (.classMem (.cv u) C)))
      p0057 p0143
  have p0145 := @g_brlnqordkern C R (.cv v) (.cv u) dv_cache_0001
  have p0146 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
        (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem (.cv v) C) (.classMem (.cv u) C))))
      (syn_wb (syn_wbr (syn_cec (.cv v) (syn_clnker R)) (syn_clnqord R C)
          (syn_cec (.cv u) (syn_clnker R))) (syn_wbr (.cv v) R (.cv u)))
      p0144 p0145
  have p0147 :=
    @g_bitrd
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
        (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))
      (syn_wbr (syn_cec (.cv v) (syn_clnker R)) (syn_clnqord R C)
        (syn_cec (.cv u) (syn_clnker R)))
      (syn_wbr (.cv v) R (.cv u)) p0103 p0146
  have p0148 :=
    @g_orbi12d
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
        (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wbr (.cv x) (syn_clnqord R C) (.cv y)) (syn_wbr (.cv u) R (.cv v))
      (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)) (syn_wbr (.cv v) R (.cv u)) p0092 p0147
  have p0149 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
        (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wo (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))
      (syn_wo (syn_wbr (.cv u) R (.cv v)) (syn_wbr (.cv v) R (.cv u))) p0037 p0148
  have p0150 :=
    @g_rexlimddv
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
      (syn_wo (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))
      v C dv_cache_0012 dv_cache_0013 p0017 p0149
  have p0151 :=
    @g_rexlimddv
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
      (syn_wo (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))
      u C dv_cache_0014 dv_cache_0015 p0010 p0150
  have p0152 :=
    @g_connexrd
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      x y (syn_clnquo R C) (syn_clnqord R C) (syn_cvv) (syn_cvv) dv_cache_0016
      dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
      p0002 p0005 p0151
  exact p0152


end NFChoice.DirectNominalPrf.WPPReplay

end
