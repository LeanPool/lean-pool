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

/-- Checked nominal proof certificate identified upstream as `g_brlnqordkern`. -/
@[expose]
noncomputable def gBrlnqordkern (C : Class) (R : Class) (X : Class) (Y : Class)
    (_dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem R (synCvv)) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))) (synWb
          (synWbr (synCec X (synClnker R)) (synClnqord R C) (synCec Y (synClnker R)))
          (synWbr X R Y))) :=
  by
  have p0000 := (Nominal.classEqRefl (synClnqord R C))
  have p0001 :=
    @gBreqi (synCec X (synClnker R)) (synCec Y (synClnker R)) (synClnqord R C)
      (synCin (synClnqrel R) (synCxp (synClnquo R C) (synClnquo R C))) p0000
  have p0002 :=
    @gBrin (synCec X (synClnker R)) (synCec Y (synClnker R)) (synClnqrel R)
      (synCxp (synClnquo R C) (synClnquo R C))
  have p0003 :=
    @gBitri
      (synWbr (synCec X (synClnker R)) (synClnqord R C) (synCec Y (synClnker R)))
      (synWbr (synCec X (synClnker R))
        (synCin (synClnqrel R) (synCxp (synClnquo R C) (synClnquo R C)))
        (synCec Y (synClnker R)))
      (synWa (synWbr (synCec X (synClnker R)) (synClnqrel R) (synCec Y (synClnker R)))
        (synWbr (synCec X (synClnker R)) (synCxp (synClnquo R C) (synClnquo R C))
          (synCec Y (synClnker R))))
      p0001 p0002
  have p0004 :=
    @gA1i
      (synWb (synWbr (synCec X (synClnker R)) (synClnqord R C) (synCec Y (synClnker R)))
        (synWa (synWbr (synCec X (synClnker R)) (synClnqrel R) (synCec Y (synClnker R)))
          (synWbr (synCec X (synClnker R)) (synCxp (synClnquo R C) (synClnquo R C))
            (synCec Y (synClnker R)))))
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C))))
      p0003
  have p0005 :=
    @gSimpl (.classMem R (synCvv))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
  have p0006 := @gLnkerexg R
  have p0007 :=
    @gSyl
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C))))
      (.classMem R (synCvv)) (.classMem (synClnker R) (synCvv)) p0005 p0006
  have p0008 :=
    @gSimpr (.classMem R (synCvv))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
  have p0009 :=
    @gSimpr
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWss R (synCxp C C)))
      (synWa (.classMem X C) (.classMem Y C))
  have p0010 :=
    @gSyl
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C))))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
      (synWa (.classMem X C) (.classMem Y C)) p0008 p0009
  have p0011 := @gSimpl (.classMem X C) (.classMem Y C)
  have p0012 :=
    @gSyl
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C))))
      (synWa (.classMem X C) (.classMem Y C)) (.classMem X C) p0010 p0011
  have p0013 :=
    @gJca
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C))))
      (.classMem (synClnker R) (synCvv)) (.classMem X C) p0007 p0012
  have p0014 := @gEcelqsg C X (synClnker R) (synCvv)
  have p0015 :=
    @gSyl
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C))))
      (synWa (.classMem (synClnker R) (synCvv)) (.classMem X C))
      (.classMem (synCec X (synClnker R)) (synCqs C (synClnker R))) p0013 p0014
  have p0016 := (Nominal.classEqRefl (synClnquo R C))
  have p0017 :=
    @gSyl6eleqr
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C))))
      (synCec X (synClnker R)) (synCqs C (synClnker R)) (synClnquo R C) p0015 p0016
  have p0024 := @gSimpr (.classMem X C) (.classMem Y C)
  have p0025 :=
    @gSyl
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C))))
      (synWa (.classMem X C) (.classMem Y C)) (.classMem Y C) p0010 p0024
  have p0026 :=
    @gJca
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C))))
      (.classMem (synClnker R) (synCvv)) (.classMem Y C) p0007 p0025
  have p0027 := @gEcelqsg C Y (synClnker R) (synCvv)
  have p0028 :=
    @gSyl
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C))))
      (synWa (.classMem (synClnker R) (synCvv)) (.classMem Y C))
      (.classMem (synCec Y (synClnker R)) (synCqs C (synClnker R))) p0026 p0027
  have p0030 :=
    @gSyl6eleqr
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C))))
      (synCec Y (synClnker R)) (synCqs C (synClnker R)) (synClnquo R C) p0028 p0016
  have p0031 :=
    @gJca
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C))))
      (.classMem (synCec X (synClnker R)) (synClnquo R C))
      (.classMem (synCec Y (synClnker R)) (synClnquo R C)) p0017 p0030
  have p0032 :=
    @gBrxp (synCec X (synClnker R)) (synCec Y (synClnker R)) (synClnquo R C)
      (synClnquo R C)
  have p0033 :=
    @gSylibr
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C))))
      (synWa (.classMem (synCec X (synClnker R)) (synClnquo R C))
        (.classMem (synCec Y (synClnker R)) (synClnquo R C)))
      (synWbr (synCec X (synClnker R)) (synCxp (synClnquo R C) (synClnquo R C))
        (synCec Y (synClnker R)))
      p0031 p0032
  have p0034 :=
    @gBiantrud
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C))))
      (synWbr (synCec X (synClnker R)) (synCxp (synClnquo R C) (synClnquo R C))
        (synCec Y (synClnker R)))
      (synWbr (synCec X (synClnker R)) (synClnqrel R) (synCec Y (synClnker R)))
      p0033
  have p0035 :=
    @gBitr4d
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C))))
      (synWbr (synCec X (synClnker R)) (synClnqord R C) (synCec Y (synClnker R)))
      (synWa (synWbr (synCec X (synClnker R)) (synClnqrel R) (synCec Y (synClnker R)))
        (synWbr (synCec X (synClnker R)) (synCxp (synClnquo R C) (synClnquo R C))
          (synCec Y (synClnker R))))
      (synWbr (synCec X (synClnker R)) (synClnqrel R) (synCec Y (synClnker R)))
      p0004 p0034
  have p0036 := @gBrlnqrelkern C R X Y
  have p0037 :=
    @gBitrd
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C))))
      (synWbr (synCec X (synClnker R)) (synClnqord R C) (synCec Y (synClnker R)))
      (synWbr (synCec X (synClnker R)) (synClnqrel R) (synCec Y (synClnker R)))
      (synWbr X R Y) p0035 p0036
  exact p0037

/-- Checked nominal proof certificate identified upstream as `g_lnqordref`. -/
@[expose]
noncomputable def gLnqordref (C : Class) (R : Class) (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf
      (.imp (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWbr (synClnqord R C) (synCref) (synClnquo R C))) :=
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
  have dv_cache_0007 : u ∉ ((synWbr (.cv x) (synClnqord R C) (.cv x))).fv :=
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
      ((synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (.classMem (.cv x) (synClnquo R C)))).fv :=
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
  have dv_cache_0009 : x ∉ ((synClnquo R C)).fv :=
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
  have dv_cache_0010 : x ∉ ((synClnqord R C)).fv :=
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
      ((synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))).fv :=
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
    @gSimpl (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
  have p0001 := @gLnqordexg C R dv_cache_0001
  have p0002 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (.classMem (synClnqord R C) (synCvv)) p0000 p0001
  have p0004 := @gLnquoexg C R dv_cache_0001
  have p0005 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (.classMem (synClnquo R C) (synCvv)) p0000 p0004
  have p0006 :=
    @gSimpr
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (.classMem (.cv x) (synClnquo R C))
  have p0007 := @gVex x
  have p0008 :=
    @gEllnquo u C (.cv x) R dv_cache_0002 dv_cache_0001 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 p0007
  have p0009 :=
    @gBiimpi (.classMem (.cv x) (synClnquo R C))
      (synWrex u C (.classEq (.cv x) (synCec (.cv u) (synClnker R)))) p0008
  have p0010 :=
    @gSyl
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (.classMem (.cv x) (synClnquo R C)))
      (.classMem (.cv x) (synClnquo R C))
      (synWrex u C (.classEq (.cv x) (synCec (.cv u) (synClnker R)))) p0006 p0009
  have p0011 :=
    @gSimpl
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (.classMem (.cv x) (synClnquo R C)))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0012 :=
    @gSimpl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (.classMem (.cv x) (synClnquo R C))
  have p0013 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (.classMem (.cv x) (synClnquo R C))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (.classMem (.cv x) (synClnquo R C)))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0011 p0012
  have p0014 :=
    @gSimpr (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
  have p0015 :=
    @gSimpl
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWss R (synCxp C C))
  have p0016 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      p0014 p0015
  have p0017 :=
    @gSimpl (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWbr R (synCconnex) C)
  have p0018 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C)) p0016 p0017
  have p0019 := @gSimpl (synWbr R (synCref) C) (synWbr R (synCtrans) C)
  have p0020 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWbr R (synCref) C) p0018 p0019
  have p0021 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (.classMem (.cv x) (synClnquo R C))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWbr R (synCref) C) p0013 p0020
  have p0022 :=
    @gSimpr
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (.classMem (.cv x) (synClnquo R C)))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0023 :=
    @gSimpl (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
  have p0024 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (.classMem (.cv x) (synClnquo R C))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
      (.classMem (.cv u) C) p0022 p0023
  have p0025 :=
    @gRefd
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (.classMem (.cv x) (synClnquo R C))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      C R (.cv u) p0021 p0024
  have p0027 :=
    @gSimpr (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
  have p0028 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (.classMem (.cv x) (synClnquo R C))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
      (.classEq (.cv x) (synCec (.cv u) (synClnker R))) p0022 p0027
  have p0032 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (.classMem (.cv x) (synClnquo R C))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
      (.classEq (.cv x) (synCec (.cv u) (synClnker R))) p0028 p0028
  have p0033 :=
    @gBreq12 (.cv x) (synCec (.cv u) (synClnker R)) (.cv x)
      (synCec (.cv u) (synClnker R)) (synClnqord R C)
  have p0034 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (.classMem (.cv x) (synClnquo R C))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
        (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
      (synWb (synWbr (.cv x) (synClnqord R C) (.cv x))
        (synWbr (synCec (.cv u) (synClnker R)) (synClnqord R C)
          (synCec (.cv u) (synClnker R))))
      p0032 p0033
  have p0039 := @gSimpl (.classMem R (synCvv)) (.classMem C (synCvv))
  have p0040 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (.classMem R (synCvv))
      p0000 p0039
  have p0041 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (.classMem (.cv x) (synClnquo R C))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (.classMem R (synCvv)) p0013 p0040
  have p0050 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (.classMem (.cv x) (synClnquo R C))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C)) p0013 p0018
  have p0055 :=
    @gSimpr
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWss R (synCxp C C))
  have p0056 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
      (synWss R (synCxp C C)) p0014 p0055
  have p0057 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (.classMem (.cv x) (synClnquo R C))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWss R (synCxp C C)) p0013 p0056
  have p0058 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (.classMem (.cv x) (synClnquo R C))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWss R (synCxp C C)) p0050 p0057
  have p0065 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (.classMem (.cv x) (synClnquo R C))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (.classMem (.cv u) C) (.classMem (.cv u) C) p0024 p0024
  have p0066 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (.classMem (.cv x) (synClnquo R C))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWss R (synCxp C C)))
      (synWa (.classMem (.cv u) C) (.classMem (.cv u) C)) p0058 p0065
  have p0067 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (.classMem (.cv x) (synClnquo R C))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (.classMem R (synCvv))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem (.cv u) C) (.classMem (.cv u) C)))
      p0041 p0066
  have p0068 := @gBrlnqordkern C R (.cv u) (.cv u) dv_cache_0001
  have p0069 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (.classMem (.cv x) (synClnquo R C))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem (.cv u) C) (.classMem (.cv u) C))))
      (synWb (synWbr (synCec (.cv u) (synClnker R)) (synClnqord R C)
          (synCec (.cv u) (synClnker R))) (synWbr (.cv u) R (.cv u)))
      p0067 p0068
  have p0070 :=
    @gBitrd
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (.classMem (.cv x) (synClnquo R C))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWbr (.cv x) (synClnqord R C) (.cv x))
      (synWbr (synCec (.cv u) (synClnker R)) (synClnqord R C)
        (synCec (.cv u) (synClnker R)))
      (synWbr (.cv u) R (.cv u)) p0034 p0069
  have p0071 :=
    @gMpbird
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (.classMem (.cv x) (synClnquo R C))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWbr (.cv x) (synClnqord R C) (.cv x)) (synWbr (.cv u) R (.cv u)) p0025 p0070
  have p0072 :=
    @gRexlimddv
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (.classMem (.cv x) (synClnquo R C)))
      (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
      (synWbr (.cv x) (synClnqord R C) (.cv x)) u C dv_cache_0007 dv_cache_0008 p0010
      p0071
  have p0073 :=
    @gRefrd
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      x (synClnquo R C) (synClnqord R C) (synCvv) (synCvv) dv_cache_0009 dv_cache_0010
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

/-- Checked nominal proof certificate identified upstream as `g_lnqordtrans`. -/
@[expose]
noncomputable def gLnqordtrans (C : Class) (R : Class) (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf
      (.imp (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWbr (synClnqord R C) (synCtrans) (synClnquo R C))) :=
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
  have dv_cache_0017 : w ∉ ((synWbr (.cv x) (synClnqord R C) (.cv z))).fv :=
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
      ((synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
                (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C)
            (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))).fv :=
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
  have dv_cache_0019 : v ∉ ((synWbr (.cv x) (synClnqord R C) (.cv z))).fv :=
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
      ((synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synW3a (.classMem (.cv x) (synClnquo R C))
              (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))).fv :=
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
  have dv_cache_0021 : u ∉ ((synWbr (.cv x) (synClnqord R C) (.cv z))).fv :=
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
      ((synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synW3a (.classMem (.cv x) (synClnquo R C))
            (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv z))))).fv :=
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
  have dv_cache_0023 : x ∉ ((synClnquo R C)).fv :=
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
  have dv_cache_0024 : y ∉ ((synClnquo R C)).fv :=
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
  have dv_cache_0025 : z ∉ ((synClnquo R C)).fv :=
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
  have dv_cache_0026 : x ∉ ((synClnqord R C)).fv :=
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
  have dv_cache_0027 : y ∉ ((synClnqord R C)).fv :=
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
  have dv_cache_0028 : z ∉ ((synClnqord R C)).fv :=
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
      ((synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))).fv :=
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
      ((synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))).fv :=
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
      ((synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))).fv :=
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
    @gSimpl (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
  have p0001 := @gLnqordexg C R dv_cache_0001
  have p0002 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (.classMem (synClnqord R C) (synCvv)) p0000 p0001
  have p0004 := @gLnquoexg C R dv_cache_0001
  have p0005 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (.classMem (synClnquo R C) (synCvv)) p0000 p0004
  have p0006 :=
    @gSimp2
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synW3a (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C))
        (.classMem (.cv z) (synClnquo R C)))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv z)))
  have p0007 :=
    @gSimp1 (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C))
      (.classMem (.cv z) (synClnquo R C))
  have p0008 :=
    @gSyl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synW3a (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C))
          (.classMem (.cv z) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv z))))
      (synW3a (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C))
        (.classMem (.cv z) (synClnquo R C)))
      (.classMem (.cv x) (synClnquo R C)) p0006 p0007
  have p0009 := @gVex x
  have p0010 :=
    @gEllnquo u C (.cv x) R dv_cache_0002 dv_cache_0001 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 p0009
  have p0011 :=
    @gBiimpi (.classMem (.cv x) (synClnquo R C))
      (synWrex u C (.classEq (.cv x) (synCec (.cv u) (synClnker R)))) p0010
  have p0012 :=
    @gSyl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synW3a (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C))
          (.classMem (.cv z) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv z))))
      (.classMem (.cv x) (synClnquo R C))
      (synWrex u C (.classEq (.cv x) (synCec (.cv u) (synClnker R)))) p0008 p0011
  have p0013 :=
    @gSimpl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synW3a (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C))
          (.classMem (.cv z) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv z))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0015 :=
    @gSimp2 (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C))
      (.classMem (.cv z) (synClnquo R C))
  have p0016 :=
    @gSyl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synW3a (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C))
          (.classMem (.cv z) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv z))))
      (synW3a (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C))
        (.classMem (.cv z) (synClnquo R C)))
      (.classMem (.cv y) (synClnquo R C)) p0006 p0015
  have p0017 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synW3a (.classMem (.cv x) (synClnquo R C))
            (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synW3a (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C))
          (.classMem (.cv z) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv z))))
      (.classMem (.cv y) (synClnquo R C)) p0013 p0016
  have p0018 := @gVex y
  have p0019 :=
    @gEllnquo v C (.cv y) R dv_cache_0007 dv_cache_0001 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 p0018
  have p0020 :=
    @gBiimpi (.classMem (.cv y) (synClnquo R C))
      (synWrex v C (.classEq (.cv y) (synCec (.cv v) (synClnker R)))) p0019
  have p0021 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synW3a (.classMem (.cv x) (synClnquo R C))
            (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (.classMem (.cv y) (synClnquo R C))
      (synWrex v C (.classEq (.cv y) (synCec (.cv v) (synClnker R)))) p0017 p0020
  have p0022 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synW3a (.classMem (.cv x) (synClnquo R C))
            (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0024 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synW3a (.classMem (.cv x) (synClnquo R C))
              (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synW3a (.classMem (.cv x) (synClnquo R C))
            (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synW3a (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C))
          (.classMem (.cv z) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv z))))
      p0022 p0013
  have p0026 :=
    @gSimp3 (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C))
      (.classMem (.cv z) (synClnquo R C))
  have p0027 :=
    @gSyl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synW3a (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C))
          (.classMem (.cv z) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv z))))
      (synW3a (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C))
        (.classMem (.cv z) (synClnquo R C)))
      (.classMem (.cv z) (synClnquo R C)) p0006 p0026
  have p0028 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synW3a (.classMem (.cv x) (synClnquo R C))
              (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synW3a (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C))
          (.classMem (.cv z) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv z))))
      (.classMem (.cv z) (synClnquo R C)) p0024 p0027
  have p0029 := @gVex z
  have p0030 :=
    @gEllnquo w C (.cv z) R dv_cache_0012 dv_cache_0001 dv_cache_0013 dv_cache_0014
      dv_cache_0015 dv_cache_0016 p0029
  have p0031 :=
    @gBiimpi (.classMem (.cv z) (synClnquo R C))
      (synWrex w C (.classEq (.cv z) (synCec (.cv w) (synClnker R)))) p0030
  have p0032 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synW3a (.classMem (.cv x) (synClnquo R C))
              (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv z) (synClnquo R C))
      (synWrex w C (.classEq (.cv z) (synCec (.cv w) (synClnker R)))) p0028 p0031
  have p0033 :=
    @gSimpl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synW3a (.classMem (.cv x) (synClnquo R C))
              (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R))))
  have p0036 :=
    @gSimp1
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synW3a (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C))
        (.classMem (.cv z) (synClnquo R C)))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv z)))
  have p0037 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synW3a (.classMem (.cv x) (synClnquo R C))
            (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synW3a (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C))
          (.classMem (.cv z) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv z))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0013 p0036
  have p0038 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synW3a (.classMem (.cv x) (synClnquo R C))
              (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synW3a (.classMem (.cv x) (synClnquo R C))
            (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0022 p0037
  have p0039 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synW3a (.classMem (.cv x) (synClnquo R C))
              (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0033 p0038
  have p0040 :=
    @gSimpr (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
  have p0041 :=
    @gSimpl
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWss R (synCxp C C))
  have p0042 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      p0040 p0041
  have p0043 :=
    @gSimpl (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWbr R (synCconnex) C)
  have p0044 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C)) p0042 p0043
  have p0045 := @gSimpr (synWbr R (synCref) C) (synWbr R (synCtrans) C)
  have p0046 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWbr R (synCtrans) C) p0044 p0045
  have p0047 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWbr R (synCtrans) C) p0039 p0046
  have p0050 :=
    @gSimpr
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synW3a (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C))
          (.classMem (.cv z) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv z))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0051 :=
    @gSimpl (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
  have p0052 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synW3a (.classMem (.cv x) (synClnquo R C))
            (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
      (.classMem (.cv u) C) p0050 p0051
  have p0053 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synW3a (.classMem (.cv x) (synClnquo R C))
              (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synW3a (.classMem (.cv x) (synClnquo R C))
            (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (.classMem (.cv u) C) p0022 p0052
  have p0054 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synW3a (.classMem (.cv x) (synClnquo R C))
              (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv u) C) p0033 p0053
  have p0056 :=
    @gSimpr
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synW3a (.classMem (.cv x) (synClnquo R C))
            (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0057 :=
    @gSimpl (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
  have p0058 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synW3a (.classMem (.cv x) (synClnquo R C))
              (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
      (.classMem (.cv v) C) p0056 p0057
  have p0059 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synW3a (.classMem (.cv x) (synClnquo R C))
              (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv v) C) p0033 p0058
  have p0060 :=
    @gSimpr
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synW3a (.classMem (.cv x) (synClnquo R C))
              (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R))))
  have p0061 :=
    @gSimpl (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))
  have p0062 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R))))
      (.classMem (.cv w) C) p0060 p0061
  have p0067 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synW3a (.classMem (.cv x) (synClnquo R C))
              (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synW3a (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C))
          (.classMem (.cv z) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv z))))
      p0033 p0024
  have p0068 :=
    @gSimp3
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synW3a (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C))
        (.classMem (.cv z) (synClnquo R C)))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv z)))
  have p0069 :=
    @gSimpl (synWbr (.cv x) (synClnqord R C) (.cv y))
      (synWbr (.cv y) (synClnqord R C) (.cv z))
  have p0070 :=
    @gSyl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synW3a (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C))
          (.classMem (.cv z) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv z))))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv z)))
      (synWbr (.cv x) (synClnqord R C) (.cv y)) p0068 p0069
  have p0071 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synW3a (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C))
          (.classMem (.cv z) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv z))))
      (synWbr (.cv x) (synClnqord R C) (.cv y)) p0067 p0070
  have p0075 :=
    @gSimpr (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
  have p0076 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synW3a (.classMem (.cv x) (synClnquo R C))
            (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
      (.classEq (.cv x) (synCec (.cv u) (synClnker R))) p0050 p0075
  have p0077 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synW3a (.classMem (.cv x) (synClnquo R C))
              (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synW3a (.classMem (.cv x) (synClnquo R C))
            (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (.classEq (.cv x) (synCec (.cv u) (synClnker R))) p0022 p0076
  have p0078 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synW3a (.classMem (.cv x) (synClnquo R C))
              (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classEq (.cv x) (synCec (.cv u) (synClnker R))) p0033 p0077
  have p0081 :=
    @gSimpr (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
  have p0082 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synW3a (.classMem (.cv x) (synClnquo R C))
              (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
      (.classEq (.cv y) (synCec (.cv v) (synClnker R))) p0056 p0081
  have p0083 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synW3a (.classMem (.cv x) (synClnquo R C))
              (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classEq (.cv y) (synCec (.cv v) (synClnker R))) p0033 p0082
  have p0084 :=
    @gJca
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
      (.classEq (.cv y) (synCec (.cv v) (synClnker R))) p0078 p0083
  have p0085 :=
    @gBreq12 (.cv x) (synCec (.cv u) (synClnker R)) (.cv y)
      (synCec (.cv v) (synClnker R)) (synClnqord R C)
  have p0086 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (synWa (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
        (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
      (synWb (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (synCec (.cv u) (synClnker R)) (synClnqord R C)
          (synCec (.cv v) (synClnker R))))
      p0084 p0085
  have p0095 := @gSimpl (.classMem R (synCvv)) (.classMem C (synCvv))
  have p0096 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (.classMem R (synCvv))
      p0000 p0095
  have p0097 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (.classMem R (synCvv)) p0039 p0096
  have p0110 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C)) p0039 p0044
  have p0119 :=
    @gSimpr
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWss R (synCxp C C))
  have p0120 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
      (synWss R (synCxp C C)) p0040 p0119
  have p0121 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWss R (synCxp C C)) p0039 p0120
  have p0122 :=
    @gJca
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWss R (synCxp C C)) p0110 p0121
  have p0135 :=
    @gJca
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (.classMem (.cv u) C) (.classMem (.cv v) C) p0054 p0059
  have p0136 :=
    @gJca
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWss R (synCxp C C)))
      (synWa (.classMem (.cv u) C) (.classMem (.cv v) C)) p0122 p0135
  have p0137 :=
    @gJca
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (.classMem R (synCvv))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem (.cv u) C) (.classMem (.cv v) C)))
      p0097 p0136
  have p0138 := @gBrlnqordkern C R (.cv u) (.cv v) dv_cache_0001
  have p0139 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem (.cv u) C) (.classMem (.cv v) C))))
      (synWb (synWbr (synCec (.cv u) (synClnker R)) (synClnqord R C)
          (synCec (.cv v) (synClnker R))) (synWbr (.cv u) R (.cv v)))
      p0137 p0138
  have p0140 :=
    @gBitrd
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (synWbr (.cv x) (synClnqord R C) (.cv y))
      (synWbr (synCec (.cv u) (synClnker R)) (synClnqord R C)
        (synCec (.cv v) (synClnker R)))
      (synWbr (.cv u) R (.cv v)) p0086 p0139
  have p0141 :=
    @gMpbid
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (synWbr (.cv x) (synClnqord R C) (.cv y)) (synWbr (.cv u) R (.cv v)) p0071 p0140
  have p0148 :=
    @gSimpr (synWbr (.cv x) (synClnqord R C) (.cv y))
      (synWbr (.cv y) (synClnqord R C) (.cv z))
  have p0149 :=
    @gSyl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synW3a (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C))
          (.classMem (.cv z) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv z))))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv z)))
      (synWbr (.cv y) (synClnqord R C) (.cv z)) p0068 p0148
  have p0150 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synW3a (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C))
          (.classMem (.cv z) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv z))))
      (synWbr (.cv y) (synClnqord R C) (.cv z)) p0067 p0149
  have p0157 :=
    @gSimpr (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))
  have p0158 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R))))
      (.classEq (.cv z) (synCec (.cv w) (synClnker R))) p0060 p0157
  have p0159 :=
    @gJca
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
      (.classEq (.cv z) (synCec (.cv w) (synClnker R))) p0083 p0158
  have p0160 :=
    @gBreq12 (.cv y) (synCec (.cv v) (synClnker R)) (.cv z)
      (synCec (.cv w) (synClnker R)) (synClnqord R C)
  have p0161 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (synWa (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
        (.classEq (.cv z) (synCec (.cv w) (synClnker R))))
      (synWb (synWbr (.cv y) (synClnqord R C) (.cv z))
        (synWbr (synCec (.cv v) (synClnker R)) (synClnqord R C)
          (synCec (.cv w) (synClnker R))))
      p0159 p0160
  have p0206 :=
    @gJca
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (.classMem (.cv v) C) (.classMem (.cv w) C) p0059 p0062
  have p0207 :=
    @gJca
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWss R (synCxp C C)))
      (synWa (.classMem (.cv v) C) (.classMem (.cv w) C)) p0122 p0206
  have p0208 :=
    @gJca
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (.classMem R (synCvv))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem (.cv v) C) (.classMem (.cv w) C)))
      p0097 p0207
  have p0209 := @gBrlnqordkern C R (.cv v) (.cv w) dv_cache_0001
  have p0210 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem (.cv v) C) (.classMem (.cv w) C))))
      (synWb (synWbr (synCec (.cv v) (synClnker R)) (synClnqord R C)
          (synCec (.cv w) (synClnker R))) (synWbr (.cv v) R (.cv w)))
      p0208 p0209
  have p0211 :=
    @gBitrd
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (synWbr (.cv y) (synClnqord R C) (.cv z))
      (synWbr (synCec (.cv v) (synClnker R)) (synClnqord R C)
        (synCec (.cv w) (synClnker R)))
      (synWbr (.cv v) R (.cv w)) p0161 p0210
  have p0212 :=
    @gMpbid
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (synWbr (.cv y) (synClnqord R C) (.cv z)) (synWbr (.cv v) R (.cv w)) p0150 p0211
  have p0213 :=
    @gTrd
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      C R (.cv u) (.cv v) (.cv w) p0047 p0054 p0059 p0062 p0141 p0212
  have p0224 :=
    @gJca
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
      (.classEq (.cv z) (synCec (.cv w) (synClnker R))) p0078 p0158
  have p0225 :=
    @gBreq12 (.cv x) (synCec (.cv u) (synClnker R)) (.cv z)
      (synCec (.cv w) (synClnker R)) (synClnqord R C)
  have p0226 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (synWa (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
        (.classEq (.cv z) (synCec (.cv w) (synClnker R))))
      (synWb (synWbr (.cv x) (synClnqord R C) (.cv z))
        (synWbr (synCec (.cv u) (synClnker R)) (synClnqord R C)
          (synCec (.cv w) (synClnker R))))
      p0224 p0225
  have p0273 :=
    @gJca
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (.classMem (.cv u) C) (.classMem (.cv w) C) p0054 p0062
  have p0274 :=
    @gJca
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWss R (synCxp C C)))
      (synWa (.classMem (.cv u) C) (.classMem (.cv w) C)) p0122 p0273
  have p0275 :=
    @gJca
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (.classMem R (synCvv))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem (.cv u) C) (.classMem (.cv w) C)))
      p0097 p0274
  have p0276 := @gBrlnqordkern C R (.cv u) (.cv w) dv_cache_0001
  have p0277 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem (.cv u) C) (.classMem (.cv w) C))))
      (synWb (synWbr (synCec (.cv u) (synClnker R)) (synClnqord R C)
          (synCec (.cv w) (synClnker R))) (synWbr (.cv u) R (.cv w)))
      p0275 p0276
  have p0278 :=
    @gBitrd
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (synWbr (.cv x) (synClnqord R C) (.cv z))
      (synWbr (synCec (.cv u) (synClnker R)) (synClnqord R C)
        (synCec (.cv w) (synClnker R)))
      (synWbr (.cv u) R (.cv w)) p0226 p0277
  have p0279 :=
    @gMpbird
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synW3a (.classMem (.cv x) (synClnquo R C))
                (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv z) (synCec (.cv w) (synClnker R)))))
      (synWbr (.cv x) (synClnqord R C) (.cv z)) (synWbr (.cv u) R (.cv w)) p0213 p0278
  have p0280 :=
    @gRexlimddv
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synW3a (.classMem (.cv x) (synClnquo R C))
              (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classEq (.cv z) (synCec (.cv w) (synClnker R)))
      (synWbr (.cv x) (synClnqord R C) (.cv z)) w C dv_cache_0017 dv_cache_0018 p0032
      p0279
  have p0281 :=
    @gRexlimddv
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synW3a (.classMem (.cv x) (synClnquo R C))
            (.classMem (.cv y) (synClnquo R C)) (.classMem (.cv z) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv z)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
      (synWbr (.cv x) (synClnqord R C) (.cv z)) v C dv_cache_0019 dv_cache_0020 p0021
      p0280
  have p0282 :=
    @gRexlimddv
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synW3a (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C))
          (.classMem (.cv z) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv z))))
      (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
      (synWbr (.cv x) (synClnqord R C) (.cv z)) u C dv_cache_0021 dv_cache_0022 p0012
      p0281
  have p0283 :=
    @gTrrd
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      x y z (synClnquo R C) (synClnqord R C) (synCvv) (synCvv) dv_cache_0023
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

/-- Checked nominal proof certificate identified upstream as `g_lnqordconnex`. -/
@[expose]
noncomputable def gLnqordconnex (C : Class) (R : Class) (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf
      (.imp (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWbr (synClnqord R C) (synCconnex) (synClnquo R C))) :=
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
      ((synWo (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x)))).fv :=
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
      ((synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))).fv :=
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
      ((synWo (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x)))).fv :=
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
      ((synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))).fv :=
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
  have dv_cache_0016 : x ∉ ((synClnquo R C)).fv :=
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
  have dv_cache_0017 : y ∉ ((synClnquo R C)).fv :=
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
  have dv_cache_0018 : x ∉ ((synClnqord R C)).fv :=
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
  have dv_cache_0019 : y ∉ ((synClnqord R C)).fv :=
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
      ((synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))).fv :=
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
      ((synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))).fv :=
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
    @gSimpl (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
  have p0001 := @gLnqordexg C R dv_cache_0001
  have p0002 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (.classMem (synClnqord R C) (synCvv)) p0000 p0001
  have p0004 := @gLnquoexg C R dv_cache_0001
  have p0005 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (.classMem (synClnquo R C) (synCvv)) p0000 p0004
  have p0006 :=
    @gSimp2
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C))
  have p0007 := @gVex x
  have p0008 :=
    @gEllnquo u C (.cv x) R dv_cache_0002 dv_cache_0001 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 p0007
  have p0009 :=
    @gBiimpi (.classMem (.cv x) (synClnquo R C))
      (synWrex u C (.classEq (.cv x) (synCec (.cv u) (synClnker R)))) p0008
  have p0010 :=
    @gSyl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (.classMem (.cv x) (synClnquo R C))
      (synWrex u C (.classEq (.cv x) (synCec (.cv u) (synClnker R)))) p0006 p0009
  have p0011 :=
    @gSimpl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0012 :=
    @gSimp3
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C))
  have p0013 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (.classMem (.cv y) (synClnquo R C)) p0011 p0012
  have p0014 := @gVex y
  have p0015 :=
    @gEllnquo v C (.cv y) R dv_cache_0007 dv_cache_0001 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 p0014
  have p0016 :=
    @gBiimpi (.classMem (.cv y) (synClnquo R C))
      (synWrex v C (.classEq (.cv y) (synCec (.cv v) (synClnker R)))) p0015
  have p0017 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (.classMem (.cv y) (synClnquo R C))
      (synWrex v C (.classEq (.cv y) (synCec (.cv v) (synClnker R)))) p0013 p0016
  have p0018 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0020 :=
    @gSimp1
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C))
  have p0021 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0011 p0020
  have p0022 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
        (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0018 p0021
  have p0023 :=
    @gSimpr (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
  have p0024 :=
    @gSimpl
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWss R (synCxp C C))
  have p0025 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      p0023 p0024
  have p0026 :=
    @gSimpr (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWbr R (synCconnex) C)
  have p0027 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWbr R (synCconnex) C) p0025 p0026
  have p0028 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
        (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWbr R (synCconnex) C) p0022 p0027
  have p0030 :=
    @gSimpr
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0031 :=
    @gSimpl (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
  have p0032 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
      (.classMem (.cv u) C) p0030 p0031
  have p0033 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
        (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (.classMem (.cv u) C) p0018 p0032
  have p0034 :=
    @gSimpr
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0035 :=
    @gSimpl (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
  have p0036 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
        (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
      (.classMem (.cv v) C) p0034 p0035
  have p0037 :=
    @gConnexd
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
        (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      C R (.cv u) (.cv v) p0028 p0033 p0036
  have p0040 :=
    @gSimpr (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
  have p0041 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
      (.classEq (.cv x) (synCec (.cv u) (synClnker R))) p0030 p0040
  have p0042 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
        (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (.classEq (.cv x) (synCec (.cv u) (synClnker R))) p0018 p0041
  have p0044 :=
    @gSimpr (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
  have p0045 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
        (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
      (.classEq (.cv y) (synCec (.cv v) (synClnker R))) p0034 p0044
  have p0046 :=
    @gJca
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
        (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
      (.classEq (.cv y) (synCec (.cv v) (synClnker R))) p0042 p0045
  have p0047 :=
    @gBreq12 (.cv x) (synCec (.cv u) (synClnker R)) (.cv y)
      (synCec (.cv v) (synClnker R)) (synClnqord R C)
  have p0048 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
        (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
        (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
      (synWb (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (synCec (.cv u) (synClnker R)) (synClnqord R C)
          (synCec (.cv v) (synClnker R))))
      p0046 p0047
  have p0055 := @gSimpl (.classMem R (synCvv)) (.classMem C (synCvv))
  have p0056 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (.classMem R (synCvv))
      p0000 p0055
  have p0057 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
        (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (.classMem R (synCvv)) p0022 p0056
  have p0066 :=
    @gSimpl (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWbr R (synCconnex) C)
  have p0067 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C)) p0025 p0066
  have p0068 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
        (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C)) p0022 p0067
  have p0075 :=
    @gSimpr
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWss R (synCxp C C))
  have p0076 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
      (synWss R (synCxp C C)) p0023 p0075
  have p0077 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
        (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWss R (synCxp C C)) p0022 p0076
  have p0078 :=
    @gJca
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
        (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWss R (synCxp C C)) p0068 p0077
  have p0087 :=
    @gJca
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
        (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv u) C) (.classMem (.cv v) C) p0033 p0036
  have p0088 :=
    @gJca
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
        (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWss R (synCxp C C)))
      (synWa (.classMem (.cv u) C) (.classMem (.cv v) C)) p0078 p0087
  have p0089 :=
    @gJca
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
        (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem R (synCvv))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem (.cv u) C) (.classMem (.cv v) C)))
      p0057 p0088
  have p0090 := @gBrlnqordkern C R (.cv u) (.cv v) dv_cache_0001
  have p0091 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
        (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem (.cv u) C) (.classMem (.cv v) C))))
      (synWb (synWbr (synCec (.cv u) (synClnker R)) (synClnqord R C)
          (synCec (.cv v) (synClnker R))) (synWbr (.cv u) R (.cv v)))
      p0089 p0090
  have p0092 :=
    @gBitrd
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
        (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWbr (.cv x) (synClnqord R C) (.cv y))
      (synWbr (synCec (.cv u) (synClnker R)) (synClnqord R C)
        (synCec (.cv v) (synClnker R)))
      (synWbr (.cv u) R (.cv v)) p0048 p0091
  have p0101 :=
    @gJca
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
        (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
      (.classEq (.cv x) (synCec (.cv u) (synClnker R))) p0045 p0042
  have p0102 :=
    @gBreq12 (.cv y) (synCec (.cv v) (synClnker R)) (.cv x)
      (synCec (.cv u) (synClnker R)) (synClnqord R C)
  have p0103 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
        (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
        (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
      (synWb (synWbr (.cv y) (synClnqord R C) (.cv x))
        (synWbr (synCec (.cv v) (synClnker R)) (synClnqord R C)
          (synCec (.cv u) (synClnker R))))
      p0101 p0102
  have p0142 :=
    @gJca
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
        (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv v) C) (.classMem (.cv u) C) p0036 p0033
  have p0143 :=
    @gJca
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
        (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWss R (synCxp C C)))
      (synWa (.classMem (.cv v) C) (.classMem (.cv u) C)) p0078 p0142
  have p0144 :=
    @gJca
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
        (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem R (synCvv))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem (.cv v) C) (.classMem (.cv u) C)))
      p0057 p0143
  have p0145 := @gBrlnqordkern C R (.cv v) (.cv u) dv_cache_0001
  have p0146 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
        (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem (.cv v) C) (.classMem (.cv u) C))))
      (synWb (synWbr (synCec (.cv v) (synClnker R)) (synClnqord R C)
          (synCec (.cv u) (synClnker R))) (synWbr (.cv v) R (.cv u)))
      p0144 p0145
  have p0147 :=
    @gBitrd
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
        (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWbr (.cv y) (synClnqord R C) (.cv x))
      (synWbr (synCec (.cv v) (synClnker R)) (synClnqord R C)
        (synCec (.cv u) (synClnker R)))
      (synWbr (.cv v) R (.cv u)) p0103 p0146
  have p0148 :=
    @gOrbi12d
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
        (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWbr (.cv x) (synClnqord R C) (.cv y)) (synWbr (.cv u) R (.cv v))
      (synWbr (.cv y) (synClnqord R C) (.cv x)) (synWbr (.cv v) R (.cv u)) p0092 p0147
  have p0149 :=
    @gMpbird
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
        (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWo (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv x)))
      (synWo (synWbr (.cv u) R (.cv v)) (synWbr (.cv v) R (.cv u))) p0037 p0148
  have p0150 :=
    @gRexlimddv
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
      (synWo (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv x)))
      v C dv_cache_0012 dv_cache_0013 p0017 p0149
  have p0151 :=
    @gRexlimddv
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
      (synWo (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv x)))
      u C dv_cache_0014 dv_cache_0015 p0010 p0150
  have p0152 :=
    @gConnexrd
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      x y (synClnquo R C) (synClnqord R C) (synCvv) (synCvv) dv_cache_0016
      dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
      p0002 p0005 p0151
  exact p0152


end NFChoice.DirectNominalPrf.WPPReplay

end
