/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk017Compact001Block013

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk017Compact001Part062`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hwcardslecconnexndv`. -/
@[expose]
noncomputable def gHwcardslecconnexndv (K : Class) (L : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem K (synChwcards (synCvv)))
          (.classMem L (synChwcards (synCvv))))
        (synWo (synWbr K (synClec) L) (synWbr L (synClec) K))) :=
  by
  let proofSupport : Finset Var := K.fv ∪ L.fv
  let r : Var := freshVar proofSupport 0
  let d : Var := freshVar proofSupport 1
  let s : Var := freshVar proofSupport 2
  let e : Var := freshVar proofSupport 3
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_not_K : r ∉ K.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (h))
  have fresh_r_not_L : r ∉ L.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_d_not_K : d ∉ K.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (h))
  have fresh_d_not_L : d ∉ L.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_s : s ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_s_not_K : s ∉ K.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (h))
  have fresh_s_not_L : s ∉ L.fv := by
    intro h
    exact fresh_s (Finset.mem_union_right _ (h))
  have fresh_e : e ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_e_not_K : e ∉ K.fv := by
    intro h
    exact fresh_e (Finset.mem_union_left _ (h))
  have fresh_e_not_L : e ∉ L.fv := by
    intro h
    exact fresh_e (Finset.mem_union_right _ (h))
  have fresh_r_ne_d : r ≠ d :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_d_ne_r : d ≠ r := Ne.symm fresh_r_ne_d
  have fresh_r_ne_s : r ≠ s :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_s_ne_r : s ≠ r := Ne.symm fresh_r_ne_s
  have fresh_r_ne_e : r ≠ e :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_e_ne_r : e ≠ r := Ne.symm fresh_r_ne_e
  have fresh_d_ne_s : d ≠ s :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_s_ne_d : s ≠ d := Ne.symm fresh_d_ne_s
  have fresh_d_ne_e : d ≠ e :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_e_ne_d : e ≠ d := Ne.symm fresh_d_ne_e
  have fresh_s_ne_e : s ≠ e :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_e_ne_s : e ≠ s := Ne.symm fresh_s_ne_e
  have dv_cache_0001 : d ∉ (K).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_K, not_false_eq_true])
  have dv_cache_0002 : r ∉ (K).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_K, not_false_eq_true])
  have dv_cache_0003 : d ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show d ≠ r from (by exact fresh_d_ne_r))
  have dv_cache_0004 : e ∉ (L).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_e_not_L, not_false_eq_true])
  have dv_cache_0005 : s ∉ (L).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_s_not_L, not_false_eq_true])
  have dv_cache_0006 : e ≠ s :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show e ≠ s from (by exact fresh_e_ne_s))
  have dv_cache_0007 :
    e ∉ ((synWo (synWbr K (synClec) L) (synWbr L (synClec) K))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          fresh_e_not_K, fresh_e_not_L, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0008 :
    s ∉ ((synWo (synWbr K (synClec) L) (synWbr L (synClec) K))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          fresh_s_not_K, fresh_s_not_L, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0009 :
    e ∉
      ((synWa (synWa (.classMem K (synChwcards (synCvv)))
            (.classMem L (synChwcards (synCvv)))) (synWa (synWbr (.cv r) (synCwe) (.cv d))
            (.classEq K (synCnc (.cv d)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_singleton, fresh_e_not_K, fresh_e_not_L, fresh_e_ne_r, fresh_e_ne_d,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 :
    s ∉
      ((synWa (synWa (.classMem K (synChwcards (synCvv)))
            (.classMem L (synChwcards (synCvv)))) (synWa (synWbr (.cv r) (synCwe) (.cv d))
            (.classEq K (synCnc (.cv d)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_singleton, fresh_s_not_K, fresh_s_not_L, fresh_s_ne_r, fresh_s_ne_d,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 :
    d ∉ ((synWo (synWbr K (synClec) L) (synWbr L (synClec) K))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          fresh_d_not_K, fresh_d_not_L, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0012 :
    r ∉ ((synWo (synWbr K (synClec) L) (synWbr L (synClec) K))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          fresh_r_not_K, fresh_r_not_L, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0013 :
    d ∉
      ((synWa (.classMem K (synChwcards (synCvv)))
          (.classMem L (synChwcards (synCvv))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_d_not_K, fresh_d_not_L, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0014 :
    r ∉
      ((synWa (.classMem K (synChwcards (synCvv)))
          (.classMem L (synChwcards (synCvv))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_r_not_K, fresh_r_not_L, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 :=
    @gSimpl (.classMem K (synChwcards (synCvv))) (.classMem L (synChwcards (synCvv)))
  have p0002 := @gElex K (synChwcards (synCvv))
  have p0003 :=
    @gSyl
      (synWa (.classMem K (synChwcards (synCvv))) (.classMem L (synChwcards (synCvv))))
      (.classMem K (synChwcards (synCvv))) (.classMem K (synCvv)) p0000 p0002
  have p0004 := @gElhwcardsweclndv K r d dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0005 :=
    @gSyl
      (synWa (.classMem K (synChwcards (synCvv))) (.classMem L (synChwcards (synCvv))))
      (.classMem K (synCvv))
      (synWb (.classMem K (synChwcards (synCvv))) (synWex d (synWex r
            (synWa (synWbr (.cv r) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d)))))))
      p0003 p0004
  have p0006 :=
    @gMpbid
      (synWa (.classMem K (synChwcards (synCvv))) (.classMem L (synChwcards (synCvv))))
      (.classMem K (synChwcards (synCvv)))
      (synWex d (synWex r
          (synWa (synWbr (.cv r) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d))))))
      p0000 p0005
  have p0007 :=
    @gSimpl
      (synWa (.classMem K (synChwcards (synCvv))) (.classMem L (synChwcards (synCvv))))
      (synWa (synWbr (.cv r) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d))))
  have p0008 :=
    @gSimpr (.classMem K (synChwcards (synCvv))) (.classMem L (synChwcards (synCvv)))
  have p0010 := @gElex L (synChwcards (synCvv))
  have p0011 :=
    @gSyl
      (synWa (.classMem K (synChwcards (synCvv))) (.classMem L (synChwcards (synCvv))))
      (.classMem L (synChwcards (synCvv))) (.classMem L (synCvv)) p0008 p0010
  have p0012 := @gElhwcardsweclndv L s e dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0013 :=
    @gSyl
      (synWa (.classMem K (synChwcards (synCvv))) (.classMem L (synChwcards (synCvv))))
      (.classMem L (synCvv))
      (synWb (.classMem L (synChwcards (synCvv))) (synWex e (synWex s
            (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq L (synCnc (.cv e)))))))
      p0011 p0012
  have p0014 :=
    @gMpbid
      (synWa (.classMem K (synChwcards (synCvv))) (.classMem L (synChwcards (synCvv))))
      (.classMem L (synChwcards (synCvv)))
      (synWex e (synWex s
          (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq L (synCnc (.cv e))))))
      p0008 p0013
  have p0015 :=
    @gSyl
      (synWa (synWa (.classMem K (synChwcards (synCvv)))
          (.classMem L (synChwcards (synCvv))))
        (synWa (synWbr (.cv r) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d)))))
      (synWa (.classMem K (synChwcards (synCvv))) (.classMem L (synChwcards (synCvv))))
      (synWex e (synWex s
          (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq L (synCnc (.cv e))))))
      p0007 p0014
  have p0016 :=
    @gSimpl
      (synWa (synWa (.classMem K (synChwcards (synCvv)))
          (.classMem L (synChwcards (synCvv))))
        (synWa (synWbr (.cv r) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d)))))
      (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq L (synCnc (.cv e))))
  have p0017 :=
    @gSimpr
      (synWa (.classMem K (synChwcards (synCvv))) (.classMem L (synChwcards (synCvv))))
      (synWa (synWbr (.cv r) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d))))
  have p0018 :=
    @gSyl
      (synWa (synWa (synWa (.classMem K (synChwcards (synCvv)))
            (.classMem L (synChwcards (synCvv))))
          (synWa (synWbr (.cv r) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d)))))
        (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq L (synCnc (.cv e)))))
      (synWa (synWa (.classMem K (synChwcards (synCvv)))
          (.classMem L (synChwcards (synCvv))))
        (synWa (synWbr (.cv r) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d)))))
      (synWa (synWbr (.cv r) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d)))) p0016
      p0017
  have p0019 :=
    @gSimpl (synWbr (.cv r) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d)))
  have p0020 :=
    @gSyl
      (synWa (synWa (synWa (.classMem K (synChwcards (synCvv)))
            (.classMem L (synChwcards (synCvv))))
          (synWa (synWbr (.cv r) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d)))))
        (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq L (synCnc (.cv e)))))
      (synWa (synWbr (.cv r) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d))))
      (synWbr (.cv r) (synCwe) (.cv d)) p0018 p0019
  have p0021 :=
    @gSimpr
      (synWa (synWa (.classMem K (synChwcards (synCvv)))
          (.classMem L (synChwcards (synCvv))))
        (synWa (synWbr (.cv r) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d)))))
      (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq L (synCnc (.cv e))))
  have p0022 :=
    @gSimpl (synWbr (.cv s) (synCwe) (.cv e)) (.classEq L (synCnc (.cv e)))
  have p0023 :=
    @gSyl
      (synWa (synWa (synWa (.classMem K (synChwcards (synCvv)))
            (.classMem L (synChwcards (synCvv))))
          (synWa (synWbr (.cv r) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d)))))
        (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq L (synCnc (.cv e)))))
      (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq L (synCnc (.cv e))))
      (synWbr (.cv s) (synCwe) (.cv e)) p0021 p0022
  have p0024 :=
    @gJca
      (synWa (synWa (synWa (.classMem K (synChwcards (synCvv)))
            (.classMem L (synChwcards (synCvv))))
          (synWa (synWbr (.cv r) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d)))))
        (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq L (synCnc (.cv e)))))
      (synWbr (.cv r) (synCwe) (.cv d)) (synWbr (.cv s) (synCwe) (.cv e)) p0020 p0023
  have p0025 := @gWecomparisonnclecandndv e s r d
  have p0026 :=
    @gSyl
      (synWa (synWa (synWa (.classMem K (synChwcards (synCvv)))
            (.classMem L (synChwcards (synCvv))))
          (synWa (synWbr (.cv r) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d)))))
        (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq L (synCnc (.cv e)))))
      (synWa (synWbr (.cv r) (synCwe) (.cv d)) (synWbr (.cv s) (synCwe) (.cv e)))
      (synWo (synWbr (synCnc (.cv d)) (synClec) (synCnc (.cv e)))
        (synWbr (synCnc (.cv e)) (synClec) (synCnc (.cv d))))
      p0024 p0025
  have p0030 :=
    @gSimpr (synWbr (.cv r) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d)))
  have p0031 :=
    @gSyl
      (synWa (synWa (synWa (.classMem K (synChwcards (synCvv)))
            (.classMem L (synChwcards (synCvv))))
          (synWa (synWbr (.cv r) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d)))))
        (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq L (synCnc (.cv e)))))
      (synWa (synWbr (.cv r) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d))))
      (.classEq K (synCnc (.cv d))) p0018 p0030
  have p0032 :=
    @gEqcomd
      (synWa (synWa (synWa (.classMem K (synChwcards (synCvv)))
            (.classMem L (synChwcards (synCvv))))
          (synWa (synWbr (.cv r) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d)))))
        (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq L (synCnc (.cv e)))))
      K (synCnc (.cv d)) p0031
  have p0034 :=
    @gSimpr (synWbr (.cv s) (synCwe) (.cv e)) (.classEq L (synCnc (.cv e)))
  have p0035 :=
    @gSyl
      (synWa (synWa (synWa (.classMem K (synChwcards (synCvv)))
            (.classMem L (synChwcards (synCvv))))
          (synWa (synWbr (.cv r) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d)))))
        (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq L (synCnc (.cv e)))))
      (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq L (synCnc (.cv e))))
      (.classEq L (synCnc (.cv e))) p0021 p0034
  have p0036 :=
    @gEqcomd
      (synWa (synWa (synWa (.classMem K (synChwcards (synCvv)))
            (.classMem L (synChwcards (synCvv))))
          (synWa (synWbr (.cv r) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d)))))
        (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq L (synCnc (.cv e)))))
      L (synCnc (.cv e)) p0035
  have p0037 :=
    @gBreq12d
      (synWa (synWa (synWa (.classMem K (synChwcards (synCvv)))
            (.classMem L (synChwcards (synCvv))))
          (synWa (synWbr (.cv r) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d)))))
        (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq L (synCnc (.cv e)))))
      (synCnc (.cv d)) K (synCnc (.cv e)) L (synClec) p0032 p0036
  have p0048 :=
    @gBreq12d
      (synWa (synWa (synWa (.classMem K (synChwcards (synCvv)))
            (.classMem L (synChwcards (synCvv))))
          (synWa (synWbr (.cv r) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d)))))
        (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq L (synCnc (.cv e)))))
      (synCnc (.cv e)) L (synCnc (.cv d)) K (synClec) p0036 p0032
  have p0049 :=
    @gOrbi12d
      (synWa (synWa (synWa (.classMem K (synChwcards (synCvv)))
            (.classMem L (synChwcards (synCvv))))
          (synWa (synWbr (.cv r) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d)))))
        (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq L (synCnc (.cv e)))))
      (synWbr (synCnc (.cv d)) (synClec) (synCnc (.cv e))) (synWbr K (synClec) L)
      (synWbr (synCnc (.cv e)) (synClec) (synCnc (.cv d))) (synWbr L (synClec) K)
      p0037 p0048
  have p0050 :=
    @gMpbid
      (synWa (synWa (synWa (.classMem K (synChwcards (synCvv)))
            (.classMem L (synChwcards (synCvv))))
          (synWa (synWbr (.cv r) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d)))))
        (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq L (synCnc (.cv e)))))
      (synWo (synWbr (synCnc (.cv d)) (synClec) (synCnc (.cv e)))
        (synWbr (synCnc (.cv e)) (synClec) (synCnc (.cv d))))
      (synWo (synWbr K (synClec) L) (synWbr L (synClec) K)) p0026 p0049
  have p0051 :=
    @gEx
      (synWa (synWa (.classMem K (synChwcards (synCvv)))
          (.classMem L (synChwcards (synCvv))))
        (synWa (synWbr (.cv r) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d)))))
      (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq L (synCnc (.cv e))))
      (synWo (synWbr K (synClec) L) (synWbr L (synClec) K)) p0050
  have p0052 :=
    @gExlimdvv
      (synWa (synWa (.classMem K (synChwcards (synCvv)))
          (.classMem L (synChwcards (synCvv))))
        (synWa (synWbr (.cv r) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d)))))
      (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq L (synCnc (.cv e))))
      (synWo (synWbr K (synClec) L) (synWbr L (synClec) K)) e s dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 p0051
  have p0053 :=
    @gMpd
      (synWa (synWa (.classMem K (synChwcards (synCvv)))
          (.classMem L (synChwcards (synCvv))))
        (synWa (synWbr (.cv r) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d)))))
      (synWex e (synWex s
          (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq L (synCnc (.cv e))))))
      (synWo (synWbr K (synClec) L) (synWbr L (synClec) K)) p0015 p0052
  have p0054 :=
    @gEx
      (synWa (.classMem K (synChwcards (synCvv))) (.classMem L (synChwcards (synCvv))))
      (synWa (synWbr (.cv r) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d))))
      (synWo (synWbr K (synClec) L) (synWbr L (synClec) K)) p0053
  have p0055 :=
    @gExlimdvv
      (synWa (.classMem K (synChwcards (synCvv))) (.classMem L (synChwcards (synCvv))))
      (synWa (synWbr (.cv r) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d))))
      (synWo (synWbr K (synClec) L) (synWbr L (synClec) K)) d r dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 p0054
  have p0056 :=
    @gMpd
      (synWa (.classMem K (synChwcards (synCvv))) (.classMem L (synChwcards (synCvv))))
      (synWex d (synWex r
          (synWa (synWbr (.cv r) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d))))))
      (synWo (synWbr K (synClec) L) (synWbr L (synClec) K)) p0006 p0055
  exact p0056

/-- Checked nominal proof certificate identified upstream as `g_wpporbithwcldmndv`. -/
@[expose]
noncomputable def gWpporbithwcldmndv (F : Class) (I : Class) (q : Var)
    (_dv_F_q : q ∉ F.fv) (_dv_I_q : q ∉ I.fv)
    (hyp_wpporbithwcldmndv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wpporbithwcldmndv_2 : Nominal.NPrf (.classMem I (synCdm F)))
    (hyp_wpporbithwcldmndv_3 : Nominal.NPrf (synWss (synCrn F) (synCdm F)))
    (hyp_wpporbithwcldmndv_4 : Nominal.NPrf (.classEq (synCdm F) (synChwcards (synCvv)))) :
    Nominal.NPrf
      (synWral q (synCnnc)
        (.classMem (synCfv (synCfrec F I) (.cv q)) (synChwcards (synCvv)))) :=
  by
  have p0000 :=
    @gN3pm32i (.classMem F (synCfuns)) (.classMem I (synCdm F))
      (synWss (synCrn F) (synCdm F)) hyp_wpporbithwcldmndv_1 hyp_wpporbithwcldmndv_2
      hyp_wpporbithwcldmndv_3
  have p0001 := @gId (.classMem (.cv q) (synCnnc))
  have p0002 := @gFrecdomfv F I (.cv q)
  have p0003 :=
    @gSylancr (.classMem (.cv q) (synCnnc))
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (.classMem (.cv q) (synCnnc))
      (.classMem (synCfv (synCfrec F I) (.cv q)) (synCdm F)) p0000 p0001 p0002
  have p0004 :=
    @gEleq2i (synCdm F) (synChwcards (synCvv)) (synCfv (synCfrec F I) (.cv q))
      hyp_wpporbithwcldmndv_4
  have p0005 :=
    @gSylib (.classMem (.cv q) (synCnnc))
      (.classMem (synCfv (synCfrec F I) (.cv q)) (synCdm F))
      (.classMem (synCfv (synCfrec F I) (.cv q)) (synChwcards (synCvv))) p0003 p0004
  have p0006 := Nominal.gen p0005 q
  have p0007 :=
    (Nominal.biimpRefl (synWral q (synCnnc)
        (.classMem (synCfv (synCfrec F I) (.cv q)) (synChwcards (synCvv)))))
  have p0008 :=
    @gMpbir
      (synWral q (synCnnc)
        (.classMem (synCfv (synCfrec F I) (.cv q)) (synChwcards (synCvv))))
      (.all q (.imp (.classMem (.cv q) (synCnnc))
          (.classMem (synCfv (synCfrec F I) (.cv q)) (synChwcards (synCvv)))))
      p0006 p0007
  exact p0008


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part063`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_wppgammaprefixeqhwselfmapndv`. -/
@[expose]
noncomputable def gWppgammaprefixeqhwselfmapndv (y : Var) (F : Class) (G : Class)
    (L : Class) (dv_F_y : y ∉ F.fv) (dv_G_y : y ∉ G.fv) (dv_L_y : y ∉ L.fv)
    (hyp_wppgammaprefixeqhwselfmapndv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppgammaprefixeqhwselfmapndv_2 : Nominal.NPrf (synWss (synCrn F) (synCdm F)))
    (hyp_wppgammaprefixeqhwselfmapndv_3 :
      Nominal.NPrf (.classEq (synCdm F) (synChwcards (synCvv))))
    (hyp_wppgammaprefixeqhwselfmapndv_4 : Nominal.NPrf (.classMem G (synCfuns)))
    (hyp_wppgammaprefixeqhwselfmapndv_5 : Nominal.NPrf (synWss (synCrn G) (synCdm G)))
    (hyp_wppgammaprefixeqhwselfmapndv_6 :
      Nominal.NPrf (.classEq (synCdm G) (synChwcards (synCvv))))
    (hyp_wppgammaprefixeqhwselfmapndv_7 : Nominal.NPrf (.classMem L (synChwcards (synCvv))))
    (hyp_wppgammaprefixeqhwselfmapndv_8 : Nominal.NPrf (synWral y (synChwcards (synCvv))
          (.imp (synWbr (.cv y) (synClec) L)
            (.classEq (synCfv F (.cv y)) (synCfv G (.cv y)))))) :
    Nominal.NPrf (.classEq (synCwppgamma F L) (synCwppgamma G L)) :=
  by
  let proofSupport : Finset Var := ({ y } : Finset Var) ∪ F.fv ∪ G.fv ∪ L.fv
  let q : Var := freshVar proofSupport 0
  let k : Var := freshVar proofSupport 1
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_ne_y : q ≠ y := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_q : y ≠ q := Ne.symm fresh_q_ne_y
  have fresh_q_not_F : q ∉ F.fv := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_q_not_G : q ∉ G.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_not_L : q ∉ L.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_k : k ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_k_not_F : k ∉ F.fv := by
    intro h
    exact
      fresh_k
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_k_not_G : k ∉ G.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_k_not_L : k ∉ L.fv := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (h))
  have dv_cache_0001 : k ∉ (L).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_k_not_L, not_false_eq_true])
  have dv_cache_0002 : k ∉ (F).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_k_not_F, not_false_eq_true])
  have dv_cache_0003 : q ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_F, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((synCwppgamma F L)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          Finset.mem_union, fresh_q_not_L, fresh_q_not_F, or_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((synCfv (synCfrec F (synCwppgamma F L)) (.cv q))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_q, dv_F_y, dv_L_y, or_false,
          not_false_eq_true])
  have dv_cache_0006 : y ∉ ((synChwcards (synCvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0007 :
    y ∉
      ((Wff.imp (synWbr (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) (synClec) L)
          (.classEq (synCfv F (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)))
            (synCfv G (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_q, dv_F_y, dv_L_y, dv_G_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 : q ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_G, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((synCfv (synCfrec G (synCwppgamma F L)) (.cv q))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_q, dv_G_y, dv_L_y, dv_F_y, or_false,
          not_false_eq_true])
  have dv_cache_0010 :
    y ∉
      ((Wff.imp (synWbr (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)) (synClec) L)
          (.classEq (synCfv F (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)))
            (synCfv G (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_q, dv_G_y, dv_L_y, dv_F_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 : k ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_k_not_G, not_false_eq_true])
  have dv_cache_0012 : q ∉ ((synCwppgamma G L)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          Finset.mem_union, fresh_q_not_L, fresh_q_not_G, or_false, not_false_eq_true])
  have dv_cache_0013 : y ∉ ((synCfv (synCfrec F (synCwppgamma G L)) (.cv q))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_q, dv_F_y, dv_L_y, dv_G_y, or_false,
          not_false_eq_true])
  have dv_cache_0014 :
    y ∉
      ((Wff.imp (synWbr (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) (synClec) L)
          (.classEq (synCfv F (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)))
            (synCfv G (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_q, dv_F_y, dv_L_y, dv_G_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ ((synCfv (synCfrec G (synCwppgamma G L)) (.cv q))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_q, dv_G_y, dv_L_y, or_false,
          not_false_eq_true])
  have dv_cache_0016 :
    y ∉
      ((Wff.imp (synWbr (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)) (synClec) L)
          (.classEq (synCfv F (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)))
            (synCfv G (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_q, dv_G_y, dv_L_y, dv_F_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0017 : q ∉ (L).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_L, not_false_eq_true])
  have p0000 := @gElex F (synCfuns)
  have p0001 := Nominal.mp hyp_wppgammaprefixeqhwselfmapndv_1 p0000
  have p0002 :=
    @gPm32i (.classMem F (synCvv)) (.classMem L (synChwcards (synCvv))) p0001
      hyp_wppgammaprefixeqhwselfmapndv_7
  have p0003 := @gWppgammaminhwndv L k F dv_cache_0001 dv_cache_0002
  have p0004 := Nominal.mp p0002 p0003
  have p0005 :=
    @gSimpl (.classMem (synCwppgamma F L) (synCwppcand F L))
      (synWral k (synCwppcand F L) (synWbr (synCwppgamma F L) (synClec) (.cv k)))
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := @gElwppcand L (synCwppgamma F L) F
  have p0008 :=
    @gMpbi (.classMem (synCwppgamma F L) (synCwppcand F L))
      (synWa (synWa (.classMem (synCwppgamma F L) (synChwcards (synCvv)))
          (synWbr (synCwppgamma F L) (synClec) L))
        (.classMem (synCwppgamma F L) (synCwppreach F L)))
      p0006 p0007
  have p0009 :=
    @gSimpl
      (synWa (.classMem (synCwppgamma F L) (synChwcards (synCvv)))
        (synWbr (synCwppgamma F L) (synClec) L))
      (.classMem (synCwppgamma F L) (synCwppreach F L))
  have p0010 := Nominal.mp p0008 p0009
  have p0011 :=
    @gSimpl (.classMem (synCwppgamma F L) (synChwcards (synCvv)))
      (synWbr (synCwppgamma F L) (synClec) L)
  have p0012 := Nominal.mp p0010 p0011
  have p0013 :=
    @gEleq2i (synCdm F) (synChwcards (synCvv)) (synCwppgamma F L)
      hyp_wppgammaprefixeqhwselfmapndv_3
  have p0014 :=
    @gMpbir (.classMem (synCwppgamma F L) (synCdm F))
      (.classMem (synCwppgamma F L) (synChwcards (synCvv))) p0012 p0013
  have p0028 :=
    @gEleq2i (synCdm G) (synChwcards (synCvv)) (synCwppgamma F L)
      hyp_wppgammaprefixeqhwselfmapndv_6
  have p0029 :=
    @gMpbir (.classMem (synCwppgamma F L) (synCdm G))
      (.classMem (synCwppgamma F L) (synChwcards (synCvv))) p0012 p0028
  have p0045 :=
    @gWpporbithwcldmndv F (synCwppgamma F L) q dv_cache_0003 dv_cache_0004
      hyp_wppgammaprefixeqhwselfmapndv_1 p0014 hyp_wppgammaprefixeqhwselfmapndv_2
      hyp_wppgammaprefixeqhwselfmapndv_3
  have p0046 :=
    @gA1i (.classMem L (synChwcards (synCvv)))
      (synWa (.classMem (.cv q) (synCnnc))
        (.classMem (synCfv (synCfrec F (synCwppgamma F L)) (.cv q))
          (synChwcards (synCvv))))
      hyp_wppgammaprefixeqhwselfmapndv_7
  have p0047 :=
    @gSimpr (.classMem (.cv q) (synCnnc))
      (.classMem (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) (synChwcards (synCvv)))
  have p0048 :=
    @gJca
      (synWa (.classMem (.cv q) (synCnnc))
        (.classMem (synCfv (synCfrec F (synCwppgamma F L)) (.cv q))
          (synChwcards (synCvv))))
      (.classMem L (synChwcards (synCvv)))
      (.classMem (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) (synChwcards (synCvv)))
      p0046 p0047
  have p0049 :=
    @gHwcardslecconnexndv L (synCfv (synCfrec F (synCwppgamma F L)) (.cv q))
  have p0050 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCnnc))
        (.classMem (synCfv (synCfrec F (synCwppgamma F L)) (.cv q))
          (synChwcards (synCvv))))
      (synWa (.classMem L (synChwcards (synCvv)))
        (.classMem (synCfv (synCfrec F (synCwppgamma F L)) (.cv q))
          (synChwcards (synCvv))))
      (synWo (synWbr L (synClec) (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)))
        (synWbr (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) (synClec) L))
      p0048 p0049
  have p0051 :=
    @gNotnot (synWbr L (synClec) (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)))
  have p0052 :=
    @gBiimpi (synWbr L (synClec) (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)))
      (.neg (.neg (synWbr L (synClec) (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)))))
      p0051
  have p0053 :=
    @gPm221
      (.neg (synWbr L (synClec) (synCfv (synCfrec F (synCwppgamma F L)) (.cv q))))
      (synWbr (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) (synClec) L)
  have p0054 :=
    @gSyl (synWbr L (synClec) (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)))
      (.neg (.neg (synWbr L (synClec) (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)))))
      (.imp (.neg (synWbr L (synClec) (synCfv (synCfrec F (synCwppgamma F L)) (.cv q))))
        (synWbr (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) (synClec) L))
      p0052 p0053
  have p0055 :=
    @gId (synWbr (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) (synClec) L)
  have p0056 :=
    @gA1d (synWbr (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) (synClec) L)
      (synWbr (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) (synClec) L)
      (.neg (synWbr L (synClec) (synCfv (synCfrec F (synCwppgamma F L)) (.cv q))))
      p0055
  have p0057 :=
    @gJaoi (synWbr L (synClec) (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)))
      (.imp (.neg (synWbr L (synClec) (synCfv (synCfrec F (synCwppgamma F L)) (.cv q))))
        (synWbr (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) (synClec) L))
      (synWbr (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) (synClec) L) p0054
      p0056
  have p0058 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCnnc))
        (.classMem (synCfv (synCfrec F (synCwppgamma F L)) (.cv q))
          (synChwcards (synCvv))))
      (synWo (synWbr L (synClec) (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)))
        (synWbr (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) (synClec) L))
      (.imp (.neg (synWbr L (synClec) (synCfv (synCfrec F (synCwppgamma F L)) (.cv q))))
        (synWbr (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) (synClec) L))
      p0050 p0057
  have p0059 :=
    @gRalimiaa
      (.classMem (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) (synChwcards (synCvv)))
      (.imp (.neg (synWbr L (synClec) (synCfv (synCfrec F (synCwppgamma F L)) (.cv q))))
        (synWbr (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) (synClec) L))
      q (synCnnc) p0058
  have p0060 := Nominal.mp p0045 p0059
  have p0078 :=
    @gA1i
      (synWral y (synChwcards (synCvv)) (.imp (synWbr (.cv y) (synClec) L)
          (.classEq (synCfv F (.cv y)) (synCfv G (.cv y)))))
      (.classMem (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) (synChwcards (synCvv)))
      hyp_wppgammaprefixeqhwselfmapndv_8
  have p0079 :=
    @gId (.classEq (.cv y) (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)))
  have p0080 :=
    @gBreq1d (.classEq (.cv y) (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)))
      (.cv y) (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) L (synClec) p0079
  have p0082 :=
    @gFveq2d (.classEq (.cv y) (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)))
      (.cv y) (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) F p0079
  have p0084 :=
    @gFveq2d (.classEq (.cv y) (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)))
      (.cv y) (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) G p0079
  have p0085 :=
    @gEqeq12d (.classEq (.cv y) (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)))
      (synCfv F (.cv y)) (synCfv F (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)))
      (synCfv G (.cv y)) (synCfv G (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)))
      p0082 p0084
  have p0086 :=
    @gImbi12d (.classEq (.cv y) (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)))
      (synWbr (.cv y) (synClec) L)
      (synWbr (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) (synClec) L)
      (.classEq (synCfv F (.cv y)) (synCfv G (.cv y)))
      (.classEq (synCfv F (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)))
        (synCfv G (synCfv (synCfrec F (synCwppgamma F L)) (.cv q))))
      p0080 p0085
  have p0087 :=
    @gRspcv
      (.imp (synWbr (.cv y) (synClec) L) (.classEq (synCfv F (.cv y)) (synCfv G (.cv y))))
      (.imp (synWbr (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) (synClec) L)
        (.classEq (synCfv F (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)))
          (synCfv G (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)))))
      y (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) (synChwcards (synCvv))
      dv_cache_0005 dv_cache_0006 dv_cache_0007 p0086
  have p0088 :=
    @gMpd
      (.classMem (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) (synChwcards (synCvv)))
      (synWral y (synChwcards (synCvv)) (.imp (synWbr (.cv y) (synClec) L)
          (.classEq (synCfv F (.cv y)) (synCfv G (.cv y)))))
      (.imp (synWbr (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) (synClec) L)
        (.classEq (synCfv F (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)))
          (synCfv G (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)))))
      p0078 p0087
  have p0089 :=
    @gImpcom
      (.classMem (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) (synChwcards (synCvv)))
      (synWbr (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) (synClec) L)
      (.classEq (synCfv F (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)))
        (synCfv G (synCfv (synCfrec F (synCwppgamma F L)) (.cv q))))
      p0088
  have p0090 :=
    @gEqcomd
      (synWa (synWbr (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) (synClec) L)
        (.classMem (synCfv (synCfrec F (synCwppgamma F L)) (.cv q))
          (synChwcards (synCvv))))
      (synCfv F (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)))
      (synCfv G (synCfv (synCfrec F (synCwppgamma F L)) (.cv q))) p0089
  have p0091 :=
    @gExpcom (synWbr (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) (synClec) L)
      (.classMem (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) (synChwcards (synCvv)))
      (.classEq (synCfv G (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)))
        (synCfv F (synCfv (synCfrec F (synCwppgamma F L)) (.cv q))))
      p0090
  have p0092 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCnnc))
        (.classMem (synCfv (synCfrec F (synCwppgamma F L)) (.cv q))
          (synChwcards (synCvv))))
      (.classMem (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) (synChwcards (synCvv)))
      (.imp (synWbr (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) (synClec) L)
        (.classEq (synCfv G (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)))
          (synCfv F (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)))))
      p0047 p0091
  have p0093 :=
    @gRalimiaa
      (.classMem (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) (synChwcards (synCvv)))
      (.imp (synWbr (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) (synClec) L)
        (.classEq (synCfv G (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)))
          (synCfv F (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)))))
      q (synCnnc) p0092
  have p0094 := Nominal.mp p0045 p0093
  have p0110 :=
    @gWpporbithwcldmndv G (synCwppgamma F L) q dv_cache_0008 dv_cache_0004
      hyp_wppgammaprefixeqhwselfmapndv_4 p0029 hyp_wppgammaprefixeqhwselfmapndv_5
      hyp_wppgammaprefixeqhwselfmapndv_6
  have p0111 :=
    @gA1i (.classMem L (synChwcards (synCvv)))
      (synWa (.classMem (.cv q) (synCnnc))
        (.classMem (synCfv (synCfrec G (synCwppgamma F L)) (.cv q))
          (synChwcards (synCvv))))
      hyp_wppgammaprefixeqhwselfmapndv_7
  have p0112 :=
    @gSimpr (.classMem (.cv q) (synCnnc))
      (.classMem (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)) (synChwcards (synCvv)))
  have p0113 :=
    @gJca
      (synWa (.classMem (.cv q) (synCnnc))
        (.classMem (synCfv (synCfrec G (synCwppgamma F L)) (.cv q))
          (synChwcards (synCvv))))
      (.classMem L (synChwcards (synCvv)))
      (.classMem (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)) (synChwcards (synCvv)))
      p0111 p0112
  have p0114 :=
    @gHwcardslecconnexndv L (synCfv (synCfrec G (synCwppgamma F L)) (.cv q))
  have p0115 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCnnc))
        (.classMem (synCfv (synCfrec G (synCwppgamma F L)) (.cv q))
          (synChwcards (synCvv))))
      (synWa (.classMem L (synChwcards (synCvv)))
        (.classMem (synCfv (synCfrec G (synCwppgamma F L)) (.cv q))
          (synChwcards (synCvv))))
      (synWo (synWbr L (synClec) (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)))
        (synWbr (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)) (synClec) L))
      p0113 p0114
  have p0116 :=
    @gNotnot (synWbr L (synClec) (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)))
  have p0117 :=
    @gBiimpi (synWbr L (synClec) (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)))
      (.neg (.neg (synWbr L (synClec) (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)))))
      p0116
  have p0118 :=
    @gPm221
      (.neg (synWbr L (synClec) (synCfv (synCfrec G (synCwppgamma F L)) (.cv q))))
      (synWbr (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)) (synClec) L)
  have p0119 :=
    @gSyl (synWbr L (synClec) (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)))
      (.neg (.neg (synWbr L (synClec) (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)))))
      (.imp (.neg (synWbr L (synClec) (synCfv (synCfrec G (synCwppgamma F L)) (.cv q))))
        (synWbr (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)) (synClec) L))
      p0117 p0118
  have p0120 :=
    @gId (synWbr (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)) (synClec) L)
  have p0121 :=
    @gA1d (synWbr (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)) (synClec) L)
      (synWbr (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)) (synClec) L)
      (.neg (synWbr L (synClec) (synCfv (synCfrec G (synCwppgamma F L)) (.cv q))))
      p0120
  have p0122 :=
    @gJaoi (synWbr L (synClec) (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)))
      (.imp (.neg (synWbr L (synClec) (synCfv (synCfrec G (synCwppgamma F L)) (.cv q))))
        (synWbr (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)) (synClec) L))
      (synWbr (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)) (synClec) L) p0119
      p0121
  have p0123 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCnnc))
        (.classMem (synCfv (synCfrec G (synCwppgamma F L)) (.cv q))
          (synChwcards (synCvv))))
      (synWo (synWbr L (synClec) (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)))
        (synWbr (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)) (synClec) L))
      (.imp (.neg (synWbr L (synClec) (synCfv (synCfrec G (synCwppgamma F L)) (.cv q))))
        (synWbr (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)) (synClec) L))
      p0115 p0122
  have p0124 :=
    @gRalimiaa
      (.classMem (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)) (synChwcards (synCvv)))
      (.imp (.neg (synWbr L (synClec) (synCfv (synCfrec G (synCwppgamma F L)) (.cv q))))
        (synWbr (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)) (synClec) L))
      q (synCnnc) p0123
  have p0125 := Nominal.mp p0110 p0124
  have p0143 :=
    @gA1i
      (synWral y (synChwcards (synCvv)) (.imp (synWbr (.cv y) (synClec) L)
          (.classEq (synCfv F (.cv y)) (synCfv G (.cv y)))))
      (.classMem (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)) (synChwcards (synCvv)))
      hyp_wppgammaprefixeqhwselfmapndv_8
  have p0144 :=
    @gId (.classEq (.cv y) (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)))
  have p0145 :=
    @gBreq1d (.classEq (.cv y) (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)))
      (.cv y) (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)) L (synClec) p0144
  have p0147 :=
    @gFveq2d (.classEq (.cv y) (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)))
      (.cv y) (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)) F p0144
  have p0149 :=
    @gFveq2d (.classEq (.cv y) (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)))
      (.cv y) (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)) G p0144
  have p0150 :=
    @gEqeq12d (.classEq (.cv y) (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)))
      (synCfv F (.cv y)) (synCfv F (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)))
      (synCfv G (.cv y)) (synCfv G (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)))
      p0147 p0149
  have p0151 :=
    @gImbi12d (.classEq (.cv y) (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)))
      (synWbr (.cv y) (synClec) L)
      (synWbr (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)) (synClec) L)
      (.classEq (synCfv F (.cv y)) (synCfv G (.cv y)))
      (.classEq (synCfv F (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)))
        (synCfv G (synCfv (synCfrec G (synCwppgamma F L)) (.cv q))))
      p0145 p0150
  have p0152 :=
    @gRspcv
      (.imp (synWbr (.cv y) (synClec) L) (.classEq (synCfv F (.cv y)) (synCfv G (.cv y))))
      (.imp (synWbr (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)) (synClec) L)
        (.classEq (synCfv F (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)))
          (synCfv G (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)))))
      y (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)) (synChwcards (synCvv))
      dv_cache_0009 dv_cache_0006 dv_cache_0010 p0151
  have p0153 :=
    @gMpd
      (.classMem (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)) (synChwcards (synCvv)))
      (synWral y (synChwcards (synCvv)) (.imp (synWbr (.cv y) (synClec) L)
          (.classEq (synCfv F (.cv y)) (synCfv G (.cv y)))))
      (.imp (synWbr (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)) (synClec) L)
        (.classEq (synCfv F (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)))
          (synCfv G (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)))))
      p0143 p0152
  have p0154 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCnnc))
        (.classMem (synCfv (synCfrec G (synCwppgamma F L)) (.cv q))
          (synChwcards (synCvv))))
      (.classMem (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)) (synChwcards (synCvv)))
      (.imp (synWbr (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)) (synClec) L)
        (.classEq (synCfv F (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)))
          (synCfv G (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)))))
      p0112 p0153
  have p0155 :=
    @gRalimiaa
      (.classMem (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)) (synChwcards (synCvv)))
      (.imp (synWbr (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)) (synClec) L)
        (.classEq (synCfv F (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)))
          (synCfv G (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)))))
      q (synCnnc) p0154
  have p0156 := Nominal.mp p0110 p0155
  have p0157 := @gElex G (synCfuns)
  have p0158 := Nominal.mp hyp_wppgammaprefixeqhwselfmapndv_4 p0157
  have p0159 :=
    @gPm32i (.classMem G (synCvv)) (.classMem L (synChwcards (synCvv))) p0158
      hyp_wppgammaprefixeqhwselfmapndv_7
  have p0160 := @gWppgammaminhwndv L k G dv_cache_0001 dv_cache_0011
  have p0161 := Nominal.mp p0159 p0160
  have p0162 :=
    @gSimpl (.classMem (synCwppgamma G L) (synCwppcand G L))
      (synWral k (synCwppcand G L) (synWbr (synCwppgamma G L) (synClec) (.cv k)))
  have p0163 := Nominal.mp p0161 p0162
  have p0164 := @gElwppcand L (synCwppgamma G L) G
  have p0165 :=
    @gMpbi (.classMem (synCwppgamma G L) (synCwppcand G L))
      (synWa (synWa (.classMem (synCwppgamma G L) (synChwcards (synCvv)))
          (synWbr (synCwppgamma G L) (synClec) L))
        (.classMem (synCwppgamma G L) (synCwppreach G L)))
      p0163 p0164
  have p0166 :=
    @gSimpl
      (synWa (.classMem (synCwppgamma G L) (synChwcards (synCvv)))
        (synWbr (synCwppgamma G L) (synClec) L))
      (.classMem (synCwppgamma G L) (synCwppreach G L))
  have p0167 := Nominal.mp p0165 p0166
  have p0168 :=
    @gSimpl (.classMem (synCwppgamma G L) (synChwcards (synCvv)))
      (synWbr (synCwppgamma G L) (synClec) L)
  have p0169 := Nominal.mp p0167 p0168
  have p0170 :=
    @gEleq2i (synCdm F) (synChwcards (synCvv)) (synCwppgamma G L)
      hyp_wppgammaprefixeqhwselfmapndv_3
  have p0171 :=
    @gMpbir (.classMem (synCwppgamma G L) (synCdm F))
      (.classMem (synCwppgamma G L) (synChwcards (synCvv))) p0169 p0170
  have p0185 :=
    @gEleq2i (synCdm G) (synChwcards (synCvv)) (synCwppgamma G L)
      hyp_wppgammaprefixeqhwselfmapndv_6
  have p0186 :=
    @gMpbir (.classMem (synCwppgamma G L) (synCdm G))
      (.classMem (synCwppgamma G L) (synChwcards (synCvv))) p0169 p0185
  have p0202 :=
    @gWpporbithwcldmndv F (synCwppgamma G L) q dv_cache_0003 dv_cache_0012
      hyp_wppgammaprefixeqhwselfmapndv_1 p0171 hyp_wppgammaprefixeqhwselfmapndv_2
      hyp_wppgammaprefixeqhwselfmapndv_3
  have p0203 :=
    @gA1i (.classMem L (synChwcards (synCvv)))
      (synWa (.classMem (.cv q) (synCnnc))
        (.classMem (synCfv (synCfrec F (synCwppgamma G L)) (.cv q))
          (synChwcards (synCvv))))
      hyp_wppgammaprefixeqhwselfmapndv_7
  have p0204 :=
    @gSimpr (.classMem (.cv q) (synCnnc))
      (.classMem (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) (synChwcards (synCvv)))
  have p0205 :=
    @gJca
      (synWa (.classMem (.cv q) (synCnnc))
        (.classMem (synCfv (synCfrec F (synCwppgamma G L)) (.cv q))
          (synChwcards (synCvv))))
      (.classMem L (synChwcards (synCvv)))
      (.classMem (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) (synChwcards (synCvv)))
      p0203 p0204
  have p0206 :=
    @gHwcardslecconnexndv L (synCfv (synCfrec F (synCwppgamma G L)) (.cv q))
  have p0207 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCnnc))
        (.classMem (synCfv (synCfrec F (synCwppgamma G L)) (.cv q))
          (synChwcards (synCvv))))
      (synWa (.classMem L (synChwcards (synCvv)))
        (.classMem (synCfv (synCfrec F (synCwppgamma G L)) (.cv q))
          (synChwcards (synCvv))))
      (synWo (synWbr L (synClec) (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)))
        (synWbr (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) (synClec) L))
      p0205 p0206
  have p0208 :=
    @gNotnot (synWbr L (synClec) (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)))
  have p0209 :=
    @gBiimpi (synWbr L (synClec) (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)))
      (.neg (.neg (synWbr L (synClec) (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)))))
      p0208
  have p0210 :=
    @gPm221
      (.neg (synWbr L (synClec) (synCfv (synCfrec F (synCwppgamma G L)) (.cv q))))
      (synWbr (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) (synClec) L)
  have p0211 :=
    @gSyl (synWbr L (synClec) (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)))
      (.neg (.neg (synWbr L (synClec) (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)))))
      (.imp (.neg (synWbr L (synClec) (synCfv (synCfrec F (synCwppgamma G L)) (.cv q))))
        (synWbr (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) (synClec) L))
      p0209 p0210
  have p0212 :=
    @gId (synWbr (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) (synClec) L)
  have p0213 :=
    @gA1d (synWbr (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) (synClec) L)
      (synWbr (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) (synClec) L)
      (.neg (synWbr L (synClec) (synCfv (synCfrec F (synCwppgamma G L)) (.cv q))))
      p0212
  have p0214 :=
    @gJaoi (synWbr L (synClec) (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)))
      (.imp (.neg (synWbr L (synClec) (synCfv (synCfrec F (synCwppgamma G L)) (.cv q))))
        (synWbr (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) (synClec) L))
      (synWbr (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) (synClec) L) p0211
      p0213
  have p0215 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCnnc))
        (.classMem (synCfv (synCfrec F (synCwppgamma G L)) (.cv q))
          (synChwcards (synCvv))))
      (synWo (synWbr L (synClec) (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)))
        (synWbr (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) (synClec) L))
      (.imp (.neg (synWbr L (synClec) (synCfv (synCfrec F (synCwppgamma G L)) (.cv q))))
        (synWbr (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) (synClec) L))
      p0207 p0214
  have p0216 :=
    @gRalimiaa
      (.classMem (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) (synChwcards (synCvv)))
      (.imp (.neg (synWbr L (synClec) (synCfv (synCfrec F (synCwppgamma G L)) (.cv q))))
        (synWbr (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) (synClec) L))
      q (synCnnc) p0215
  have p0217 := Nominal.mp p0202 p0216
  have p0235 :=
    @gA1i
      (synWral y (synChwcards (synCvv)) (.imp (synWbr (.cv y) (synClec) L)
          (.classEq (synCfv F (.cv y)) (synCfv G (.cv y)))))
      (.classMem (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) (synChwcards (synCvv)))
      hyp_wppgammaprefixeqhwselfmapndv_8
  have p0236 :=
    @gId (.classEq (.cv y) (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)))
  have p0237 :=
    @gBreq1d (.classEq (.cv y) (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)))
      (.cv y) (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) L (synClec) p0236
  have p0239 :=
    @gFveq2d (.classEq (.cv y) (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)))
      (.cv y) (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) F p0236
  have p0241 :=
    @gFveq2d (.classEq (.cv y) (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)))
      (.cv y) (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) G p0236
  have p0242 :=
    @gEqeq12d (.classEq (.cv y) (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)))
      (synCfv F (.cv y)) (synCfv F (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)))
      (synCfv G (.cv y)) (synCfv G (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)))
      p0239 p0241
  have p0243 :=
    @gImbi12d (.classEq (.cv y) (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)))
      (synWbr (.cv y) (synClec) L)
      (synWbr (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) (synClec) L)
      (.classEq (synCfv F (.cv y)) (synCfv G (.cv y)))
      (.classEq (synCfv F (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)))
        (synCfv G (synCfv (synCfrec F (synCwppgamma G L)) (.cv q))))
      p0237 p0242
  have p0244 :=
    @gRspcv
      (.imp (synWbr (.cv y) (synClec) L) (.classEq (synCfv F (.cv y)) (synCfv G (.cv y))))
      (.imp (synWbr (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) (synClec) L)
        (.classEq (synCfv F (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)))
          (synCfv G (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)))))
      y (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) (synChwcards (synCvv))
      dv_cache_0013 dv_cache_0006 dv_cache_0014 p0243
  have p0245 :=
    @gMpd
      (.classMem (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) (synChwcards (synCvv)))
      (synWral y (synChwcards (synCvv)) (.imp (synWbr (.cv y) (synClec) L)
          (.classEq (synCfv F (.cv y)) (synCfv G (.cv y)))))
      (.imp (synWbr (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) (synClec) L)
        (.classEq (synCfv F (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)))
          (synCfv G (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)))))
      p0235 p0244
  have p0246 :=
    @gImpcom
      (.classMem (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) (synChwcards (synCvv)))
      (synWbr (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) (synClec) L)
      (.classEq (synCfv F (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)))
        (synCfv G (synCfv (synCfrec F (synCwppgamma G L)) (.cv q))))
      p0245
  have p0247 :=
    @gEqcomd
      (synWa (synWbr (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) (synClec) L)
        (.classMem (synCfv (synCfrec F (synCwppgamma G L)) (.cv q))
          (synChwcards (synCvv))))
      (synCfv F (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)))
      (synCfv G (synCfv (synCfrec F (synCwppgamma G L)) (.cv q))) p0246
  have p0248 :=
    @gExpcom (synWbr (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) (synClec) L)
      (.classMem (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) (synChwcards (synCvv)))
      (.classEq (synCfv G (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)))
        (synCfv F (synCfv (synCfrec F (synCwppgamma G L)) (.cv q))))
      p0247
  have p0249 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCnnc))
        (.classMem (synCfv (synCfrec F (synCwppgamma G L)) (.cv q))
          (synChwcards (synCvv))))
      (.classMem (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) (synChwcards (synCvv)))
      (.imp (synWbr (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) (synClec) L)
        (.classEq (synCfv G (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)))
          (synCfv F (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)))))
      p0204 p0248
  have p0250 :=
    @gRalimiaa
      (.classMem (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) (synChwcards (synCvv)))
      (.imp (synWbr (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) (synClec) L)
        (.classEq (synCfv G (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)))
          (synCfv F (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)))))
      q (synCnnc) p0249
  have p0251 := Nominal.mp p0202 p0250
  have p0267 :=
    @gWpporbithwcldmndv G (synCwppgamma G L) q dv_cache_0008 dv_cache_0012
      hyp_wppgammaprefixeqhwselfmapndv_4 p0186 hyp_wppgammaprefixeqhwselfmapndv_5
      hyp_wppgammaprefixeqhwselfmapndv_6
  have p0268 :=
    @gA1i (.classMem L (synChwcards (synCvv)))
      (synWa (.classMem (.cv q) (synCnnc))
        (.classMem (synCfv (synCfrec G (synCwppgamma G L)) (.cv q))
          (synChwcards (synCvv))))
      hyp_wppgammaprefixeqhwselfmapndv_7
  have p0269 :=
    @gSimpr (.classMem (.cv q) (synCnnc))
      (.classMem (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)) (synChwcards (synCvv)))
  have p0270 :=
    @gJca
      (synWa (.classMem (.cv q) (synCnnc))
        (.classMem (synCfv (synCfrec G (synCwppgamma G L)) (.cv q))
          (synChwcards (synCvv))))
      (.classMem L (synChwcards (synCvv)))
      (.classMem (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)) (synChwcards (synCvv)))
      p0268 p0269
  have p0271 :=
    @gHwcardslecconnexndv L (synCfv (synCfrec G (synCwppgamma G L)) (.cv q))
  have p0272 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCnnc))
        (.classMem (synCfv (synCfrec G (synCwppgamma G L)) (.cv q))
          (synChwcards (synCvv))))
      (synWa (.classMem L (synChwcards (synCvv)))
        (.classMem (synCfv (synCfrec G (synCwppgamma G L)) (.cv q))
          (synChwcards (synCvv))))
      (synWo (synWbr L (synClec) (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)))
        (synWbr (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)) (synClec) L))
      p0270 p0271
  have p0273 :=
    @gNotnot (synWbr L (synClec) (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)))
  have p0274 :=
    @gBiimpi (synWbr L (synClec) (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)))
      (.neg (.neg (synWbr L (synClec) (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)))))
      p0273
  have p0275 :=
    @gPm221
      (.neg (synWbr L (synClec) (synCfv (synCfrec G (synCwppgamma G L)) (.cv q))))
      (synWbr (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)) (synClec) L)
  have p0276 :=
    @gSyl (synWbr L (synClec) (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)))
      (.neg (.neg (synWbr L (synClec) (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)))))
      (.imp (.neg (synWbr L (synClec) (synCfv (synCfrec G (synCwppgamma G L)) (.cv q))))
        (synWbr (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)) (synClec) L))
      p0274 p0275
  have p0277 :=
    @gId (synWbr (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)) (synClec) L)
  have p0278 :=
    @gA1d (synWbr (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)) (synClec) L)
      (synWbr (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)) (synClec) L)
      (.neg (synWbr L (synClec) (synCfv (synCfrec G (synCwppgamma G L)) (.cv q))))
      p0277
  have p0279 :=
    @gJaoi (synWbr L (synClec) (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)))
      (.imp (.neg (synWbr L (synClec) (synCfv (synCfrec G (synCwppgamma G L)) (.cv q))))
        (synWbr (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)) (synClec) L))
      (synWbr (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)) (synClec) L) p0276
      p0278
  have p0280 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCnnc))
        (.classMem (synCfv (synCfrec G (synCwppgamma G L)) (.cv q))
          (synChwcards (synCvv))))
      (synWo (synWbr L (synClec) (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)))
        (synWbr (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)) (synClec) L))
      (.imp (.neg (synWbr L (synClec) (synCfv (synCfrec G (synCwppgamma G L)) (.cv q))))
        (synWbr (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)) (synClec) L))
      p0272 p0279
  have p0281 :=
    @gRalimiaa
      (.classMem (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)) (synChwcards (synCvv)))
      (.imp (.neg (synWbr L (synClec) (synCfv (synCfrec G (synCwppgamma G L)) (.cv q))))
        (synWbr (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)) (synClec) L))
      q (synCnnc) p0280
  have p0282 := Nominal.mp p0267 p0281
  have p0300 :=
    @gA1i
      (synWral y (synChwcards (synCvv)) (.imp (synWbr (.cv y) (synClec) L)
          (.classEq (synCfv F (.cv y)) (synCfv G (.cv y)))))
      (.classMem (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)) (synChwcards (synCvv)))
      hyp_wppgammaprefixeqhwselfmapndv_8
  have p0301 :=
    @gId (.classEq (.cv y) (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)))
  have p0302 :=
    @gBreq1d (.classEq (.cv y) (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)))
      (.cv y) (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)) L (synClec) p0301
  have p0304 :=
    @gFveq2d (.classEq (.cv y) (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)))
      (.cv y) (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)) F p0301
  have p0306 :=
    @gFveq2d (.classEq (.cv y) (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)))
      (.cv y) (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)) G p0301
  have p0307 :=
    @gEqeq12d (.classEq (.cv y) (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)))
      (synCfv F (.cv y)) (synCfv F (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)))
      (synCfv G (.cv y)) (synCfv G (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)))
      p0304 p0306
  have p0308 :=
    @gImbi12d (.classEq (.cv y) (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)))
      (synWbr (.cv y) (synClec) L)
      (synWbr (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)) (synClec) L)
      (.classEq (synCfv F (.cv y)) (synCfv G (.cv y)))
      (.classEq (synCfv F (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)))
        (synCfv G (synCfv (synCfrec G (synCwppgamma G L)) (.cv q))))
      p0302 p0307
  have p0309 :=
    @gRspcv
      (.imp (synWbr (.cv y) (synClec) L) (.classEq (synCfv F (.cv y)) (synCfv G (.cv y))))
      (.imp (synWbr (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)) (synClec) L)
        (.classEq (synCfv F (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)))
          (synCfv G (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)))))
      y (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)) (synChwcards (synCvv))
      dv_cache_0015 dv_cache_0006 dv_cache_0016 p0308
  have p0310 :=
    @gMpd
      (.classMem (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)) (synChwcards (synCvv)))
      (synWral y (synChwcards (synCvv)) (.imp (synWbr (.cv y) (synClec) L)
          (.classEq (synCfv F (.cv y)) (synCfv G (.cv y)))))
      (.imp (synWbr (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)) (synClec) L)
        (.classEq (synCfv F (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)))
          (synCfv G (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)))))
      p0300 p0309
  have p0311 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCnnc))
        (.classMem (synCfv (synCfrec G (synCwppgamma G L)) (.cv q))
          (synChwcards (synCvv))))
      (.classMem (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)) (synChwcards (synCvv)))
      (.imp (synWbr (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)) (synClec) L)
        (.classEq (synCfv F (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)))
          (synCfv G (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)))))
      p0269 p0310
  have p0312 :=
    @gRalimiaa
      (.classMem (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)) (synChwcards (synCvv)))
      (.imp (synWbr (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)) (synClec) L)
        (.classEq (synCfv F (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)))
          (synCfv G (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)))))
      q (synCnnc) p0311
  have p0313 := Nominal.mp p0267 p0312
  have p0314 :=
    @gWppgammaprefixeqpointndv F G L q dv_cache_0003 dv_cache_0008 dv_cache_0017
      hyp_wppgammaprefixeqhwselfmapndv_1 hyp_wppgammaprefixeqhwselfmapndv_2
      hyp_wppgammaprefixeqhwselfmapndv_4 hyp_wppgammaprefixeqhwselfmapndv_5
      hyp_wppgammaprefixeqhwselfmapndv_7 p0014 p0029 p0060 p0094 p0125 p0156 p0171 p0186
      p0217 p0251 p0282 p0313
  exact p0314


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part064`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_wppstopgammaprefixeqndv`. -/
@[expose]
noncomputable def gWppstopgammaprefixeqndv (C : Class) (F : Class) (p : Var)
    (dv_C_p : p ∉ C.fv) (dv_F_p : p ∉ F.fv)
    (hyp_wppstopgammaprefixeqndv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppstopgammaprefixeqndv_2 :
      Nominal.NPrf (synWss (synCrn F) (synChwcards (synCvv))))
    (hyp_wppstopgammaprefixeqndv_3 : Nominal.NPrf (.classMem C (synChwcards (synCvv))))
    (hyp_wppstopgammaprefixeqndv_4 : Nominal.NPrf (synWbr (synCtc C) (synClec) C))
    (hyp_wppstopgammaprefixeqndv_5 : Nominal.NPrf (synWral p (synChwcards (synCvv))
          (.imp (synWbr (.cv p) (synClec) C) (.classMem (.cv p) (synCdm F))))) :
    Nominal.NPrf
      (.classEq (synCwppgamma (synCwppstopstep F (synCtc C)) (synCtc C))
        (synCwppgamma (synCwppstopstep F C) (synCtc C))) :=
  by
  let proofSupport : Finset Var := C.fv ∪ F.fv ∪ ({ p } : Finset Var)
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_p : y ≠ p := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_y : p ≠ y := Ne.symm fresh_y_ne_p
  have dv_cache_0001 : p ∉ (C).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_p, not_false_eq_true])
  have dv_cache_0002 : p ∉ (F).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_p, not_false_eq_true])
  have dv_cache_0003 : p ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show p ≠ y from (by exact fresh_p_ne_y))
  have dv_cache_0004 : y ∉ ((synCwppstopstep F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, fresh_y_not_C, fresh_y_not_F, or_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((synCwppstopstep F (synCtc C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union,
          fresh_y_not_C, fresh_y_not_F, or_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((synCtc C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, fresh_y_not_C,
          not_false_eq_true])
  have p0000 :=
    @gWppstopstepfunsndv C F hyp_wppstopgammaprefixeqndv_1 hyp_wppstopgammaprefixeqndv_2
  have p0001 :=
    @gWppstopsteprndmndv C F hyp_wppstopgammaprefixeqndv_1 hyp_wppstopgammaprefixeqndv_2
  have p0002 :=
    @gWppstopstepdmndv C F hyp_wppstopgammaprefixeqndv_1 hyp_wppstopgammaprefixeqndv_2
  have p0003 :=
    @gWppstopstepfunsndv (synCtc C) F hyp_wppstopgammaprefixeqndv_1
      hyp_wppstopgammaprefixeqndv_2
  have p0004 :=
    @gWppstopsteprndmndv (synCtc C) F hyp_wppstopgammaprefixeqndv_1
      hyp_wppstopgammaprefixeqndv_2
  have p0005 :=
    @gWppstopstepdmndv (synCtc C) F hyp_wppstopgammaprefixeqndv_1
      hyp_wppstopgammaprefixeqndv_2
  have p0006 := @gHwcardstcclndv C
  have p0007 := Nominal.mp hyp_wppstopgammaprefixeqndv_3 p0006
  have p0008 :=
    @gWppstopstepsamebelowdndv y C F p dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_wppstopgammaprefixeqndv_1 hyp_wppstopgammaprefixeqndv_2
      hyp_wppstopgammaprefixeqndv_3 hyp_wppstopgammaprefixeqndv_4
      hyp_wppstopgammaprefixeqndv_5
  have p0009 := Nominal.gen p0008 y
  have p0010 :=
    (Nominal.biimpRefl (synWral y (synChwcards (synCvv))
        (.imp (synWbr (.cv y) (synClec) (synCtc C))
          (.classEq (synCfv (synCwppstopstep F C) (.cv y))
            (synCfv (synCwppstopstep F (synCtc C)) (.cv y))))))
  have p0011 :=
    @gMpbir
      (synWral y (synChwcards (synCvv)) (.imp (synWbr (.cv y) (synClec) (synCtc C))
          (.classEq (synCfv (synCwppstopstep F C) (.cv y))
            (synCfv (synCwppstopstep F (synCtc C)) (.cv y)))))
      (.all y (.imp (.classMem (.cv y) (synChwcards (synCvv)))
          (.imp (synWbr (.cv y) (synClec) (synCtc C))
            (.classEq (synCfv (synCwppstopstep F C) (.cv y))
              (synCfv (synCwppstopstep F (synCtc C)) (.cv y))))))
      p0009 p0010
  have p0012 :=
    @gWppgammaprefixeqhwselfmapndv y (synCwppstopstep F C)
      (synCwppstopstep F (synCtc C)) (synCtc C) dv_cache_0004 dv_cache_0005
      dv_cache_0006 p0000 p0001 p0002 p0003 p0004 p0005 p0007 p0011
  have p0013 :=
    @gEqcomi (synCwppgamma (synCwppstopstep F C) (synCtc C))
      (synCwppgamma (synCwppstopstep F (synCtc C)) (synCtc C)) p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_wpphitstartcongrndv`. -/
@[expose]
noncomputable def gWpphitstartcongrndv (C : Class) (F : Class) (I : Class) (J : Class) :
    Nominal.NPrf
      (.imp (.classEq I J) (.classEq (synCwpphit F I C) (synCwpphit F J C))) :=
  by
  have p0000 := @gId (.classEq I J)
  have p0001 := @gEqid F
  have p0002 := @gJctil (.classEq I J) (.classEq I J) (.classEq F F) p0000 p0001
  have p0003 := @gFreceq12 F F I J
  have p0004 :=
    @gSyl (.classEq I J) (synWa (.classEq F F) (.classEq I J))
      (.classEq (synCfrec F I) (synCfrec F J)) p0002 p0003
  have p0005 := @gCnveqd (.classEq I J) (synCfrec F I) (synCfrec F J) p0004
  have p0006 :=
    @gImaeq1d (.classEq I J) (synCcnv (synCfrec F I)) (synCcnv (synCfrec F J))
      (synCima (synClec) (synCsn C)) p0005
  have p0007 := (Nominal.classEqRefl (synCwpphit F I C))
  have p0008 := (Nominal.classEqRefl (synCwpphit F J C))
  have p0009 :=
    @gN3eqtr4g (.classEq I J)
      (synCima (synCcnv (synCfrec F I)) (synCima (synClec) (synCsn C)))
      (synCima (synCcnv (synCfrec F J)) (synCima (synClec) (synCsn C)))
      (synCwpphit F I C) (synCwpphit F J C) p0006 p0007 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_wppcrossgammaleasthitpairhwndv`. -/
@[expose]
noncomputable def gWppcrossgammaleasthitpairhwndv (C : Class) (k : Var) (m : Var)
    (n : Var) (F : Class) (G : Class) (q : Var) (p : Var) (dv_C_k : k ∉ C.fv)
    (dv_C_m : m ∉ C.fv) (dv_C_n : n ∉ C.fv) (dv_C_p : p ∉ C.fv) (dv_C_q : q ∉ C.fv)
    (_dv_F_k : k ∉ F.fv) (dv_F_m : m ∉ F.fv) (dv_F_n : n ∉ F.fv) (dv_F_p : p ∉ F.fv)
    (_dv_F_q : q ∉ F.fv) (dv_G_k : k ∉ G.fv) (_dv_G_m : m ∉ G.fv) (_dv_G_n : n ∉ G.fv)
    (dv_G_p : p ∉ G.fv) (dv_G_q : q ∉ G.fv) (_dv_k_m : k ≠ m) (_dv_k_n : k ≠ n)
    (_dv_k_p : k ≠ p) (dv_k_q : k ≠ q) (dv_m_n : m ≠ n) (_dv_m_p : m ≠ p)
    (_dv_m_q : m ≠ q) (_dv_n_p : n ≠ p) (_dv_n_q : n ≠ q) (_dv_p_q : p ≠ q)
    (hyp_wppcrossgammaleasthitpairhwndv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppcrossgammaleasthitpairhwndv_2 : Nominal.NPrf (synWss (synCrn F) (synCdm F)))
    (hyp_wppcrossgammaleasthitpairhwndv_3 : Nominal.NPrf (synWral p (synChwcards (synCvv))
          (.imp (synWbr (.cv p) (synClec) C) (.classMem (.cv p) (synCdm F)))))
    (hyp_wppcrossgammaleasthitpairhwndv_4 : Nominal.NPrf (.classMem G (synCfuns)))
    (hyp_wppcrossgammaleasthitpairhwndv_5 : Nominal.NPrf (synWss (synCrn G) (synCdm G)))
    (hyp_wppcrossgammaleasthitpairhwndv_6 : Nominal.NPrf (synWral p (synChwcards (synCvv))
          (.imp (synWbr (.cv p) (synClec) (synCtc C)) (.classMem (.cv p) (synCdm G)))))
    (hyp_wppcrossgammaleasthitpairhwndv_7 : Nominal.NPrf (.classMem C (synChwcards (synCvv))))
    (hyp_wppcrossgammaleasthitpairhwndv_8 : Nominal.NPrf
        (.classEq (synCtc (synCwppgamma F C)) (synCwppgamma G (synCtc C)))) :
    Nominal.NPrf
      (synWa (synWrex m (synCnnc)
          (synWa (.classMem (.cv m) (synCwpphit F (synCwppgamma F C) C))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) (synCwpphit F (synCwppgamma F C) C))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))))) (synWrex k (synCnnc)
          (synWa (.classMem (.cv k) (synCwpphit G (synCtc (synCwppgamma F C)) (synCtc C)))
            (synWral q (synCnnc) (.imp (.classMem (.cv q)
                  (synCwpphit G (synCtc (synCwppgamma F C)) (synCtc C)))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))) :=
  by
  have dv_cache_0001 : m ∉ (C).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_m, not_false_eq_true])
  have dv_cache_0002 : n ∉ (C).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_n, not_false_eq_true])
  have dv_cache_0003 : p ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_p, not_false_eq_true])
  have dv_cache_0004 : m ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_m, not_false_eq_true])
  have dv_cache_0005 : n ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_n, not_false_eq_true])
  have dv_cache_0006 : p ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_p, not_false_eq_true])
  have dv_cache_0007 : m ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show m ≠ n from (by exact dv_m_n))
  have dv_cache_0008 : k ∉ ((synCtc C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, dv_C_k,
          not_false_eq_true])
  have dv_cache_0009 : q ∉ ((synCtc C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, dv_C_q,
          not_false_eq_true])
  have dv_cache_0010 : p ∉ ((synCtc C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, dv_C_p,
          not_false_eq_true])
  have dv_cache_0011 : k ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_G_k, not_false_eq_true])
  have dv_cache_0012 : q ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_G_q, not_false_eq_true])
  have dv_cache_0013 : p ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_G_p, not_false_eq_true])
  have dv_cache_0014 : k ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show k ≠ q from (by exact dv_k_q))
  have p0000 :=
    @gWppgammaleasthithwndv C m n F p dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      hyp_wppcrossgammaleasthitpairhwndv_1 hyp_wppcrossgammaleasthitpairhwndv_2
      hyp_wppcrossgammaleasthitpairhwndv_3 hyp_wppcrossgammaleasthitpairhwndv_7
  have p0001 := @gHwcardstcclndv C
  have p0002 := Nominal.mp hyp_wppcrossgammaleasthitpairhwndv_7 p0001
  have p0003 :=
    @gWppgammaleasthithwndv (synCtc C) k q G p dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
      hyp_wppcrossgammaleasthitpairhwndv_4 hyp_wppcrossgammaleasthitpairhwndv_5
      hyp_wppcrossgammaleasthitpairhwndv_6 p0002
  have p0004 :=
    @gEqcomi (synCtc (synCwppgamma F C)) (synCwppgamma G (synCtc C))
      hyp_wppcrossgammaleasthitpairhwndv_8
  have p0005 :=
    @gWpphitstartcongrndv (synCtc C) G (synCwppgamma G (synCtc C))
      (synCtc (synCwppgamma F C))
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @gEleq2i (synCwpphit G (synCwppgamma G (synCtc C)) (synCtc C))
      (synCwpphit G (synCtc (synCwppgamma F C)) (synCtc C)) (.cv k) p0006
  have p0011 :=
    @gEleq2i (synCwpphit G (synCwppgamma G (synCtc C)) (synCtc C))
      (synCwpphit G (synCtc (synCwppgamma F C)) (synCtc C)) (.cv q) p0006
  have p0012 :=
    @gImbi1i
      (.classMem (.cv q) (synCwpphit G (synCwppgamma G (synCtc C)) (synCtc C)))
      (.classMem (.cv q) (synCwpphit G (synCtc (synCwppgamma F C)) (synCtc C)))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q)) p0011
  have p0013 :=
    @gRalbii
      (.imp (.classMem (.cv q) (synCwpphit G (synCwppgamma G (synCtc C)) (synCtc C)))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q)))
      (.imp (.classMem (.cv q) (synCwpphit G (synCtc (synCwppgamma F C)) (synCtc C)))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q)))
      q (synCnnc) p0012
  have p0014 :=
    @gAnbi12i
      (.classMem (.cv k) (synCwpphit G (synCwppgamma G (synCtc C)) (synCtc C)))
      (.classMem (.cv k) (synCwpphit G (synCtc (synCwppgamma F C)) (synCtc C)))
      (synWral q (synCnnc) (.imp
          (.classMem (.cv q) (synCwpphit G (synCwppgamma G (synCtc C)) (synCtc C)))
          (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))
      (synWral q (synCnnc) (.imp
          (.classMem (.cv q) (synCwpphit G (synCtc (synCwppgamma F C)) (synCtc C)))
          (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))
      p0007 p0013
  have p0015 :=
    @gRexbii
      (synWa (.classMem (.cv k) (synCwpphit G (synCwppgamma G (synCtc C)) (synCtc C)))
        (synWral q (synCnnc) (.imp
            (.classMem (.cv q) (synCwpphit G (synCwppgamma G (synCtc C)) (synCtc C)))
            (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q)))))
      (synWa (.classMem (.cv k) (synCwpphit G (synCtc (synCwppgamma F C)) (synCtc C)))
        (synWral q (synCnnc) (.imp
            (.classMem (.cv q) (synCwpphit G (synCtc (synCwppgamma F C)) (synCtc C)))
            (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q)))))
      k (synCnnc) p0014
  have p0016 :=
    @gMpbi
      (synWrex k (synCnnc) (synWa
          (.classMem (.cv k) (synCwpphit G (synCwppgamma G (synCtc C)) (synCtc C)))
          (synWral q (synCnnc) (.imp (.classMem (.cv q)
                (synCwpphit G (synCwppgamma G (synCtc C)) (synCtc C)))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWrex k (synCnnc) (synWa
          (.classMem (.cv k) (synCwpphit G (synCtc (synCwppgamma F C)) (synCtc C)))
          (synWral q (synCnnc) (.imp (.classMem (.cv q)
                (synCwpphit G (synCtc (synCwppgamma F C)) (synCtc C)))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      p0003 p0015
  have p0017 :=
    @gPm32i
      (synWrex m (synCnnc) (synWa (.classMem (.cv m) (synCwpphit F (synCwppgamma F C) C))
          (synWral n (synCnnc) (.imp (.classMem (.cv n) (synCwpphit F (synCwppgamma F C) C))
              (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n))))))
      (synWrex k (synCnnc) (synWa
          (.classMem (.cv k) (synCwpphit G (synCtc (synCwppgamma F C)) (synCtc C)))
          (synWral q (synCnnc) (.imp (.classMem (.cv q)
                (synCwpphit G (synCtc (synCwppgamma F C)) (synCtc C)))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      p0000 p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_wppstopgammaleasthitpairndv`. -/
@[expose]
noncomputable def gWppstopgammaleasthitpairndv (x : Var) (C : Class) (k : Var) (m : Var)
    (n : Var) (F : Class) (q : Var) (dv_C_k : k ∉ C.fv) (dv_C_m : m ∉ C.fv)
    (dv_C_n : n ∉ C.fv) (dv_C_q : q ∉ C.fv) (dv_C_x : x ∉ C.fv) (dv_F_k : k ∉ F.fv)
    (dv_F_m : m ∉ F.fv) (dv_F_n : n ∉ F.fv) (dv_F_q : q ∉ F.fv) (dv_F_x : x ∉ F.fv)
    (dv_k_m : k ≠ m) (dv_k_n : k ≠ n) (dv_k_q : k ≠ q) (_dv_k_x : k ≠ x) (dv_m_n : m ≠ n)
    (dv_m_q : m ≠ q) (_dv_m_x : m ≠ x) (dv_n_q : n ≠ q) (_dv_n_x : n ≠ x)
    (_dv_q_x : q ≠ x)
    (hyp_wppstopgammaleasthitpairndv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppstopgammaleasthitpairndv_2 :
      Nominal.NPrf (synWss (synCrn F) (synChwcards (synCvv))))
    (hyp_wppstopgammaleasthitpairndv_3 : Nominal.NPrf (.classMem C (synChwcards (synCvv))))
    (hyp_wppstopgammaleasthitpairndv_4 : Nominal.NPrf
        (synWral x (synCdm (synCwppstopstep F C))
          (.classEq (synCtc (synCfv (synCwppstopstep F C) (.cv x)))
            (synCfv (synCwppstopstep F (synCtc C)) (synCtc (.cv x)))))) :
    Nominal.NPrf
      (synWa (synWrex m (synCnnc) (synWa (.classMem (.cv m)
              (synCwpphit (synCwppstopstep F C) (synCwppgamma (synCwppstopstep F C) C) C))
            (synWral n (synCnnc) (.imp (.classMem (.cv n) (synCwpphit (synCwppstopstep F C)
                    (synCwppgamma (synCwppstopstep F C) C) C))
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))))) (synWrex k (synCnnc)
          (synWa (.classMem (.cv k) (synCwpphit (synCwppstopstep F (synCtc C))
                (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
            (synWral q (synCnnc) (.imp (.classMem (.cv q)
                  (synCwpphit (synCwppstopstep F (synCtc C))
                    (synCtc (synCwppgamma (synCwppstopstep F C) C)) (synCtc C)))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ C.fv ∪ ({ k } : Finset Var) ∪ ({ m } : Finset Var) ∪
          ({ n } : Finset Var) ∪
        F.fv ∪
      ({ q } : Finset Var)
  let p : Var := freshVar proofSupport 0
  let r : Var := freshVar proofSupport 1
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_ne_x : p ≠ x := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_p_not_C : p ∉ C.fv := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_p_ne_k : p ≠ k := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_k_ne_p : k ≠ p := Ne.symm fresh_p_ne_k
  have fresh_p_ne_m : p ≠ m := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_m_ne_p : m ≠ p := Ne.symm fresh_p_ne_m
  have fresh_p_ne_n : p ≠ n := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_n_ne_p : n ≠ p := Ne.symm fresh_p_ne_n
  have fresh_p_not_F : p ∉ F.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_ne_q : p ≠ q := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_r_ne_x : r ≠ x := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_r_not_C : r ∉ C.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_r_not_F : r ∉ F.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_ne_r : p ≠ r :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : r ∉ ((synChwcards (synCvv))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0002 : p ≠ r := by
    clear dv_cache_0001
    exact (show p ≠ r from (by exact fresh_p_ne_r))
  have dv_cache_0003 : p ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_C, not_false_eq_true])
  have dv_cache_0004 : r ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_C, not_false_eq_true])
  have dv_cache_0005 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_x, not_false_eq_true])
  have dv_cache_0006 : p ∉ ((synCwppstopstep F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, fresh_p_not_C, fresh_p_not_F, or_false, not_false_eq_true])
  have dv_cache_0007 : r ∉ ((synCwppstopstep F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, fresh_r_not_C, fresh_r_not_F, or_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((synCwppstopstep F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, dv_C_x, dv_F_x, or_false, not_false_eq_true])
  have dv_cache_0009 : p ∉ ((synCwppstopstep F (synCtc C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union,
          fresh_p_not_C, fresh_p_not_F, or_false, not_false_eq_true])
  have dv_cache_0010 : r ∉ ((synCwppstopstep F (synCtc C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union,
          fresh_r_not_C, fresh_r_not_F, or_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((synCwppstopstep F (synCtc C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, dv_C_x,
          dv_F_x, or_false, not_false_eq_true])
  have dv_cache_0012 : p ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show p ≠ x from (by exact fresh_p_ne_x))
  have dv_cache_0013 : r ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0014 : k ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_k, not_false_eq_true])
  have dv_cache_0015 : m ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_m, not_false_eq_true])
  have dv_cache_0016 : n ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_n, not_false_eq_true])
  have dv_cache_0017 : q ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_q, not_false_eq_true])
  have dv_cache_0018 : k ∉ ((synCwppstopstep F C)).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, dv_C_k, dv_F_k, or_false, not_false_eq_true])
  have dv_cache_0019 : m ∉ ((synCwppstopstep F C)).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, dv_C_m, dv_F_m, or_false, not_false_eq_true])
  have dv_cache_0020 : n ∉ ((synCwppstopstep F C)).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, dv_C_n, dv_F_n, or_false, not_false_eq_true])
  have dv_cache_0021 : q ∉ ((synCwppstopstep F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, dv_C_q, dv_F_q, or_false, not_false_eq_true])
  have dv_cache_0022 : k ∉ ((synCwppstopstep F (synCtc C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, dv_C_k,
          dv_F_k, or_false, not_false_eq_true])
  have dv_cache_0023 : m ∉ ((synCwppstopstep F (synCtc C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, dv_C_m,
          dv_F_m, or_false, not_false_eq_true])
  have dv_cache_0024 : n ∉ ((synCwppstopstep F (synCtc C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, dv_C_n,
          dv_F_n, or_false, not_false_eq_true])
  have dv_cache_0025 : q ∉ ((synCwppstopstep F (synCtc C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, dv_C_q,
          dv_F_q, or_false, not_false_eq_true])
  have dv_cache_0026 : k ≠ m :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact (show k ≠ m from (by exact dv_k_m))
  have dv_cache_0027 : k ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (show k ≠ n from (by exact dv_k_n))
  have dv_cache_0028 : k ≠ p :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (show k ≠ p from (by exact fresh_k_ne_p))
  have dv_cache_0029 : k ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (show k ≠ q from (by exact dv_k_q))
  have dv_cache_0030 : m ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (show m ≠ n from (by exact dv_m_n))
  have dv_cache_0031 : m ≠ p :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact (show m ≠ p from (by exact fresh_m_ne_p))
  have dv_cache_0032 : m ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact (show m ≠ q from (by exact dv_m_q))
  have dv_cache_0033 : n ≠ p :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (show n ≠ p from (by exact fresh_n_ne_p))
  have dv_cache_0034 : n ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (show n ≠ q from (by exact dv_n_q))
  have dv_cache_0035 : p ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact (show p ≠ q from (by exact fresh_p_ne_q))
  have p0000 :=
    @gWppstopstepfunsndv C F hyp_wppstopgammaleasthitpairndv_1
      hyp_wppstopgammaleasthitpairndv_2
  have p0001 :=
    @gWppstopsteprndmndv C F hyp_wppstopgammaleasthitpairndv_1
      hyp_wppstopgammaleasthitpairndv_2
  have p0002 :=
    @gWppstopstepdmndv C F hyp_wppstopgammaleasthitpairndv_1
      hyp_wppstopgammaleasthitpairndv_2
  have p0003 :=
    @gEleq2i (synCdm (synCwppstopstep F C)) (synChwcards (synCvv)) (.cv p) p0002
  have p0004 :=
    @gBiimpri (.classMem (.cv p) (synCdm (synCwppstopstep F C)))
      (.classMem (.cv p) (synChwcards (synCvv))) p0003
  have p0005 := Nominal.gen p0004 p
  have p0006 :=
    (Nominal.biimpRefl (synWral p (synChwcards (synCvv))
        (.classMem (.cv p) (synCdm (synCwppstopstep F C)))))
  have p0007 :=
    @gMpbir
      (synWral p (synChwcards (synCvv)) (.classMem (.cv p) (synCdm (synCwppstopstep F C))))
      (.all p (.imp (.classMem (.cv p) (synChwcards (synCvv)))
          (.classMem (.cv p) (synCdm (synCwppstopstep F C)))))
      p0005 p0006
  have p0008 :=
    Nominal.ax1 (.classMem (.cv p) (synCdm (synCwppstopstep F C)))
      (synWbr (.cv p) (synClec) C)
  have p0009 :=
    @gA1i
      (.imp (.classMem (.cv p) (synCdm (synCwppstopstep F C)))
        (.imp (synWbr (.cv p) (synClec) C)
          (.classMem (.cv p) (synCdm (synCwppstopstep F C)))))
      (.classMem (.cv p) (synChwcards (synCvv))) p0008
  have p0010 :=
    @gRalimia (.classMem (.cv p) (synCdm (synCwppstopstep F C)))
      (.imp (synWbr (.cv p) (synClec) C) (.classMem (.cv p) (synCdm (synCwppstopstep F C))))
      p (synChwcards (synCvv)) p0009
  have p0011 := Nominal.mp p0007 p0010
  have p0012 :=
    @gWppstopstepfunsndv (synCtc C) F hyp_wppstopgammaleasthitpairndv_1
      hyp_wppstopgammaleasthitpairndv_2
  have p0013 :=
    @gWppstopsteprndmndv (synCtc C) F hyp_wppstopgammaleasthitpairndv_1
      hyp_wppstopgammaleasthitpairndv_2
  have p0014 :=
    @gWppstopstepdmndv (synCtc C) F hyp_wppstopgammaleasthitpairndv_1
      hyp_wppstopgammaleasthitpairndv_2
  have p0015 :=
    @gEleq2i (synCdm (synCwppstopstep F (synCtc C))) (synChwcards (synCvv)) (.cv p)
      p0014
  have p0016 :=
    @gBiimpri (.classMem (.cv p) (synCdm (synCwppstopstep F (synCtc C))))
      (.classMem (.cv p) (synChwcards (synCvv))) p0015
  have p0017 := Nominal.gen p0016 p
  have p0018 :=
    (Nominal.biimpRefl (synWral p (synChwcards (synCvv))
        (.classMem (.cv p) (synCdm (synCwppstopstep F (synCtc C))))))
  have p0019 :=
    @gMpbir
      (synWral p (synChwcards (synCvv))
        (.classMem (.cv p) (synCdm (synCwppstopstep F (synCtc C)))))
      (.all p (.imp (.classMem (.cv p) (synChwcards (synCvv)))
          (.classMem (.cv p) (synCdm (synCwppstopstep F (synCtc C))))))
      p0017 p0018
  have p0020 :=
    Nominal.ax1 (.classMem (.cv p) (synCdm (synCwppstopstep F (synCtc C))))
      (synWbr (.cv p) (synClec) (synCtc C))
  have p0021 :=
    @gA1i
      (.imp (.classMem (.cv p) (synCdm (synCwppstopstep F (synCtc C))))
        (.imp (synWbr (.cv p) (synClec) (synCtc C))
          (.classMem (.cv p) (synCdm (synCwppstopstep F (synCtc C))))))
      (.classMem (.cv p) (synChwcards (synCvv))) p0020
  have p0022 :=
    @gRalimia (.classMem (.cv p) (synCdm (synCwppstopstep F (synCtc C))))
      (.imp (synWbr (.cv p) (synClec) (synCtc C))
        (.classMem (.cv p) (synCdm (synCwppstopstep F (synCtc C)))))
      p (synChwcards (synCvv)) p0021
  have p0023 := Nominal.mp p0019 p0022
  have p0031 := @gHwcardstcclndv (.cv p)
  have p0033 :=
    @gEleq2i (synCdm (synCwppstopstep F (synCtc C))) (synChwcards (synCvv))
      (synCtc (.cv p)) p0014
  have p0034 :=
    @gSylibr (.classMem (.cv p) (synChwcards (synCvv)))
      (.classMem (synCtc (.cv p)) (synChwcards (synCvv)))
      (.classMem (synCtc (.cv p)) (synCdm (synCwppstopstep F (synCtc C)))) p0031 p0033
  have p0035 :=
    @gJca (.classMem (.cv p) (synChwcards (synCvv)))
      (.classMem (.cv p) (synCdm (synCwppstopstep F C)))
      (.classMem (synCtc (.cv p)) (synCdm (synCwppstopstep F (synCtc C)))) p0004 p0034
  have p0036 := Nominal.gen p0035 p
  have p0037 :=
    (Nominal.biimpRefl (synWral p (synChwcards (synCvv))
        (synWa (.classMem (.cv p) (synCdm (synCwppstopstep F C)))
          (.classMem (synCtc (.cv p)) (synCdm (synCwppstopstep F (synCtc C)))))))
  have p0038 :=
    @gMpbir
      (synWral p (synChwcards (synCvv))
        (synWa (.classMem (.cv p) (synCdm (synCwppstopstep F C)))
          (.classMem (synCtc (.cv p)) (synCdm (synCwppstopstep F (synCtc C))))))
      (.all p (.imp (.classMem (.cv p) (synChwcards (synCvv)))
          (synWa (.classMem (.cv p) (synCdm (synCwppstopstep F C)))
            (.classMem (synCtc (.cv p)) (synCdm (synCwppstopstep F (synCtc C)))))))
      p0036 p0037
  have p0039 :=
    Nominal.ax1
      (synWa (.classMem (.cv p) (synCdm (synCwppstopstep F C)))
        (.classMem (synCtc (.cv p)) (synCdm (synCwppstopstep F (synCtc C)))))
      (synWbr (.cv p) (synClec) C)
  have p0040 :=
    @gA1i
      (.imp (synWa (.classMem (.cv p) (synCdm (synCwppstopstep F C)))
          (.classMem (synCtc (.cv p)) (synCdm (synCwppstopstep F (synCtc C)))))
        (.imp (synWbr (.cv p) (synClec) C)
          (synWa (.classMem (.cv p) (synCdm (synCwppstopstep F C)))
            (.classMem (synCtc (.cv p)) (synCdm (synCwppstopstep F (synCtc C)))))))
      (.classMem (.cv p) (synChwcards (synCvv))) p0039
  have p0041 :=
    @gRalimia
      (synWa (.classMem (.cv p) (synCdm (synCwppstopstep F C)))
        (.classMem (synCtc (.cv p)) (synCdm (synCwppstopstep F (synCtc C)))))
      (.imp (synWbr (.cv p) (synClec) C)
        (synWa (.classMem (.cv p) (synCdm (synCwppstopstep F C)))
          (.classMem (synCtc (.cv p)) (synCdm (synCwppstopstep F (synCtc C))))))
      p (synChwcards (synCvv)) p0040
  have p0042 := Nominal.mp p0038 p0041
  have p0044 :=
    @gA1i (.classMem (synCwppstopstep F C) (synCfuns))
      (synWa (.classMem (.cv p) (synChwcards (synCvv))) (.classMem (.cv r) (synCnnc)))
      p0000
  have p0045 :=
    @gSimpl (.classMem (.cv p) (synChwcards (synCvv))) (.classMem (.cv r) (synCnnc))
  have p0049 :=
    @gSyl
      (synWa (.classMem (.cv p) (synChwcards (synCvv))) (.classMem (.cv r) (synCnnc)))
      (.classMem (.cv p) (synChwcards (synCvv)))
      (.classMem (.cv p) (synCdm (synCwppstopstep F C))) p0045 p0004
  have p0051 :=
    @gA1i (synWss (synCrn (synCwppstopstep F C)) (synCdm (synCwppstopstep F C)))
      (synWa (.classMem (.cv p) (synChwcards (synCvv))) (.classMem (.cv r) (synCnnc)))
      p0001
  have p0052 :=
    @gN3jca
      (synWa (.classMem (.cv p) (synChwcards (synCvv))) (.classMem (.cv r) (synCnnc)))
      (.classMem (synCwppstopstep F C) (synCfuns))
      (.classMem (.cv p) (synCdm (synCwppstopstep F C)))
      (synWss (synCrn (synCwppstopstep F C)) (synCdm (synCwppstopstep F C))) p0044
      p0049 p0051
  have p0053 :=
    @gSimpr (.classMem (.cv p) (synChwcards (synCvv))) (.classMem (.cv r) (synCnnc))
  have p0054 :=
    @gJca
      (synWa (.classMem (.cv p) (synChwcards (synCvv))) (.classMem (.cv r) (synCnnc)))
      (synW3a (.classMem (synCwppstopstep F C) (synCfuns))
        (.classMem (.cv p) (synCdm (synCwppstopstep F C)))
        (synWss (synCrn (synCwppstopstep F C)) (synCdm (synCwppstopstep F C))))
      (.classMem (.cv r) (synCnnc)) p0052 p0053
  have p0055 := @gFrecdomfv (synCwppstopstep F C) (.cv p) (.cv r)
  have p0056 :=
    @gSyl
      (synWa (.classMem (.cv p) (synChwcards (synCvv))) (.classMem (.cv r) (synCnnc)))
      (synWa (synW3a (.classMem (synCwppstopstep F C) (synCfuns))
          (.classMem (.cv p) (synCdm (synCwppstopstep F C)))
          (synWss (synCrn (synCwppstopstep F C)) (synCdm (synCwppstopstep F C))))
        (.classMem (.cv r) (synCnnc)))
      (.classMem (synCfv (synCfrec (synCwppstopstep F C) (.cv p)) (.cv r))
        (synCdm (synCwppstopstep F C)))
      p0054 p0055
  have p0058 :=
    @gEleq2i (synCdm (synCwppstopstep F C)) (synChwcards (synCvv))
      (synCfv (synCfrec (synCwppstopstep F C) (.cv p)) (.cv r)) p0002
  have p0059 :=
    @gSylib
      (synWa (.classMem (.cv p) (synChwcards (synCvv))) (.classMem (.cv r) (synCnnc)))
      (.classMem (synCfv (synCfrec (synCwppstopstep F C) (.cv p)) (.cv r))
        (synCdm (synCwppstopstep F C)))
      (.classMem (synCfv (synCfrec (synCwppstopstep F C) (.cv p)) (.cv r))
        (synChwcards (synCvv)))
      p0056 p0058
  have p0060 := @gHwcardssnc (synCvv)
  have p0061 :=
    @gSseli (synChwcards (synCvv)) (synCncs)
      (synCfv (synCfrec (synCwppstopstep F C) (.cv p)) (.cv r)) p0060
  have p0062 :=
    @gSyl
      (synWa (.classMem (.cv p) (synChwcards (synCvv))) (.classMem (.cv r) (synCnnc)))
      (.classMem (synCfv (synCfrec (synCwppstopstep F C) (.cv p)) (.cv r))
        (synChwcards (synCvv)))
      (.classMem (synCfv (synCfrec (synCwppstopstep F C) (.cv p)) (.cv r)) (synCncs))
      p0059 p0061
  have p0063 :=
    @gRgen2
      (.classMem (synCfv (synCfrec (synCwppstopstep F C) (.cv p)) (.cv r)) (synCncs))
      p r (synChwcards (synCvv)) (synCnnc) dv_cache_0001 dv_cache_0002 p0062
  have p0064 :=
    Nominal.ax1
      (synWral r (synCnnc)
        (.classMem (synCfv (synCfrec (synCwppstopstep F C) (.cv p)) (.cv r)) (synCncs)))
      (synWbr (.cv p) (synClec) C)
  have p0065 :=
    @gA1i
      (.imp (synWral r (synCnnc)
          (.classMem (synCfv (synCfrec (synCwppstopstep F C) (.cv p)) (.cv r)) (synCncs)))
        (.imp (synWbr (.cv p) (synClec) C) (synWral r (synCnnc)
            (.classMem (synCfv (synCfrec (synCwppstopstep F C) (.cv p)) (.cv r))
              (synCncs)))))
      (.classMem (.cv p) (synChwcards (synCvv))) p0064
  have p0066 :=
    @gRalimia
      (synWral r (synCnnc)
        (.classMem (synCfv (synCfrec (synCwppstopstep F C) (.cv p)) (.cv r)) (synCncs)))
      (.imp (synWbr (.cv p) (synClec) C) (synWral r (synCnnc)
          (.classMem (synCfv (synCfrec (synCwppstopstep F C) (.cv p)) (.cv r)) (synCncs))))
      p (synChwcards (synCvv)) p0065
  have p0067 := Nominal.mp p0063 p0066
  have p0068 :=
    @gWppgammatchwboundedeqndv x C (synCwppstopstep F C)
      (synCwppstopstep F (synCtc C)) r p dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0002 dv_cache_0012 dv_cache_0013 p0000 p0001 p0012 p0013
      hyp_wppstopgammaleasthitpairndv_4 p0042 p0067 hyp_wppstopgammaleasthitpairndv_3
  have p0069 :=
    @gWppcrossgammaleasthitpairhwndv C k m n (synCwppstopstep F C)
      (synCwppstopstep F (synCtc C)) q p dv_cache_0014 dv_cache_0015 dv_cache_0016
      dv_cache_0003 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0006
      dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0009 dv_cache_0025
      dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
      dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 p0000 p0001 p0011 p0012
      p0013 p0023 hyp_wppstopgammaleasthitpairndv_3 p0068
  exact p0069


end NFChoice.DirectNominalPrf.WPPReplay

end
