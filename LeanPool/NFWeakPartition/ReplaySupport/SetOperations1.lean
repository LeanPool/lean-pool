/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalWPPReplayChunk007

/-! NF weak partition development: NominalWPPReplayChunk008. -/


public section


namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_unineq (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (syn_wb (syn_wa (.classEq (syn_cun A C) (syn_cun B C))
          (.classEq (syn_cin A C) (syn_cin B C))) (.classEq A B)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 := @g_eleq2 (syn_cin A C) (syn_cin B C) (.cv x)
  have p0001 := @g_elin (.cv x) A C
  have p0002 := @g_elin (.cv x) B C
  have p0003 :=
    @g_n_3bitr3g (.classEq (syn_cin A C) (syn_cin B C)) (.classMem (.cv x) (syn_cin A C))
      (.classMem (.cv x) (syn_cin B C))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) C))
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv x) C)) p0000 p0001 p0002
  have p0004 := @g_iba (.classMem (.cv x) C) (.classMem (.cv x) A)
  have p0005 := @g_iba (.classMem (.cv x) C) (.classMem (.cv x) B)
  have p0006 :=
    @g_bibi12d (.classMem (.cv x) C) (.classMem (.cv x) A)
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) C)) (.classMem (.cv x) B)
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv x) C)) p0004 p0005
  have p0007 :=
    @g_syl5ibr (.classEq (syn_cin A C) (syn_cin B C))
      (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) C)
      (syn_wb (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) C))
        (syn_wa (.classMem (.cv x) B) (.classMem (.cv x) C)))
      p0003 p0006
  have p0008 :=
    @g_adantld (.classMem (.cv x) C) (.classEq (syn_cin A C) (syn_cin B C))
      (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B))
      (.classEq (syn_cun A C) (syn_cun B C)) p0007
  have p0009 := @g_uncom A C
  have p0010 := @g_uncom B C
  have p0011 :=
    @g_eqeq12i (syn_cun A C) (syn_cun C A) (syn_cun B C) (syn_cun C B) p0009 p0010
  have p0012 := @g_eleq2 (syn_cun C A) (syn_cun C B) (.cv x)
  have p0013 :=
    @g_sylbi (.classEq (syn_cun A C) (syn_cun B C)) (.classEq (syn_cun C A) (syn_cun C B))
      (syn_wb (.classMem (.cv x) (syn_cun C A)) (.classMem (.cv x) (syn_cun C B))) p0011
      p0012
  have p0014 := @g_elun (.cv x) C A
  have p0015 := @g_elun (.cv x) C B
  have p0016 :=
    @g_n_3bitr3g (.classEq (syn_cun A C) (syn_cun B C)) (.classMem (.cv x) (syn_cun C A))
      (.classMem (.cv x) (syn_cun C B))
      (syn_wo (.classMem (.cv x) C) (.classMem (.cv x) A))
      (syn_wo (.classMem (.cv x) C) (.classMem (.cv x) B)) p0013 p0014 p0015
  have p0017 := @g_biorf (.classMem (.cv x) C) (.classMem (.cv x) A)
  have p0018 := @g_biorf (.classMem (.cv x) C) (.classMem (.cv x) B)
  have p0019 :=
    @g_bibi12d (.neg (.classMem (.cv x) C)) (.classMem (.cv x) A)
      (syn_wo (.classMem (.cv x) C) (.classMem (.cv x) A)) (.classMem (.cv x) B)
      (syn_wo (.classMem (.cv x) C) (.classMem (.cv x) B)) p0017 p0018
  have p0020 :=
    @g_syl5ibr (.classEq (syn_cun A C) (syn_cun B C))
      (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B)) (.neg (.classMem (.cv x) C))
      (syn_wb (syn_wo (.classMem (.cv x) C) (.classMem (.cv x) A))
        (syn_wo (.classMem (.cv x) C) (.classMem (.cv x) B)))
      p0016 p0019
  have p0021 :=
    @g_adantrd (.neg (.classMem (.cv x) C)) (.classEq (syn_cun A C) (syn_cun B C))
      (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B))
      (.classEq (syn_cin A C) (syn_cin B C)) p0020
  have p0022 :=
    @g_pm2_61i (.classMem (.cv x) C)
      (.imp (syn_wa (.classEq (syn_cun A C) (syn_cun B C))
          (.classEq (syn_cin A C) (syn_cin B C)))
        (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B)))
      p0008 p0021
  have p0023 :=
    @g_eqrdv
      (syn_wa (.classEq (syn_cun A C) (syn_cun B C)) (.classEq (syn_cin A C) (syn_cin B C)))
      x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
              Finset.mem_union] at ⊢;
            aesop))
      p0022
  have p0024 := @g_uneq1 A B C
  have p0025 := @g_ineq1 A B C
  have p0026 :=
    @g_jca (.classEq A B) (.classEq (syn_cun A C) (syn_cun B C))
      (.classEq (syn_cin A C) (syn_cin B C)) p0024 p0025
  have p0027 :=
    @g_impbii
      (syn_wa (.classEq (syn_cun A C) (syn_cun B C)) (.classEq (syn_cin A C) (syn_cin B C)))
      (.classEq A B) p0023 p0026
  exact p0027

@[expose]
noncomputable def g_difundir (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.classEq (syn_cdif (syn_cun A B) C) (syn_cun (syn_cdif A C) (syn_cdif B C))) :=
  by
  have p0000 := @g_indir A B (syn_cdif (syn_cvv) C)
  have p0001 := @g_invdif (syn_cun A B) C
  have p0002 := @g_invdif A C
  have p0003 := @g_invdif B C
  have p0004 :=
    @g_uneq12i (syn_cin A (syn_cdif (syn_cvv) C)) (syn_cdif A C)
      (syn_cin B (syn_cdif (syn_cvv) C)) (syn_cdif B C) p0002 p0003
  have p0005 :=
    @g_n_3eqtr3i (syn_cin (syn_cun A B) (syn_cdif (syn_cvv) C))
      (syn_cun (syn_cin A (syn_cdif (syn_cvv) C)) (syn_cin B (syn_cdif (syn_cvv) C)))
      (syn_cdif (syn_cun A B) C) (syn_cun (syn_cdif A C) (syn_cdif B C)) p0000 p0001 p0004
  exact p0005

@[expose]
noncomputable def g_unab (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (.classEq (syn_cun (.cab x ph) (.cab x ps)) (.cab x (syn_wo ph ps))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_ps : y ∉ ps.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have p0000 := @g_sbor ph ps x y
  have p0001 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      y x (syn_wo ph ps))
  have p0002 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      y x ph)
  have p0003 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      y x ps)
  have p0004 :=
    @g_orbi12i (.classMem (.cv y) (.cab x ph)) (syn_wsb y x ph)
      (.classMem (.cv y) (.cab x ps)) (syn_wsb y x ps) p0002 p0003
  have p0005 :=
    @g_n_3bitr4ri (syn_wsb y x (syn_wo ph ps)) (syn_wo (syn_wsb y x ph) (syn_wsb y x ps))
      (.classMem (.cv y) (.cab x (syn_wo ph ps)))
      (syn_wo (.classMem (.cv y) (.cab x ph)) (.classMem (.cv y) (.cab x ps))) p0000 p0001
      p0004
  have p0006 :=
    @g_uneqri y (.cab x ph) (.cab x ps) (.cab x (syn_wo ph ps))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
              Finset.mem_erase] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
              Finset.mem_erase] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, Finset.mem_union,
              Finset.mem_erase] at ⊢;
            aesop))
      p0005
  exact p0006

@[expose]
noncomputable def g_inab (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (.classEq (syn_cin (.cab x ph) (.cab x ps)) (.cab x (syn_wa ph ps))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_ps : y ∉ ps.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have p0000 := @g_sban ph ps x y
  have p0001 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      y x (syn_wa ph ps))
  have p0002 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      y x ph)
  have p0003 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      y x ps)
  have p0004 :=
    @g_anbi12i (.classMem (.cv y) (.cab x ph)) (syn_wsb y x ph)
      (.classMem (.cv y) (.cab x ps)) (syn_wsb y x ps) p0002 p0003
  have p0005 :=
    @g_n_3bitr4ri (syn_wsb y x (syn_wa ph ps)) (syn_wa (syn_wsb y x ph) (syn_wsb y x ps))
      (.classMem (.cv y) (.cab x (syn_wa ph ps)))
      (syn_wa (.classMem (.cv y) (.cab x ph)) (.classMem (.cv y) (.cab x ps))) p0000 p0001
      p0004
  have p0006 :=
    @g_ineqri y (.cab x ph) (.cab x ps) (.cab x (syn_wa ph ps))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
              Finset.mem_erase] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
              Finset.mem_erase] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, Finset.mem_union,
              Finset.mem_erase] at ⊢;
            aesop))
      p0005
  exact p0006

@[expose]
noncomputable def g_difab (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf
      (.classEq (syn_cdif (.cab x ph) (.cab x ps)) (.cab x (syn_wa ph (.neg ps)))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_ps : y ∉ ps.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have p0000 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      y x (syn_wa ph (.neg ps)))
  have p0001 := @g_sban ph (.neg ps) x y
  have p0002 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      y x ph)
  have p0003 := @g_bicomi (.classMem (.cv y) (.cab x ph)) (syn_wsb y x ph) p0002
  have p0004 := @g_sbn ps x y
  have p0005 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      y x ps)
  have p0006 :=
    @g_xchbinxr (syn_wsb y x (.neg ps)) (syn_wsb y x ps) (.classMem (.cv y) (.cab x ps))
      p0004 p0005
  have p0007 :=
    @g_anbi12i (syn_wsb y x ph) (.classMem (.cv y) (.cab x ph)) (syn_wsb y x (.neg ps))
      (.neg (.classMem (.cv y) (.cab x ps))) p0003 p0006
  have p0008 :=
    @g_n_3bitrri (.classMem (.cv y) (.cab x (syn_wa ph (.neg ps))))
      (syn_wsb y x (syn_wa ph (.neg ps)))
      (syn_wa (syn_wsb y x ph) (syn_wsb y x (.neg ps)))
      (syn_wa (.classMem (.cv y) (.cab x ph)) (.neg (.classMem (.cv y) (.cab x ps))))
      p0000 p0001 p0007
  have p0009 :=
    @g_difeqri y (.cab x ph) (.cab x ps) (.cab x (syn_wa ph (.neg ps)))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
              Finset.mem_erase] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
              Finset.mem_erase] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
              NFChoice.Compiler.CoreFVSimp.fv_wff_neg, Finset.mem_union,
              Finset.mem_erase] at ⊢;
            aesop))
      p0008
  exact p0009

@[expose]
noncomputable def g_complab (ph : Wff) (x : Var) :
    Nominal.NPrf (.classEq (syn_ccompl (.cab x ph)) (.cab x (.neg ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var)
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have p0000 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      y x ph)
  have p0001 := @g_notbii (.classMem (.cv y) (.cab x ph)) (syn_wsb y x ph) p0000
  have p0002 := @g_sbn ph x y
  have p0003 :=
    @g_bitr4i (.neg (.classMem (.cv y) (.cab x ph))) (.neg (syn_wsb y x ph))
      (syn_wsb y x (.neg ph)) p0001 p0002
  have p0004 := @g_vex y
  have p0005 := @g_elcompl (.cv y) (.cab x ph) p0004
  have p0006 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      y x (.neg ph))
  have p0007 :=
    @g_n_3bitr4i (.neg (.classMem (.cv y) (.cab x ph))) (syn_wsb y x (.neg ph))
      (.classMem (.cv y) (syn_ccompl (.cab x ph))) (.classMem (.cv y) (.cab x (.neg ph)))
      p0003 p0005 p0006
  have p0008 :=
    @g_eqriv y (syn_ccompl (.cab x ph)) (.cab x (.neg ph))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
              NFChoice.Compiler.CoreFVSimp.fv_class_cab, Finset.mem_erase] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
              NFChoice.Compiler.CoreFVSimp.fv_wff_neg, Finset.mem_erase] at ⊢;
            aesop))
      p0007
  exact p0008

@[expose]
noncomputable def g_notab (ph : Wff) (x : Var) :
    Nominal.NPrf (.classEq (.cab x (.neg ph)) (syn_cdif (syn_cvv) (.cab x ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var)
  have p0000 := (Nominal.classEqRefl (syn_crab x (syn_cvv) (.neg ph)))
  have p0001 := @g_rabab (.neg ph) x
  have p0002 :=
    @g_eqtr3i (syn_crab x (syn_cvv) (.neg ph))
      (.cab x (syn_wa (.classMem (.cv x) (syn_cvv)) (.neg ph))) (.cab x (.neg ph)) p0000
      p0001
  have p0003 := @g_difab (.classMem (.cv x) (syn_cvv)) ph x
  have p0004 :=
    @g_abid2 x (syn_cvv)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv] at ⊢;
            aesop))
  have p0005 :=
    @g_difeq1i (.cab x (.classMem (.cv x) (syn_cvv))) (syn_cvv) (.cab x ph) p0004
  have p0006 :=
    @g_eqtr3i (syn_cdif (.cab x (.classMem (.cv x) (syn_cvv))) (.cab x ph))
      (.cab x (syn_wa (.classMem (.cv x) (syn_cvv)) (.neg ph)))
      (syn_cdif (syn_cvv) (.cab x ph)) p0003 p0005
  have p0007 :=
    @g_eqtr3i (.cab x (syn_wa (.classMem (.cv x) (syn_cvv)) (.neg ph))) (.cab x (.neg ph))
      (syn_cdif (syn_cvv) (.cab x ph)) p0002 p0006
  exact p0007

@[expose]
noncomputable def g_unrab (ph : Wff) (ps : Wff) (x : Var) (A : Class) :
    Nominal.NPrf
      (.classEq (syn_cun (syn_crab x A ph) (syn_crab x A ps)) (syn_crab x A (syn_wo ph ps))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_crab x A ph))
  have p0001 := (Nominal.classEqRefl (syn_crab x A ps))
  have p0002 :=
    @g_uneq12i (syn_crab x A ph) (.cab x (syn_wa (.classMem (.cv x) A) ph))
      (syn_crab x A ps) (.cab x (syn_wa (.classMem (.cv x) A) ps)) p0000 p0001
  have p0003 := (Nominal.classEqRefl (syn_crab x A (syn_wo ph ps)))
  have p0004 :=
    @g_unab (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv x) A) ps) x
  have p0005 := @g_andi (.classMem (.cv x) A) ph ps
  have p0006 :=
    @g_abbii (syn_wa (.classMem (.cv x) A) (syn_wo ph ps))
      (syn_wo (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv x) A) ps)) x p0005
  have p0007 :=
    @g_eqtr4i
      (syn_cun (.cab x (syn_wa (.classMem (.cv x) A) ph))
        (.cab x (syn_wa (.classMem (.cv x) A) ps)))
      (.cab x (syn_wo (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv x) A) ps)))
      (.cab x (syn_wa (.classMem (.cv x) A) (syn_wo ph ps))) p0004 p0006
  have p0008 :=
    @g_eqtr4i (syn_crab x A (syn_wo ph ps))
      (.cab x (syn_wa (.classMem (.cv x) A) (syn_wo ph ps)))
      (syn_cun (.cab x (syn_wa (.classMem (.cv x) A) ph))
        (.cab x (syn_wa (.classMem (.cv x) A) ps)))
      p0003 p0007
  have p0009 :=
    @g_eqtr4i (syn_cun (syn_crab x A ph) (syn_crab x A ps))
      (syn_cun (.cab x (syn_wa (.classMem (.cv x) A) ph))
        (.cab x (syn_wa (.classMem (.cv x) A) ps)))
      (syn_crab x A (syn_wo ph ps)) p0002 p0008
  exact p0009

@[expose]
noncomputable def g_dfrab2 (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.classEq (syn_crab x A ph) (syn_cin (.cab x ph) A)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := (Nominal.classEqRefl (syn_crab x A ph))
  have p0001 := @g_inab (.classMem (.cv x) A) ph x
  have p0002 :=
    @g_abid2 x A
      (by
        first
        | (aesop))
  have p0003 := @g_ineq1i (.cab x (.classMem (.cv x) A)) A (.cab x ph) p0002
  have p0004 :=
    @g_eqtr3i (syn_cin (.cab x (.classMem (.cv x) A)) (.cab x ph))
      (.cab x (syn_wa (.classMem (.cv x) A) ph)) (syn_cin A (.cab x ph)) p0001 p0003
  have p0005 := @g_incom A (.cab x ph)
  have p0006 :=
    @g_n_3eqtri (syn_crab x A ph) (.cab x (syn_wa (.classMem (.cv x) A) ph))
      (syn_cin A (.cab x ph)) (syn_cin (.cab x ph) A) p0000 p0004 p0005
  exact p0006

@[expose]
noncomputable def g_dfrab3 (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.classEq (syn_crab x A ph) (syn_cin A (.cab x ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := (Nominal.classEqRefl (syn_crab x A ph))
  have p0001 := @g_inab (.classMem (.cv x) A) ph x
  have p0002 :=
    @g_abid2 x A
      (by
        first
        | (aesop))
  have p0003 := @g_ineq1i (.cab x (.classMem (.cv x) A)) A (.cab x ph) p0002
  have p0004 :=
    @g_n_3eqtr2i (syn_crab x A ph) (.cab x (syn_wa (.classMem (.cv x) A) ph))
      (syn_cin (.cab x (.classMem (.cv x) A)) (.cab x ph)) (syn_cin A (.cab x ph)) p0000
      p0001 p0003
  exact p0004

@[expose]
noncomputable def g_notrab (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.classEq (syn_cdif A (syn_crab x A ph)) (syn_crab x A (.neg ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := @g_difab (.classMem (.cv x) A) ph x
  have p0001 := @g_difin A (.cab x ph)
  have p0002 :=
    @g_dfrab3 ph x A
      (by
        first
        | (aesop))
  have p0003 := @g_difeq2i (syn_crab x A ph) (syn_cin A (.cab x ph)) A p0002
  have p0004 :=
    @g_abid2 x A
      (by
        first
        | (aesop))
  have p0005 := @g_difeq1i (.cab x (.classMem (.cv x) A)) A (.cab x ph) p0004
  have p0006 :=
    @g_n_3eqtr4i (syn_cdif A (syn_cin A (.cab x ph))) (syn_cdif A (.cab x ph))
      (syn_cdif A (syn_crab x A ph)) (syn_cdif (.cab x (.classMem (.cv x) A)) (.cab x ph))
      p0001 p0003 p0005
  have p0007 := (Nominal.classEqRefl (syn_crab x A (.neg ph)))
  have p0008 :=
    @g_n_3eqtr4i (syn_cdif (.cab x (.classMem (.cv x) A)) (.cab x ph))
      (.cab x (syn_wa (.classMem (.cv x) A) (.neg ph))) (syn_cdif A (syn_crab x A ph))
      (syn_crab x A (.neg ph)) p0000 p0006 p0007
  exact p0008

@[expose]
noncomputable def g_compleqb (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (.classEq A B) (.classEq (syn_ccompl A) (syn_ccompl B))) :=
  by
  have p0000 := @g_compleq A B
  have p0001 := @g_compleq (syn_ccompl A) (syn_ccompl B)
  have p0002 := @g_dblcompl A
  have p0003 := @g_dblcompl B
  have p0004 :=
    @g_n_3eqtr3g (.classEq (syn_ccompl A) (syn_ccompl B)) (syn_ccompl (syn_ccompl A))
      (syn_ccompl (syn_ccompl B)) A B p0001 p0002 p0003
  have p0005 :=
    @g_impbii (.classEq A B) (.classEq (syn_ccompl A) (syn_ccompl B)) p0000 p0004
  exact p0005

@[expose]
noncomputable def g_necompl (A : Class) : Nominal.NPrf (syn_wne (syn_ccompl A) A) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have p0000 := @g_pm5_19 (.classMem (.cv x) A)
  have p0001 := @g_vex x
  have p0002 := @g_elcompl (.cv x) A p0001
  have p0003 :=
    @g_bibi2i (.classMem (.cv x) (syn_ccompl A)) (.neg (.classMem (.cv x) A))
      (.classMem (.cv x) A) p0002
  have p0004 :=
    @g_mtbir (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (syn_ccompl A)))
      (syn_wb (.classMem (.cv x) A) (.neg (.classMem (.cv x) A))) p0000 p0003
  have p0005 :=
    @g_n_19_8a (.neg (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (syn_ccompl A)))) x
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @g_dfcleq x A (syn_ccompl A)
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl] at ⊢;
            aesop))
  have p0008 :=
    @g_necon3abii
      (.all x (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (syn_ccompl A)))) A
      (syn_ccompl A) p0007
  have p0009 :=
    @g_exnal (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (syn_ccompl A))) x
  have p0010 :=
    @g_bitr4i (syn_wne A (syn_ccompl A))
      (.neg (.all x (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (syn_ccompl A)))))
      (syn_wex x (.neg (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (syn_ccompl A)))))
      p0008 p0009
  have p0011 :=
    @g_mpbir (syn_wne A (syn_ccompl A))
      (syn_wex x (.neg (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (syn_ccompl A)))))
      p0006 p0010
  have p0012 := @g_necomi A (syn_ccompl A) p0011
  exact p0012

@[expose]
noncomputable def g_dfin5 (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (syn_cin A B) (syn_ccompl (syn_cun (syn_ccompl A) (syn_ccompl B)))) :=
  by
  have p0000 := @g_dblcompl A
  have p0001 := @g_dblcompl B
  have p0002 :=
    @g_nineq12i (syn_ccompl (syn_ccompl A)) A (syn_ccompl (syn_ccompl B)) B p0000 p0001
  have p0003 :=
    @g_compleqi (syn_cnin (syn_ccompl (syn_ccompl A)) (syn_ccompl (syn_ccompl B)))
      (syn_cnin A B) p0002
  have p0004 := (Nominal.classEqRefl (syn_cun (syn_ccompl A) (syn_ccompl B)))
  have p0005 :=
    @g_compleqi (syn_cun (syn_ccompl A) (syn_ccompl B))
      (syn_cnin (syn_ccompl (syn_ccompl A)) (syn_ccompl (syn_ccompl B))) p0004
  have p0006 := (Nominal.classEqRefl (syn_cin A B))
  have p0007 :=
    @g_n_3eqtr4ri
      (syn_ccompl (syn_cnin (syn_ccompl (syn_ccompl A)) (syn_ccompl (syn_ccompl B))))
      (syn_ccompl (syn_cnin A B)) (syn_ccompl (syn_cun (syn_ccompl A) (syn_ccompl B)))
      (syn_cin A B) p0003 p0005 p0006
  exact p0007

@[expose]
noncomputable def g_dfun4 (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (syn_cun A B) (syn_ccompl (syn_cin (syn_ccompl A) (syn_ccompl B)))) :=
  by
  have p0000 := @g_dfin5 (syn_ccompl A) (syn_ccompl B)
  have p0001 :=
    @g_compleqi (syn_cin (syn_ccompl A) (syn_ccompl B))
      (syn_ccompl (syn_cun (syn_ccompl (syn_ccompl A)) (syn_ccompl (syn_ccompl B)))) p0000
  have p0002 :=
    @g_dblcompl (syn_cun (syn_ccompl (syn_ccompl A)) (syn_ccompl (syn_ccompl B)))
  have p0003 := @g_dblcompl A
  have p0004 := @g_dblcompl B
  have p0005 :=
    @g_uneq12i (syn_ccompl (syn_ccompl A)) A (syn_ccompl (syn_ccompl B)) B p0003 p0004
  have p0006 :=
    @g_n_3eqtrri (syn_ccompl (syn_cin (syn_ccompl A) (syn_ccompl B)))
      (syn_ccompl
        (syn_ccompl (syn_cun (syn_ccompl (syn_ccompl A)) (syn_ccompl (syn_ccompl B)))))
      (syn_cun (syn_ccompl (syn_ccompl A)) (syn_ccompl (syn_ccompl B))) (syn_cun A B)
      p0001 p0002 p0005
  exact p0006

@[expose]
noncomputable def g_iunin (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (syn_ccompl (syn_cun A B)) (syn_cin (syn_ccompl A) (syn_ccompl B))) :=
  by
  have p0000 := @g_dfin5 (syn_ccompl A) (syn_ccompl B)
  have p0001 := @g_dblcompl A
  have p0002 := @g_dblcompl B
  have p0003 :=
    @g_uneq12i (syn_ccompl (syn_ccompl A)) A (syn_ccompl (syn_ccompl B)) B p0001 p0002
  have p0004 :=
    @g_compleqi (syn_cun (syn_ccompl (syn_ccompl A)) (syn_ccompl (syn_ccompl B)))
      (syn_cun A B) p0003
  have p0005 :=
    @g_eqtr2i (syn_cin (syn_ccompl A) (syn_ccompl B))
      (syn_ccompl (syn_cun (syn_ccompl (syn_ccompl A)) (syn_ccompl (syn_ccompl B))))
      (syn_ccompl (syn_cun A B)) p0000 p0004
  exact p0005

@[expose]
noncomputable def g_iinun (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (syn_ccompl (syn_cin A B)) (syn_cun (syn_ccompl A) (syn_ccompl B))) :=
  by
  have p0000 := @g_dfun4 (syn_ccompl A) (syn_ccompl B)
  have p0001 := @g_dblcompl A
  have p0002 := @g_dblcompl B
  have p0003 :=
    @g_ineq12i (syn_ccompl (syn_ccompl A)) A (syn_ccompl (syn_ccompl B)) B p0001 p0002
  have p0004 :=
    @g_compleqi (syn_cin (syn_ccompl (syn_ccompl A)) (syn_ccompl (syn_ccompl B)))
      (syn_cin A B) p0003
  have p0005 :=
    @g_eqtr2i (syn_cun (syn_ccompl A) (syn_ccompl B))
      (syn_ccompl (syn_cin (syn_ccompl (syn_ccompl A)) (syn_ccompl (syn_ccompl B))))
      (syn_ccompl (syn_cin A B)) p0000 p0004
  exact p0005

@[expose]
noncomputable def g_difsscompl (A : Class) (B : Class) :
    Nominal.NPrf (syn_wss (syn_cdif A B) (syn_ccompl B)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cdif A B))
  have p0001 := @g_inss2 A (syn_ccompl B)
  have p0002 :=
    @g_eqsstri (syn_cdif A B) (syn_cin A (syn_ccompl B)) (syn_ccompl B) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_dfnul2 (x : Var) :
    Nominal.NPrf (.classEq (syn_c0) (.cab x (.neg (.classEq (.cv x) (.cv x))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var)
  have p0000 := (Nominal.classEqRefl (syn_c0))
  have p0001 := @g_eleq2i (syn_c0) (syn_cdif (syn_cvv) (syn_cvv)) (.cv x) p0000
  have p0002 := @g_eldif (.cv x) (syn_cvv) (syn_cvv)
  have p0003 := @g_eqid (.cv x)
  have p0004 := @g_pm3_24 (.classMem (.cv x) (syn_cvv))
  have p0005 :=
    @g_n_2th (.classEq (.cv x) (.cv x))
      (.neg (syn_wa (.classMem (.cv x) (syn_cvv)) (.neg (.classMem (.cv x) (syn_cvv)))))
      p0003 p0004
  have p0006 :=
    @g_con2bii (.classEq (.cv x) (.cv x))
      (syn_wa (.classMem (.cv x) (syn_cvv)) (.neg (.classMem (.cv x) (syn_cvv)))) p0005
  have p0007 :=
    @g_n_3bitri (.classMem (.cv x) (syn_c0))
      (.classMem (.cv x) (syn_cdif (syn_cvv) (syn_cvv)))
      (syn_wa (.classMem (.cv x) (syn_cvv)) (.neg (.classMem (.cv x) (syn_cvv))))
      (.neg (.classEq (.cv x) (.cv x))) p0001 p0002 p0006
  have p0008 :=
    @g_eqabi (.neg (.classEq (.cv x) (.cv x))) x (syn_c0)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0] at ⊢;
            aesop))
      p0007
  exact p0008

@[expose]
noncomputable def g_noel (A : Class) : Nominal.NPrf (.neg (.classMem A (syn_c0))) :=
  by
  have p0000 := @g_eldifi A (syn_cvv) (syn_cvv)
  have p0001 := @g_eldifn A (syn_cvv) (syn_cvv)
  have p0002 :=
    @g_pm2_65i (.classMem A (syn_cdif (syn_cvv) (syn_cvv))) (.classMem A (syn_cvv)) p0000
      p0001
  have p0003 := (Nominal.classEqRefl (syn_c0))
  have p0004 := @g_eleq2i (syn_c0) (syn_cdif (syn_cvv) (syn_cvv)) A p0003
  have p0005 :=
    @g_mtbir (.classMem A (syn_c0)) (.classMem A (syn_cdif (syn_cvv) (syn_cvv))) p0002
      p0004
  exact p0005

@[expose]
noncomputable def g_n0i (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem B A) (.neg (.classEq A (syn_c0)))) :=
  by
  have p0000 := @g_noel B
  have p0001 := @g_eleq2 A (syn_c0) B
  have p0002 :=
    @g_mtbiri (.classEq A (syn_c0)) (.classMem B A) (.classMem B (syn_c0)) p0000 p0001
  have p0003 := @g_con2i (.classEq A (syn_c0)) (.classMem B A) p0002
  exact p0003

@[expose]
noncomputable def g_ne0i (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem B A) (syn_wne A (syn_c0))) :=
  by
  have p0000 := @g_n0i A B
  have p0001 := (Nominal.biimpRefl (syn_wne A (syn_c0)))
  have p0002 :=
    @g_sylibr (.classMem B A) (.neg (.classEq A (syn_c0))) (syn_wne A (syn_c0)) p0000
      p0001
  exact p0002

@[expose]
noncomputable def g_vn0 : Nominal.NPrf (syn_wne (syn_cvv) (syn_c0)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have p0000 := @g_vex x
  have p0001 := @g_ne0i (syn_cvv) (.cv x)
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

@[expose]
noncomputable def g_n0f (x : Var) (A : Class) (hyp_n0f_1 : Nominal.NPrf (syn_wnfc x A)) :
    Nominal.NPrf (syn_wb (syn_wne A (syn_c0)) (syn_wex x (.classMem (.cv x) A))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_nfcv x (syn_c0)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0] at ⊢;
            aesop))
  have p0001 := @g_cleqf x A (syn_c0) hyp_n0f_1 p0000
  have p0002 := @g_noel (.cv x)
  have p0003 := @g_nbn (.classMem (.cv x) (syn_c0)) (.classMem (.cv x) A) p0002
  have p0004 :=
    @g_albii (.neg (.classMem (.cv x) A))
      (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (syn_c0))) x p0003
  have p0005 :=
    @g_bitr4i (.classEq A (syn_c0))
      (.all x (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (syn_c0))))
      (.all x (.neg (.classMem (.cv x) A))) p0001 p0004
  have p0006 := @g_necon3abii (.all x (.neg (.classMem (.cv x) A))) A (syn_c0) p0005
  have p0007 := (Nominal.biimpRefl (syn_wex x (.classMem (.cv x) A)))
  have p0008 :=
    @g_bitr4i (syn_wne A (syn_c0)) (.neg (.all x (.neg (.classMem (.cv x) A))))
      (syn_wex x (.classMem (.cv x) A)) p0006 p0007
  exact p0008

@[expose]
noncomputable def g_n0 (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wb (syn_wne A (syn_c0)) (syn_wex x (.classMem (.cv x) A))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_nfcv x A
      (by
        first
        | (aesop))
  have p0001 := @g_n0f x A p0000
  exact p0001

@[expose]
noncomputable def g_neq0 (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (syn_wb (.neg (.classEq A (syn_c0))) (syn_wex x (.classMem (.cv x) A))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  have p0000 := (Nominal.biimpRefl (syn_wne A (syn_c0)))
  have p0001 :=
    @g_n0 x A
      (by
        first
        | (aesop))
  have p0002 :=
    @g_bitr3i (.neg (.classEq A (syn_c0))) (syn_wne A (syn_c0))
      (syn_wex x (.classMem (.cv x) A)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_rex0 (ph : Wff) (x : Var) :
    Nominal.NPrf (.neg (syn_wrex x (syn_c0) ph)) :=
  by
  have p0000 := @g_noel (.cv x)
  have p0001 := @g_pm2_21i (.classMem (.cv x) (syn_c0)) (.neg ph) p0000
  have p0002 := @g_nrex ph x (syn_c0) p0001
  exact p0002

@[expose]
noncomputable def g_eq0 (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wb (.classEq A (syn_c0)) (.all x (.neg (.classMem (.cv x) A)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_neq0 x A
      (by
        first
        | (aesop))
  have p0001 := (Nominal.biimpRefl (syn_wex x (.classMem (.cv x) A)))
  have p0002 :=
    @g_bitri (.neg (.classEq A (syn_c0))) (syn_wex x (.classMem (.cv x) A))
      (.neg (.all x (.neg (.classMem (.cv x) A)))) p0000 p0001
  have p0003 :=
    @g_con4bii (.classEq A (syn_c0)) (.all x (.neg (.classMem (.cv x) A))) p0002
  exact p0003

@[expose]
noncomputable def g_eqv (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wb (.classEq A (syn_cvv)) (.all x (.classMem (.cv x) A))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_dfcleq x A (syn_cvv)
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv] at ⊢;
            aesop))
  have p0001 := @g_vex x
  have p0002 := @g_tbt (.classMem (.cv x) (syn_cvv)) (.classMem (.cv x) A) p0001
  have p0003 :=
    @g_albii (.classMem (.cv x) A)
      (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (syn_cvv))) x p0002
  have p0004 :=
    @g_bitr4i (.classEq A (syn_cvv))
      (.all x (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (syn_cvv))))
      (.all x (.classMem (.cv x) A)) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_abvor0 (ph : Wff) (x : Var) (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf
      (syn_wo (.classEq (.cab x ph) (syn_cvv)) (.classEq (.cab x ph) (syn_c0))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var)
  have p0000 := @g_id ph
  have p0001 := @g_vex x
  have p0002 := @g_a1i (.classMem (.cv x) (syn_cvv)) ph p0001
  have p0003 := @g_n_2thd ph ph (.classMem (.cv x) (syn_cvv)) p0000 p0002
  have p0004 :=
    @g_eqabcdv ph ph x (syn_cvv)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      p0003
  have p0005 := @g_con3i ph (.classEq (.cab x ph) (syn_cvv)) p0004
  have p0006 := @g_id (.neg ph)
  have p0007 := @g_noel (.cv x)
  have p0008 := @g_a1i (.neg (.classMem (.cv x) (syn_c0))) (.neg ph) p0007
  have p0009 := @g_n_2falsed (.neg ph) ph (.classMem (.cv x) (syn_c0)) p0006 p0008
  have p0010 :=
    @g_eqabcdv (.neg ph) ph x (syn_c0)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg] at ⊢;
            aesop))
      p0009
  have p0011 :=
    @g_syl (.neg (.classEq (.cab x ph) (syn_cvv))) (.neg ph)
      (.classEq (.cab x ph) (syn_c0)) p0005 p0010
  have p0012 :=
    @g_orri (.classEq (.cab x ph) (syn_cvv)) (.classEq (.cab x ph) (syn_c0)) p0011
  exact p0012

@[expose]
noncomputable def g_abn0 (ph : Wff) (x : Var) :
    Nominal.NPrf (syn_wb (syn_wne (.cab x ph) (syn_c0)) (syn_wex x ph)) :=
  by
  have p0000 := @g_nfab1 ph x
  have p0001 := @g_n0f x (.cab x ph) p0000
  have p0002 := @g_abid ph x
  have p0003 := @g_exbii (.classMem (.cv x) (.cab x ph)) ph x p0002
  have p0004 :=
    @g_bitri (syn_wne (.cab x ph) (syn_c0)) (syn_wex x (.classMem (.cv x) (.cab x ph)))
      (syn_wex x ph) p0001 p0003
  exact p0004

@[expose]
noncomputable def g_ab0 (ph : Wff) (x : Var) :
    Nominal.NPrf (syn_wb (.classEq (.cab x ph) (syn_c0)) (.all x (.neg ph))) :=
  by
  have p0000 := @g_abn0 ph x
  have p0001 := (Nominal.biimpRefl (syn_wne (.cab x ph) (syn_c0)))
  have p0002 := (Nominal.biimpRefl (syn_wex x ph))
  have p0003 :=
    @g_n_3bitr3i (syn_wne (.cab x ph) (syn_c0)) (syn_wex x ph)
      (.neg (.classEq (.cab x ph) (syn_c0))) (.neg (.all x (.neg ph))) p0000 p0001 p0002
  have p0004 := @g_con4bii (.classEq (.cab x ph) (syn_c0)) (.all x (.neg ph)) p0003
  exact p0004

@[expose]
noncomputable def g_un0 (A : Class) : Nominal.NPrf (.classEq (syn_cun A (syn_c0)) A) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have p0000 := @g_noel (.cv x)
  have p0001 := @g_biorfi (.classMem (.cv x) (syn_c0)) (.classMem (.cv x) A) p0000
  have p0002 :=
    @g_bicomi (.classMem (.cv x) A)
      (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) (syn_c0))) p0001
  have p0003 :=
    @g_uneqri x A (syn_c0) A
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      p0002
  exact p0003

@[expose]
noncomputable def g_in0 (A : Class) :
    Nominal.NPrf (.classEq (syn_cin A (syn_c0)) (syn_c0)) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have p0000 := @g_noel (.cv x)
  have p0001 := @g_bianfi (.classMem (.cv x) (syn_c0)) (.classMem (.cv x) A) p0000
  have p0002 :=
    @g_bicomi (.classMem (.cv x) (syn_c0))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) (syn_c0))) p0001
  have p0003 :=
    @g_ineqri x A (syn_c0) (syn_c0)
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0] at ⊢;
            aesop))
      p0002
  exact p0003

@[expose]
noncomputable def g_inv1 (A : Class) : Nominal.NPrf (.classEq (syn_cin A (syn_cvv)) A) :=
  by
  have p0000 := @g_inss1 A (syn_cvv)
  have p0001 := @g_ssid A
  have p0002 := @g_ssv A
  have p0003 := @g_ssini A A (syn_cvv) p0001 p0002
  have p0004 := @g_eqssi (syn_cin A (syn_cvv)) A p0000 p0003
  exact p0004

@[expose]
noncomputable def g_n_0ss (A : Class) : Nominal.NPrf (syn_wss (syn_c0) A) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have p0000 := @g_noel (.cv x)
  have p0001 := @g_pm2_21i (.classMem (.cv x) (syn_c0)) (.classMem (.cv x) A) p0000
  have p0002 :=
    @g_ssriv x (syn_c0) A
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      p0001
  exact p0002

@[expose]
noncomputable def g_ss0b (A : Class) :
    Nominal.NPrf (syn_wb (syn_wss A (syn_c0)) (.classEq A (syn_c0))) :=
  by
  have p0000 := @g_n_0ss A
  have p0001 := @g_eqss A (syn_c0)
  have p0002 :=
    @g_mpbiran2 (.classEq A (syn_c0)) (syn_wss A (syn_c0)) (syn_wss (syn_c0) A) p0000
      p0001
  have p0003 := @g_bicomi (.classEq A (syn_c0)) (syn_wss A (syn_c0)) p0002
  exact p0003

@[expose]
noncomputable def g_ss0 (A : Class) :
    Nominal.NPrf (.imp (syn_wss A (syn_c0)) (.classEq A (syn_c0))) :=
  by
  have p0000 := @g_ss0b A
  have p0001 := @g_biimpi (syn_wss A (syn_c0)) (.classEq A (syn_c0)) p0000
  exact p0001

@[expose]
noncomputable def g_abf (ph : Wff) (x : Var) (hyp_abf_1 : Nominal.NPrf (.neg ph)) :
    Nominal.NPrf (.classEq (.cab x ph) (syn_c0)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var)
  have p0000 := @g_pm2_21i ph (.classMem (.cv x) (syn_c0)) hyp_abf_1
  have p0001 :=
    @g_abssi ph x (syn_c0)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0] at ⊢;
            aesop))
      p0000
  have p0002 := @g_ss0 (.cab x ph)
  have p0003 := Nominal.mp p0001 p0002
  exact p0003

@[expose]
noncomputable def g_eq0rdv (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_ph_x : x ∉ ph.fv)
    (hyp_eq0rdv_1 : Nominal.NPrf (.imp ph (.neg (.classMem (.cv x) A)))) :
    Nominal.NPrf (.imp ph (.classEq A (syn_c0))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_pm2_21d ph (.classMem (.cv x) A) (.classMem (.cv x) (syn_c0)) hyp_eq0rdv_1
  have p0001 :=
    @g_ssrdv ph x A (syn_c0)
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      p0000
  have p0002 := @g_ss0 A
  have p0003 := @g_syl ph (syn_wss A (syn_c0)) (.classEq A (syn_c0)) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_un00 (A : Class) (B : Class) :
    Nominal.NPrf
      (syn_wb (syn_wa (.classEq A (syn_c0)) (.classEq B (syn_c0)))
        (.classEq (syn_cun A B) (syn_c0))) :=
  by
  have p0000 := @g_uneq12 A (syn_c0) B (syn_c0)
  have p0001 := @g_un0 (syn_c0)
  have p0002 :=
    @g_syl6eq (syn_wa (.classEq A (syn_c0)) (.classEq B (syn_c0))) (syn_cun A B)
      (syn_cun (syn_c0) (syn_c0)) (syn_c0) p0000 p0001
  have p0003 := @g_ssun1 A B
  have p0004 := @g_sseq2 (syn_cun A B) (syn_c0) A
  have p0005 :=
    @g_mpbii (.classEq (syn_cun A B) (syn_c0)) (syn_wss A (syn_cun A B))
      (syn_wss A (syn_c0)) p0003 p0004
  have p0006 := @g_ss0b A
  have p0007 :=
    @g_sylib (.classEq (syn_cun A B) (syn_c0)) (syn_wss A (syn_c0)) (.classEq A (syn_c0))
      p0005 p0006
  have p0008 := @g_ssun2 B A
  have p0009 := @g_sseq2 (syn_cun A B) (syn_c0) B
  have p0010 :=
    @g_mpbii (.classEq (syn_cun A B) (syn_c0)) (syn_wss B (syn_cun A B))
      (syn_wss B (syn_c0)) p0008 p0009
  have p0011 := @g_ss0b B
  have p0012 :=
    @g_sylib (.classEq (syn_cun A B) (syn_c0)) (syn_wss B (syn_c0)) (.classEq B (syn_c0))
      p0010 p0011
  have p0013 :=
    @g_jca (.classEq (syn_cun A B) (syn_c0)) (.classEq A (syn_c0)) (.classEq B (syn_c0))
      p0007 p0012
  have p0014 :=
    @g_impbii (syn_wa (.classEq A (syn_c0)) (.classEq B (syn_c0)))
      (.classEq (syn_cun A B) (syn_c0)) p0002 p0013
  exact p0014

@[expose]
noncomputable def g_vss (A : Class) :
    Nominal.NPrf (syn_wb (syn_wss (syn_cvv) A) (.classEq A (syn_cvv))) :=
  by
  have p0000 := @g_ssv A
  have p0001 := @g_biantrur (syn_wss A (syn_cvv)) (syn_wss (syn_cvv) A) p0000
  have p0002 := @g_eqss A (syn_cvv)
  have p0003 :=
    @g_bitr4i (syn_wss (syn_cvv) A) (syn_wa (syn_wss A (syn_cvv)) (syn_wss (syn_cvv) A))
      (.classEq A (syn_cvv)) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_disj (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (syn_wb (.classEq (syn_cin A B) (syn_c0)) (syn_wral x A (.neg (.classMem (.cv x) B)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := @g_elin (.cv x) A B
  have p0001 := (Nominal.biimpRefl (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)))
  have p0002 :=
    @g_bitr2i (.classMem (.cv x) (syn_cin A B))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B))
      (.neg (.imp (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))) p0000 p0001
  have p0003 :=
    @g_con1bii (.imp (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))
      (.classMem (.cv x) (syn_cin A B)) p0002
  have p0004 :=
    @g_albii (.neg (.classMem (.cv x) (syn_cin A B)))
      (.imp (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))) x p0003
  have p0005 :=
    @g_eq0 x (syn_cin A B)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
              Finset.mem_union] at ⊢;
            aesop))
  have p0006 := (Nominal.biimpRefl (syn_wral x A (.neg (.classMem (.cv x) B))))
  have p0007 :=
    @g_n_3bitr4i (.all x (.neg (.classMem (.cv x) (syn_cin A B))))
      (.all x (.imp (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))))
      (.classEq (syn_cin A B) (syn_c0)) (syn_wral x A (.neg (.classMem (.cv x) B))) p0004
      p0005 p0006
  exact p0007

@[expose]
noncomputable def g_disjr (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (syn_wb (.classEq (syn_cin A B) (syn_c0)) (syn_wral x B (.neg (.classMem (.cv x) A)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := @g_incom A B
  have p0001 := @g_eqeq1i (syn_cin A B) (syn_cin B A) (syn_c0) p0000
  have p0002 :=
    @g_disj x B A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0003 :=
    @g_bitri (.classEq (syn_cin A B) (syn_c0)) (.classEq (syn_cin B A) (syn_c0))
      (syn_wral x B (.neg (.classMem (.cv x) A))) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_disj1 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (syn_wb (.classEq (syn_cin A B) (syn_c0))
        (.all x (.imp (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_disj x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 := (Nominal.biimpRefl (syn_wral x A (.neg (.classMem (.cv x) B))))
  have p0002 :=
    @g_bitri (.classEq (syn_cin A B) (syn_c0)) (syn_wral x A (.neg (.classMem (.cv x) B)))
      (.all x (.imp (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_ssdif0 (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (syn_wss A B) (.classEq (syn_cdif A B) (syn_c0))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 := @g_iman (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0001 := @g_eldif (.cv x) A B
  have p0002 :=
    @g_xchbinxr (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))
      (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))
      (.classMem (.cv x) (syn_cdif A B)) p0000 p0001
  have p0003 :=
    @g_albii (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))
      (.neg (.classMem (.cv x) (syn_cdif A B))) x p0002
  have p0004 :=
    @g_dfss2 x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0005 :=
    @g_eq0 x (syn_cdif A B)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
              Finset.mem_union] at ⊢;
            aesop))
  have p0006 :=
    @g_n_3bitr4i (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (.all x (.neg (.classMem (.cv x) (syn_cdif A B)))) (syn_wss A B)
      (.classEq (syn_cdif A B) (syn_c0)) p0003 p0004 p0005
  exact p0006

@[expose]
noncomputable def g_inssdif0 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (syn_wb (syn_wss (syn_cin A B) C) (.classEq (syn_cin A (syn_cdif B C)) (syn_c0))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 := @g_elin (.cv x) A B
  have p0001 :=
    @g_imbi1i (.classMem (.cv x) (syn_cin A B))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) C) p0000
  have p0002 :=
    @g_iman (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) C)
  have p0003 :=
    @g_bitri (.imp (.classMem (.cv x) (syn_cin A B)) (.classMem (.cv x) C))
      (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) C))
      (.neg (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B))
          (.neg (.classMem (.cv x) C))))
      p0001 p0002
  have p0004 := @g_eldif (.cv x) B C
  have p0005 :=
    @g_anbi2i (.classMem (.cv x) (syn_cdif B C))
      (syn_wa (.classMem (.cv x) B) (.neg (.classMem (.cv x) C))) (.classMem (.cv x) A)
      p0004
  have p0006 := @g_elin (.cv x) A (syn_cdif B C)
  have p0007 :=
    @g_anass (.classMem (.cv x) A) (.classMem (.cv x) B) (.neg (.classMem (.cv x) C))
  have p0008 :=
    @g_n_3bitr4ri (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) (syn_cdif B C)))
      (syn_wa (.classMem (.cv x) A) (syn_wa (.classMem (.cv x) B) (.neg (.classMem (.cv x) C))))
      (.classMem (.cv x) (syn_cin A (syn_cdif B C)))
      (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)) (.neg (.classMem (.cv x) C)))
      p0005 p0006 p0007
  have p0009 :=
    @g_xchbinx (.imp (.classMem (.cv x) (syn_cin A B)) (.classMem (.cv x) C))
      (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)) (.neg (.classMem (.cv x) C)))
      (.classMem (.cv x) (syn_cin A (syn_cdif B C))) p0003 p0008
  have p0010 :=
    @g_albii (.imp (.classMem (.cv x) (syn_cin A B)) (.classMem (.cv x) C))
      (.neg (.classMem (.cv x) (syn_cin A (syn_cdif B C)))) x p0009
  have p0011 :=
    @g_dfss2 x (syn_cin A B) C
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        | (aesop))
  have p0012 :=
    @g_eq0 x (syn_cin A (syn_cdif B C))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
              Finset.mem_union] at ⊢;
            aesop))
  have p0013 :=
    @g_n_3bitr4i (.all x (.imp (.classMem (.cv x) (syn_cin A B)) (.classMem (.cv x) C)))
      (.all x (.neg (.classMem (.cv x) (syn_cin A (syn_cdif B C)))))
      (syn_wss (syn_cin A B) C) (.classEq (syn_cin A (syn_cdif B C)) (syn_c0)) p0010 p0011
      p0012
  exact p0013

@[expose]
noncomputable def g_difid (A : Class) : Nominal.NPrf (.classEq (syn_cdif A A) (syn_c0)) :=
  by
  have p0000 := @g_ssid A
  have p0001 := @g_ssdif0 A A
  have p0002 := @g_mpbi (syn_wss A A) (.classEq (syn_cdif A A) (syn_c0)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_dif0 (A : Class) : Nominal.NPrf (.classEq (syn_cdif A (syn_c0)) A) :=
  by
  have p0000 := @g_difid A
  have p0001 := @g_difeq2i (syn_cdif A A) (syn_c0) A p0000
  have p0002 := @g_difdif A A
  have p0003 := @g_eqtr3i (syn_cdif A (syn_cdif A A)) (syn_cdif A (syn_c0)) A p0001 p0002
  exact p0003

@[expose]
noncomputable def g_disjdif (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cin A (syn_cdif B A)) (syn_c0)) :=
  by
  have p0000 := @g_inss1 A B
  have p0001 := @g_inssdif0 A B A
  have p0002 :=
    @g_mpbi (syn_wss (syn_cin A B) A) (.classEq (syn_cin A (syn_cdif B A)) (syn_c0)) p0000
      p0001
  exact p0002

@[expose]
noncomputable def g_undifv (A : Class) :
    Nominal.NPrf (.classEq (syn_cun A (syn_cdif (syn_cvv) A)) (syn_cvv)) :=
  by
  have p0000 := @g_dfun3 A (syn_cdif (syn_cvv) A)
  have p0001 := @g_disjdif (syn_cdif (syn_cvv) A) (syn_cvv)
  have p0002 :=
    @g_difeq2i
      (syn_cin (syn_cdif (syn_cvv) A) (syn_cdif (syn_cvv) (syn_cdif (syn_cvv) A)))
      (syn_c0) (syn_cvv) p0001
  have p0003 := @g_dif0 (syn_cvv)
  have p0004 :=
    @g_n_3eqtri (syn_cun A (syn_cdif (syn_cvv) A))
      (syn_cdif (syn_cvv)
        (syn_cin (syn_cdif (syn_cvv) A) (syn_cdif (syn_cvv) (syn_cdif (syn_cvv) A))))
      (syn_cdif (syn_cvv) (syn_c0)) (syn_cvv) p0000 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_undif1 (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cun (syn_cdif A B) B) (syn_cun A B)) :=
  by
  have p0000 := @g_undir A (syn_cdif (syn_cvv) B) B
  have p0001 := @g_invdif A B
  have p0002 := @g_uneq1i (syn_cin A (syn_cdif (syn_cvv) B)) (syn_cdif A B) B p0001
  have p0003 := @g_uncom (syn_cdif (syn_cvv) B) B
  have p0004 := @g_undifv B
  have p0005 :=
    @g_eqtri (syn_cun (syn_cdif (syn_cvv) B) B) (syn_cun B (syn_cdif (syn_cvv) B))
      (syn_cvv) p0003 p0004
  have p0006 := @g_ineq2i (syn_cun (syn_cdif (syn_cvv) B) B) (syn_cvv) (syn_cun A B) p0005
  have p0007 := @g_inv1 (syn_cun A B)
  have p0008 :=
    @g_eqtri (syn_cin (syn_cun A B) (syn_cun (syn_cdif (syn_cvv) B) B))
      (syn_cin (syn_cun A B) (syn_cvv)) (syn_cun A B) p0006 p0007
  have p0009 :=
    @g_n_3eqtr3i (syn_cun (syn_cin A (syn_cdif (syn_cvv) B)) B)
      (syn_cin (syn_cun A B) (syn_cun (syn_cdif (syn_cvv) B) B))
      (syn_cun (syn_cdif A B) B) (syn_cun A B) p0000 p0002 p0008
  exact p0009

@[expose]
noncomputable def g_undif2 (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cun A (syn_cdif B A)) (syn_cun A B)) :=
  by
  have p0000 := @g_uncom A (syn_cdif B A)
  have p0001 := @g_undif1 B A
  have p0002 := @g_uncom B A
  have p0003 :=
    @g_n_3eqtri (syn_cun A (syn_cdif B A)) (syn_cun (syn_cdif B A) A) (syn_cun B A)
      (syn_cun A B) p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_inundif (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cun (syn_cin A B) (syn_cdif A B)) A) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 := @g_elin (.cv x) A B
  have p0001 := @g_eldif (.cv x) A B
  have p0002 :=
    @g_orbi12i (.classMem (.cv x) (syn_cin A B))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B))
      (.classMem (.cv x) (syn_cdif A B))
      (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))) p0000 p0001
  have p0003 := @g_pm4_42 (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0004 :=
    @g_bitr4i
      (syn_wo (.classMem (.cv x) (syn_cin A B)) (.classMem (.cv x) (syn_cdif A B)))
      (syn_wo (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B))
        (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))))
      (.classMem (.cv x) A) p0002 p0003
  have p0005 :=
    @g_uneqri x (syn_cin A B) (syn_cdif A B) A
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      p0004
  exact p0005

@[expose]
noncomputable def g_difun2 (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cdif (syn_cun A B) B) (syn_cdif A B)) :=
  by
  have p0000 := @g_difundir A B B
  have p0001 := @g_difid B
  have p0002 := @g_uneq2i (syn_cdif B B) (syn_c0) (syn_cdif A B) p0001
  have p0003 := @g_un0 (syn_cdif A B)
  have p0004 :=
    @g_n_3eqtri (syn_cdif (syn_cun A B) B) (syn_cun (syn_cdif A B) (syn_cdif B B))
      (syn_cun (syn_cdif A B) (syn_c0)) (syn_cdif A B) p0000 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_undif (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (syn_wss A B) (.classEq (syn_cun A (syn_cdif B A)) B)) :=
  by
  have p0000 := @g_ssequn1 A B
  have p0001 := @g_undif2 A B
  have p0002 := @g_eqeq1i (syn_cun A (syn_cdif B A)) (syn_cun A B) B p0001
  have p0003 :=
    @g_bitr4i (syn_wss A B) (.classEq (syn_cun A B) B)
      (.classEq (syn_cun A (syn_cdif B A)) B) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_ssundif (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (syn_wb (syn_wss A (syn_cun B C)) (syn_wss (syn_cdif A B) C)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 := @g_pm5_6 (.classMem (.cv x) A) (.classMem (.cv x) B) (.classMem (.cv x) C)
  have p0001 := @g_eldif (.cv x) A B
  have p0002 :=
    @g_imbi1i (.classMem (.cv x) (syn_cdif A B))
      (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))) (.classMem (.cv x) C)
      p0001
  have p0003 := @g_elun (.cv x) B C
  have p0004 :=
    @g_imbi2i (.classMem (.cv x) (syn_cun B C))
      (syn_wo (.classMem (.cv x) B) (.classMem (.cv x) C)) (.classMem (.cv x) A) p0003
  have p0005 :=
    @g_n_3bitr4ri
      (.imp (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))) (.classMem (.cv x) C))
      (.imp (.classMem (.cv x) A) (syn_wo (.classMem (.cv x) B) (.classMem (.cv x) C)))
      (.imp (.classMem (.cv x) (syn_cdif A B)) (.classMem (.cv x) C))
      (.imp (.classMem (.cv x) A) (.classMem (.cv x) (syn_cun B C))) p0000 p0002 p0004
  have p0006 :=
    @g_albii (.imp (.classMem (.cv x) A) (.classMem (.cv x) (syn_cun B C)))
      (.imp (.classMem (.cv x) (syn_cdif A B)) (.classMem (.cv x) C)) x p0005
  have p0007 :=
    @g_dfss2 x A (syn_cun B C)
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              Finset.mem_union] at ⊢;
            aesop))
  have p0008 :=
    @g_dfss2 x (syn_cdif A B) C
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        | (aesop))
  have p0009 :=
    @g_n_3bitr4i (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) (syn_cun B C))))
      (.all x (.imp (.classMem (.cv x) (syn_cdif A B)) (.classMem (.cv x) C)))
      (syn_wss A (syn_cun B C)) (syn_wss (syn_cdif A B) C) p0006 p0007 p0008
  exact p0009

@[expose]
noncomputable def g_r19_2z (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wne A (syn_c0)) (syn_wral x A ph)) (syn_wrex x A ph)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := (Nominal.biimpRefl (syn_wral x A ph))
  have p0001 := @g_exintr (.classMem (.cv x) A) ph x
  have p0002 :=
    @g_sylbi (syn_wral x A ph) (.all x (.imp (.classMem (.cv x) A) ph))
      (.imp (syn_wex x (.classMem (.cv x) A)) (syn_wex x (syn_wa (.classMem (.cv x) A) ph)))
      p0000 p0001
  have p0003 :=
    @g_n0 x A
      (by
        first
        | (aesop))
  have p0004 := (Nominal.biimpRefl (syn_wrex x A ph))
  have p0005 :=
    @g_n_3imtr4g (syn_wral x A ph) (syn_wex x (.classMem (.cv x) A))
      (syn_wex x (syn_wa (.classMem (.cv x) A) ph)) (syn_wne A (syn_c0)) (syn_wrex x A ph)
      p0002 p0003 p0004
  have p0006 := @g_impcom (syn_wral x A ph) (syn_wne A (syn_c0)) (syn_wrex x A ph) p0005
  exact p0006

@[expose]
noncomputable def g_sscon34 (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (syn_wss A B) (syn_wss (syn_ccompl B) (syn_ccompl A))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 := @g_con34b (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0001 := @g_vex x
  have p0002 := @g_elcompl (.cv x) B p0001
  have p0003 := @g_elcompl (.cv x) A p0001
  have p0004 :=
    @g_imbi12i (.classMem (.cv x) (syn_ccompl B)) (.neg (.classMem (.cv x) B))
      (.classMem (.cv x) (syn_ccompl A)) (.neg (.classMem (.cv x) A)) p0002 p0003
  have p0005 :=
    @g_bitr4i (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))
      (.imp (.neg (.classMem (.cv x) B)) (.neg (.classMem (.cv x) A)))
      (.imp (.classMem (.cv x) (syn_ccompl B)) (.classMem (.cv x) (syn_ccompl A))) p0000
      p0004
  have p0006 :=
    @g_albii (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))
      (.imp (.classMem (.cv x) (syn_ccompl B)) (.classMem (.cv x) (syn_ccompl A))) x p0005
  have p0007 :=
    @g_dfss2 x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0008 :=
    @g_dfss2 x (syn_ccompl B) (syn_ccompl A)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl] at ⊢;
            aesop))
  have p0009 :=
    @g_n_3bitr4i (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (.all x (.imp (.classMem (.cv x) (syn_ccompl B)) (.classMem (.cv x) (syn_ccompl A))))
      (syn_wss A B) (syn_wss (syn_ccompl B) (syn_ccompl A)) p0006 p0007 p0008
  exact p0009

@[expose]
noncomputable def g_dfif2 (ph : Wff) (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf
      (.classEq (syn_cif ph A B) (.cab x
          (.imp (.imp (.classMem (.cv x) B) ph) (syn_wa (.classMem (.cv x) A) ph)))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_if ph x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    (Nominal.biimpRefl
      (syn_wo (syn_wa (.classMem (.cv x) B) (.neg ph)) (syn_wa (.classMem (.cv x) A) ph)))
  have p0002 :=
    @g_orcom (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv x) B) (.neg ph))
  have p0003 := @g_iman (.classMem (.cv x) B) ph
  have p0004 :=
    @g_imbi1i (.imp (.classMem (.cv x) B) ph)
      (.neg (syn_wa (.classMem (.cv x) B) (.neg ph))) (syn_wa (.classMem (.cv x) A) ph)
      p0003
  have p0005 :=
    @g_n_3bitr4i
      (syn_wo (syn_wa (.classMem (.cv x) B) (.neg ph)) (syn_wa (.classMem (.cv x) A) ph))
      (.imp (.neg (syn_wa (.classMem (.cv x) B) (.neg ph))) (syn_wa (.classMem (.cv x) A) ph))
      (syn_wo (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv x) B) (.neg ph)))
      (.imp (.imp (.classMem (.cv x) B) ph) (syn_wa (.classMem (.cv x) A) ph)) p0001 p0002
      p0004
  have p0006 :=
    @g_abbii
      (syn_wo (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv x) B) (.neg ph)))
      (.imp (.imp (.classMem (.cv x) B) ph) (syn_wa (.classMem (.cv x) A) ph)) x p0005
  have p0007 :=
    @g_eqtri (syn_cif ph A B)
      (.cab x (syn_wo (syn_wa (.classMem (.cv x) A) ph)
          (syn_wa (.classMem (.cv x) B) (.neg ph))))
      (.cab x (.imp (.imp (.classMem (.cv x) B) ph) (syn_wa (.classMem (.cv x) A) ph)))
      p0000 p0006
  exact p0007

@[expose]
noncomputable def g_dfif6 (ph : Wff) (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf
      (.classEq (syn_cif ph A B) (syn_cun (syn_crab x A ph) (syn_crab x B (.neg ph)))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_unab (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv x) B) (.neg ph)) x
  have p0001 := (Nominal.classEqRefl (syn_crab x A ph))
  have p0002 := (Nominal.classEqRefl (syn_crab x B (.neg ph)))
  have p0003 :=
    @g_uneq12i (syn_crab x A ph) (.cab x (syn_wa (.classMem (.cv x) A) ph))
      (syn_crab x B (.neg ph)) (.cab x (syn_wa (.classMem (.cv x) B) (.neg ph))) p0001
      p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_if ph x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0005 :=
    @g_n_3eqtr4ri
      (syn_cun (.cab x (syn_wa (.classMem (.cv x) A) ph))
        (.cab x (syn_wa (.classMem (.cv x) B) (.neg ph))))
      (.cab x (syn_wo (syn_wa (.classMem (.cv x) A) ph)
          (syn_wa (.classMem (.cv x) B) (.neg ph))))
      (syn_cun (syn_crab x A ph) (syn_crab x B (.neg ph))) (syn_cif ph A B) p0000 p0003
      p0004
  exact p0005

@[expose]
noncomputable def g_ifeq1 (ph : Wff) (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cif ph A C) (syn_cif ph B C))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_ph : x ∉ ph.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_rabeq ph x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @g_uneq1d (.classEq A B) (syn_crab x A ph) (syn_crab x B ph) (syn_crab x C (.neg ph))
      p0000
  have p0002 :=
    @g_dfif6 ph x A C
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0003 :=
    @g_dfif6 ph x B C
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cun (syn_crab x A ph) (syn_crab x C (.neg ph)))
      (syn_cun (syn_crab x B ph) (syn_crab x C (.neg ph))) (syn_cif ph A C)
      (syn_cif ph B C) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_ifeq2 (ph : Wff) (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cif ph C A) (syn_cif ph C B))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_ph : x ∉ ph.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_rabeq (.neg ph) x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @g_uneq2d (.classEq A B) (syn_crab x A (.neg ph)) (syn_crab x B (.neg ph))
      (syn_crab x C ph) p0000
  have p0002 :=
    @g_dfif6 ph x C A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0003 :=
    @g_dfif6 ph x C B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cun (syn_crab x C ph) (syn_crab x A (.neg ph)))
      (syn_cun (syn_crab x C ph) (syn_crab x B (.neg ph))) (syn_cif ph C A)
      (syn_cif ph C B) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_iftrue (ph : Wff) (A : Class) (B : Class) :
    Nominal.NPrf (.imp ph (.classEq (syn_cif ph A B) A)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_ph : x ∉ ph.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 := @g_dedlem0a ph (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0001 :=
    @g_eqabdv ph (.imp (.imp (.classMem (.cv x) B) ph) (syn_wa (.classMem (.cv x) A) ph))
      x A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000
  have p0002 :=
    @g_dfif2 ph x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0003 :=
    @g_syl6reqr ph A
      (.cab x (.imp (.imp (.classMem (.cv x) B) ph) (syn_wa (.classMem (.cv x) A) ph)))
      (syn_cif ph A B) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_iffalse (ph : Wff) (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.neg ph) (.classEq (syn_cif ph A B) B)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_ph : x ∉ ph.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 := @g_dedlemb ph (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0001 :=
    @g_eqabdv (.neg ph)
      (syn_wo (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv x) B) (.neg ph)))
      x B
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg] at ⊢;
            aesop))
      p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_if ph x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0003 :=
    @g_syl6reqr (.neg ph) B
      (.cab x (syn_wo (syn_wa (.classMem (.cv x) A) ph)
          (syn_wa (.classMem (.cv x) B) (.neg ph))))
      (syn_cif ph A B) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_ifeq1d (ph : Wff) (ps : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_ifeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cif ps A C) (syn_cif ps B C))) :=
  by
  have p0000 := @g_ifeq1 ps A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cif ps A C) (syn_cif ps B C)) hyp_ifeq1d_1
      p0000
  exact p0001

@[expose]
noncomputable def g_ifeq2d (ph : Wff) (ps : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_ifeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cif ps C A) (syn_cif ps C B))) :=
  by
  have p0000 := @g_ifeq2 ps A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cif ps C A) (syn_cif ps C B)) hyp_ifeq1d_1
      p0000
  exact p0001

@[expose]
noncomputable def g_ifeq12d (ph : Wff) (ps : Wff) (A : Class) (B : Class) (C : Class)
    (D : Class) (hyp_ifeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_ifeq12d_2 : Nominal.NPrf (.imp ph (.classEq C D))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cif ps A C) (syn_cif ps B D))) :=
  by
  have p0000 := @g_ifeq1d ph ps A B C hyp_ifeq1d_1
  have p0001 := @g_ifeq2d ph ps C D B hyp_ifeq12d_2
  have p0002 := @g_eqtrd ph (syn_cif ps A C) (syn_cif ps B C) (syn_cif ps B D) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_ifbi (ph : Wff) (ps : Wff) (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wb ph ps) (.classEq (syn_cif ph A B) (syn_cif ps A B))) :=
  by
  have p0000 := @g_dfbi3 ph ps
  have p0001 := @g_iftrue ph A B
  have p0002 := @g_iftrue ps A B
  have p0003 := @g_eqcomd ps (syn_cif ps A B) A p0002
  have p0004 := @g_sylan9eq ph ps (syn_cif ph A B) A (syn_cif ps A B) p0001 p0003
  have p0005 := @g_iffalse ph A B
  have p0006 := @g_iffalse ps A B
  have p0007 := @g_eqcomd (.neg ps) (syn_cif ps A B) B p0006
  have p0008 :=
    @g_sylan9eq (.neg ph) (.neg ps) (syn_cif ph A B) B (syn_cif ps A B) p0005 p0007
  have p0009 :=
    @g_jaoi (syn_wa ph ps) (.classEq (syn_cif ph A B) (syn_cif ps A B))
      (syn_wa (.neg ph) (.neg ps)) p0004 p0008
  have p0010 :=
    @g_sylbi (syn_wb ph ps) (syn_wo (syn_wa ph ps) (syn_wa (.neg ph) (.neg ps)))
      (.classEq (syn_cif ph A B) (syn_cif ps A B)) p0000 p0009
  exact p0010

@[expose]
noncomputable def g_ifbid (ph : Wff) (ps : Wff) (ch : Wff) (A : Class) (B : Class)
    (hyp_ifbid_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cif ps A B) (syn_cif ch A B))) :=
  by
  have p0000 := @g_ifbi ps ch A B
  have p0001 :=
    @g_syl ph (syn_wb ps ch) (.classEq (syn_cif ps A B) (syn_cif ch A B)) hyp_ifbid_1
      p0000
  exact p0001

@[expose]
noncomputable def g_ifbieq2d (ph : Wff) (ps : Wff) (ch : Wff) (A : Class) (B : Class)
    (C : Class) (hyp_ifbieq2d_1 : Nominal.NPrf (.imp ph (syn_wb ps ch)))
    (hyp_ifbieq2d_2 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cif ps C A) (syn_cif ch C B))) :=
  by
  have p0000 := @g_ifbid ph ps ch C A hyp_ifbieq2d_1
  have p0001 := @g_ifeq2d ph ch A B C hyp_ifbieq2d_2
  have p0002 := @g_eqtrd ph (syn_cif ps C A) (syn_cif ch C A) (syn_cif ch C B) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_ifbieq12d (ph : Wff) (ps : Wff) (ch : Wff) (A : Class) (B : Class)
    (C : Class) (D : Class) (hyp_ifbieq12d_1 : Nominal.NPrf (.imp ph (syn_wb ps ch)))
    (hyp_ifbieq12d_2 : Nominal.NPrf (.imp ph (.classEq A C)))
    (hyp_ifbieq12d_3 : Nominal.NPrf (.imp ph (.classEq B D))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cif ps A B) (syn_cif ch C D))) :=
  by
  have p0000 := @g_ifbid ph ps ch A B hyp_ifbieq12d_1
  have p0001 := @g_ifeq12d ph ch A C B D hyp_ifbieq12d_2 hyp_ifbieq12d_3
  have p0002 := @g_eqtrd ph (syn_cif ps A B) (syn_cif ch A B) (syn_cif ch C D) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_ifclda (ph : Wff) (ps : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_ifclda_1 : Nominal.NPrf (.imp (syn_wa ph ps) (.classMem A C)))
    (hyp_ifclda_2 : Nominal.NPrf (.imp (syn_wa ph (.neg ps)) (.classMem B C))) :
    Nominal.NPrf (.imp ph (.classMem (syn_cif ps A B) C)) :=
  by
  have p0000 := @g_iftrue ps A B
  have p0001 := @g_adantl ps (.classEq (syn_cif ps A B) A) ph p0000
  have p0002 := @g_eqeltrd (syn_wa ph ps) (syn_cif ps A B) A C p0001 hyp_ifclda_1
  have p0003 := @g_iffalse ps A B
  have p0004 := @g_adantl (.neg ps) (.classEq (syn_cif ps A B) B) ph p0003
  have p0005 := @g_eqeltrd (syn_wa ph (.neg ps)) (syn_cif ps A B) B C p0004 hyp_ifclda_2
  have p0006 := @g_pm2_61dan ph ps (.classMem (syn_cif ps A B) C) p0002 p0005
  exact p0006

@[expose]
noncomputable def g_elimif (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (A : Class)
    (B : Class)
    (hyp_elimif_1 : Nominal.NPrf (.imp (.classEq (syn_cif ph A B) A) (syn_wb ps ch)))
    (hyp_elimif_2 : Nominal.NPrf (.imp (.classEq (syn_cif ph A B) B) (syn_wb ps th))) :
    Nominal.NPrf (syn_wb ps (syn_wo (syn_wa ph ch) (syn_wa (.neg ph) th))) :=
  by
  have p0000 := @g_exmid ph
  have p0001 := @g_biantrur (syn_wo ph (.neg ph)) ps p0000
  have p0002 := @g_andir ph (.neg ph) ps
  have p0003 := @g_iftrue ph A B
  have p0004 := @g_syl ph (.classEq (syn_cif ph A B) A) (syn_wb ps ch) p0003 hyp_elimif_1
  have p0005 := @g_pm5_32i ph ps ch p0004
  have p0006 := @g_iffalse ph A B
  have p0007 :=
    @g_syl (.neg ph) (.classEq (syn_cif ph A B) B) (syn_wb ps th) p0006 hyp_elimif_2
  have p0008 := @g_pm5_32i (.neg ph) ps th p0007
  have p0009 :=
    @g_orbi12i (syn_wa ph ps) (syn_wa ph ch) (syn_wa (.neg ph) ps) (syn_wa (.neg ph) th)
      p0005 p0008
  have p0010 :=
    @g_n_3bitri ps (syn_wa (syn_wo ph (.neg ph)) ps)
      (syn_wo (syn_wa ph ps) (syn_wa (.neg ph) ps))
      (syn_wo (syn_wa ph ch) (syn_wa (.neg ph) th)) p0001 p0002 p0009
  exact p0010

@[expose]
noncomputable def g_ifbothda (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (et : Wff)
    (A : Class) (B : Class)
    (hyp_ifboth_1 : Nominal.NPrf (.imp (.classEq A (syn_cif ph A B)) (syn_wb ps th)))
    (hyp_ifboth_2 : Nominal.NPrf (.imp (.classEq B (syn_cif ph A B)) (syn_wb ch th)))
    (hyp_ifbothda_3 : Nominal.NPrf (.imp (syn_wa et ph) ps))
    (hyp_ifbothda_4 : Nominal.NPrf (.imp (syn_wa et (.neg ph)) ch)) :
    Nominal.NPrf (.imp et th) :=
  by
  have p0000 := @g_iftrue ph A B
  have p0001 := @g_eqcomd ph (syn_cif ph A B) A p0000
  have p0002 := @g_syl ph (.classEq A (syn_cif ph A B)) (syn_wb ps th) p0001 hyp_ifboth_1
  have p0003 := @g_adantl ph (syn_wb ps th) et p0002
  have p0004 := @g_mpbid (syn_wa et ph) ps th hyp_ifbothda_3 p0003
  have p0005 := @g_iffalse ph A B
  have p0006 := @g_eqcomd (.neg ph) (syn_cif ph A B) B p0005
  have p0007 :=
    @g_syl (.neg ph) (.classEq B (syn_cif ph A B)) (syn_wb ch th) p0006 hyp_ifboth_2
  have p0008 := @g_adantl (.neg ph) (syn_wb ch th) et p0007
  have p0009 := @g_mpbid (syn_wa et (.neg ph)) ch th hyp_ifbothda_4 p0008
  have p0010 := @g_pm2_61dan et ph th p0004 p0009
  exact p0010

@[expose]
noncomputable def g_ifboth (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (A : Class)
    (B : Class)
    (hyp_ifboth_1 : Nominal.NPrf (.imp (.classEq A (syn_cif ph A B)) (syn_wb ps th)))
    (hyp_ifboth_2 : Nominal.NPrf (.imp (.classEq B (syn_cif ph A B)) (syn_wb ch th))) :
    Nominal.NPrf (.imp (syn_wa ps ch) th) :=
  by
  have p0000 := @g_simpll ps ch ph
  have p0001 := @g_simplr ps ch (.neg ph)
  have p0002 :=
    @g_ifbothda ph ps ch th (syn_wa ps ch) A B hyp_ifboth_1 hyp_ifboth_2 p0000 p0001
  exact p0002

@[expose]
noncomputable def g_elif (ph : Wff) (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cif ph B C))
        (syn_wo (syn_wa ph (.classMem A B)) (syn_wa (.neg ph) (.classMem A C)))) :=
  by
  have p0000 := @g_eleq2 (syn_cif ph B C) B A
  have p0001 := @g_eleq2 (syn_cif ph B C) C A
  have p0002 :=
    @g_elimif ph (.classMem A (syn_cif ph B C)) (.classMem A B) (.classMem A C) B C p0000
      p0001
  exact p0002

@[expose]
noncomputable def g_ifcl (ph : Wff) (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A C) (.classMem B C)) (.classMem (syn_cif ph A B) C)) :=
  by
  have p0000 := @g_eleq1 A (syn_cif ph A B) C
  have p0001 := @g_eleq1 B (syn_cif ph A B) C
  have p0002 :=
    @g_ifboth ph (.classMem A C) (.classMem B C) (.classMem (syn_cif ph A B) C) A B p0000
      p0001
  exact p0002

@[expose]
noncomputable def g_ifeqor (ph : Wff) (A : Class) (B : Class) :
    Nominal.NPrf (syn_wo (.classEq (syn_cif ph A B) A) (.classEq (syn_cif ph A B) B)) :=
  by
  have p0000 := @g_iftrue ph A B
  have p0001 := @g_con3i ph (.classEq (syn_cif ph A B) A) p0000
  have p0002 := @g_iffalse ph A B
  have p0003 :=
    @g_syl (.neg (.classEq (syn_cif ph A B) A)) (.neg ph) (.classEq (syn_cif ph A B) B)
      p0001 p0002
  have p0004 := @g_orri (.classEq (syn_cif ph A B) A) (.classEq (syn_cif ph A B) B) p0003
  exact p0004

@[expose]
noncomputable def g_dedth (ph : Wff) (ps : Wff) (ch : Wff) (A : Class) (B : Class)
    (hyp_dedth_1 : Nominal.NPrf (.imp (.classEq A (syn_cif ph A B)) (syn_wb ps ch)))
    (hyp_dedth_2 : Nominal.NPrf ch) : Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @g_iftrue ph A B
  have p0001 := @g_eqcomd ph (syn_cif ph A B) A p0000
  have p0002 := @g_syl ph (.classEq A (syn_cif ph A B)) (syn_wb ps ch) p0001 hyp_dedth_1
  have p0003 := @g_mpbiri ph ps ch hyp_dedth_2 p0002
  exact p0003


end NFChoice.DirectNominalPrf.WPPReplay
