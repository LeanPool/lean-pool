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

/-- Checked nominal proof certificate identified upstream as `g_unineq`. -/
@[expose]
noncomputable def gUnineq (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (synWb (synWa (.classEq (synCun A C) (synCun B C))
          (.classEq (synCin A C) (synCin B C))) (.classEq A B)) :=
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
  have p0000 := @gEleq2 (synCin A C) (synCin B C) (.cv x)
  have p0001 := @gElin (.cv x) A C
  have p0002 := @gElin (.cv x) B C
  have p0003 :=
    @gN3bitr3g (.classEq (synCin A C) (synCin B C)) (.classMem (.cv x) (synCin A C))
      (.classMem (.cv x) (synCin B C))
      (synWa (.classMem (.cv x) A) (.classMem (.cv x) C))
      (synWa (.classMem (.cv x) B) (.classMem (.cv x) C)) p0000 p0001 p0002
  have p0004 := @gIba (.classMem (.cv x) C) (.classMem (.cv x) A)
  have p0005 := @gIba (.classMem (.cv x) C) (.classMem (.cv x) B)
  have p0006 :=
    @gBibi12d (.classMem (.cv x) C) (.classMem (.cv x) A)
      (synWa (.classMem (.cv x) A) (.classMem (.cv x) C)) (.classMem (.cv x) B)
      (synWa (.classMem (.cv x) B) (.classMem (.cv x) C)) p0004 p0005
  have p0007 :=
    @gSyl5ibr (.classEq (synCin A C) (synCin B C))
      (synWb (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) C)
      (synWb (synWa (.classMem (.cv x) A) (.classMem (.cv x) C))
        (synWa (.classMem (.cv x) B) (.classMem (.cv x) C)))
      p0003 p0006
  have p0008 :=
    @gAdantld (.classMem (.cv x) C) (.classEq (synCin A C) (synCin B C))
      (synWb (.classMem (.cv x) A) (.classMem (.cv x) B))
      (.classEq (synCun A C) (synCun B C)) p0007
  have p0009 := @gUncom A C
  have p0010 := @gUncom B C
  have p0011 :=
    @gEqeq12i (synCun A C) (synCun C A) (synCun B C) (synCun C B) p0009 p0010
  have p0012 := @gEleq2 (synCun C A) (synCun C B) (.cv x)
  have p0013 :=
    @gSylbi (.classEq (synCun A C) (synCun B C)) (.classEq (synCun C A) (synCun C B))
      (synWb (.classMem (.cv x) (synCun C A)) (.classMem (.cv x) (synCun C B))) p0011
      p0012
  have p0014 := @gElun (.cv x) C A
  have p0015 := @gElun (.cv x) C B
  have p0016 :=
    @gN3bitr3g (.classEq (synCun A C) (synCun B C)) (.classMem (.cv x) (synCun C A))
      (.classMem (.cv x) (synCun C B))
      (synWo (.classMem (.cv x) C) (.classMem (.cv x) A))
      (synWo (.classMem (.cv x) C) (.classMem (.cv x) B)) p0013 p0014 p0015
  have p0017 := @gBiorf (.classMem (.cv x) C) (.classMem (.cv x) A)
  have p0018 := @gBiorf (.classMem (.cv x) C) (.classMem (.cv x) B)
  have p0019 :=
    @gBibi12d (.neg (.classMem (.cv x) C)) (.classMem (.cv x) A)
      (synWo (.classMem (.cv x) C) (.classMem (.cv x) A)) (.classMem (.cv x) B)
      (synWo (.classMem (.cv x) C) (.classMem (.cv x) B)) p0017 p0018
  have p0020 :=
    @gSyl5ibr (.classEq (synCun A C) (synCun B C))
      (synWb (.classMem (.cv x) A) (.classMem (.cv x) B)) (.neg (.classMem (.cv x) C))
      (synWb (synWo (.classMem (.cv x) C) (.classMem (.cv x) A))
        (synWo (.classMem (.cv x) C) (.classMem (.cv x) B)))
      p0016 p0019
  have p0021 :=
    @gAdantrd (.neg (.classMem (.cv x) C)) (.classEq (synCun A C) (synCun B C))
      (synWb (.classMem (.cv x) A) (.classMem (.cv x) B))
      (.classEq (synCin A C) (synCin B C)) p0020
  have p0022 :=
    @gPm261i (.classMem (.cv x) C)
      (.imp (synWa (.classEq (synCun A C) (synCun B C))
          (.classEq (synCin A C) (synCin B C)))
        (synWb (.classMem (.cv x) A) (.classMem (.cv x) B)))
      p0008 p0021
  have p0023 :=
    @gEqrdv
      (synWa (.classEq (synCun A C) (synCun B C)) (.classEq (synCin A C) (synCin B C)))
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
  have p0024 := @gUneq1 A B C
  have p0025 := @gIneq1 A B C
  have p0026 :=
    @gJca (.classEq A B) (.classEq (synCun A C) (synCun B C))
      (.classEq (synCin A C) (synCin B C)) p0024 p0025
  have p0027 :=
    @gImpbii
      (synWa (.classEq (synCun A C) (synCun B C)) (.classEq (synCin A C) (synCin B C)))
      (.classEq A B) p0023 p0026
  exact p0027

/-- Checked nominal proof certificate identified upstream as `g_difundir`. -/
@[expose]
noncomputable def gDifundir (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.classEq (synCdif (synCun A B) C) (synCun (synCdif A C) (synCdif B C))) :=
  by
  have p0000 := @gIndir A B (synCdif (synCvv) C)
  have p0001 := @gInvdif (synCun A B) C
  have p0002 := @gInvdif A C
  have p0003 := @gInvdif B C
  have p0004 :=
    @gUneq12i (synCin A (synCdif (synCvv) C)) (synCdif A C)
      (synCin B (synCdif (synCvv) C)) (synCdif B C) p0002 p0003
  have p0005 :=
    @gN3eqtr3i (synCin (synCun A B) (synCdif (synCvv) C))
      (synCun (synCin A (synCdif (synCvv) C)) (synCin B (synCdif (synCvv) C)))
      (synCdif (synCun A B) C) (synCun (synCdif A C) (synCdif B C)) p0000 p0001 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_unab`. -/
@[expose]
noncomputable def gUnab (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (.classEq (synCun (.cab x ph) (.cab x ps)) (.cab x (synWo ph ps))) :=
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
  have p0000 := @gSbor ph ps x y
  have p0001 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      y x (synWo ph ps))
  have p0002 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      y x ph)
  have p0003 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      y x ps)
  have p0004 :=
    @gOrbi12i (.classMem (.cv y) (.cab x ph)) (synWsb y x ph)
      (.classMem (.cv y) (.cab x ps)) (synWsb y x ps) p0002 p0003
  have p0005 :=
    @gN3bitr4ri (synWsb y x (synWo ph ps)) (synWo (synWsb y x ph) (synWsb y x ps))
      (.classMem (.cv y) (.cab x (synWo ph ps)))
      (synWo (.classMem (.cv y) (.cab x ph)) (.classMem (.cv y) (.cab x ps))) p0000 p0001
      p0004
  have p0006 :=
    @gUneqri y (.cab x ph) (.cab x ps) (.cab x (synWo ph ps))
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

/-- Checked nominal proof certificate identified upstream as `g_inab`. -/
@[expose]
noncomputable def gInab (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (.classEq (synCin (.cab x ph) (.cab x ps)) (.cab x (synWa ph ps))) :=
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
  have p0000 := @gSban ph ps x y
  have p0001 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      y x (synWa ph ps))
  have p0002 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      y x ph)
  have p0003 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      y x ps)
  have p0004 :=
    @gAnbi12i (.classMem (.cv y) (.cab x ph)) (synWsb y x ph)
      (.classMem (.cv y) (.cab x ps)) (synWsb y x ps) p0002 p0003
  have p0005 :=
    @gN3bitr4ri (synWsb y x (synWa ph ps)) (synWa (synWsb y x ph) (synWsb y x ps))
      (.classMem (.cv y) (.cab x (synWa ph ps)))
      (synWa (.classMem (.cv y) (.cab x ph)) (.classMem (.cv y) (.cab x ps))) p0000 p0001
      p0004
  have p0006 :=
    @gIneqri y (.cab x ph) (.cab x ps) (.cab x (synWa ph ps))
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

/-- Checked nominal proof certificate identified upstream as `g_difab`. -/
@[expose]
noncomputable def gDifab (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf
      (.classEq (synCdif (.cab x ph) (.cab x ps)) (.cab x (synWa ph (.neg ps)))) :=
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
      y x (synWa ph (.neg ps)))
  have p0001 := @gSban ph (.neg ps) x y
  have p0002 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      y x ph)
  have p0003 := @gBicomi (.classMem (.cv y) (.cab x ph)) (synWsb y x ph) p0002
  have p0004 := @gSbn ps x y
  have p0005 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      y x ps)
  have p0006 :=
    @gXchbinxr (synWsb y x (.neg ps)) (synWsb y x ps) (.classMem (.cv y) (.cab x ps))
      p0004 p0005
  have p0007 :=
    @gAnbi12i (synWsb y x ph) (.classMem (.cv y) (.cab x ph)) (synWsb y x (.neg ps))
      (.neg (.classMem (.cv y) (.cab x ps))) p0003 p0006
  have p0008 :=
    @gN3bitrri (.classMem (.cv y) (.cab x (synWa ph (.neg ps))))
      (synWsb y x (synWa ph (.neg ps)))
      (synWa (synWsb y x ph) (synWsb y x (.neg ps)))
      (synWa (.classMem (.cv y) (.cab x ph)) (.neg (.classMem (.cv y) (.cab x ps))))
      p0000 p0001 p0007
  have p0009 :=
    @gDifeqri y (.cab x ph) (.cab x ps) (.cab x (synWa ph (.neg ps)))
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

/-- Checked nominal proof certificate identified upstream as `g_complab`. -/
@[expose]
noncomputable def gComplab (ph : Wff) (x : Var) :
    Nominal.NPrf (.classEq (synCcompl (.cab x ph)) (.cab x (.neg ph))) :=
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
  have p0001 := @gNotbii (.classMem (.cv y) (.cab x ph)) (synWsb y x ph) p0000
  have p0002 := @gSbn ph x y
  have p0003 :=
    @gBitr4i (.neg (.classMem (.cv y) (.cab x ph))) (.neg (synWsb y x ph))
      (synWsb y x (.neg ph)) p0001 p0002
  have p0004 := @gVex y
  have p0005 := @gElcompl (.cv y) (.cab x ph) p0004
  have p0006 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      y x (.neg ph))
  have p0007 :=
    @gN3bitr4i (.neg (.classMem (.cv y) (.cab x ph))) (synWsb y x (.neg ph))
      (.classMem (.cv y) (synCcompl (.cab x ph))) (.classMem (.cv y) (.cab x (.neg ph)))
      p0003 p0005 p0006
  have p0008 :=
    @gEqriv y (synCcompl (.cab x ph)) (.cab x (.neg ph))
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

/-- Checked nominal proof certificate identified upstream as `g_notab`. -/
@[expose]
noncomputable def gNotab (ph : Wff) (x : Var) :
    Nominal.NPrf (.classEq (.cab x (.neg ph)) (synCdif (synCvv) (.cab x ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var)
  have p0000 := (Nominal.classEqRefl (synCrab x (synCvv) (.neg ph)))
  have p0001 := @gRabab (.neg ph) x
  have p0002 :=
    @gEqtr3i (synCrab x (synCvv) (.neg ph))
      (.cab x (synWa (.classMem (.cv x) (synCvv)) (.neg ph))) (.cab x (.neg ph)) p0000
      p0001
  have p0003 := @gDifab (.classMem (.cv x) (synCvv)) ph x
  have p0004 :=
    @gAbid2 x (synCvv)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv] at ⊢;
            aesop))
  have p0005 :=
    @gDifeq1i (.cab x (.classMem (.cv x) (synCvv))) (synCvv) (.cab x ph) p0004
  have p0006 :=
    @gEqtr3i (synCdif (.cab x (.classMem (.cv x) (synCvv))) (.cab x ph))
      (.cab x (synWa (.classMem (.cv x) (synCvv)) (.neg ph)))
      (synCdif (synCvv) (.cab x ph)) p0003 p0005
  have p0007 :=
    @gEqtr3i (.cab x (synWa (.classMem (.cv x) (synCvv)) (.neg ph))) (.cab x (.neg ph))
      (synCdif (synCvv) (.cab x ph)) p0002 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_unrab`. -/
@[expose]
noncomputable def gUnrab (ph : Wff) (ps : Wff) (x : Var) (A : Class) :
    Nominal.NPrf
      (.classEq (synCun (synCrab x A ph) (synCrab x A ps)) (synCrab x A (synWo ph ps))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCrab x A ph))
  have p0001 := (Nominal.classEqRefl (synCrab x A ps))
  have p0002 :=
    @gUneq12i (synCrab x A ph) (.cab x (synWa (.classMem (.cv x) A) ph))
      (synCrab x A ps) (.cab x (synWa (.classMem (.cv x) A) ps)) p0000 p0001
  have p0003 := (Nominal.classEqRefl (synCrab x A (synWo ph ps)))
  have p0004 :=
    @gUnab (synWa (.classMem (.cv x) A) ph) (synWa (.classMem (.cv x) A) ps) x
  have p0005 := @gAndi (.classMem (.cv x) A) ph ps
  have p0006 :=
    @gAbbii (synWa (.classMem (.cv x) A) (synWo ph ps))
      (synWo (synWa (.classMem (.cv x) A) ph) (synWa (.classMem (.cv x) A) ps)) x p0005
  have p0007 :=
    @gEqtr4i
      (synCun (.cab x (synWa (.classMem (.cv x) A) ph))
        (.cab x (synWa (.classMem (.cv x) A) ps)))
      (.cab x (synWo (synWa (.classMem (.cv x) A) ph) (synWa (.classMem (.cv x) A) ps)))
      (.cab x (synWa (.classMem (.cv x) A) (synWo ph ps))) p0004 p0006
  have p0008 :=
    @gEqtr4i (synCrab x A (synWo ph ps))
      (.cab x (synWa (.classMem (.cv x) A) (synWo ph ps)))
      (synCun (.cab x (synWa (.classMem (.cv x) A) ph))
        (.cab x (synWa (.classMem (.cv x) A) ps)))
      p0003 p0007
  have p0009 :=
    @gEqtr4i (synCun (synCrab x A ph) (synCrab x A ps))
      (synCun (.cab x (synWa (.classMem (.cv x) A) ph))
        (.cab x (synWa (.classMem (.cv x) A) ps)))
      (synCrab x A (synWo ph ps)) p0002 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_dfrab2`. -/
@[expose]
noncomputable def gDfrab2 (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.classEq (synCrab x A ph) (synCin (.cab x ph) A)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := (Nominal.classEqRefl (synCrab x A ph))
  have p0001 := @gInab (.classMem (.cv x) A) ph x
  have p0002 :=
    @gAbid2 x A
      (by
        first
        | (aesop))
  have p0003 := @gIneq1i (.cab x (.classMem (.cv x) A)) A (.cab x ph) p0002
  have p0004 :=
    @gEqtr3i (synCin (.cab x (.classMem (.cv x) A)) (.cab x ph))
      (.cab x (synWa (.classMem (.cv x) A) ph)) (synCin A (.cab x ph)) p0001 p0003
  have p0005 := @gIncom A (.cab x ph)
  have p0006 :=
    @gN3eqtri (synCrab x A ph) (.cab x (synWa (.classMem (.cv x) A) ph))
      (synCin A (.cab x ph)) (synCin (.cab x ph) A) p0000 p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_dfrab3`. -/
@[expose]
noncomputable def gDfrab3 (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.classEq (synCrab x A ph) (synCin A (.cab x ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := (Nominal.classEqRefl (synCrab x A ph))
  have p0001 := @gInab (.classMem (.cv x) A) ph x
  have p0002 :=
    @gAbid2 x A
      (by
        first
        | (aesop))
  have p0003 := @gIneq1i (.cab x (.classMem (.cv x) A)) A (.cab x ph) p0002
  have p0004 :=
    @gN3eqtr2i (synCrab x A ph) (.cab x (synWa (.classMem (.cv x) A) ph))
      (synCin (.cab x (.classMem (.cv x) A)) (.cab x ph)) (synCin A (.cab x ph)) p0000
      p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_notrab`. -/
@[expose]
noncomputable def gNotrab (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.classEq (synCdif A (synCrab x A ph)) (synCrab x A (.neg ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := @gDifab (.classMem (.cv x) A) ph x
  have p0001 := @gDifin A (.cab x ph)
  have p0002 :=
    @gDfrab3 ph x A
      (by
        first
        | (aesop))
  have p0003 := @gDifeq2i (synCrab x A ph) (synCin A (.cab x ph)) A p0002
  have p0004 :=
    @gAbid2 x A
      (by
        first
        | (aesop))
  have p0005 := @gDifeq1i (.cab x (.classMem (.cv x) A)) A (.cab x ph) p0004
  have p0006 :=
    @gN3eqtr4i (synCdif A (synCin A (.cab x ph))) (synCdif A (.cab x ph))
      (synCdif A (synCrab x A ph)) (synCdif (.cab x (.classMem (.cv x) A)) (.cab x ph))
      p0001 p0003 p0005
  have p0007 := (Nominal.classEqRefl (synCrab x A (.neg ph)))
  have p0008 :=
    @gN3eqtr4i (synCdif (.cab x (.classMem (.cv x) A)) (.cab x ph))
      (.cab x (synWa (.classMem (.cv x) A) (.neg ph))) (synCdif A (synCrab x A ph))
      (synCrab x A (.neg ph)) p0000 p0006 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_compleqb`. -/
@[expose]
noncomputable def gCompleqb (A : Class) (B : Class) :
    Nominal.NPrf (synWb (.classEq A B) (.classEq (synCcompl A) (synCcompl B))) :=
  by
  have p0000 := @gCompleq A B
  have p0001 := @gCompleq (synCcompl A) (synCcompl B)
  have p0002 := @gDblcompl A
  have p0003 := @gDblcompl B
  have p0004 :=
    @gN3eqtr3g (.classEq (synCcompl A) (synCcompl B)) (synCcompl (synCcompl A))
      (synCcompl (synCcompl B)) A B p0001 p0002 p0003
  have p0005 :=
    @gImpbii (.classEq A B) (.classEq (synCcompl A) (synCcompl B)) p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_necompl`. -/
@[expose]
noncomputable def gNecompl (A : Class) : Nominal.NPrf (synWne (synCcompl A) A) :=
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
  have p0000 := @gPm519 (.classMem (.cv x) A)
  have p0001 := @gVex x
  have p0002 := @gElcompl (.cv x) A p0001
  have p0003 :=
    @gBibi2i (.classMem (.cv x) (synCcompl A)) (.neg (.classMem (.cv x) A))
      (.classMem (.cv x) A) p0002
  have p0004 :=
    @gMtbir (synWb (.classMem (.cv x) A) (.classMem (.cv x) (synCcompl A)))
      (synWb (.classMem (.cv x) A) (.neg (.classMem (.cv x) A))) p0000 p0003
  have p0005 :=
    @gN198a (.neg (synWb (.classMem (.cv x) A) (.classMem (.cv x) (synCcompl A)))) x
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @gDfcleq x A (synCcompl A)
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
    @gNecon3abii
      (.all x (synWb (.classMem (.cv x) A) (.classMem (.cv x) (synCcompl A)))) A
      (synCcompl A) p0007
  have p0009 :=
    @gExnal (synWb (.classMem (.cv x) A) (.classMem (.cv x) (synCcompl A))) x
  have p0010 :=
    @gBitr4i (synWne A (synCcompl A))
      (.neg (.all x (synWb (.classMem (.cv x) A) (.classMem (.cv x) (synCcompl A)))))
      (synWex x (.neg (synWb (.classMem (.cv x) A) (.classMem (.cv x) (synCcompl A)))))
      p0008 p0009
  have p0011 :=
    @gMpbir (synWne A (synCcompl A))
      (synWex x (.neg (synWb (.classMem (.cv x) A) (.classMem (.cv x) (synCcompl A)))))
      p0006 p0010
  have p0012 := @gNecomi A (synCcompl A) p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_dfin5`. -/
@[expose]
noncomputable def gDfin5 (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (synCin A B) (synCcompl (synCun (synCcompl A) (synCcompl B)))) :=
  by
  have p0000 := @gDblcompl A
  have p0001 := @gDblcompl B
  have p0002 :=
    @gNineq12i (synCcompl (synCcompl A)) A (synCcompl (synCcompl B)) B p0000 p0001
  have p0003 :=
    @gCompleqi (synCnin (synCcompl (synCcompl A)) (synCcompl (synCcompl B)))
      (synCnin A B) p0002
  have p0004 := (Nominal.classEqRefl (synCun (synCcompl A) (synCcompl B)))
  have p0005 :=
    @gCompleqi (synCun (synCcompl A) (synCcompl B))
      (synCnin (synCcompl (synCcompl A)) (synCcompl (synCcompl B))) p0004
  have p0006 := (Nominal.classEqRefl (synCin A B))
  have p0007 :=
    @gN3eqtr4ri
      (synCcompl (synCnin (synCcompl (synCcompl A)) (synCcompl (synCcompl B))))
      (synCcompl (synCnin A B)) (synCcompl (synCun (synCcompl A) (synCcompl B)))
      (synCin A B) p0003 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_dfun4`. -/
@[expose]
noncomputable def gDfun4 (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (synCun A B) (synCcompl (synCin (synCcompl A) (synCcompl B)))) :=
  by
  have p0000 := @gDfin5 (synCcompl A) (synCcompl B)
  have p0001 :=
    @gCompleqi (synCin (synCcompl A) (synCcompl B))
      (synCcompl (synCun (synCcompl (synCcompl A)) (synCcompl (synCcompl B)))) p0000
  have p0002 :=
    @gDblcompl (synCun (synCcompl (synCcompl A)) (synCcompl (synCcompl B)))
  have p0003 := @gDblcompl A
  have p0004 := @gDblcompl B
  have p0005 :=
    @gUneq12i (synCcompl (synCcompl A)) A (synCcompl (synCcompl B)) B p0003 p0004
  have p0006 :=
    @gN3eqtrri (synCcompl (synCin (synCcompl A) (synCcompl B)))
      (synCcompl
        (synCcompl (synCun (synCcompl (synCcompl A)) (synCcompl (synCcompl B)))))
      (synCun (synCcompl (synCcompl A)) (synCcompl (synCcompl B))) (synCun A B)
      p0001 p0002 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_iunin`. -/
@[expose]
noncomputable def gIunin (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (synCcompl (synCun A B)) (synCin (synCcompl A) (synCcompl B))) :=
  by
  have p0000 := @gDfin5 (synCcompl A) (synCcompl B)
  have p0001 := @gDblcompl A
  have p0002 := @gDblcompl B
  have p0003 :=
    @gUneq12i (synCcompl (synCcompl A)) A (synCcompl (synCcompl B)) B p0001 p0002
  have p0004 :=
    @gCompleqi (synCun (synCcompl (synCcompl A)) (synCcompl (synCcompl B)))
      (synCun A B) p0003
  have p0005 :=
    @gEqtr2i (synCin (synCcompl A) (synCcompl B))
      (synCcompl (synCun (synCcompl (synCcompl A)) (synCcompl (synCcompl B))))
      (synCcompl (synCun A B)) p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_iinun`. -/
@[expose]
noncomputable def gIinun (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (synCcompl (synCin A B)) (synCun (synCcompl A) (synCcompl B))) :=
  by
  have p0000 := @gDfun4 (synCcompl A) (synCcompl B)
  have p0001 := @gDblcompl A
  have p0002 := @gDblcompl B
  have p0003 :=
    @gIneq12i (synCcompl (synCcompl A)) A (synCcompl (synCcompl B)) B p0001 p0002
  have p0004 :=
    @gCompleqi (synCin (synCcompl (synCcompl A)) (synCcompl (synCcompl B)))
      (synCin A B) p0003
  have p0005 :=
    @gEqtr2i (synCun (synCcompl A) (synCcompl B))
      (synCcompl (synCin (synCcompl (synCcompl A)) (synCcompl (synCcompl B))))
      (synCcompl (synCin A B)) p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_difsscompl`. -/
@[expose]
noncomputable def gDifsscompl (A : Class) (B : Class) :
    Nominal.NPrf (synWss (synCdif A B) (synCcompl B)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCdif A B))
  have p0001 := @gInss2 A (synCcompl B)
  have p0002 :=
    @gEqsstri (synCdif A B) (synCin A (synCcompl B)) (synCcompl B) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_dfnul2`. -/
@[expose]
noncomputable def gDfnul2 (x : Var) :
    Nominal.NPrf (.classEq (synC0) (.cab x (.neg (.classEq (.cv x) (.cv x))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var)
  have p0000 := (Nominal.classEqRefl (synC0))
  have p0001 := @gEleq2i (synC0) (synCdif (synCvv) (synCvv)) (.cv x) p0000
  have p0002 := @gEldif (.cv x) (synCvv) (synCvv)
  have p0003 := @gEqid (.cv x)
  have p0004 := @gPm324 (.classMem (.cv x) (synCvv))
  have p0005 :=
    @gN2th (.classEq (.cv x) (.cv x))
      (.neg (synWa (.classMem (.cv x) (synCvv)) (.neg (.classMem (.cv x) (synCvv)))))
      p0003 p0004
  have p0006 :=
    @gCon2bii (.classEq (.cv x) (.cv x))
      (synWa (.classMem (.cv x) (synCvv)) (.neg (.classMem (.cv x) (synCvv)))) p0005
  have p0007 :=
    @gN3bitri (.classMem (.cv x) (synC0))
      (.classMem (.cv x) (synCdif (synCvv) (synCvv)))
      (synWa (.classMem (.cv x) (synCvv)) (.neg (.classMem (.cv x) (synCvv))))
      (.neg (.classEq (.cv x) (.cv x))) p0001 p0002 p0006
  have p0008 :=
    @gEqabi (.neg (.classEq (.cv x) (.cv x))) x (synC0)
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

/-- Checked nominal proof certificate identified upstream as `g_noel`. -/
@[expose]
noncomputable def gNoel (A : Class) : Nominal.NPrf (.neg (.classMem A (synC0))) :=
  by
  have p0000 := @gEldifi A (synCvv) (synCvv)
  have p0001 := @gEldifn A (synCvv) (synCvv)
  have p0002 :=
    @gPm265i (.classMem A (synCdif (synCvv) (synCvv))) (.classMem A (synCvv)) p0000
      p0001
  have p0003 := (Nominal.classEqRefl (synC0))
  have p0004 := @gEleq2i (synC0) (synCdif (synCvv) (synCvv)) A p0003
  have p0005 :=
    @gMtbir (.classMem A (synC0)) (.classMem A (synCdif (synCvv) (synCvv))) p0002
      p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_n0i`. -/
@[expose]
noncomputable def gN0i (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem B A) (.neg (.classEq A (synC0)))) :=
  by
  have p0000 := @gNoel B
  have p0001 := @gEleq2 A (synC0) B
  have p0002 :=
    @gMtbiri (.classEq A (synC0)) (.classMem B A) (.classMem B (synC0)) p0000 p0001
  have p0003 := @gCon2i (.classEq A (synC0)) (.classMem B A) p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_ne0i`. -/
@[expose]
noncomputable def gNe0i (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem B A) (synWne A (synC0))) :=
  by
  have p0000 := @gN0i A B
  have p0001 := (Nominal.biimpRefl (synWne A (synC0)))
  have p0002 :=
    @gSylibr (.classMem B A) (.neg (.classEq A (synC0))) (synWne A (synC0)) p0000
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_vn0`. -/
@[expose]
noncomputable def gVn0 : Nominal.NPrf (synWne (synCvv) (synC0)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have p0000 := @gVex x
  have p0001 := @gNe0i (synCvv) (.cv x)
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_n0f`. -/
@[expose]
noncomputable def gN0f (x : Var) (A : Class) (hyp_n0f_1 : Nominal.NPrf (synWnfc x A)) :
    Nominal.NPrf (synWb (synWne A (synC0)) (synWex x (.classMem (.cv x) A))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @gNfcv x (synC0)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0] at ⊢;
            aesop))
  have p0001 := @gCleqf x A (synC0) hyp_n0f_1 p0000
  have p0002 := @gNoel (.cv x)
  have p0003 := @gNbn (.classMem (.cv x) (synC0)) (.classMem (.cv x) A) p0002
  have p0004 :=
    @gAlbii (.neg (.classMem (.cv x) A))
      (synWb (.classMem (.cv x) A) (.classMem (.cv x) (synC0))) x p0003
  have p0005 :=
    @gBitr4i (.classEq A (synC0))
      (.all x (synWb (.classMem (.cv x) A) (.classMem (.cv x) (synC0))))
      (.all x (.neg (.classMem (.cv x) A))) p0001 p0004
  have p0006 := @gNecon3abii (.all x (.neg (.classMem (.cv x) A))) A (synC0) p0005
  have p0007 := (Nominal.biimpRefl (synWex x (.classMem (.cv x) A)))
  have p0008 :=
    @gBitr4i (synWne A (synC0)) (.neg (.all x (.neg (.classMem (.cv x) A))))
      (synWex x (.classMem (.cv x) A)) p0006 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_n0`. -/
@[expose]
noncomputable def gN0 (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (synWb (synWne A (synC0)) (synWex x (.classMem (.cv x) A))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @gNfcv x A
      (by
        first
        | (aesop))
  have p0001 := @gN0f x A p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_neq0`. -/
@[expose]
noncomputable def gNeq0 (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (synWb (.neg (.classEq A (synC0))) (synWex x (.classMem (.cv x) A))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  have p0000 := (Nominal.biimpRefl (synWne A (synC0)))
  have p0001 :=
    @gN0 x A
      (by
        first
        | (aesop))
  have p0002 :=
    @gBitr3i (.neg (.classEq A (synC0))) (synWne A (synC0))
      (synWex x (.classMem (.cv x) A)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_rex0`. -/
@[expose]
noncomputable def gRex0 (ph : Wff) (x : Var) :
    Nominal.NPrf (.neg (synWrex x (synC0) ph)) :=
  by
  have p0000 := @gNoel (.cv x)
  have p0001 := @gPm221i (.classMem (.cv x) (synC0)) (.neg ph) p0000
  have p0002 := @gNrex ph x (synC0) p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_eq0`. -/
@[expose]
noncomputable def gEq0 (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (synWb (.classEq A (synC0)) (.all x (.neg (.classMem (.cv x) A)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @gNeq0 x A
      (by
        first
        | (aesop))
  have p0001 := (Nominal.biimpRefl (synWex x (.classMem (.cv x) A)))
  have p0002 :=
    @gBitri (.neg (.classEq A (synC0))) (synWex x (.classMem (.cv x) A))
      (.neg (.all x (.neg (.classMem (.cv x) A)))) p0000 p0001
  have p0003 :=
    @gCon4bii (.classEq A (synC0)) (.all x (.neg (.classMem (.cv x) A))) p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_eqv`. -/
@[expose]
noncomputable def gEqv (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (synWb (.classEq A (synCvv)) (.all x (.classMem (.cv x) A))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @gDfcleq x A (synCvv)
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
  have p0001 := @gVex x
  have p0002 := @gTbt (.classMem (.cv x) (synCvv)) (.classMem (.cv x) A) p0001
  have p0003 :=
    @gAlbii (.classMem (.cv x) A)
      (synWb (.classMem (.cv x) A) (.classMem (.cv x) (synCvv))) x p0002
  have p0004 :=
    @gBitr4i (.classEq A (synCvv))
      (.all x (synWb (.classMem (.cv x) A) (.classMem (.cv x) (synCvv))))
      (.all x (.classMem (.cv x) A)) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_abvor0`. -/
@[expose]
noncomputable def gAbvor0 (ph : Wff) (x : Var) (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf
      (synWo (.classEq (.cab x ph) (synCvv)) (.classEq (.cab x ph) (synC0))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var)
  have p0000 := @gId ph
  have p0001 := @gVex x
  have p0002 := @gA1i (.classMem (.cv x) (synCvv)) ph p0001
  have p0003 := @gN2thd ph ph (.classMem (.cv x) (synCvv)) p0000 p0002
  have p0004 :=
    @gEqabcdv ph ph x (synCvv)
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
  have p0005 := @gCon3i ph (.classEq (.cab x ph) (synCvv)) p0004
  have p0006 := @gId (.neg ph)
  have p0007 := @gNoel (.cv x)
  have p0008 := @gA1i (.neg (.classMem (.cv x) (synC0))) (.neg ph) p0007
  have p0009 := @gN2falsed (.neg ph) ph (.classMem (.cv x) (synC0)) p0006 p0008
  have p0010 :=
    @gEqabcdv (.neg ph) ph x (synC0)
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
    @gSyl (.neg (.classEq (.cab x ph) (synCvv))) (.neg ph)
      (.classEq (.cab x ph) (synC0)) p0005 p0010
  have p0012 :=
    @gOrri (.classEq (.cab x ph) (synCvv)) (.classEq (.cab x ph) (synC0)) p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_abn0`. -/
@[expose]
noncomputable def gAbn0 (ph : Wff) (x : Var) :
    Nominal.NPrf (synWb (synWne (.cab x ph) (synC0)) (synWex x ph)) :=
  by
  have p0000 := @gNfab1 ph x
  have p0001 := @gN0f x (.cab x ph) p0000
  have p0002 := @gAbid ph x
  have p0003 := @gExbii (.classMem (.cv x) (.cab x ph)) ph x p0002
  have p0004 :=
    @gBitri (synWne (.cab x ph) (synC0)) (synWex x (.classMem (.cv x) (.cab x ph)))
      (synWex x ph) p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_ab0`. -/
@[expose]
noncomputable def gAb0 (ph : Wff) (x : Var) :
    Nominal.NPrf (synWb (.classEq (.cab x ph) (synC0)) (.all x (.neg ph))) :=
  by
  have p0000 := @gAbn0 ph x
  have p0001 := (Nominal.biimpRefl (synWne (.cab x ph) (synC0)))
  have p0002 := (Nominal.biimpRefl (synWex x ph))
  have p0003 :=
    @gN3bitr3i (synWne (.cab x ph) (synC0)) (synWex x ph)
      (.neg (.classEq (.cab x ph) (synC0))) (.neg (.all x (.neg ph))) p0000 p0001 p0002
  have p0004 := @gCon4bii (.classEq (.cab x ph) (synC0)) (.all x (.neg ph)) p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_un0`. -/
@[expose]
noncomputable def gUn0 (A : Class) : Nominal.NPrf (.classEq (synCun A (synC0)) A) :=
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
  have p0000 := @gNoel (.cv x)
  have p0001 := @gBiorfi (.classMem (.cv x) (synC0)) (.classMem (.cv x) A) p0000
  have p0002 :=
    @gBicomi (.classMem (.cv x) A)
      (synWo (.classMem (.cv x) A) (.classMem (.cv x) (synC0))) p0001
  have p0003 :=
    @gUneqri x A (synC0) A
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

/-- Checked nominal proof certificate identified upstream as `g_in0`. -/
@[expose]
noncomputable def gIn0 (A : Class) :
    Nominal.NPrf (.classEq (synCin A (synC0)) (synC0)) :=
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
  have p0000 := @gNoel (.cv x)
  have p0001 := @gBianfi (.classMem (.cv x) (synC0)) (.classMem (.cv x) A) p0000
  have p0002 :=
    @gBicomi (.classMem (.cv x) (synC0))
      (synWa (.classMem (.cv x) A) (.classMem (.cv x) (synC0))) p0001
  have p0003 :=
    @gIneqri x A (synC0) (synC0)
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

/-- Checked nominal proof certificate identified upstream as `g_inv1`. -/
@[expose]
noncomputable def gInv1 (A : Class) : Nominal.NPrf (.classEq (synCin A (synCvv)) A) :=
  by
  have p0000 := @gInss1 A (synCvv)
  have p0001 := @gSsid A
  have p0002 := @gSsv A
  have p0003 := @gSsini A A (synCvv) p0001 p0002
  have p0004 := @gEqssi (synCin A (synCvv)) A p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_n_0ss`. -/
@[expose]
noncomputable def gN0ss (A : Class) : Nominal.NPrf (synWss (synC0) A) :=
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
  have p0000 := @gNoel (.cv x)
  have p0001 := @gPm221i (.classMem (.cv x) (synC0)) (.classMem (.cv x) A) p0000
  have p0002 :=
    @gSsriv x (synC0) A
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

/-- Checked nominal proof certificate identified upstream as `g_ss0b`. -/
@[expose]
noncomputable def gSs0b (A : Class) :
    Nominal.NPrf (synWb (synWss A (synC0)) (.classEq A (synC0))) :=
  by
  have p0000 := @gN0ss A
  have p0001 := @gEqss A (synC0)
  have p0002 :=
    @gMpbiran2 (.classEq A (synC0)) (synWss A (synC0)) (synWss (synC0) A) p0000
      p0001
  have p0003 := @gBicomi (.classEq A (synC0)) (synWss A (synC0)) p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_ss0`. -/
@[expose]
noncomputable def gSs0 (A : Class) :
    Nominal.NPrf (.imp (synWss A (synC0)) (.classEq A (synC0))) :=
  by
  have p0000 := @gSs0b A
  have p0001 := @gBiimpi (synWss A (synC0)) (.classEq A (synC0)) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_abf`. -/
@[expose]
noncomputable def gAbf (ph : Wff) (x : Var) (hyp_abf_1 : Nominal.NPrf (.neg ph)) :
    Nominal.NPrf (.classEq (.cab x ph) (synC0)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var)
  have p0000 := @gPm221i ph (.classMem (.cv x) (synC0)) hyp_abf_1
  have p0001 :=
    @gAbssi ph x (synC0)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0] at ⊢;
            aesop))
      p0000
  have p0002 := @gSs0 (.cab x ph)
  have p0003 := Nominal.mp p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_eq0rdv`. -/
@[expose]
noncomputable def gEq0rdv (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_ph_x : x ∉ ph.fv)
    (hyp_eq0rdv_1 : Nominal.NPrf (.imp ph (.neg (.classMem (.cv x) A)))) :
    Nominal.NPrf (.imp ph (.classEq A (synC0))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @gPm221d ph (.classMem (.cv x) A) (.classMem (.cv x) (synC0)) hyp_eq0rdv_1
  have p0001 :=
    @gSsrdv ph x A (synC0)
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
  have p0002 := @gSs0 A
  have p0003 := @gSyl ph (synWss A (synC0)) (.classEq A (synC0)) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_un00`. -/
@[expose]
noncomputable def gUn00 (A : Class) (B : Class) :
    Nominal.NPrf
      (synWb (synWa (.classEq A (synC0)) (.classEq B (synC0)))
        (.classEq (synCun A B) (synC0))) :=
  by
  have p0000 := @gUneq12 A (synC0) B (synC0)
  have p0001 := @gUn0 (synC0)
  have p0002 :=
    @gSyl6eq (synWa (.classEq A (synC0)) (.classEq B (synC0))) (synCun A B)
      (synCun (synC0) (synC0)) (synC0) p0000 p0001
  have p0003 := @gSsun1 A B
  have p0004 := @gSseq2 (synCun A B) (synC0) A
  have p0005 :=
    @gMpbii (.classEq (synCun A B) (synC0)) (synWss A (synCun A B))
      (synWss A (synC0)) p0003 p0004
  have p0006 := @gSs0b A
  have p0007 :=
    @gSylib (.classEq (synCun A B) (synC0)) (synWss A (synC0)) (.classEq A (synC0))
      p0005 p0006
  have p0008 := @gSsun2 B A
  have p0009 := @gSseq2 (synCun A B) (synC0) B
  have p0010 :=
    @gMpbii (.classEq (synCun A B) (synC0)) (synWss B (synCun A B))
      (synWss B (synC0)) p0008 p0009
  have p0011 := @gSs0b B
  have p0012 :=
    @gSylib (.classEq (synCun A B) (synC0)) (synWss B (synC0)) (.classEq B (synC0))
      p0010 p0011
  have p0013 :=
    @gJca (.classEq (synCun A B) (synC0)) (.classEq A (synC0)) (.classEq B (synC0))
      p0007 p0012
  have p0014 :=
    @gImpbii (synWa (.classEq A (synC0)) (.classEq B (synC0)))
      (.classEq (synCun A B) (synC0)) p0002 p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_vss`. -/
@[expose]
noncomputable def gVss (A : Class) :
    Nominal.NPrf (synWb (synWss (synCvv) A) (.classEq A (synCvv))) :=
  by
  have p0000 := @gSsv A
  have p0001 := @gBiantrur (synWss A (synCvv)) (synWss (synCvv) A) p0000
  have p0002 := @gEqss A (synCvv)
  have p0003 :=
    @gBitr4i (synWss (synCvv) A) (synWa (synWss A (synCvv)) (synWss (synCvv) A))
      (.classEq A (synCvv)) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_disj`. -/
@[expose]
noncomputable def gDisj (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (synWb (.classEq (synCin A B) (synC0)) (synWral x A (.neg (.classMem (.cv x) B)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := @gElin (.cv x) A B
  have p0001 := (Nominal.biimpRefl (synWa (.classMem (.cv x) A) (.classMem (.cv x) B)))
  have p0002 :=
    @gBitr2i (.classMem (.cv x) (synCin A B))
      (synWa (.classMem (.cv x) A) (.classMem (.cv x) B))
      (.neg (.imp (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))) p0000 p0001
  have p0003 :=
    @gCon1bii (.imp (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))
      (.classMem (.cv x) (synCin A B)) p0002
  have p0004 :=
    @gAlbii (.neg (.classMem (.cv x) (synCin A B)))
      (.imp (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))) x p0003
  have p0005 :=
    @gEq0 x (synCin A B)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
              Finset.mem_union] at ⊢;
            aesop))
  have p0006 := (Nominal.biimpRefl (synWral x A (.neg (.classMem (.cv x) B))))
  have p0007 :=
    @gN3bitr4i (.all x (.neg (.classMem (.cv x) (synCin A B))))
      (.all x (.imp (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))))
      (.classEq (synCin A B) (synC0)) (synWral x A (.neg (.classMem (.cv x) B))) p0004
      p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_disjr`. -/
@[expose]
noncomputable def gDisjr (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (synWb (.classEq (synCin A B) (synC0)) (synWral x B (.neg (.classMem (.cv x) A)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := @gIncom A B
  have p0001 := @gEqeq1i (synCin A B) (synCin B A) (synC0) p0000
  have p0002 :=
    @gDisj x B A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0003 :=
    @gBitri (.classEq (synCin A B) (synC0)) (.classEq (synCin B A) (synC0))
      (synWral x B (.neg (.classMem (.cv x) A))) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_disj1`. -/
@[expose]
noncomputable def gDisj1 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (synWb (.classEq (synCin A B) (synC0))
        (.all x (.imp (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @gDisj x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 := (Nominal.biimpRefl (synWral x A (.neg (.classMem (.cv x) B))))
  have p0002 :=
    @gBitri (.classEq (synCin A B) (synC0)) (synWral x A (.neg (.classMem (.cv x) B)))
      (.all x (.imp (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ssdif0`. -/
@[expose]
noncomputable def gSsdif0 (A : Class) (B : Class) :
    Nominal.NPrf (synWb (synWss A B) (.classEq (synCdif A B) (synC0))) :=
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
  have p0000 := @gIman (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0001 := @gEldif (.cv x) A B
  have p0002 :=
    @gXchbinxr (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))
      (synWa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)))
      (.classMem (.cv x) (synCdif A B)) p0000 p0001
  have p0003 :=
    @gAlbii (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))
      (.neg (.classMem (.cv x) (synCdif A B))) x p0002
  have p0004 :=
    @gDfss2 x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0005 :=
    @gEq0 x (synCdif A B)
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
    @gN3bitr4i (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (.all x (.neg (.classMem (.cv x) (synCdif A B)))) (synWss A B)
      (.classEq (synCdif A B) (synC0)) p0003 p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_inssdif0`. -/
@[expose]
noncomputable def gInssdif0 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (synWb (synWss (synCin A B) C) (.classEq (synCin A (synCdif B C)) (synC0))) :=
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
  have p0000 := @gElin (.cv x) A B
  have p0001 :=
    @gImbi1i (.classMem (.cv x) (synCin A B))
      (synWa (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) C) p0000
  have p0002 :=
    @gIman (synWa (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) C)
  have p0003 :=
    @gBitri (.imp (.classMem (.cv x) (synCin A B)) (.classMem (.cv x) C))
      (.imp (synWa (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv x) C))
      (.neg (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv x) B))
          (.neg (.classMem (.cv x) C))))
      p0001 p0002
  have p0004 := @gEldif (.cv x) B C
  have p0005 :=
    @gAnbi2i (.classMem (.cv x) (synCdif B C))
      (synWa (.classMem (.cv x) B) (.neg (.classMem (.cv x) C))) (.classMem (.cv x) A)
      p0004
  have p0006 := @gElin (.cv x) A (synCdif B C)
  have p0007 :=
    @gAnass (.classMem (.cv x) A) (.classMem (.cv x) B) (.neg (.classMem (.cv x) C))
  have p0008 :=
    @gN3bitr4ri (synWa (.classMem (.cv x) A) (.classMem (.cv x) (synCdif B C)))
      (synWa (.classMem (.cv x) A) (synWa (.classMem (.cv x) B) (.neg (.classMem (.cv x) C))))
      (.classMem (.cv x) (synCin A (synCdif B C)))
      (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv x) B)) (.neg (.classMem (.cv x) C)))
      p0005 p0006 p0007
  have p0009 :=
    @gXchbinx (.imp (.classMem (.cv x) (synCin A B)) (.classMem (.cv x) C))
      (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv x) B)) (.neg (.classMem (.cv x) C)))
      (.classMem (.cv x) (synCin A (synCdif B C))) p0003 p0008
  have p0010 :=
    @gAlbii (.imp (.classMem (.cv x) (synCin A B)) (.classMem (.cv x) C))
      (.neg (.classMem (.cv x) (synCin A (synCdif B C)))) x p0009
  have p0011 :=
    @gDfss2 x (synCin A B) C
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
    @gEq0 x (synCin A (synCdif B C))
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
    @gN3bitr4i (.all x (.imp (.classMem (.cv x) (synCin A B)) (.classMem (.cv x) C)))
      (.all x (.neg (.classMem (.cv x) (synCin A (synCdif B C)))))
      (synWss (synCin A B) C) (.classEq (synCin A (synCdif B C)) (synC0)) p0010 p0011
      p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_difid`. -/
@[expose]
noncomputable def gDifid (A : Class) : Nominal.NPrf (.classEq (synCdif A A) (synC0)) :=
  by
  have p0000 := @gSsid A
  have p0001 := @gSsdif0 A A
  have p0002 := @gMpbi (synWss A A) (.classEq (synCdif A A) (synC0)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_dif0`. -/
@[expose]
noncomputable def gDif0 (A : Class) : Nominal.NPrf (.classEq (synCdif A (synC0)) A) :=
  by
  have p0000 := @gDifid A
  have p0001 := @gDifeq2i (synCdif A A) (synC0) A p0000
  have p0002 := @gDifdif A A
  have p0003 := @gEqtr3i (synCdif A (synCdif A A)) (synCdif A (synC0)) A p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_disjdif`. -/
@[expose]
noncomputable def gDisjdif (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (synCin A (synCdif B A)) (synC0)) :=
  by
  have p0000 := @gInss1 A B
  have p0001 := @gInssdif0 A B A
  have p0002 :=
    @gMpbi (synWss (synCin A B) A) (.classEq (synCin A (synCdif B A)) (synC0)) p0000
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_undifv`. -/
@[expose]
noncomputable def gUndifv (A : Class) :
    Nominal.NPrf (.classEq (synCun A (synCdif (synCvv) A)) (synCvv)) :=
  by
  have p0000 := @gDfun3 A (synCdif (synCvv) A)
  have p0001 := @gDisjdif (synCdif (synCvv) A) (synCvv)
  have p0002 :=
    @gDifeq2i
      (synCin (synCdif (synCvv) A) (synCdif (synCvv) (synCdif (synCvv) A)))
      (synC0) (synCvv) p0001
  have p0003 := @gDif0 (synCvv)
  have p0004 :=
    @gN3eqtri (synCun A (synCdif (synCvv) A))
      (synCdif (synCvv)
        (synCin (synCdif (synCvv) A) (synCdif (synCvv) (synCdif (synCvv) A))))
      (synCdif (synCvv) (synC0)) (synCvv) p0000 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_undif1`. -/
@[expose]
noncomputable def gUndif1 (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (synCun (synCdif A B) B) (synCun A B)) :=
  by
  have p0000 := @gUndir A (synCdif (synCvv) B) B
  have p0001 := @gInvdif A B
  have p0002 := @gUneq1i (synCin A (synCdif (synCvv) B)) (synCdif A B) B p0001
  have p0003 := @gUncom (synCdif (synCvv) B) B
  have p0004 := @gUndifv B
  have p0005 :=
    @gEqtri (synCun (synCdif (synCvv) B) B) (synCun B (synCdif (synCvv) B))
      (synCvv) p0003 p0004
  have p0006 := @gIneq2i (synCun (synCdif (synCvv) B) B) (synCvv) (synCun A B) p0005
  have p0007 := @gInv1 (synCun A B)
  have p0008 :=
    @gEqtri (synCin (synCun A B) (synCun (synCdif (synCvv) B) B))
      (synCin (synCun A B) (synCvv)) (synCun A B) p0006 p0007
  have p0009 :=
    @gN3eqtr3i (synCun (synCin A (synCdif (synCvv) B)) B)
      (synCin (synCun A B) (synCun (synCdif (synCvv) B) B))
      (synCun (synCdif A B) B) (synCun A B) p0000 p0002 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_undif2`. -/
@[expose]
noncomputable def gUndif2 (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (synCun A (synCdif B A)) (synCun A B)) :=
  by
  have p0000 := @gUncom A (synCdif B A)
  have p0001 := @gUndif1 B A
  have p0002 := @gUncom B A
  have p0003 :=
    @gN3eqtri (synCun A (synCdif B A)) (synCun (synCdif B A) A) (synCun B A)
      (synCun A B) p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_inundif`. -/
@[expose]
noncomputable def gInundif (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (synCun (synCin A B) (synCdif A B)) A) :=
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
  have p0000 := @gElin (.cv x) A B
  have p0001 := @gEldif (.cv x) A B
  have p0002 :=
    @gOrbi12i (.classMem (.cv x) (synCin A B))
      (synWa (.classMem (.cv x) A) (.classMem (.cv x) B))
      (.classMem (.cv x) (synCdif A B))
      (synWa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))) p0000 p0001
  have p0003 := @gPm442 (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0004 :=
    @gBitr4i
      (synWo (.classMem (.cv x) (synCin A B)) (.classMem (.cv x) (synCdif A B)))
      (synWo (synWa (.classMem (.cv x) A) (.classMem (.cv x) B))
        (synWa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))))
      (.classMem (.cv x) A) p0002 p0003
  have p0005 :=
    @gUneqri x (synCin A B) (synCdif A B) A
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

/-- Checked nominal proof certificate identified upstream as `g_difun2`. -/
@[expose]
noncomputable def gDifun2 (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (synCdif (synCun A B) B) (synCdif A B)) :=
  by
  have p0000 := @gDifundir A B B
  have p0001 := @gDifid B
  have p0002 := @gUneq2i (synCdif B B) (synC0) (synCdif A B) p0001
  have p0003 := @gUn0 (synCdif A B)
  have p0004 :=
    @gN3eqtri (synCdif (synCun A B) B) (synCun (synCdif A B) (synCdif B B))
      (synCun (synCdif A B) (synC0)) (synCdif A B) p0000 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_undif`. -/
@[expose]
noncomputable def gUndif (A : Class) (B : Class) :
    Nominal.NPrf (synWb (synWss A B) (.classEq (synCun A (synCdif B A)) B)) :=
  by
  have p0000 := @gSsequn1 A B
  have p0001 := @gUndif2 A B
  have p0002 := @gEqeq1i (synCun A (synCdif B A)) (synCun A B) B p0001
  have p0003 :=
    @gBitr4i (synWss A B) (.classEq (synCun A B) B)
      (.classEq (synCun A (synCdif B A)) B) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_ssundif`. -/
@[expose]
noncomputable def gSsundif (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (synWb (synWss A (synCun B C)) (synWss (synCdif A B) C)) :=
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
  have p0000 := @gPm56 (.classMem (.cv x) A) (.classMem (.cv x) B) (.classMem (.cv x) C)
  have p0001 := @gEldif (.cv x) A B
  have p0002 :=
    @gImbi1i (.classMem (.cv x) (synCdif A B))
      (synWa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))) (.classMem (.cv x) C)
      p0001
  have p0003 := @gElun (.cv x) B C
  have p0004 :=
    @gImbi2i (.classMem (.cv x) (synCun B C))
      (synWo (.classMem (.cv x) B) (.classMem (.cv x) C)) (.classMem (.cv x) A) p0003
  have p0005 :=
    @gN3bitr4ri
      (.imp (synWa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))) (.classMem (.cv x) C))
      (.imp (.classMem (.cv x) A) (synWo (.classMem (.cv x) B) (.classMem (.cv x) C)))
      (.imp (.classMem (.cv x) (synCdif A B)) (.classMem (.cv x) C))
      (.imp (.classMem (.cv x) A) (.classMem (.cv x) (synCun B C))) p0000 p0002 p0004
  have p0006 :=
    @gAlbii (.imp (.classMem (.cv x) A) (.classMem (.cv x) (synCun B C)))
      (.imp (.classMem (.cv x) (synCdif A B)) (.classMem (.cv x) C)) x p0005
  have p0007 :=
    @gDfss2 x A (synCun B C)
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
    @gDfss2 x (synCdif A B) C
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
    @gN3bitr4i (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) (synCun B C))))
      (.all x (.imp (.classMem (.cv x) (synCdif A B)) (.classMem (.cv x) C)))
      (synWss A (synCun B C)) (synWss (synCdif A B) C) p0006 p0007 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_r19_2z`. -/
@[expose]
noncomputable def gR192z (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (.imp (synWa (synWne A (synC0)) (synWral x A ph)) (synWrex x A ph)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 := (Nominal.biimpRefl (synWral x A ph))
  have p0001 := @gExintr (.classMem (.cv x) A) ph x
  have p0002 :=
    @gSylbi (synWral x A ph) (.all x (.imp (.classMem (.cv x) A) ph))
      (.imp (synWex x (.classMem (.cv x) A)) (synWex x (synWa (.classMem (.cv x) A) ph)))
      p0000 p0001
  have p0003 :=
    @gN0 x A
      (by
        first
        | (aesop))
  have p0004 := (Nominal.biimpRefl (synWrex x A ph))
  have p0005 :=
    @gN3imtr4g (synWral x A ph) (synWex x (.classMem (.cv x) A))
      (synWex x (synWa (.classMem (.cv x) A) ph)) (synWne A (synC0)) (synWrex x A ph)
      p0002 p0003 p0004
  have p0006 := @gImpcom (synWral x A ph) (synWne A (synC0)) (synWrex x A ph) p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_sscon34`. -/
@[expose]
noncomputable def gSscon34 (A : Class) (B : Class) :
    Nominal.NPrf (synWb (synWss A B) (synWss (synCcompl B) (synCcompl A))) :=
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
  have p0000 := @gCon34b (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0001 := @gVex x
  have p0002 := @gElcompl (.cv x) B p0001
  have p0003 := @gElcompl (.cv x) A p0001
  have p0004 :=
    @gImbi12i (.classMem (.cv x) (synCcompl B)) (.neg (.classMem (.cv x) B))
      (.classMem (.cv x) (synCcompl A)) (.neg (.classMem (.cv x) A)) p0002 p0003
  have p0005 :=
    @gBitr4i (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))
      (.imp (.neg (.classMem (.cv x) B)) (.neg (.classMem (.cv x) A)))
      (.imp (.classMem (.cv x) (synCcompl B)) (.classMem (.cv x) (synCcompl A))) p0000
      p0004
  have p0006 :=
    @gAlbii (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))
      (.imp (.classMem (.cv x) (synCcompl B)) (.classMem (.cv x) (synCcompl A))) x p0005
  have p0007 :=
    @gDfss2 x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0008 :=
    @gDfss2 x (synCcompl B) (synCcompl A)
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
    @gN3bitr4i (.all x (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (.all x (.imp (.classMem (.cv x) (synCcompl B)) (.classMem (.cv x) (synCcompl A))))
      (synWss A B) (synWss (synCcompl B) (synCcompl A)) p0006 p0007 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_dfif2`. -/
@[expose]
noncomputable def gDfif2 (ph : Wff) (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf
      (.classEq (synCif ph A B) (.cab x
          (.imp (.imp (.classMem (.cv x) B) ph) (synWa (.classMem (.cv x) A) ph)))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIf ph x A B
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
      (synWo (synWa (.classMem (.cv x) B) (.neg ph)) (synWa (.classMem (.cv x) A) ph)))
  have p0002 :=
    @gOrcom (synWa (.classMem (.cv x) A) ph) (synWa (.classMem (.cv x) B) (.neg ph))
  have p0003 := @gIman (.classMem (.cv x) B) ph
  have p0004 :=
    @gImbi1i (.imp (.classMem (.cv x) B) ph)
      (.neg (synWa (.classMem (.cv x) B) (.neg ph))) (synWa (.classMem (.cv x) A) ph)
      p0003
  have p0005 :=
    @gN3bitr4i
      (synWo (synWa (.classMem (.cv x) B) (.neg ph)) (synWa (.classMem (.cv x) A) ph))
      (.imp (.neg (synWa (.classMem (.cv x) B) (.neg ph))) (synWa (.classMem (.cv x) A) ph))
      (synWo (synWa (.classMem (.cv x) A) ph) (synWa (.classMem (.cv x) B) (.neg ph)))
      (.imp (.imp (.classMem (.cv x) B) ph) (synWa (.classMem (.cv x) A) ph)) p0001 p0002
      p0004
  have p0006 :=
    @gAbbii
      (synWo (synWa (.classMem (.cv x) A) ph) (synWa (.classMem (.cv x) B) (.neg ph)))
      (.imp (.imp (.classMem (.cv x) B) ph) (synWa (.classMem (.cv x) A) ph)) x p0005
  have p0007 :=
    @gEqtri (synCif ph A B)
      (.cab x (synWo (synWa (.classMem (.cv x) A) ph)
          (synWa (.classMem (.cv x) B) (.neg ph))))
      (.cab x (.imp (.imp (.classMem (.cv x) B) ph) (synWa (.classMem (.cv x) A) ph)))
      p0000 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_dfif6`. -/
@[expose]
noncomputable def gDfif6 (ph : Wff) (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf
      (.classEq (synCif ph A B) (synCun (synCrab x A ph) (synCrab x B (.neg ph)))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @gUnab (synWa (.classMem (.cv x) A) ph) (synWa (.classMem (.cv x) B) (.neg ph)) x
  have p0001 := (Nominal.classEqRefl (synCrab x A ph))
  have p0002 := (Nominal.classEqRefl (synCrab x B (.neg ph)))
  have p0003 :=
    @gUneq12i (synCrab x A ph) (.cab x (synWa (.classMem (.cv x) A) ph))
      (synCrab x B (.neg ph)) (.cab x (synWa (.classMem (.cv x) B) (.neg ph))) p0001
      p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIf ph x A B
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
    @gN3eqtr4ri
      (synCun (.cab x (synWa (.classMem (.cv x) A) ph))
        (.cab x (synWa (.classMem (.cv x) B) (.neg ph))))
      (.cab x (synWo (synWa (.classMem (.cv x) A) ph)
          (synWa (.classMem (.cv x) B) (.neg ph))))
      (synCun (synCrab x A ph) (synCrab x B (.neg ph))) (synCif ph A B) p0000 p0003
      p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_ifeq1`. -/
@[expose]
noncomputable def gIfeq1 (ph : Wff) (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCif ph A C) (synCif ph B C))) :=
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
    @gRabeq ph x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @gUneq1d (.classEq A B) (synCrab x A ph) (synCrab x B ph) (synCrab x C (.neg ph))
      p0000
  have p0002 :=
    @gDfif6 ph x A C
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
    @gDfif6 ph x B C
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
    @gN3eqtr4g (.classEq A B) (synCun (synCrab x A ph) (synCrab x C (.neg ph)))
      (synCun (synCrab x B ph) (synCrab x C (.neg ph))) (synCif ph A C)
      (synCif ph B C) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_ifeq2`. -/
@[expose]
noncomputable def gIfeq2 (ph : Wff) (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCif ph C A) (synCif ph C B))) :=
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
    @gRabeq (.neg ph) x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @gUneq2d (.classEq A B) (synCrab x A (.neg ph)) (synCrab x B (.neg ph))
      (synCrab x C ph) p0000
  have p0002 :=
    @gDfif6 ph x C A
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
    @gDfif6 ph x C B
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
    @gN3eqtr4g (.classEq A B) (synCun (synCrab x C ph) (synCrab x A (.neg ph)))
      (synCun (synCrab x C ph) (synCrab x B (.neg ph))) (synCif ph C A)
      (synCif ph C B) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_iftrue`. -/
@[expose]
noncomputable def gIftrue (ph : Wff) (A : Class) (B : Class) :
    Nominal.NPrf (.imp ph (.classEq (synCif ph A B) A)) :=
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
  have p0000 := @gDedlem0a ph (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0001 :=
    @gEqabdv ph (.imp (.imp (.classMem (.cv x) B) ph) (synWa (.classMem (.cv x) A) ph))
      x A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000
  have p0002 :=
    @gDfif2 ph x A B
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
    @gSyl6reqr ph A
      (.cab x (.imp (.imp (.classMem (.cv x) B) ph) (synWa (.classMem (.cv x) A) ph)))
      (synCif ph A B) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_iffalse`. -/
@[expose]
noncomputable def gIffalse (ph : Wff) (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.neg ph) (.classEq (synCif ph A B) B)) :=
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
  have p0000 := @gDedlemb ph (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0001 :=
    @gEqabdv (.neg ph)
      (synWo (synWa (.classMem (.cv x) A) ph) (synWa (.classMem (.cv x) B) (.neg ph)))
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIf ph x A B
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
    @gSyl6reqr (.neg ph) B
      (.cab x (synWo (synWa (.classMem (.cv x) A) ph)
          (synWa (.classMem (.cv x) B) (.neg ph))))
      (synCif ph A B) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_ifeq1d`. -/
@[expose]
noncomputable def gIfeq1d (ph : Wff) (ps : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_ifeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCif ps A C) (synCif ps B C))) :=
  by
  have p0000 := @gIfeq1 ps A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCif ps A C) (synCif ps B C)) hyp_ifeq1d_1
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ifeq2d`. -/
@[expose]
noncomputable def gIfeq2d (ph : Wff) (ps : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_ifeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCif ps C A) (synCif ps C B))) :=
  by
  have p0000 := @gIfeq2 ps A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCif ps C A) (synCif ps C B)) hyp_ifeq1d_1
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ifeq12d`. -/
@[expose]
noncomputable def gIfeq12d (ph : Wff) (ps : Wff) (A : Class) (B : Class) (C : Class)
    (D : Class) (hyp_ifeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_ifeq12d_2 : Nominal.NPrf (.imp ph (.classEq C D))) :
    Nominal.NPrf (.imp ph (.classEq (synCif ps A C) (synCif ps B D))) :=
  by
  have p0000 := @gIfeq1d ph ps A B C hyp_ifeq1d_1
  have p0001 := @gIfeq2d ph ps C D B hyp_ifeq12d_2
  have p0002 := @gEqtrd ph (synCif ps A C) (synCif ps B C) (synCif ps B D) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ifbi`. -/
@[expose]
noncomputable def gIfbi (ph : Wff) (ps : Wff) (A : Class) (B : Class) :
    Nominal.NPrf (.imp (synWb ph ps) (.classEq (synCif ph A B) (synCif ps A B))) :=
  by
  have p0000 := @gDfbi3 ph ps
  have p0001 := @gIftrue ph A B
  have p0002 := @gIftrue ps A B
  have p0003 := @gEqcomd ps (synCif ps A B) A p0002
  have p0004 := @gSylan9eq ph ps (synCif ph A B) A (synCif ps A B) p0001 p0003
  have p0005 := @gIffalse ph A B
  have p0006 := @gIffalse ps A B
  have p0007 := @gEqcomd (.neg ps) (synCif ps A B) B p0006
  have p0008 :=
    @gSylan9eq (.neg ph) (.neg ps) (synCif ph A B) B (synCif ps A B) p0005 p0007
  have p0009 :=
    @gJaoi (synWa ph ps) (.classEq (synCif ph A B) (synCif ps A B))
      (synWa (.neg ph) (.neg ps)) p0004 p0008
  have p0010 :=
    @gSylbi (synWb ph ps) (synWo (synWa ph ps) (synWa (.neg ph) (.neg ps)))
      (.classEq (synCif ph A B) (synCif ps A B)) p0000 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_ifbid`. -/
@[expose]
noncomputable def gIfbid (ph : Wff) (ps : Wff) (ch : Wff) (A : Class) (B : Class)
    (hyp_ifbid_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (.classEq (synCif ps A B) (synCif ch A B))) :=
  by
  have p0000 := @gIfbi ps ch A B
  have p0001 :=
    @gSyl ph (synWb ps ch) (.classEq (synCif ps A B) (synCif ch A B)) hyp_ifbid_1
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ifbieq2d`. -/
@[expose]
noncomputable def gIfbieq2d (ph : Wff) (ps : Wff) (ch : Wff) (A : Class) (B : Class)
    (C : Class) (hyp_ifbieq2d_1 : Nominal.NPrf (.imp ph (synWb ps ch)))
    (hyp_ifbieq2d_2 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCif ps C A) (synCif ch C B))) :=
  by
  have p0000 := @gIfbid ph ps ch C A hyp_ifbieq2d_1
  have p0001 := @gIfeq2d ph ch A B C hyp_ifbieq2d_2
  have p0002 := @gEqtrd ph (synCif ps C A) (synCif ch C A) (synCif ch C B) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ifbieq12d`. -/
@[expose]
noncomputable def gIfbieq12d (ph : Wff) (ps : Wff) (ch : Wff) (A : Class) (B : Class)
    (C : Class) (D : Class) (hyp_ifbieq12d_1 : Nominal.NPrf (.imp ph (synWb ps ch)))
    (hyp_ifbieq12d_2 : Nominal.NPrf (.imp ph (.classEq A C)))
    (hyp_ifbieq12d_3 : Nominal.NPrf (.imp ph (.classEq B D))) :
    Nominal.NPrf (.imp ph (.classEq (synCif ps A B) (synCif ch C D))) :=
  by
  have p0000 := @gIfbid ph ps ch A B hyp_ifbieq12d_1
  have p0001 := @gIfeq12d ph ch A C B D hyp_ifbieq12d_2 hyp_ifbieq12d_3
  have p0002 := @gEqtrd ph (synCif ps A B) (synCif ch A B) (synCif ch C D) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ifclda`. -/
@[expose]
noncomputable def gIfclda (ph : Wff) (ps : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_ifclda_1 : Nominal.NPrf (.imp (synWa ph ps) (.classMem A C)))
    (hyp_ifclda_2 : Nominal.NPrf (.imp (synWa ph (.neg ps)) (.classMem B C))) :
    Nominal.NPrf (.imp ph (.classMem (synCif ps A B) C)) :=
  by
  have p0000 := @gIftrue ps A B
  have p0001 := @gAdantl ps (.classEq (synCif ps A B) A) ph p0000
  have p0002 := @gEqeltrd (synWa ph ps) (synCif ps A B) A C p0001 hyp_ifclda_1
  have p0003 := @gIffalse ps A B
  have p0004 := @gAdantl (.neg ps) (.classEq (synCif ps A B) B) ph p0003
  have p0005 := @gEqeltrd (synWa ph (.neg ps)) (synCif ps A B) B C p0004 hyp_ifclda_2
  have p0006 := @gPm261dan ph ps (.classMem (synCif ps A B) C) p0002 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_elimif`. -/
@[expose]
noncomputable def gElimif (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (A : Class)
    (B : Class)
    (hyp_elimif_1 : Nominal.NPrf (.imp (.classEq (synCif ph A B) A) (synWb ps ch)))
    (hyp_elimif_2 : Nominal.NPrf (.imp (.classEq (synCif ph A B) B) (synWb ps th))) :
    Nominal.NPrf (synWb ps (synWo (synWa ph ch) (synWa (.neg ph) th))) :=
  by
  have p0000 := @gExmid ph
  have p0001 := @gBiantrur (synWo ph (.neg ph)) ps p0000
  have p0002 := @gAndir ph (.neg ph) ps
  have p0003 := @gIftrue ph A B
  have p0004 := @gSyl ph (.classEq (synCif ph A B) A) (synWb ps ch) p0003 hyp_elimif_1
  have p0005 := @gPm532i ph ps ch p0004
  have p0006 := @gIffalse ph A B
  have p0007 :=
    @gSyl (.neg ph) (.classEq (synCif ph A B) B) (synWb ps th) p0006 hyp_elimif_2
  have p0008 := @gPm532i (.neg ph) ps th p0007
  have p0009 :=
    @gOrbi12i (synWa ph ps) (synWa ph ch) (synWa (.neg ph) ps) (synWa (.neg ph) th)
      p0005 p0008
  have p0010 :=
    @gN3bitri ps (synWa (synWo ph (.neg ph)) ps)
      (synWo (synWa ph ps) (synWa (.neg ph) ps))
      (synWo (synWa ph ch) (synWa (.neg ph) th)) p0001 p0002 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_ifbothda`. -/
@[expose]
noncomputable def gIfbothda (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (et : Wff)
    (A : Class) (B : Class)
    (hyp_ifboth_1 : Nominal.NPrf (.imp (.classEq A (synCif ph A B)) (synWb ps th)))
    (hyp_ifboth_2 : Nominal.NPrf (.imp (.classEq B (synCif ph A B)) (synWb ch th)))
    (hyp_ifbothda_3 : Nominal.NPrf (.imp (synWa et ph) ps))
    (hyp_ifbothda_4 : Nominal.NPrf (.imp (synWa et (.neg ph)) ch)) :
    Nominal.NPrf (.imp et th) :=
  by
  have p0000 := @gIftrue ph A B
  have p0001 := @gEqcomd ph (synCif ph A B) A p0000
  have p0002 := @gSyl ph (.classEq A (synCif ph A B)) (synWb ps th) p0001 hyp_ifboth_1
  have p0003 := @gAdantl ph (synWb ps th) et p0002
  have p0004 := @gMpbid (synWa et ph) ps th hyp_ifbothda_3 p0003
  have p0005 := @gIffalse ph A B
  have p0006 := @gEqcomd (.neg ph) (synCif ph A B) B p0005
  have p0007 :=
    @gSyl (.neg ph) (.classEq B (synCif ph A B)) (synWb ch th) p0006 hyp_ifboth_2
  have p0008 := @gAdantl (.neg ph) (synWb ch th) et p0007
  have p0009 := @gMpbid (synWa et (.neg ph)) ch th hyp_ifbothda_4 p0008
  have p0010 := @gPm261dan et ph th p0004 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_ifboth`. -/
@[expose]
noncomputable def gIfboth (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (A : Class)
    (B : Class)
    (hyp_ifboth_1 : Nominal.NPrf (.imp (.classEq A (synCif ph A B)) (synWb ps th)))
    (hyp_ifboth_2 : Nominal.NPrf (.imp (.classEq B (synCif ph A B)) (synWb ch th))) :
    Nominal.NPrf (.imp (synWa ps ch) th) :=
  by
  have p0000 := @gSimpll ps ch ph
  have p0001 := @gSimplr ps ch (.neg ph)
  have p0002 :=
    @gIfbothda ph ps ch th (synWa ps ch) A B hyp_ifboth_1 hyp_ifboth_2 p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_elif`. -/
@[expose]
noncomputable def gElif (ph : Wff) (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (synWb (.classMem A (synCif ph B C))
        (synWo (synWa ph (.classMem A B)) (synWa (.neg ph) (.classMem A C)))) :=
  by
  have p0000 := @gEleq2 (synCif ph B C) B A
  have p0001 := @gEleq2 (synCif ph B C) C A
  have p0002 :=
    @gElimif ph (.classMem A (synCif ph B C)) (.classMem A B) (.classMem A C) B C p0000
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ifcl`. -/
@[expose]
noncomputable def gIfcl (ph : Wff) (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A C) (.classMem B C)) (.classMem (synCif ph A B) C)) :=
  by
  have p0000 := @gEleq1 A (synCif ph A B) C
  have p0001 := @gEleq1 B (synCif ph A B) C
  have p0002 :=
    @gIfboth ph (.classMem A C) (.classMem B C) (.classMem (synCif ph A B) C) A B p0000
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ifeqor`. -/
@[expose]
noncomputable def gIfeqor (ph : Wff) (A : Class) (B : Class) :
    Nominal.NPrf (synWo (.classEq (synCif ph A B) A) (.classEq (synCif ph A B) B)) :=
  by
  have p0000 := @gIftrue ph A B
  have p0001 := @gCon3i ph (.classEq (synCif ph A B) A) p0000
  have p0002 := @gIffalse ph A B
  have p0003 :=
    @gSyl (.neg (.classEq (synCif ph A B) A)) (.neg ph) (.classEq (synCif ph A B) B)
      p0001 p0002
  have p0004 := @gOrri (.classEq (synCif ph A B) A) (.classEq (synCif ph A B) B) p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_dedth`. -/
@[expose]
noncomputable def gDedth (ph : Wff) (ps : Wff) (ch : Wff) (A : Class) (B : Class)
    (hyp_dedth_1 : Nominal.NPrf (.imp (.classEq A (synCif ph A B)) (synWb ps ch)))
    (hyp_dedth_2 : Nominal.NPrf ch) : Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @gIftrue ph A B
  have p0001 := @gEqcomd ph (synCif ph A B) A p0000
  have p0002 := @gSyl ph (.classEq A (synCif ph A B)) (synWb ps ch) p0001 hyp_dedth_1
  have p0003 := @gMpbiri ph ps ch hyp_dedth_2 p0002
  exact p0003


end NFChoice.DirectNominalPrf.WPPReplay
