/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk012BCompact001Block006

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk013Compact001Part001`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_brdisj`. -/
@[expose]
noncomputable def gBrdisj (A : Class) (B : Class)
    (hyp_brdisj_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_brdisj_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (synWb (synWbr A (synCdisj) B) (.classEq (synCin A B) (synC0))) :=
  by
  have p0000 := @gBrdisjg A B (synCvv) (synCvv)
  have p0001 :=
    @gMp2an (.classMem A (synCvv)) (.classMem B (synCvv))
      (synWb (synWbr A (synCdisj) B) (.classEq (synCin A B) (synC0))) hyp_brdisj_1
      hyp_brdisj_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_disjex`. -/
@[expose]
noncomputable def gDisjex : Nominal.NPrf (.classMem (synCdisj) (synCvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0002 : z ∉ ((synCop (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, or_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((synCtxp (synCsset) (synCsset))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0006 :
    x ∉ ((synCcompl (synCima (synCtxp (synCsset) (synCsset)) (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 :
    y ∉ ((synCcompl (synCima (synCtxp (synCsset) (synCsset)) (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfDisj x y
      dv_cache_0001
  have p0001 := @gOteltxp (synCsn (.cv z)) (.cv x) (.cv y) (synCsset) (synCsset)
  have p0002 := @gVex z
  have p0003 := @gVex x
  have p0004 := @gOpelssetsn (.cv z) (.cv x) p0002 p0003
  have p0005 := @gVex y
  have p0006 := @gOpelssetsn (.cv z) (.cv y) p0002 p0005
  have p0007_e00_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv z)) (.cv x)) (synCsset)) (.objMem z x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synCsn synCsset synCopab synWss synCin
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0004
  have p0007_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv z)) (.cv y)) (synCsset)) (.objMem z y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synCsn synCsset synCopab synWss synCin
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0007 :=
    @gAnbi12i (.classMem (synCop (synCsn (.cv z)) (.cv x)) (synCsset)) (.objMem z x)
      (.classMem (synCop (synCsn (.cv z)) (.cv y)) (synCsset)) (.objMem z y)
      p0007_e00_recanon p0007_e01_recanon
  have p0008 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))
        (synCtxp (synCsset) (synCsset)))
      (synWa (.classMem (synCop (synCsn (.cv z)) (.cv x)) (synCsset))
        (.classMem (synCop (synCsn (.cv z)) (.cv y)) (synCsset)))
      (synWa (.objMem z x) (.objMem z y)) p0001 p0007
  have p0009 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))
        (synCtxp (synCsset) (synCsset)))
      (synWa (.objMem z x) (.objMem z y)) z p0008
  have p0010 :=
    @gElima1c z (synCop (.cv x) (.cv y)) (synCtxp (synCsset) (synCsset))
      dv_cache_0002 dv_cache_0003
  have p0011 := (Nominal.biimpRefl (synWrex z (.cv x) (.objMem z y)))
  have p0012_e02_recanon :
    Nominal.NPrf
      (synWb (synWrex z (.cv x) (.objMem z y))
        (synWex z (synWa (.objMem z x) (.objMem z y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0011
  have p0012 :=
    @gN3bitr4i
      (synWex z (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))
          (synCtxp (synCsset) (synCsset))))
      (synWex z (synWa (.objMem z x) (.objMem z y)))
      (.classMem (synCop (.cv x) (.cv y))
        (synCima (synCtxp (synCsset) (synCsset)) (synC1c)))
      (synWrex z (.cv x) (.objMem z y)) p0009 p0010 p0012_e02_recanon
  have p0013 := @gDfrex2 (.objMem z y) z (.cv x)
  have p0014 :=
    @gBitri
      (.classMem (synCop (.cv x) (.cv y))
        (synCima (synCtxp (synCsset) (synCsset)) (synC1c)))
      (synWrex z (.cv x) (.objMem z y)) (.neg (synWral z (.cv x) (.neg (.objMem z y))))
      p0012 p0013
  have p0015 :=
    @gCon2bii
      (.classMem (synCop (.cv x) (.cv y))
        (synCima (synCtxp (synCsset) (synCsset)) (synC1c)))
      (synWral z (.cv x) (.neg (.objMem z y))) p0014
  have p0016 := @gDisj z (.cv x) (.cv y) dv_cache_0004 dv_cache_0005
  have p0017 := @gOpex (.cv x) (.cv y) p0003 p0005
  have p0018 :=
    @gElcompl (synCop (.cv x) (.cv y))
      (synCima (synCtxp (synCsset) (synCsset)) (synC1c)) p0017
  have p0019_e01_recanon :
    Nominal.NPrf
      (synWb (.classEq (synCin (.cv x) (.cv y)) (synC0))
        (synWral z (.cv x) (.neg (.objMem z y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCin synCcompl synCnin synWnan synWa synC0 synCdif synCvv
          synWral
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0016
  have p0019 :=
    @gN3bitr4ri (synWral z (.cv x) (.neg (.objMem z y)))
      (.neg (.classMem (synCop (.cv x) (.cv y))
          (synCima (synCtxp (synCsset) (synCsset)) (synC1c))))
      (.classEq (synCin (.cv x) (.cv y)) (synC0))
      (.classMem (synCop (.cv x) (.cv y))
        (synCcompl (synCima (synCtxp (synCsset) (synCsset)) (synC1c))))
      p0015 p0019_e01_recanon p0018
  have p0020 :=
    @gOpabbi2i (.classEq (synCin (.cv x) (.cv y)) (synC0)) x y
      (synCcompl (synCima (synCtxp (synCsset) (synCsset)) (synC1c))) dv_cache_0006
      dv_cache_0007 dv_cache_0001 p0019
  have p0021 :=
    @gEqtr4i (synCdisj) (synCopab x y (.classEq (synCin (.cv x) (.cv y)) (synC0)))
      (synCcompl (synCima (synCtxp (synCsset) (synCsset)) (synC1c))) p0000 p0020
  have p0022 := @gSsetex
  have p0024 := @gTxpex (synCsset) (synCsset) p0022 p0022
  have p0025 := @gN1cex
  have p0026 := @gImaex (synCtxp (synCsset) (synCsset)) (synC1c) p0024 p0025
  have p0027 := @gComplex (synCima (synCtxp (synCsset) (synCsset)) (synC1c)) p0026
  have p0028 :=
    @gEqeltri (synCdisj)
      (synCcompl (synCima (synCtxp (synCsset) (synCsset)) (synC1c))) (synCvv) p0021
      p0027
  exact p0028


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part002`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_addcfnex`. -/
@[expose]
noncomputable def gAddcfnex : Nominal.NPrf (.classMem (synCaddcfn) (synCvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let a : Var := freshVar proofSupport 3
  let b : Var := freshVar proofSupport 4
  let p : Var := freshVar proofSupport 5
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_x_ne_b : x ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_b_ne_x : b ≠ x := Ne.symm fresh_x_ne_b
  have fresh_x_ne_p : x ≠ p :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_y_ne_a : y ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_a_ne_y : a ≠ y := Ne.symm fresh_y_ne_a
  have fresh_y_ne_b : y ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_b_ne_y : b ≠ y := Ne.symm fresh_y_ne_b
  have fresh_y_ne_p : y ≠ p :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_z_ne_a : z ≠ a :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_a_ne_z : a ≠ z := Ne.symm fresh_z_ne_a
  have fresh_z_ne_b : z ≠ b :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_b_ne_z : b ≠ z := Ne.symm fresh_z_ne_b
  have fresh_z_ne_p : z ≠ p :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_p_ne_z : p ≠ z := Ne.symm fresh_z_ne_p
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_a_ne_p : a ≠ p :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_p_ne_a : p ≠ a := Ne.symm fresh_a_ne_p
  have fresh_b_ne_p : b ≠ p :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_p_ne_b : p ≠ b := Ne.symm fresh_b_ne_p
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0002 : x ∉ ((Class.cv p)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_p, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_a, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((synC1st)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_a, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((synWbr (.cv p) (synC1st) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_p, fresh_y_ne_x, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((synCop (.cv a) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_a, fresh_x_ne_y, or_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((synWbr (.cv p) (synC1st) (synCop (.cv a) (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_p, fresh_x_ne_a, fresh_x_ne_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 :
    y ∉ ((synWbr (.cv p) (synCcom (synC2nd) (synC1st)) (.cv b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_p, fresh_y_ne_b, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0011 : z ∉ ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_p, not_false_eq_true])
  have dv_cache_0012 : z ∉ ((synCop (.cv a) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_a, fresh_z_ne_y, or_false, not_false_eq_true])
  have dv_cache_0013 :
    z ∉
      ((synWb (synWbr (.cv p) (synCcom (synC2nd) (synC1st)) (.cv b)) (.objEq y b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton, fresh_z_ne_p, fresh_z_ne_b, fresh_z_ne_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((Class.cv b)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_b, not_false_eq_true])
  have dv_cache_0015 : y ∉ ((synWbr (.cv p) (synC1st) (synCop (.cv a) (.cv b)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_p, fresh_y_ne_a, fresh_y_ne_b,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0016 : p ∉ ((synCop (.cv a) (synCop (.cv b) (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_a, fresh_p_ne_b, fresh_p_ne_z, or_false,
          not_false_eq_true])
  have dv_cache_0017 :
    p ∉
      ((synCtxp (synCcom (synC1st) (synC1st))
          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0018 : p ∉ ((synCcup)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccup,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0019 : p ∉ ((synCop (synCop (.cv a) (.cv b)) (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_a, fresh_p_ne_b, fresh_p_ne_z, or_false,
          not_false_eq_true])
  have dv_cache_0020 :
    a ∉ ((synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_b, fresh_a_ne_z, fresh_a_ne_x, or_false,
          not_false_eq_true])
  have dv_cache_0021 :
    a ∉
      ((synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
              (synCin (synCins3 (synCdisj)) (synCima
                  (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                  (synCcup))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdisj,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccup, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0022 : b ∉ ((synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_z, fresh_b_ne_x, fresh_b_ne_y, or_false,
          not_false_eq_true])
  have dv_cache_0023 :
    b ∉
      ((synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCima
              (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                    (synCin (synCins3 (synCdisj)) (synCima
                        (synCtxp (synCcom (synC1st) (synC1st))
                          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                        (synCcup)))))) (synC1c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdisj,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccup,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0024 : a ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_z, not_false_eq_true])
  have dv_cache_0025 : b ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_z, not_false_eq_true])
  have dv_cache_0026 : a ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_x, not_false_eq_true])
  have dv_cache_0027 : b ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_x, not_false_eq_true])
  have dv_cache_0028 : a ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_y, not_false_eq_true])
  have dv_cache_0029 : b ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_y, not_false_eq_true])
  have dv_cache_0030 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0031 : x ∉ ((synCvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0032 : y ∉ ((synCvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0033 :
    x ∉
      ((synCima (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCima
                (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                      (synCin (synCins3 (synCdisj)) (synCima
                          (synCtxp (synCcom (synC1st) (synC1st))
                            (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                          (synCcup)))))) (synC1c)))) (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdisj,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccup,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0034 :
    y ∉
      ((synCima (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCima
                (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                      (synCin (synCins3 (synCdisj)) (synCima
                          (synCtxp (synCcom (synC1st) (synC1st))
                            (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                          (synCcup)))))) (synC1c)))) (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdisj,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccup,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0035 :
    z ∉
      ((synCima (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCima
                (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                      (synCin (synCins3 (synCdisj)) (synCima
                          (synCtxp (synCcom (synC1st) (synC1st))
                            (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                          (synCcup)))))) (synC1c)))) (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdisj,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccup,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0036 : z ∉ ((synCplc (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, or_false, not_false_eq_true])
  have dv_cache_0037 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0038 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfAddcfn x y
      dv_cache_0001
  have p0001 :=
    @gElin
      (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))
      (synCins2 (synCins2 (synCsset)))
      (synCins4 (synCima (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                (synCin (synCins3 (synCdisj)) (synCima
                    (synCtxp (synCcom (synC1st) (synC1st))
                      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCcup))))))
          (synC1c)))
  have p0002 := @gSnex (.cv z)
  have p0003 :=
    @gOtelins2 (synCsn (.cv b)) (synCsn (.cv z)) (synCop (.cv x) (.cv y))
      (synCins2 (synCsset)) p0002
  have p0004 := @gVex x
  have p0005 := @gOtelins2 (synCsn (.cv b)) (.cv x) (.cv y) (synCsset) p0004
  have p0006 := @gVex b
  have p0007 := @gVex y
  have p0008 := @gOpelssetsn (.cv b) (.cv y) p0006 p0007
  have p0009_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv b)) (.cv y)) (synCsset)) (.objMem b y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synCsn synCsset synCopab synWss synCin
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0008
  have p0009 :=
    @gN3bitri
      (.classMem
        (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))
        (synCins2 (synCins2 (synCsset))))
      (.classMem (synCop (synCsn (.cv b)) (synCop (.cv x) (.cv y))) (synCins2 (synCsset)))
      (.classMem (synCop (synCsn (.cv b)) (.cv y)) (synCsset)) (.objMem b y) p0003
      p0005 p0009_e02_recanon
  have p0010 :=
    @gOqelins4 (synCsn (.cv b)) (synCsn (.cv z)) (.cv x) (.cv y)
      (synCima (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
              (synCin (synCins3 (synCdisj)) (synCima
                  (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCcup))))))
        (synC1c))
      p0007
  have p0011 :=
    @gElin
      (synCop (synCsn (.cv a))
        (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (.cv x))))
      (synCins2 (synCins2 (synCsset)))
      (synCins4 (synCsi3 (synCin (synCins3 (synCdisj)) (synCima
              (synCtxp (synCcom (synC1st) (synC1st))
                (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCcup)))))
  have p0012 := @gSnex (.cv b)
  have p0013 :=
    @gOtelins2 (synCsn (.cv a)) (synCsn (.cv b)) (synCop (synCsn (.cv z)) (.cv x))
      (synCins2 (synCsset)) p0012
  have p0014 := @gOtelins2 (synCsn (.cv a)) (synCsn (.cv z)) (.cv x) (synCsset) p0002
  have p0015 := @gVex a
  have p0016 := @gOpelssetsn (.cv a) (.cv x) p0015 p0004
  have p0017_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv a)) (.cv x)) (synCsset)) (.objMem a x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synCsn synCsset synCopab synWss synCin
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0016
  have p0017 :=
    @gN3bitri
      (.classMem (synCop (synCsn (.cv a))
          (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (.cv x))))
        (synCins2 (synCins2 (synCsset))))
      (.classMem (synCop (synCsn (.cv a)) (synCop (synCsn (.cv z)) (.cv x)))
        (synCins2 (synCsset)))
      (.classMem (synCop (synCsn (.cv a)) (.cv x)) (synCsset)) (.objMem a x) p0013
      p0014 p0017_e02_recanon
  have p0018 :=
    @gOqelins4 (synCsn (.cv a)) (synCsn (.cv b)) (synCsn (.cv z)) (.cv x)
      (synCsi3 (synCin (synCins3 (synCdisj)) (synCima
            (synCtxp (synCcom (synC1st) (synC1st))
              (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCcup))))
      p0004
  have p0019 := @gVex z
  have p0020 :=
    @gOtsnelsi3 (.cv a) (.cv b) (.cv z)
      (synCin (synCins3 (synCdisj)) (synCima (synCtxp (synCcom (synC1st) (synC1st))
            (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCcup)))
      p0015 p0006 p0019
  have p0021 :=
    @gElin (synCop (.cv a) (synCop (.cv b) (.cv z))) (synCins3 (synCdisj))
      (synCima (synCtxp (synCcom (synC1st) (synC1st))
          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCcup))
  have p0022 := @gOtelins3 (.cv a) (.cv b) (.cv z) (synCdisj) p0019
  have p0023 := (Nominal.biimpRefl (synWbr (.cv a) (synCdisj) (.cv b)))
  have p0024 := @gBrdisj (.cv a) (.cv b) p0015 p0006
  have p0025 :=
    @gN3bitr2i
      (.classMem (synCop (.cv a) (synCop (.cv b) (.cv z))) (synCins3 (synCdisj)))
      (.classMem (synCop (.cv a) (.cv b)) (synCdisj))
      (synWbr (.cv a) (synCdisj) (.cv b)) (.classEq (synCin (.cv a) (.cv b)) (synC0))
      p0022 p0023 p0024
  have p0026 :=
    @gTrtxp (.cv p) (.cv b) (.cv z) (synCcom (synC2nd) (synC1st)) (synC2nd)
  have p0027 :=
    @gAnbi2i
      (synWbr (.cv p) (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))
        (synCop (.cv b) (.cv z)))
      (synWa (synWbr (.cv p) (synCcom (synC2nd) (synC1st)) (.cv b))
        (synWbr (.cv p) (synC2nd) (.cv z)))
      (synWbr (.cv p) (synCcom (synC1st) (synC1st)) (.cv a)) p0026
  have p0028 :=
    @gTrtxp (.cv p) (.cv a) (synCop (.cv b) (.cv z)) (synCcom (synC1st) (synC1st))
      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))
  have p0029 :=
    @gAnass (synWbr (.cv p) (synCcom (synC1st) (synC1st)) (.cv a))
      (synWbr (.cv p) (synCcom (synC2nd) (synC1st)) (.cv b))
      (synWbr (.cv p) (synC2nd) (.cv z))
  have p0030 :=
    @gN3bitr4i
      (synWa (synWbr (.cv p) (synCcom (synC1st) (synC1st)) (.cv a))
        (synWbr (.cv p) (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))
          (synCop (.cv b) (.cv z))))
      (synWa (synWbr (.cv p) (synCcom (synC1st) (synC1st)) (.cv a))
        (synWa (synWbr (.cv p) (synCcom (synC2nd) (synC1st)) (.cv b))
          (synWbr (.cv p) (synC2nd) (.cv z))))
      (synWbr (.cv p) (synCtxp (synCcom (synC1st) (synC1st))
          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
        (synCop (.cv a) (synCop (.cv b) (.cv z))))
      (synWa (synWa (synWbr (.cv p) (synCcom (synC1st) (synC1st)) (.cv a))
          (synWbr (.cv p) (synCcom (synC2nd) (synC1st)) (.cv b)))
        (synWbr (.cv p) (synC2nd) (.cv z)))
      p0027 p0028 p0029
  have p0031 :=
    @gBrco x (.cv p) (.cv a) (synC1st) (synC1st) dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0004
  have p0032 := @gBr1st y (.cv x) (.cv a) dv_cache_0005 dv_cache_0006 p0015
  have p0033 :=
    @gAnbi2i (synWbr (.cv x) (synC1st) (.cv a))
      (synWex y (.classEq (.cv x) (synCop (.cv a) (.cv y))))
      (synWbr (.cv p) (synC1st) (.cv x)) p0032
  have p0034 :=
    @gN1942v (synWbr (.cv p) (synC1st) (.cv x))
      (.classEq (.cv x) (synCop (.cv a) (.cv y))) y dv_cache_0007
  have p0035 :=
    @gBitr4i
      (synWa (synWbr (.cv p) (synC1st) (.cv x)) (synWbr (.cv x) (synC1st) (.cv a)))
      (synWa (synWbr (.cv p) (synC1st) (.cv x))
        (synWex y (.classEq (.cv x) (synCop (.cv a) (.cv y)))))
      (synWex y (synWa (synWbr (.cv p) (synC1st) (.cv x))
          (.classEq (.cv x) (synCop (.cv a) (.cv y)))))
      p0033 p0034
  have p0036 :=
    @gExbii
      (synWa (synWbr (.cv p) (synC1st) (.cv x)) (synWbr (.cv x) (synC1st) (.cv a)))
      (synWex y (synWa (synWbr (.cv p) (synC1st) (.cv x))
          (.classEq (.cv x) (synCop (.cv a) (.cv y)))))
      x p0035
  have p0037 :=
    @gExcom
      (synWa (synWbr (.cv p) (synC1st) (.cv x)) (.classEq (.cv x) (synCop (.cv a) (.cv y))))
      x y
  have p0038 :=
    @gExancom (synWbr (.cv p) (synC1st) (.cv x))
      (.classEq (.cv x) (synCop (.cv a) (.cv y))) x
  have p0039 := @gOpex (.cv a) (.cv y) p0015 p0007
  have p0040 := @gBreq2 (.cv x) (synCop (.cv a) (.cv y)) (.cv p) (synC1st)
  have p0041 :=
    @gCeqsexv (synWbr (.cv p) (synC1st) (.cv x))
      (synWbr (.cv p) (synC1st) (synCop (.cv a) (.cv y))) x (synCop (.cv a) (.cv y))
      dv_cache_0008 dv_cache_0009 p0039 p0040
  have p0042 :=
    @gBitri
      (synWex x (synWa (synWbr (.cv p) (synC1st) (.cv x))
          (.classEq (.cv x) (synCop (.cv a) (.cv y)))))
      (synWex x (synWa (.classEq (.cv x) (synCop (.cv a) (.cv y)))
          (synWbr (.cv p) (synC1st) (.cv x))))
      (synWbr (.cv p) (synC1st) (synCop (.cv a) (.cv y))) p0038 p0041
  have p0043 :=
    @gExbii
      (synWex x (synWa (synWbr (.cv p) (synC1st) (.cv x))
          (.classEq (.cv x) (synCop (.cv a) (.cv y)))))
      (synWbr (.cv p) (synC1st) (synCop (.cv a) (.cv y))) y p0042
  have p0044 :=
    @gBitri
      (synWex x (synWex y (synWa (synWbr (.cv p) (synC1st) (.cv x))
            (.classEq (.cv x) (synCop (.cv a) (.cv y))))))
      (synWex y (synWex x (synWa (synWbr (.cv p) (synC1st) (.cv x))
            (.classEq (.cv x) (synCop (.cv a) (.cv y))))))
      (synWex y (synWbr (.cv p) (synC1st) (synCop (.cv a) (.cv y)))) p0037 p0043
  have p0045 :=
    @gN3bitri (synWbr (.cv p) (synCcom (synC1st) (synC1st)) (.cv a))
      (synWex x (synWa (synWbr (.cv p) (synC1st) (.cv x))
          (synWbr (.cv x) (synC1st) (.cv a))))
      (synWex x (synWex y (synWa (synWbr (.cv p) (synC1st) (.cv x))
            (.classEq (.cv x) (synCop (.cv a) (.cv y))))))
      (synWex y (synWbr (.cv p) (synC1st) (synCop (.cv a) (.cv y)))) p0031 p0036 p0044
  have p0046 :=
    @gAnbi1i (synWbr (.cv p) (synCcom (synC1st) (synC1st)) (.cv a))
      (synWex y (synWbr (.cv p) (synC1st) (synCop (.cv a) (.cv y))))
      (synWbr (.cv p) (synCcom (synC2nd) (synC1st)) (.cv b)) p0045
  have p0047 :=
    @gN1941v (synWbr (.cv p) (synC1st) (synCop (.cv a) (.cv y)))
      (synWbr (.cv p) (synCcom (synC2nd) (synC1st)) (.cv b)) y dv_cache_0010
  have p0048 :=
    @gBr1st z (.cv p) (synCop (.cv a) (.cv y)) dv_cache_0011 dv_cache_0012 p0039
  have p0049 :=
    @gBreq1 (.cv p) (synCop (synCop (.cv a) (.cv y)) (.cv z)) (.cv b)
      (synCcom (synC2nd) (synC1st))
  have p0050 :=
    @gBrco1st (synCop (.cv a) (.cv y)) (.cv z) (.cv b) (synC2nd) p0039 p0019
  have p0051 := @gOpbr2nd (.cv a) (.cv y) (.cv b) p0015 p0007
  have p0052_e01_recanon :
    Nominal.NPrf
      (synWb (synWbr (synCop (.cv a) (.cv y)) (synC2nd) (.cv b)) (.objEq y b)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synC2nd synCopab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0051
  have p0052 :=
    @gBitri
      (synWbr (synCop (synCop (.cv a) (.cv y)) (.cv z))
        (synCcom (synC2nd) (synC1st)) (.cv b))
      (synWbr (synCop (.cv a) (.cv y)) (synC2nd) (.cv b)) (.objEq y b) p0050
      p0052_e01_recanon
  have p0053 :=
    @gSyl6bb (.classEq (.cv p) (synCop (synCop (.cv a) (.cv y)) (.cv z)))
      (synWbr (.cv p) (synCcom (synC2nd) (synC1st)) (.cv b))
      (synWbr (synCop (synCop (.cv a) (.cv y)) (.cv z))
        (synCcom (synC2nd) (synC1st)) (.cv b))
      (.objEq y b) p0049 p0052
  have p0054 :=
    @gExlimiv (.classEq (.cv p) (synCop (synCop (.cv a) (.cv y)) (.cv z)))
      (synWb (synWbr (.cv p) (synCcom (synC2nd) (synC1st)) (.cv b)) (.objEq y b)) z
      dv_cache_0013 p0053
  have p0055 :=
    @gSylbi (synWbr (.cv p) (synC1st) (synCop (.cv a) (.cv y)))
      (synWex z (.classEq (.cv p) (synCop (synCop (.cv a) (.cv y)) (.cv z))))
      (synWb (synWbr (.cv p) (synCcom (synC2nd) (synC1st)) (.cv b)) (.objEq y b))
      p0048 p0054
  have p0056 :=
    @gPm532i (synWbr (.cv p) (synC1st) (synCop (.cv a) (.cv y)))
      (synWbr (.cv p) (synCcom (synC2nd) (synC1st)) (.cv b)) (.objEq y b) p0055
  have p0057 :=
    @gExbii
      (synWa (synWbr (.cv p) (synC1st) (synCop (.cv a) (.cv y)))
        (synWbr (.cv p) (synCcom (synC2nd) (synC1st)) (.cv b)))
      (synWa (synWbr (.cv p) (synC1st) (synCop (.cv a) (.cv y))) (.objEq y b)) y p0056
  have p0058 :=
    @gExancom (synWbr (.cv p) (synC1st) (synCop (.cv a) (.cv y))) (.objEq y b) y
  have p0059 :=
    @gBitri
      (synWex y (synWa (synWbr (.cv p) (synC1st) (synCop (.cv a) (.cv y)))
          (synWbr (.cv p) (synCcom (synC2nd) (synC1st)) (.cv b))))
      (synWex y (synWa (synWbr (.cv p) (synC1st) (synCop (.cv a) (.cv y))) (.objEq y b)))
      (synWex y (synWa (.objEq y b) (synWbr (.cv p) (synC1st) (synCop (.cv a) (.cv y)))))
      p0057 p0058
  have p0060 :=
    @gN3bitr2i
      (synWa (synWbr (.cv p) (synCcom (synC1st) (synC1st)) (.cv a))
        (synWbr (.cv p) (synCcom (synC2nd) (synC1st)) (.cv b)))
      (synWa (synWex y (synWbr (.cv p) (synC1st) (synCop (.cv a) (.cv y))))
        (synWbr (.cv p) (synCcom (synC2nd) (synC1st)) (.cv b)))
      (synWex y (synWa (synWbr (.cv p) (synC1st) (synCop (.cv a) (.cv y)))
          (synWbr (.cv p) (synCcom (synC2nd) (synC1st)) (.cv b))))
      (synWex y (synWa (.objEq y b) (synWbr (.cv p) (synC1st) (synCop (.cv a) (.cv y)))))
      p0046 p0047 p0059
  have p0061 := @gOpeq2 (.cv y) (.cv b) (.cv a)
  have p0062_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y b) (.classEq (synCop (.cv a) (.cv y)) (synCop (.cv a) (.cv b)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0061
  have p0062 :=
    @gBreq2d (.objEq y b) (synCop (.cv a) (.cv y)) (synCop (.cv a) (.cv b)) (.cv p)
      (synC1st) p0062_e00_recanon
  have p0063_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv y) (.cv b))
        (synWb (synWbr (.cv p) (synC1st) (synCop (.cv a) (.cv y)))
          (synWbr (.cv p) (synC1st) (synCop (.cv a) (.cv b))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synC1st synCopab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0062
  have p0063 :=
    @gCeqsexv (synWbr (.cv p) (synC1st) (synCop (.cv a) (.cv y)))
      (synWbr (.cv p) (synC1st) (synCop (.cv a) (.cv b))) y (.cv b) dv_cache_0014
      dv_cache_0015 p0006 p0063_e01_recanon
  have p0064_e01_recanon :
    Nominal.NPrf
      (synWb (synWex y
          (synWa (.objEq y b) (synWbr (.cv p) (synC1st) (synCop (.cv a) (.cv y)))))
        (synWbr (.cv p) (synC1st) (synCop (.cv a) (.cv b)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWex synWa synWbr synCop synCun synCnin synWnan synCcompl
          synWrex synCphi synC1st synCopab
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0063
  have p0064 :=
    @gBitri
      (synWa (synWbr (.cv p) (synCcom (synC1st) (synC1st)) (.cv a))
        (synWbr (.cv p) (synCcom (synC2nd) (synC1st)) (.cv b)))
      (synWex y (synWa (.objEq y b) (synWbr (.cv p) (synC1st) (synCop (.cv a) (.cv y)))))
      (synWbr (.cv p) (synC1st) (synCop (.cv a) (.cv b))) p0060 p0064_e01_recanon
  have p0065 :=
    @gAnbi1i
      (synWa (synWbr (.cv p) (synCcom (synC1st) (synC1st)) (.cv a))
        (synWbr (.cv p) (synCcom (synC2nd) (synC1st)) (.cv b)))
      (synWbr (.cv p) (synC1st) (synCop (.cv a) (.cv b)))
      (synWbr (.cv p) (synC2nd) (.cv z)) p0064
  have p0066 := @gOpex (.cv a) (.cv b) p0015 p0006
  have p0067 := @gOp1st2nd (synCop (.cv a) (.cv b)) (.cv z) (.cv p) p0066 p0019
  have p0068 :=
    @gN3bitri
      (synWbr (.cv p) (synCtxp (synCcom (synC1st) (synC1st))
          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
        (synCop (.cv a) (synCop (.cv b) (.cv z))))
      (synWa (synWa (synWbr (.cv p) (synCcom (synC1st) (synC1st)) (.cv a))
          (synWbr (.cv p) (synCcom (synC2nd) (synC1st)) (.cv b)))
        (synWbr (.cv p) (synC2nd) (.cv z)))
      (synWa (synWbr (.cv p) (synC1st) (synCop (.cv a) (.cv b)))
        (synWbr (.cv p) (synC2nd) (.cv z)))
      (.classEq (.cv p) (synCop (synCop (.cv a) (.cv b)) (.cv z))) p0030 p0065 p0067
  have p0069 :=
    @gRexbii
      (synWbr (.cv p) (synCtxp (synCcom (synC1st) (synC1st))
          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
        (synCop (.cv a) (synCop (.cv b) (.cv z))))
      (.classEq (.cv p) (synCop (synCop (.cv a) (.cv b)) (.cv z))) p (synCcup) p0068
  have p0070 :=
    @gElima p (synCop (.cv a) (synCop (.cv b) (.cv z)))
      (synCtxp (synCcom (synC1st) (synC1st))
        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
      (synCcup) dv_cache_0016 dv_cache_0017 dv_cache_0018
  have p0071 :=
    @gRisset p (synCop (synCop (.cv a) (.cv b)) (.cv z)) (synCcup) dv_cache_0019
      dv_cache_0018
  have p0072 :=
    @gN3bitr4i
      (synWrex p (synCcup) (synWbr (.cv p) (synCtxp (synCcom (synC1st) (synC1st))
            (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
          (synCop (.cv a) (synCop (.cv b) (.cv z)))))
      (synWrex p (synCcup) (.classEq (.cv p) (synCop (synCop (.cv a) (.cv b)) (.cv z))))
      (.classMem (synCop (.cv a) (synCop (.cv b) (.cv z))) (synCima
          (synCtxp (synCcom (synC1st) (synC1st))
            (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCcup)))
      (.classMem (synCop (synCop (.cv a) (.cv b)) (.cv z)) (synCcup)) p0069 p0070 p0071
  have p0073 := (Nominal.biimpRefl (synWbr (synCop (.cv a) (.cv b)) (synCcup) (.cv z)))
  have p0074 := @gBrcup (.cv a) (.cv b) (.cv z) p0015 p0006
  have p0075 :=
    @gN3bitr2i
      (.classMem (synCop (.cv a) (synCop (.cv b) (.cv z))) (synCima
          (synCtxp (synCcom (synC1st) (synC1st))
            (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCcup)))
      (.classMem (synCop (synCop (.cv a) (.cv b)) (.cv z)) (synCcup))
      (synWbr (synCop (.cv a) (.cv b)) (synCcup) (.cv z))
      (.classEq (.cv z) (synCun (.cv a) (.cv b))) p0072 p0073 p0074
  have p0076 :=
    @gAnbi12i
      (.classMem (synCop (.cv a) (synCop (.cv b) (.cv z))) (synCins3 (synCdisj)))
      (.classEq (synCin (.cv a) (.cv b)) (synC0))
      (.classMem (synCop (.cv a) (synCop (.cv b) (.cv z))) (synCima
          (synCtxp (synCcom (synC1st) (synC1st))
            (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCcup)))
      (.classEq (.cv z) (synCun (.cv a) (.cv b))) p0025 p0075
  have p0077 :=
    @gBitri
      (.classMem (synCop (.cv a) (synCop (.cv b) (.cv z))) (synCin (synCins3 (synCdisj))
          (synCima (synCtxp (synCcom (synC1st) (synC1st))
              (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCcup))))
      (synWa (.classMem (synCop (.cv a) (synCop (.cv b) (.cv z))) (synCins3 (synCdisj)))
        (.classMem (synCop (.cv a) (synCop (.cv b) (.cv z))) (synCima
            (synCtxp (synCcom (synC1st) (synC1st))
              (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCcup))))
      (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
        (.classEq (.cv z) (synCun (.cv a) (.cv b))))
      p0021 p0076
  have p0078 :=
    @gN3bitri
      (.classMem (synCop (synCsn (.cv a))
          (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (.cv x)))) (synCins4 (synCsi3
            (synCin (synCins3 (synCdisj)) (synCima
                (synCtxp (synCcom (synC1st) (synC1st))
                  (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCcup))))))
      (.classMem (synCop (synCsn (.cv a)) (synCop (synCsn (.cv b)) (synCsn (.cv z))))
        (synCsi3 (synCin (synCins3 (synCdisj)) (synCima
              (synCtxp (synCcom (synC1st) (synC1st))
                (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCcup)))))
      (.classMem (synCop (.cv a) (synCop (.cv b) (.cv z))) (synCin (synCins3 (synCdisj))
          (synCima (synCtxp (synCcom (synC1st) (synC1st))
              (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCcup))))
      (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
        (.classEq (.cv z) (synCun (.cv a) (.cv b))))
      p0018 p0020 p0077
  have p0079 :=
    @gAnbi12i
      (.classMem (synCop (synCsn (.cv a))
          (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (.cv x))))
        (synCins2 (synCins2 (synCsset))))
      (.objMem a x)
      (.classMem (synCop (synCsn (.cv a))
          (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (.cv x)))) (synCins4 (synCsi3
            (synCin (synCins3 (synCdisj)) (synCima
                (synCtxp (synCcom (synC1st) (synC1st))
                  (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCcup))))))
      (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
        (.classEq (.cv z) (synCun (.cv a) (.cv b))))
      p0017 p0078
  have p0080 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv a))
          (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (.cv x))))
        (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
              (synCin (synCins3 (synCdisj)) (synCima
                  (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCcup)))))))
      (synWa (.classMem (synCop (synCsn (.cv a))
            (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (.cv x))))
          (synCins2 (synCins2 (synCsset)))) (.classMem (synCop (synCsn (.cv a))
            (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (.cv x)))) (synCins4
            (synCsi3 (synCin (synCins3 (synCdisj)) (synCima
                  (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCcup)))))))
      (synWa (.objMem a x) (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
          (.classEq (.cv z) (synCun (.cv a) (.cv b)))))
      p0011 p0079
  have p0081 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv a))
          (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (.cv x))))
        (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
              (synCin (synCins3 (synCdisj)) (synCima
                  (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCcup)))))))
      (synWa (.objMem a x) (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
          (.classEq (.cv z) (synCun (.cv a) (.cv b)))))
      a p0080
  have p0082 :=
    @gElima1c a (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (.cv x)))
      (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
            (synCin (synCins3 (synCdisj)) (synCima
                (synCtxp (synCcom (synC1st) (synC1st))
                  (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCcup))))))
      dv_cache_0020 dv_cache_0021
  have p0083 :=
    (Nominal.biimpRefl (synWrex a (.cv x) (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
          (.classEq (.cv z) (synCun (.cv a) (.cv b))))))
  have p0084_e02_recanon :
    Nominal.NPrf
      (synWb (synWrex a (.cv x) (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
            (.classEq (.cv z) (synCun (.cv a) (.cv b))))) (synWex a (synWa (.objMem a x)
            (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
              (.classEq (.cv z) (synCun (.cv a) (.cv b))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0083
  have p0084 :=
    @gN3bitr4i
      (synWex a (.classMem (synCop (synCsn (.cv a))
            (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (.cv x))))
          (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                (synCin (synCins3 (synCdisj)) (synCima
                    (synCtxp (synCcom (synC1st) (synC1st))
                      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCcup))))))))
      (synWex a (synWa (.objMem a x) (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
            (.classEq (.cv z) (synCun (.cv a) (.cv b))))))
      (.classMem (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (.cv x))) (synCima
          (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                (synCin (synCins3 (synCdisj)) (synCima
                    (synCtxp (synCcom (synC1st) (synC1st))
                      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCcup))))))
          (synC1c)))
      (synWrex a (.cv x) (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
          (.classEq (.cv z) (synCun (.cv a) (.cv b)))))
      p0081 p0082 p0084_e02_recanon
  have p0085 :=
    @gBitri
      (.classMem
        (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))
        (synCins4 (synCima (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                  (synCin (synCins3 (synCdisj)) (synCima
                      (synCtxp (synCcom (synC1st) (synC1st))
                        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCcup))))))
            (synC1c))))
      (.classMem (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (.cv x))) (synCima
          (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                (synCin (synCins3 (synCdisj)) (synCima
                    (synCtxp (synCcom (synC1st) (synC1st))
                      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCcup))))))
          (synC1c)))
      (synWrex a (.cv x) (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
          (.classEq (.cv z) (synCun (.cv a) (.cv b)))))
      p0010 p0084
  have p0086 :=
    @gAnbi12i
      (.classMem
        (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))
        (synCins2 (synCins2 (synCsset))))
      (.objMem b y)
      (.classMem
        (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))
        (synCins4 (synCima (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                  (synCin (synCins3 (synCdisj)) (synCima
                      (synCtxp (synCcom (synC1st) (synC1st))
                        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCcup))))))
            (synC1c))))
      (synWrex a (.cv x) (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
          (.classEq (.cv z) (synCun (.cv a) (.cv b)))))
      p0009 p0085
  have p0087 :=
    @gBitri
      (.classMem
        (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))
        (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCima
              (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                    (synCin (synCins3 (synCdisj)) (synCima
                        (synCtxp (synCcom (synC1st) (synC1st))
                          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                        (synCcup)))))) (synC1c)))))
      (synWa (.classMem (synCop (synCsn (.cv b))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))
          (synCins2 (synCins2 (synCsset)))) (.classMem (synCop (synCsn (.cv b))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))) (synCins4 (synCima
              (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                    (synCin (synCins3 (synCdisj)) (synCima
                        (synCtxp (synCcom (synC1st) (synC1st))
                          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                        (synCcup)))))) (synC1c)))))
      (synWa (.objMem b y) (synWrex a (.cv x)
          (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
            (.classEq (.cv z) (synCun (.cv a) (.cv b))))))
      p0001 p0086
  have p0088 :=
    @gExbii
      (.classMem
        (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))
        (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCima
              (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                    (synCin (synCins3 (synCdisj)) (synCima
                        (synCtxp (synCcom (synC1st) (synC1st))
                          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                        (synCcup)))))) (synC1c)))))
      (synWa (.objMem b y) (synWrex a (.cv x)
          (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
            (.classEq (.cv z) (synCun (.cv a) (.cv b))))))
      b p0087
  have p0089 :=
    @gElima1c b (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))
      (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCima
            (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                  (synCin (synCins3 (synCdisj)) (synCima
                      (synCtxp (synCcom (synC1st) (synC1st))
                        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCcup))))))
            (synC1c))))
      dv_cache_0022 dv_cache_0023
  have p0090 :=
    (Nominal.biimpRefl (synWrex b (.cv y) (synWrex a (.cv x)
          (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
            (.classEq (.cv z) (synCun (.cv a) (.cv b)))))))
  have p0091_e02_recanon :
    Nominal.NPrf
      (synWb (synWrex b (.cv y) (synWrex a (.cv x)
            (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
              (.classEq (.cv z) (synCun (.cv a) (.cv b)))))) (synWex b (synWa (.objMem b y)
            (synWrex a (.cv x) (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
                (.classEq (.cv z) (synCun (.cv a) (.cv b)))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0090
  have p0091 :=
    @gN3bitr4i
      (synWex b (.classMem (synCop (synCsn (.cv b))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))
          (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCima
                (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                      (synCin (synCins3 (synCdisj)) (synCima
                          (synCtxp (synCcom (synC1st) (synC1st))
                            (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                          (synCcup)))))) (synC1c))))))
      (synWex b (synWa (.objMem b y) (synWrex a (.cv x)
            (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
              (.classEq (.cv z) (synCun (.cv a) (.cv b)))))))
      (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))) (synCima
          (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCima
                (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                      (synCin (synCins3 (synCdisj)) (synCima
                          (synCtxp (synCcom (synC1st) (synC1st))
                            (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                          (synCcup)))))) (synC1c)))) (synC1c)))
      (synWrex b (.cv y) (synWrex a (.cv x)
          (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
            (.classEq (.cv z) (synCun (.cv a) (.cv b))))))
      p0088 p0089 p0091_e02_recanon
  have p0092 :=
    @gEladdc (.cv z) (.cv x) (.cv y) a b dv_cache_0024 dv_cache_0025 dv_cache_0026
      dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
  have p0093 :=
    @gRexcom
      (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
        (.classEq (.cv z) (synCun (.cv a) (.cv b))))
      a b (.cv x) (.cv y) dv_cache_0027 dv_cache_0028 dv_cache_0030
  have p0094 :=
    @gBitri (.classMem (.cv z) (synCplc (.cv x) (.cv y)))
      (synWrex a (.cv x) (synWrex b (.cv y)
          (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
            (.classEq (.cv z) (synCun (.cv a) (.cv b))))))
      (synWrex b (.cv y) (synWrex a (.cv x)
          (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
            (.classEq (.cv z) (synCun (.cv a) (.cv b))))))
      p0092 p0093
  have p0095 :=
    @gBitr4i
      (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))) (synCima
          (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCima
                (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                      (synCin (synCins3 (synCdisj)) (synCima
                          (synCtxp (synCcom (synC1st) (synC1st))
                            (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                          (synCcup)))))) (synC1c)))) (synC1c)))
      (synWrex b (.cv y) (synWrex a (.cv x)
          (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
            (.classEq (.cv z) (synCun (.cv a) (.cv b))))))
      (.classMem (.cv z) (synCplc (.cv x) (.cv y))) p0091 p0094
  have p0096 :=
    @gReleqmpt2 x y z (synCvv) (synCvv)
      (synCima (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCima
              (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                    (synCin (synCins3 (synCdisj)) (synCima
                        (synCtxp (synCcom (synC1st) (synC1st))
                          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                        (synCcup)))))) (synC1c)))) (synC1c))
      (synCplc (.cv x) (.cv y)) dv_cache_0031 dv_cache_0032 dv_cache_0031 dv_cache_0032
      dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0001 dv_cache_0037
      dv_cache_0038 p0095
  have p0097 :=
    @gEqtr4i (synCaddcfn) (synCmpt2 x (synCvv) y (synCvv) (synCplc (.cv x) (.cv y)))
      (synCdif (synCxp (synCxp (synCvv) (synCvv)) (synCvv)) (synCima
          (synCsymdif (synCins2 (synCsset)) (synCins3 (synCima
                (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCima
                      (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                            (synCin (synCins3 (synCdisj)) (synCima
                                (synCtxp (synCcom (synC1st) (synC1st))
                                  (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                                (synCcup)))))) (synC1c)))) (synC1c)))) (synC1c)))
      p0000 p0096
  have p0098 := @gVvex
  have p0100 := @gSsetex
  have p0101 := @gIns2ex (synCsset) p0100
  have p0102 := @gIns2ex (synCins2 (synCsset)) p0101
  have p0103 := @gDisjex
  have p0104 := @gIns3ex (synCdisj) p0103
  have p0105 := @gN1stex
  have p0107 := @gCoex (synC1st) (synC1st) p0105 p0105
  have p0108 := @gN2ndex
  have p0110 := @gCoex (synC2nd) (synC1st) p0108 p0105
  have p0112 := @gTxpex (synCcom (synC2nd) (synC1st)) (synC2nd) p0110 p0108
  have p0113 :=
    @gTxpex (synCcom (synC1st) (synC1st))
      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)) p0107 p0112
  have p0114 := @gCupex
  have p0115 :=
    @gImaex
      (synCtxp (synCcom (synC1st) (synC1st))
        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
      (synCcup) p0113 p0114
  have p0116 :=
    @gInex (synCins3 (synCdisj))
      (synCima (synCtxp (synCcom (synC1st) (synC1st))
          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCcup))
      p0104 p0115
  have p0117 :=
    @gSi3ex
      (synCin (synCins3 (synCdisj)) (synCima (synCtxp (synCcom (synC1st) (synC1st))
            (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCcup)))
      p0116
  have p0118 :=
    @gIns4ex
      (synCsi3 (synCin (synCins3 (synCdisj)) (synCima
            (synCtxp (synCcom (synC1st) (synC1st))
              (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCcup))))
      p0117
  have p0119 :=
    @gInex (synCins2 (synCins2 (synCsset)))
      (synCins4 (synCsi3 (synCin (synCins3 (synCdisj)) (synCima
              (synCtxp (synCcom (synC1st) (synC1st))
                (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCcup)))))
      p0102 p0118
  have p0120 := @gN1cex
  have p0121 :=
    @gImaex
      (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
            (synCin (synCins3 (synCdisj)) (synCima
                (synCtxp (synCcom (synC1st) (synC1st))
                  (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCcup))))))
      (synC1c) p0119 p0120
  have p0122 :=
    @gIns4ex
      (synCima (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
              (synCin (synCins3 (synCdisj)) (synCima
                  (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCcup))))))
        (synC1c))
      p0121
  have p0123 :=
    @gInex (synCins2 (synCins2 (synCsset)))
      (synCins4 (synCima (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                (synCin (synCins3 (synCdisj)) (synCima
                    (synCtxp (synCcom (synC1st) (synC1st))
                      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCcup))))))
          (synC1c)))
      p0102 p0122
  have p0125 :=
    @gImaex
      (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCima
            (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                  (synCin (synCins3 (synCdisj)) (synCima
                      (synCtxp (synCcom (synC1st) (synC1st))
                        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCcup))))))
            (synC1c))))
      (synC1c) p0123 p0120
  have p0126 :=
    @gMpt2exlem (synCvv) (synCvv)
      (synCima (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCima
              (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                    (synCin (synCins3 (synCdisj)) (synCima
                        (synCtxp (synCcom (synC1st) (synC1st))
                          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                        (synCcup)))))) (synC1c)))) (synC1c))
      p0098 p0098 p0125
  have p0127 :=
    @gEqeltri (synCaddcfn)
      (synCdif (synCxp (synCxp (synCvv) (synCvv)) (synCvv)) (synCima
          (synCsymdif (synCins2 (synCsset)) (synCins3 (synCima
                (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCima
                      (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                            (synCin (synCins3 (synCdisj)) (synCima
                                (synCtxp (synCcom (synC1st) (synC1st))
                                  (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                                (synCcup)))))) (synC1c)))) (synC1c)))) (synC1c)))
      (synCvv) p0097 p0126
  exact p0127


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part003`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_addcfn`. -/
@[expose]
noncomputable def gAddcfn : Nominal.NPrf (synWfn (synCaddcfn) (synCvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0002 : x ∉ ((synCvv)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((synCvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfAddcfn x y
      dv_cache_0001
  have p0001 := @gVex x
  have p0002 := @gVex y
  have p0003 := @gAddcex (.cv x) (.cv y) p0001 p0002
  have p0004 :=
    @gFnmpt2i x y (synCvv) (synCvv) (synCplc (.cv x) (.cv y)) (synCaddcfn)
      dv_cache_0002 dv_cache_0003 dv_cache_0002 dv_cache_0003 dv_cache_0001 p0000 p0003
  have p0005 := @gXpvv
  have p0006 := @gFneq2i (synCxp (synCvv) (synCvv)) (synCvv) (synCaddcfn) p0005
  have p0007 :=
    @gMpbi (synWfn (synCaddcfn) (synCxp (synCvv) (synCvv)))
      (synWfn (synCaddcfn) (synCvv)) p0004 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_braddcfn`. -/
@[expose]
noncomputable def gBraddcfn (A : Class) (B : Class) (C : Class)
    (hyp_braddcfn_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_braddcfn_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWb (synWbr (synCop A B) (synCaddcfn) C) (.classEq (synCplc A B) C)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
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
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0002 : x ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0004 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0005 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((synCvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((synCvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((synCplc A (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_y, or_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((synCplc A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          Finset.mem_union, fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((synCplc A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          Finset.mem_union, fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have p0000 := @gAddcfn
  have p0001 := @gOpex A B hyp_braddcfn_1 hyp_braddcfn_2
  have p0002 := @gFnbrfvb (synCvv) (synCop A B) C (synCaddcfn)
  have p0003 :=
    @gMp2an (synWfn (synCaddcfn) (synCvv)) (.classMem (synCop A B) (synCvv))
      (synWb (.classEq (synCfv (synCaddcfn) (synCop A B)) C)
        (synWbr (synCop A B) (synCaddcfn) C))
      p0000 p0001 p0002
  have p0004 := (Nominal.classEqRefl (synCo A (synCaddcfn) B))
  have p0005 := @gAddceq1 (.cv x) A (.cv y)
  have p0006 := @gAddceq2 (.cv y) B A
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfAddcfn x y
      dv_cache_0001
  have p0008 := @gAddcex A B hyp_braddcfn_1 hyp_braddcfn_2
  have p0009 :=
    @gOvmpt2 x y A B (synCvv) (synCvv) (synCplc (.cv x) (.cv y)) (synCplc A B)
      (synCaddcfn) (synCplc A (.cv y)) dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0001 p0005 p0006 p0007 p0008
  have p0010 :=
    @gMp2an (.classMem A (synCvv)) (.classMem B (synCvv))
      (.classEq (synCo A (synCaddcfn) B) (synCplc A B)) hyp_braddcfn_1 hyp_braddcfn_2
      p0009
  have p0011 :=
    @gEqtr3i (synCo A (synCaddcfn) B) (synCfv (synCaddcfn) (synCop A B))
      (synCplc A B) p0004 p0010
  have p0012 := @gEqeq1i (synCfv (synCaddcfn) (synCop A B)) (synCplc A B) C p0011
  have p0013 :=
    @gBitr3i (synWbr (synCop A B) (synCaddcfn) C)
      (.classEq (synCfv (synCaddcfn) (synCop A B)) C) (.classEq (synCplc A B) C) p0003
      p0012
  exact p0013


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part004`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_funsex`. -/
@[expose]
noncomputable def gFunsex : Nominal.NPrf (.classMem (synCfuns) (synCvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let f : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let z : Var := freshVar proofSupport 3
  let p : Var := freshVar proofSupport 4
  let q : Var := freshVar proofSupport 5
  have fresh_f_ne_x : f ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_f : x ≠ f := Ne.symm fresh_f_ne_x
  have fresh_f_ne_y : f ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_f : y ≠ f := Ne.symm fresh_f_ne_y
  have fresh_f_ne_z : f ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_z_ne_f : z ≠ f := Ne.symm fresh_f_ne_z
  have fresh_f_ne_p : f ≠ p :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_p_ne_f : p ≠ f := Ne.symm fresh_f_ne_p
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_x_ne_p : x ≠ p :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_p_ne_x : p ≠ x := Ne.symm fresh_x_ne_p
  have fresh_x_ne_q : x ≠ q :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_q_ne_x : q ≠ x := Ne.symm fresh_x_ne_q
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_y_ne_p : y ≠ p :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_p_ne_y : p ≠ y := Ne.symm fresh_y_ne_p
  have fresh_y_ne_q : y ≠ q :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_q_ne_y : q ≠ y := Ne.symm fresh_y_ne_q
  have fresh_p_ne_q : p ≠ q :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_q_ne_p : q ≠ p := Ne.symm fresh_p_ne_q
  have dv_cache_0001 : x ∉ ((Class.cv f)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_f, not_false_eq_true])
  have dv_cache_0002 :
    x ∉
      ((synCcompl (synCima (synCcompl (synCima (synCdif (synCins2 (synCima (synCin
                        (synCins4 (synCima (synCtxp (synCcnv (synC1st))
                              (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                        (synCins2 (synCins2 (synC2nd)))) (synCsset))) (synCins3 (synCid)))
                (synC1c))) (synC1c)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((synCop (synCsn (.cv x)) (.cv f))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_f, or_false, not_false_eq_true])
  have dv_cache_0004 :
    z ∉
      ((synCcompl (synCima (synCdif (synCins2 (synCima (synCin (synCins4 (synCima
                        (synCtxp (synCcnv (synC1st))
                          (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                    (synCins2 (synCins2 (synC2nd)))) (synCsset))) (synCins3 (synCid)))
            (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0005 :
    y ∉ ((synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv f)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_z, fresh_y_ne_x, fresh_y_ne_f, or_false,
          not_false_eq_true])
  have dv_cache_0006 :
    y ∉
      ((synCdif (synCins2 (synCima (synCin (synCins4 (synCima
                    (synCtxp (synCcnv (synC1st)) (synCsi3 (synCtxp (synC2nd) (synC1st))))
                    (synC1c))) (synCins2 (synCins2 (synC2nd)))) (synCsset)))
          (synCins3 (synCid)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 :
    q ∉ ((synCop (.cv p) (synCop (synCsn (.cv y)) (synCsn (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_p, fresh_q_ne_y, fresh_q_ne_x, or_false,
          not_false_eq_true])
  have dv_cache_0008 :
    q ∉
      ((synCtxp (synCcnv (synC1st)) (synCsi3 (synCtxp (synC2nd) (synC1st))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 : q ∉ ((synCop (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_x, fresh_q_ne_y, or_false, not_false_eq_true])
  have dv_cache_0010 :
    q ∉ ((synWbr (.cv p) (synC1st) (synCsn (synCop (.cv x) (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_p, fresh_q_ne_x, fresh_q_ne_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 :
    p ∉ ((synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv f)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_y, fresh_p_ne_x, fresh_p_ne_f, or_false,
          not_false_eq_true])
  have dv_cache_0012 :
    p ∉
      ((synCin (synCins4 (synCima
              (synCtxp (synCcnv (synC1st)) (synCsi3 (synCtxp (synC2nd) (synC1st))))
              (synC1c))) (synCins2 (synCins2 (synC2nd))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0013 : p ∉ ((synCsset)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0014 : p ∉ ((synCop (synCsn (synCop (.cv x) (.cv y))) (.cv f))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_y, fresh_p_ne_f, or_false,
          not_false_eq_true])
  have dv_cache_0015 : y ∉ ((Class.cv f)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_f, not_false_eq_true])
  have dv_cache_0016 : z ∉ ((Class.cv f)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_f, not_false_eq_true])
  have dv_cache_0017 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0018 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0019 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0020 :
    f ∉
      ((synCcompl (synCima (synCcompl (synCima (synCcompl (synCima (synCdif (synCins2
                        (synCima (synCin (synCins4 (synCima (synCtxp (synCcnv (synC1st))
                                  (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                            (synCins2 (synCins2 (synC2nd)))) (synCsset)))
                      (synCins3 (synCid))) (synC1c))) (synC1c))) (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFuns f
  have p0001 :=
    @gElima1c x (.cv f)
      (synCcompl (synCima (synCcompl (synCima (synCdif (synCins2 (synCima (synCin
                      (synCins4 (synCima (synCtxp (synCcnv (synC1st))
                            (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                      (synCins2 (synCins2 (synC2nd)))) (synCsset))) (synCins3 (synCid)))
              (synC1c))) (synC1c)))
      dv_cache_0001 dv_cache_0002
  have p0002 := @gSnex (.cv x)
  have p0003 := @gVex f
  have p0004 := @gOpex (synCsn (.cv x)) (.cv f) p0002 p0003
  have p0005 :=
    @gElcompl (synCop (synCsn (.cv x)) (.cv f))
      (synCima (synCcompl (synCima (synCdif (synCins2 (synCima (synCin (synCins4
                      (synCima (synCtxp (synCcnv (synC1st))
                          (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                    (synCins2 (synCins2 (synC2nd)))) (synCsset))) (synCins3 (synCid)))
            (synC1c))) (synC1c))
      p0004
  have p0006 :=
    @gElima1c z (synCop (synCsn (.cv x)) (.cv f))
      (synCcompl (synCima (synCdif (synCins2 (synCima (synCin (synCins4 (synCima
                      (synCtxp (synCcnv (synC1st))
                        (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                  (synCins2 (synCins2 (synC2nd)))) (synCsset))) (synCins3 (synCid)))
          (synC1c)))
      dv_cache_0003 dv_cache_0004
  have p0007 :=
    @gElima1c y (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv f)))
      (synCdif (synCins2 (synCima (synCin (synCins4 (synCima
                  (synCtxp (synCcnv (synC1st)) (synCsi3 (synCtxp (synC2nd) (synC1st))))
                  (synC1c))) (synCins2 (synCins2 (synC2nd)))) (synCsset)))
        (synCins3 (synCid)))
      dv_cache_0005 dv_cache_0006
  have p0008 :=
    @gEldif
      (synCop (synCsn (.cv y))
        (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv f))))
      (synCins2 (synCima (synCin (synCins4 (synCima (synCtxp (synCcnv (synC1st))
                  (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
            (synCins2 (synCins2 (synC2nd)))) (synCsset)))
      (synCins3 (synCid))
  have p0009 := @gSnex (.cv z)
  have p0010 :=
    @gOtelins2 (synCsn (.cv y)) (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv f))
      (synCima (synCin (synCins4 (synCima
              (synCtxp (synCcnv (synC1st)) (synCsi3 (synCtxp (synC2nd) (synC1st))))
              (synC1c))) (synCins2 (synCins2 (synC2nd)))) (synCsset))
      p0009
  have p0011 := @gVex x
  have p0012 := @gVex y
  have p0013 := @gOpex (.cv x) (.cv y) p0011 p0012
  have p0014 := @gOpelssetsn (synCop (.cv x) (.cv y)) (.cv f) p0013 p0003
  have p0015 :=
    (Nominal.biimpRefl (synWbr (.cv p) (synCin (synCins4 (synCima
              (synCtxp (synCcnv (synC1st)) (synCsi3 (synCtxp (synC2nd) (synC1st))))
              (synC1c))) (synCins2 (synCins2 (synC2nd))))
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv f)))))
  have p0016 :=
    @gElin
      (synCop (.cv p) (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv f))))
      (synCins4 (synCima
          (synCtxp (synCcnv (synC1st)) (synCsi3 (synCtxp (synC2nd) (synC1st))))
          (synC1c)))
      (synCins2 (synCins2 (synC2nd)))
  have p0017 :=
    @gOqelins4 (.cv p) (synCsn (.cv y)) (synCsn (.cv x)) (.cv f)
      (synCima (synCtxp (synCcnv (synC1st)) (synCsi3 (synCtxp (synC2nd) (synC1st))))
        (synC1c))
      p0003
  have p0018 :=
    @gElima1c q (synCop (.cv p) (synCop (synCsn (.cv y)) (synCsn (.cv x))))
      (synCtxp (synCcnv (synC1st)) (synCsi3 (synCtxp (synC2nd) (synC1st))))
      dv_cache_0007 dv_cache_0008
  have p0019 :=
    @gOteltxp (synCsn (.cv q)) (.cv p) (synCop (synCsn (.cv y)) (synCsn (.cv x)))
      (synCcnv (synC1st)) (synCsi3 (synCtxp (synC2nd) (synC1st)))
  have p0020 := @gOpelcnv (synCsn (.cv q)) (.cv p) (synC1st)
  have p0021 := (Nominal.biimpRefl (synWbr (.cv p) (synC1st) (synCsn (.cv q))))
  have p0022 :=
    @gBitr4i (.classMem (synCop (synCsn (.cv q)) (.cv p)) (synCcnv (synC1st)))
      (.classMem (synCop (.cv p) (synCsn (.cv q))) (synC1st))
      (synWbr (.cv p) (synC1st) (synCsn (.cv q))) p0020 p0021
  have p0023 := @gVex q
  have p0024 :=
    @gOtsnelsi3 (.cv q) (.cv y) (.cv x) (synCtxp (synC2nd) (synC1st)) p0023 p0012
      p0011
  have p0025 := @gOteltxp (.cv q) (.cv y) (.cv x) (synC2nd) (synC1st)
  have p0026 := (Nominal.biimpRefl (synWbr (.cv q) (synC1st) (.cv x)))
  have p0027 := (Nominal.biimpRefl (synWbr (.cv q) (synC2nd) (.cv y)))
  have p0028 :=
    @gAnbi12i (synWbr (.cv q) (synC1st) (.cv x))
      (.classMem (synCop (.cv q) (.cv x)) (synC1st))
      (synWbr (.cv q) (synC2nd) (.cv y))
      (.classMem (synCop (.cv q) (.cv y)) (synC2nd)) p0026 p0027
  have p0029 :=
    @gAncom (.classMem (synCop (.cv q) (.cv x)) (synC1st))
      (.classMem (synCop (.cv q) (.cv y)) (synC2nd))
  have p0030 :=
    @gBitr2i
      (synWa (synWbr (.cv q) (synC1st) (.cv x)) (synWbr (.cv q) (synC2nd) (.cv y)))
      (synWa (.classMem (synCop (.cv q) (.cv x)) (synC1st))
        (.classMem (synCop (.cv q) (.cv y)) (synC2nd)))
      (synWa (.classMem (synCop (.cv q) (.cv y)) (synC2nd))
        (.classMem (synCop (.cv q) (.cv x)) (synC1st)))
      p0028 p0029
  have p0031 := @gOp1st2nd (.cv x) (.cv y) (.cv q) p0011 p0012
  have p0032 :=
    @gN3bitri
      (.classMem (synCop (.cv q) (synCop (.cv y) (.cv x))) (synCtxp (synC2nd) (synC1st)))
      (synWa (.classMem (synCop (.cv q) (.cv y)) (synC2nd))
        (.classMem (synCop (.cv q) (.cv x)) (synC1st)))
      (synWa (synWbr (.cv q) (synC1st) (.cv x)) (synWbr (.cv q) (synC2nd) (.cv y)))
      (.classEq (.cv q) (synCop (.cv x) (.cv y))) p0025 p0030 p0031
  have p0033 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv q)) (synCop (synCsn (.cv y)) (synCsn (.cv x))))
        (synCsi3 (synCtxp (synC2nd) (synC1st))))
      (.classMem (synCop (.cv q) (synCop (.cv y) (.cv x))) (synCtxp (synC2nd) (synC1st)))
      (.classEq (.cv q) (synCop (.cv x) (.cv y))) p0024 p0032
  have p0034 :=
    @gAnbi12ci (.classMem (synCop (synCsn (.cv q)) (.cv p)) (synCcnv (synC1st)))
      (synWbr (.cv p) (synC1st) (synCsn (.cv q)))
      (.classMem (synCop (synCsn (.cv q)) (synCop (synCsn (.cv y)) (synCsn (.cv x))))
        (synCsi3 (synCtxp (synC2nd) (synC1st))))
      (.classEq (.cv q) (synCop (.cv x) (.cv y))) p0022 p0033
  have p0035 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv q))
          (synCop (.cv p) (synCop (synCsn (.cv y)) (synCsn (.cv x)))))
        (synCtxp (synCcnv (synC1st)) (synCsi3 (synCtxp (synC2nd) (synC1st)))))
      (synWa (.classMem (synCop (synCsn (.cv q)) (.cv p)) (synCcnv (synC1st))) (.classMem
          (synCop (synCsn (.cv q)) (synCop (synCsn (.cv y)) (synCsn (.cv x))))
          (synCsi3 (synCtxp (synC2nd) (synC1st)))))
      (synWa (.classEq (.cv q) (synCop (.cv x) (.cv y)))
        (synWbr (.cv p) (synC1st) (synCsn (.cv q))))
      p0019 p0034
  have p0036 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv q))
          (synCop (.cv p) (synCop (synCsn (.cv y)) (synCsn (.cv x)))))
        (synCtxp (synCcnv (synC1st)) (synCsi3 (synCtxp (synC2nd) (synC1st)))))
      (synWa (.classEq (.cv q) (synCop (.cv x) (.cv y)))
        (synWbr (.cv p) (synC1st) (synCsn (.cv q))))
      q p0035
  have p0037 := @gSneq (.cv q) (synCop (.cv x) (.cv y))
  have p0038 :=
    @gBreq2d (.classEq (.cv q) (synCop (.cv x) (.cv y))) (synCsn (.cv q))
      (synCsn (synCop (.cv x) (.cv y))) (.cv p) (synC1st) p0037
  have p0039 :=
    @gCeqsexv (synWbr (.cv p) (synC1st) (synCsn (.cv q)))
      (synWbr (.cv p) (synC1st) (synCsn (synCop (.cv x) (.cv y)))) q
      (synCop (.cv x) (.cv y)) dv_cache_0009 dv_cache_0010 p0013 p0038
  have p0040 :=
    @gN3bitri
      (.classMem (synCop (.cv p) (synCop (synCsn (.cv y)) (synCsn (.cv x)))) (synCima
          (synCtxp (synCcnv (synC1st)) (synCsi3 (synCtxp (synC2nd) (synC1st))))
          (synC1c)))
      (synWex q (.classMem (synCop (synCsn (.cv q))
            (synCop (.cv p) (synCop (synCsn (.cv y)) (synCsn (.cv x)))))
          (synCtxp (synCcnv (synC1st)) (synCsi3 (synCtxp (synC2nd) (synC1st))))))
      (synWex q (synWa (.classEq (.cv q) (synCop (.cv x) (.cv y)))
          (synWbr (.cv p) (synC1st) (synCsn (.cv q)))))
      (synWbr (.cv p) (synC1st) (synCsn (synCop (.cv x) (.cv y)))) p0018 p0036 p0039
  have p0041 :=
    @gBitri
      (.classMem
        (synCop (.cv p) (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv f))))
        (synCins4 (synCima
            (synCtxp (synCcnv (synC1st)) (synCsi3 (synCtxp (synC2nd) (synC1st))))
            (synC1c))))
      (.classMem (synCop (.cv p) (synCop (synCsn (.cv y)) (synCsn (.cv x)))) (synCima
          (synCtxp (synCcnv (synC1st)) (synCsi3 (synCtxp (synC2nd) (synC1st))))
          (synC1c)))
      (synWbr (.cv p) (synC1st) (synCsn (synCop (.cv x) (.cv y)))) p0017 p0040
  have p0042 := @gOtelins2 (.cv p) (synCsn (.cv x)) (.cv f) (synC2nd) p0002
  have p0043 := @gSnex (.cv y)
  have p0044 :=
    @gOtelins2 (.cv p) (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv f))
      (synCins2 (synC2nd)) p0043
  have p0045 := (Nominal.biimpRefl (synWbr (.cv p) (synC2nd) (.cv f)))
  have p0046 :=
    @gN3bitr4i
      (.classMem (synCop (.cv p) (synCop (synCsn (.cv x)) (.cv f))) (synCins2 (synC2nd)))
      (.classMem (synCop (.cv p) (.cv f)) (synC2nd))
      (.classMem
        (synCop (.cv p) (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv f))))
        (synCins2 (synCins2 (synC2nd))))
      (synWbr (.cv p) (synC2nd) (.cv f)) p0042 p0044 p0045
  have p0047 :=
    @gAnbi12i
      (.classMem
        (synCop (.cv p) (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv f))))
        (synCins4 (synCima
            (synCtxp (synCcnv (synC1st)) (synCsi3 (synCtxp (synC2nd) (synC1st))))
            (synC1c))))
      (synWbr (.cv p) (synC1st) (synCsn (synCop (.cv x) (.cv y))))
      (.classMem
        (synCop (.cv p) (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv f))))
        (synCins2 (synCins2 (synC2nd))))
      (synWbr (.cv p) (synC2nd) (.cv f)) p0041 p0046
  have p0048 :=
    @gBitri
      (.classMem
        (synCop (.cv p) (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv f))))
        (synCin (synCins4 (synCima
              (synCtxp (synCcnv (synC1st)) (synCsi3 (synCtxp (synC2nd) (synC1st))))
              (synC1c))) (synCins2 (synCins2 (synC2nd)))))
      (synWa (.classMem (synCop (.cv p)
            (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv f)))) (synCins4
            (synCima
              (synCtxp (synCcnv (synC1st)) (synCsi3 (synCtxp (synC2nd) (synC1st))))
              (synC1c)))) (.classMem (synCop (.cv p)
            (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv f))))
          (synCins2 (synCins2 (synC2nd)))))
      (synWa (synWbr (.cv p) (synC1st) (synCsn (synCop (.cv x) (.cv y))))
        (synWbr (.cv p) (synC2nd) (.cv f)))
      p0016 p0047
  have p0049 := @gSnex (synCop (.cv x) (.cv y))
  have p0050 :=
    @gOp1st2nd (synCsn (synCop (.cv x) (.cv y))) (.cv f) (.cv p) p0049 p0003
  have p0051 :=
    @gN3bitri
      (synWbr (.cv p) (synCin (synCins4 (synCima
              (synCtxp (synCcnv (synC1st)) (synCsi3 (synCtxp (synC2nd) (synC1st))))
              (synC1c))) (synCins2 (synCins2 (synC2nd))))
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv f))))
      (.classMem
        (synCop (.cv p) (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv f))))
        (synCin (synCins4 (synCima
              (synCtxp (synCcnv (synC1st)) (synCsi3 (synCtxp (synC2nd) (synC1st))))
              (synC1c))) (synCins2 (synCins2 (synC2nd)))))
      (synWa (synWbr (.cv p) (synC1st) (synCsn (synCop (.cv x) (.cv y))))
        (synWbr (.cv p) (synC2nd) (.cv f)))
      (.classEq (.cv p) (synCop (synCsn (synCop (.cv x) (.cv y))) (.cv f))) p0015 p0048
      p0050
  have p0052 :=
    @gRexbii
      (synWbr (.cv p) (synCin (synCins4 (synCima
              (synCtxp (synCcnv (synC1st)) (synCsi3 (synCtxp (synC2nd) (synC1st))))
              (synC1c))) (synCins2 (synCins2 (synC2nd))))
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv f))))
      (.classEq (.cv p) (synCop (synCsn (synCop (.cv x) (.cv y))) (.cv f))) p
      (synCsset) p0051
  have p0053 :=
    @gElima p (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv f)))
      (synCin (synCins4 (synCima
            (synCtxp (synCcnv (synC1st)) (synCsi3 (synCtxp (synC2nd) (synC1st))))
            (synC1c))) (synCins2 (synCins2 (synC2nd))))
      (synCsset) dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0054 :=
    @gRisset p (synCop (synCsn (synCop (.cv x) (.cv y))) (.cv f)) (synCsset)
      dv_cache_0014 dv_cache_0013
  have p0055 :=
    @gN3bitr4i
      (synWrex p (synCsset) (synWbr (.cv p) (synCin (synCins4 (synCima
                (synCtxp (synCcnv (synC1st)) (synCsi3 (synCtxp (synC2nd) (synC1st))))
                (synC1c))) (synCins2 (synCins2 (synC2nd))))
          (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv f)))))
      (synWrex p (synCsset)
        (.classEq (.cv p) (synCop (synCsn (synCop (.cv x) (.cv y))) (.cv f))))
      (.classMem (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv f))) (synCima
          (synCin (synCins4 (synCima (synCtxp (synCcnv (synC1st))
                  (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
            (synCins2 (synCins2 (synC2nd)))) (synCsset)))
      (.classMem (synCop (synCsn (synCop (.cv x) (.cv y))) (.cv f)) (synCsset)) p0052
      p0053 p0054
  have p0056 := (Nominal.biimpRefl (synWbr (.cv x) (.cv f) (.cv y)))
  have p0057 :=
    @gN3bitr4i
      (.classMem (synCop (synCsn (synCop (.cv x) (.cv y))) (.cv f)) (synCsset))
      (.classMem (synCop (.cv x) (.cv y)) (.cv f))
      (.classMem (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv f))) (synCima
          (synCin (synCins4 (synCima (synCtxp (synCcnv (synC1st))
                  (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
            (synCins2 (synCins2 (synC2nd)))) (synCsset)))
      (synWbr (.cv x) (.cv f) (.cv y)) p0014 p0055 p0056
  have p0058 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv y))
          (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv f)))) (synCins2 (synCima
            (synCin (synCins4 (synCima (synCtxp (synCcnv (synC1st))
                    (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
              (synCins2 (synCins2 (synC2nd)))) (synCsset))))
      (.classMem (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv f))) (synCima
          (synCin (synCins4 (synCima (synCtxp (synCcnv (synC1st))
                  (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
            (synCins2 (synCins2 (synC2nd)))) (synCsset)))
      (synWbr (.cv x) (.cv f) (.cv y)) p0010 p0057
  have p0059 :=
    @gOtelins3 (synCsn (.cv y)) (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv f))
      (synCid) p0004
  have p0060 := @gIdeq (synCsn (.cv y)) (synCsn (.cv z)) p0009
  have p0061 :=
    (Nominal.biimpRefl (synWbr (synCsn (.cv y)) (synCid) (synCsn (.cv z))))
  have p0062 := @gSneqb (.cv y) (.cv z) p0012
  have p0063_e02_recanon :
    Nominal.NPrf (synWb (.classEq (synCsn (.cv y)) (synCsn (.cv z))) (.objEq y z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0062
  have p0063 :=
    @gN3bitr3i (synWbr (synCsn (.cv y)) (synCid) (synCsn (.cv z)))
      (.classEq (synCsn (.cv y)) (synCsn (.cv z)))
      (.classMem (synCop (synCsn (.cv y)) (synCsn (.cv z))) (synCid)) (.objEq y z)
      p0060 p0061 p0063_e02_recanon
  have p0064 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv y))
          (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv f))))
        (synCins3 (synCid)))
      (.classMem (synCop (synCsn (.cv y)) (synCsn (.cv z))) (synCid)) (.objEq y z)
      p0059 p0063
  have p0065 :=
    @gNotbii
      (.classMem (synCop (synCsn (.cv y))
          (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv f))))
        (synCins3 (synCid)))
      (.objEq y z) p0064
  have p0066 :=
    @gAnbi12i
      (.classMem (synCop (synCsn (.cv y))
          (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv f)))) (synCins2 (synCima
            (synCin (synCins4 (synCima (synCtxp (synCcnv (synC1st))
                    (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
              (synCins2 (synCins2 (synC2nd)))) (synCsset))))
      (synWbr (.cv x) (.cv f) (.cv y))
      (.neg (.classMem (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv f))))
          (synCins3 (synCid))))
      (.neg (.objEq y z)) p0058 p0065
  have p0067 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv y))
          (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv f)))) (synCdif (synCins2
            (synCima (synCin (synCins4 (synCima (synCtxp (synCcnv (synC1st))
                      (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                (synCins2 (synCins2 (synC2nd)))) (synCsset))) (synCins3 (synCid))))
      (synWa (.classMem (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv f)))) (synCins2
            (synCima (synCin (synCins4 (synCima (synCtxp (synCcnv (synC1st))
                      (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                (synCins2 (synCins2 (synC2nd)))) (synCsset)))) (.neg (.classMem
            (synCop (synCsn (.cv y))
              (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv f))))
            (synCins3 (synCid)))))
      (synWa (synWbr (.cv x) (.cv f) (.cv y)) (.neg (.objEq y z))) p0008 p0066
  have p0068 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv y))
          (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv f)))) (synCdif (synCins2
            (synCima (synCin (synCins4 (synCima (synCtxp (synCcnv (synC1st))
                      (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                (synCins2 (synCins2 (synC2nd)))) (synCsset))) (synCins3 (synCid))))
      (synWa (synWbr (.cv x) (.cv f) (.cv y)) (.neg (.objEq y z))) y p0067
  have p0069 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv f))) (synCima
          (synCdif (synCins2 (synCima (synCin (synCins4 (synCima
                      (synCtxp (synCcnv (synC1st))
                        (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                  (synCins2 (synCins2 (synC2nd)))) (synCsset))) (synCins3 (synCid)))
          (synC1c)))
      (synWex y (.classMem (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv f)))) (synCdif
            (synCins2 (synCima (synCin (synCins4 (synCima (synCtxp (synCcnv (synC1st))
                        (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                  (synCins2 (synCins2 (synC2nd)))) (synCsset))) (synCins3 (synCid)))))
      (synWex y (synWa (synWbr (.cv x) (.cv f) (.cv y)) (.neg (.objEq y z)))) p0007
      p0068
  have p0070 :=
    @gNotbii
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv f))) (synCima
          (synCdif (synCins2 (synCima (synCin (synCins4 (synCima
                      (synCtxp (synCcnv (synC1st))
                        (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                  (synCins2 (synCins2 (synC2nd)))) (synCsset))) (synCins3 (synCid)))
          (synC1c)))
      (synWex y (synWa (synWbr (.cv x) (.cv f) (.cv y)) (.neg (.objEq y z)))) p0069
  have p0071 := @gOpex (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv f)) p0009 p0004
  have p0072 :=
    @gElcompl (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv f)))
      (synCima (synCdif (synCins2 (synCima (synCin (synCins4 (synCima
                    (synCtxp (synCcnv (synC1st)) (synCsi3 (synCtxp (synC2nd) (synC1st))))
                    (synC1c))) (synCins2 (synCins2 (synC2nd)))) (synCsset)))
          (synCins3 (synCid))) (synC1c))
      p0071
  have p0073 := @gExanali (synWbr (.cv x) (.cv f) (.cv y)) (.objEq y z) y
  have p0074 :=
    @gCon2bii (synWex y (synWa (synWbr (.cv x) (.cv f) (.cv y)) (.neg (.objEq y z))))
      (.all y (.imp (synWbr (.cv x) (.cv f) (.cv y)) (.objEq y z))) p0073
  have p0075 :=
    @gN3bitr4i
      (.neg (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv f))) (synCima
            (synCdif (synCins2 (synCima (synCin (synCins4 (synCima
                        (synCtxp (synCcnv (synC1st))
                          (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                    (synCins2 (synCins2 (synC2nd)))) (synCsset))) (synCins3 (synCid)))
            (synC1c))))
      (.neg (synWex y (synWa (synWbr (.cv x) (.cv f) (.cv y)) (.neg (.objEq y z)))))
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv f))) (synCcompl
          (synCima (synCdif (synCins2 (synCima (synCin (synCins4 (synCima
                        (synCtxp (synCcnv (synC1st))
                          (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                    (synCins2 (synCins2 (synC2nd)))) (synCsset))) (synCins3 (synCid)))
            (synC1c))))
      (.all y (.imp (synWbr (.cv x) (.cv f) (.cv y)) (.objEq y z))) p0070 p0072 p0074
  have p0076 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv f))) (synCcompl
          (synCima (synCdif (synCins2 (synCima (synCin (synCins4 (synCima
                        (synCtxp (synCcnv (synC1st))
                          (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                    (synCins2 (synCins2 (synC2nd)))) (synCsset))) (synCins3 (synCid)))
            (synC1c))))
      (.all y (.imp (synWbr (.cv x) (.cv f) (.cv y)) (.objEq y z))) z p0075
  have p0077 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv x)) (.cv f)) (synCima (synCcompl (synCima (synCdif
                (synCins2 (synCima (synCin (synCins4 (synCima
                          (synCtxp (synCcnv (synC1st))
                            (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                      (synCins2 (synCins2 (synC2nd)))) (synCsset))) (synCins3 (synCid)))
              (synC1c))) (synC1c)))
      (synWex z (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv x)) (.cv f)))
          (synCcompl (synCima (synCdif (synCins2 (synCima (synCin (synCins4 (synCima
                          (synCtxp (synCcnv (synC1st))
                            (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                      (synCins2 (synCins2 (synC2nd)))) (synCsset))) (synCins3 (synCid)))
              (synC1c)))))
      (synWex z (.all y (.imp (synWbr (.cv x) (.cv f) (.cv y)) (.objEq y z)))) p0006
      p0076
  have p0078 :=
    @gNotbii
      (.classMem (synCop (synCsn (.cv x)) (.cv f)) (synCima (synCcompl (synCima (synCdif
                (synCins2 (synCima (synCin (synCins4 (synCima
                          (synCtxp (synCcnv (synC1st))
                            (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                      (synCins2 (synCins2 (synC2nd)))) (synCsset))) (synCins3 (synCid)))
              (synC1c))) (synC1c)))
      (synWex z (.all y (.imp (synWbr (.cv x) (.cv f) (.cv y)) (.objEq y z)))) p0077
  have p0079 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv x)) (.cv f)) (synCcompl (synCima (synCcompl (synCima
                (synCdif (synCins2 (synCima (synCin (synCins4 (synCima
                            (synCtxp (synCcnv (synC1st))
                              (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                        (synCins2 (synCins2 (synC2nd)))) (synCsset))) (synCins3 (synCid)))
                (synC1c))) (synC1c))))
      (.neg (.classMem (synCop (synCsn (.cv x)) (.cv f)) (synCima (synCcompl (synCima
                (synCdif (synCins2 (synCima (synCin (synCins4 (synCima
                            (synCtxp (synCcnv (synC1st))
                              (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                        (synCins2 (synCins2 (synC2nd)))) (synCsset))) (synCins3 (synCid)))
                (synC1c))) (synC1c))))
      (.neg (synWex z (.all y (.imp (synWbr (.cv x) (.cv f) (.cv y)) (.objEq y z)))))
      p0005 p0078
  have p0080 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv x)) (.cv f)) (synCcompl (synCima (synCcompl (synCima
                (synCdif (synCins2 (synCima (synCin (synCins4 (synCima
                            (synCtxp (synCcnv (synC1st))
                              (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                        (synCins2 (synCins2 (synC2nd)))) (synCsset))) (synCins3 (synCid)))
                (synC1c))) (synC1c))))
      (.neg (synWex z (.all y (.imp (synWbr (.cv x) (.cv f) (.cv y)) (.objEq y z))))) x
      p0079
  have p0081 :=
    @gBitri
      (.classMem (.cv f) (synCima (synCcompl (synCima (synCcompl (synCima (synCdif
                    (synCins2 (synCima (synCin (synCins4 (synCima
                              (synCtxp (synCcnv (synC1st))
                                (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                          (synCins2 (synCins2 (synC2nd)))) (synCsset)))
                    (synCins3 (synCid))) (synC1c))) (synC1c))) (synC1c)))
      (synWex x (.classMem (synCop (synCsn (.cv x)) (.cv f)) (synCcompl (synCima
              (synCcompl (synCima (synCdif (synCins2 (synCima (synCin (synCins4 (synCima
                              (synCtxp (synCcnv (synC1st))
                                (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                          (synCins2 (synCins2 (synC2nd)))) (synCsset)))
                    (synCins3 (synCid))) (synC1c))) (synC1c)))))
      (synWex x
        (.neg (synWex z (.all y (.imp (synWbr (.cv x) (.cv f) (.cv y)) (.objEq y z))))))
      p0001 p0080
  have p0082 :=
    @gNotbii
      (.classMem (.cv f) (synCima (synCcompl (synCima (synCcompl (synCima (synCdif
                    (synCins2 (synCima (synCin (synCins4 (synCima
                              (synCtxp (synCcnv (synC1st))
                                (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                          (synCins2 (synCins2 (synC2nd)))) (synCsset)))
                    (synCins3 (synCid))) (synC1c))) (synC1c))) (synC1c)))
      (synWex x
        (.neg (synWex z (.all y (.imp (synWbr (.cv x) (.cv f) (.cv y)) (.objEq y z))))))
      p0081
  have p0083 :=
    @gElcompl (.cv f)
      (synCima (synCcompl (synCima (synCcompl (synCima (synCdif (synCins2 (synCima
                      (synCin (synCins4 (synCima (synCtxp (synCcnv (synC1st))
                              (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                        (synCins2 (synCins2 (synC2nd)))) (synCsset))) (synCins3 (synCid)))
                (synC1c))) (synC1c))) (synC1c))
      p0003
  have p0084 :=
    @gAlex (synWex z (.all y (.imp (synWbr (.cv x) (.cv f) (.cv y)) (.objEq y z)))) x
  have p0085 :=
    @gN3bitr4i
      (.neg (.classMem (.cv f) (synCima (synCcompl (synCima (synCcompl (synCima (synCdif
                      (synCins2 (synCima (synCin (synCins4 (synCima
                                (synCtxp (synCcnv (synC1st))
                                  (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                            (synCins2 (synCins2 (synC2nd)))) (synCsset)))
                      (synCins3 (synCid))) (synC1c))) (synC1c))) (synC1c))))
      (.neg (synWex x (.neg
            (synWex z (.all y (.imp (synWbr (.cv x) (.cv f) (.cv y)) (.objEq y z)))))))
      (.classMem (.cv f) (synCcompl (synCima (synCcompl (synCima (synCcompl (synCima
                    (synCdif (synCins2 (synCima (synCin (synCins4 (synCima
                                (synCtxp (synCcnv (synC1st))
                                  (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                            (synCins2 (synCins2 (synC2nd)))) (synCsset)))
                      (synCins3 (synCid))) (synC1c))) (synC1c))) (synC1c))))
      (.all x (synWex z (.all y (.imp (synWbr (.cv x) (.cv f) (.cv y)) (.objEq y z)))))
      p0082 p0083 p0084
  have p0086 :=
    @gDffun3 x y z (.cv f) dv_cache_0001 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
  have p0087 :=
    @gBitr4i
      (.classMem (.cv f) (synCcompl (synCima (synCcompl (synCima (synCcompl (synCima
                    (synCdif (synCins2 (synCima (synCin (synCins4 (synCima
                                (synCtxp (synCcnv (synC1st))
                                  (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                            (synCins2 (synCins2 (synC2nd)))) (synCsset)))
                      (synCins3 (synCid))) (synC1c))) (synC1c))) (synC1c))))
      (.all x (synWex z (.all y (.imp (synWbr (.cv x) (.cv f) (.cv y)) (.objEq y z)))))
      (synWfun (.cv f)) p0085 p0086
  have p0088 :=
    @gEqabi (synWfun (.cv f)) f
      (synCcompl (synCima (synCcompl (synCima (synCcompl (synCima (synCdif (synCins2
                      (synCima (synCin (synCins4 (synCima (synCtxp (synCcnv (synC1st))
                                (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                          (synCins2 (synCins2 (synC2nd)))) (synCsset)))
                    (synCins3 (synCid))) (synC1c))) (synC1c))) (synC1c)))
      dv_cache_0020 p0087
  have p0089 :=
    @gEqtr4i (synCfuns) (.cab f (synWfun (.cv f)))
      (synCcompl (synCima (synCcompl (synCima (synCcompl (synCima (synCdif (synCins2
                      (synCima (synCin (synCins4 (synCima (synCtxp (synCcnv (synC1st))
                                (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                          (synCins2 (synCins2 (synC2nd)))) (synCsset)))
                    (synCins3 (synCid))) (synC1c))) (synC1c))) (synC1c)))
      p0000 p0088
  have p0090 := @gN1stex
  have p0091 := @gCnvex (synC1st) p0090
  have p0092 := @gN2ndex
  have p0094 := @gTxpex (synC2nd) (synC1st) p0092 p0090
  have p0095 := @gSi3ex (synCtxp (synC2nd) (synC1st)) p0094
  have p0096 :=
    @gTxpex (synCcnv (synC1st)) (synCsi3 (synCtxp (synC2nd) (synC1st))) p0091 p0095
  have p0097 := @gN1cex
  have p0098 :=
    @gImaex (synCtxp (synCcnv (synC1st)) (synCsi3 (synCtxp (synC2nd) (synC1st))))
      (synC1c) p0096 p0097
  have p0099 :=
    @gIns4ex
      (synCima (synCtxp (synCcnv (synC1st)) (synCsi3 (synCtxp (synC2nd) (synC1st))))
        (synC1c))
      p0098
  have p0101 := @gIns2ex (synC2nd) p0092
  have p0102 := @gIns2ex (synCins2 (synC2nd)) p0101
  have p0103 :=
    @gInex
      (synCins4 (synCima
          (synCtxp (synCcnv (synC1st)) (synCsi3 (synCtxp (synC2nd) (synC1st))))
          (synC1c)))
      (synCins2 (synCins2 (synC2nd))) p0099 p0102
  have p0104 := @gSsetex
  have p0105 :=
    @gImaex
      (synCin (synCins4 (synCima
            (synCtxp (synCcnv (synC1st)) (synCsi3 (synCtxp (synC2nd) (synC1st))))
            (synC1c))) (synCins2 (synCins2 (synC2nd))))
      (synCsset) p0103 p0104
  have p0106 :=
    @gIns2ex
      (synCima (synCin (synCins4 (synCima
              (synCtxp (synCcnv (synC1st)) (synCsi3 (synCtxp (synC2nd) (synC1st))))
              (synC1c))) (synCins2 (synCins2 (synC2nd)))) (synCsset))
      p0105
  have p0107 := @gIdex
  have p0108 := @gIns3ex (synCid) p0107
  have p0109 :=
    @gDifex
      (synCins2 (synCima (synCin (synCins4 (synCima (synCtxp (synCcnv (synC1st))
                  (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
            (synCins2 (synCins2 (synC2nd)))) (synCsset)))
      (synCins3 (synCid)) p0106 p0108
  have p0111 :=
    @gImaex
      (synCdif (synCins2 (synCima (synCin (synCins4 (synCima
                  (synCtxp (synCcnv (synC1st)) (synCsi3 (synCtxp (synC2nd) (synC1st))))
                  (synC1c))) (synCins2 (synCins2 (synC2nd)))) (synCsset)))
        (synCins3 (synCid)))
      (synC1c) p0109 p0097
  have p0112 :=
    @gComplex
      (synCima (synCdif (synCins2 (synCima (synCin (synCins4 (synCima
                    (synCtxp (synCcnv (synC1st)) (synCsi3 (synCtxp (synC2nd) (synC1st))))
                    (synC1c))) (synCins2 (synCins2 (synC2nd)))) (synCsset)))
          (synCins3 (synCid))) (synC1c))
      p0111
  have p0114 :=
    @gImaex
      (synCcompl (synCima (synCdif (synCins2 (synCima (synCin (synCins4 (synCima
                      (synCtxp (synCcnv (synC1st))
                        (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                  (synCins2 (synCins2 (synC2nd)))) (synCsset))) (synCins3 (synCid)))
          (synC1c)))
      (synC1c) p0112 p0097
  have p0115 :=
    @gComplex
      (synCima (synCcompl (synCima (synCdif (synCins2 (synCima (synCin (synCins4
                      (synCima (synCtxp (synCcnv (synC1st))
                          (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                    (synCins2 (synCins2 (synC2nd)))) (synCsset))) (synCins3 (synCid)))
            (synC1c))) (synC1c))
      p0114
  have p0117 :=
    @gImaex
      (synCcompl (synCima (synCcompl (synCima (synCdif (synCins2 (synCima (synCin
                      (synCins4 (synCima (synCtxp (synCcnv (synC1st))
                            (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                      (synCins2 (synCins2 (synC2nd)))) (synCsset))) (synCins3 (synCid)))
              (synC1c))) (synC1c)))
      (synC1c) p0115 p0097
  have p0118 :=
    @gComplex
      (synCima (synCcompl (synCima (synCcompl (synCima (synCdif (synCins2 (synCima
                      (synCin (synCins4 (synCima (synCtxp (synCcnv (synC1st))
                              (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                        (synCins2 (synCins2 (synC2nd)))) (synCsset))) (synCins3 (synCid)))
                (synC1c))) (synC1c))) (synC1c))
      p0117
  have p0119 :=
    @gEqeltri (synCfuns)
      (synCcompl (synCima (synCcompl (synCima (synCcompl (synCima (synCdif (synCins2
                      (synCima (synCin (synCins4 (synCima (synCtxp (synCcnv (synC1st))
                                (synCsi3 (synCtxp (synC2nd) (synC1st)))) (synC1c)))
                          (synCins2 (synCins2 (synC2nd)))) (synCsset)))
                    (synCins3 (synCid))) (synC1c))) (synC1c))) (synC1c)))
      (synCvv) p0089 p0118
  exact p0119

/-- Checked nominal proof certificate identified upstream as `g_elfuns`. -/
@[expose]
noncomputable def gElfuns (F : Class)
    (hyp_elfuns_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf (synWb (.classMem F (synCfuns)) (synWfun F)) :=
  by
  let proofSupport : Finset Var := F.fv
  let f : Var := freshVar proofSupport 0
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_F : f ∉ F.fv := by
    intro h
    exact fresh_f (h)
  have dv_cache_0001 : f ∉ (F).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_F, not_false_eq_true])
  have dv_cache_0002 : f ∉ ((synWfun F)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, fresh_f_not_F,
          not_false_eq_true])
  have p0000 := @gFuneq (.cv f) F
  have p0001 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFuns f
  have p0002 :=
    @gElab2 (synWfun (.cv f)) (synWfun F) f F (synCfuns) dv_cache_0001 dv_cache_0002
      hyp_elfuns_1 p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_elfunsg`. -/
@[expose]
noncomputable def gElfunsg (F : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem F V) (synWb (.classMem F (synCfuns)) (synWfun F))) :=
  by
  let proofSupport : Finset Var := F.fv ∪ V.fv
  let f : Var := freshVar proofSupport 0
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_F : f ∉ F.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (h))
  have dv_cache_0001 : f ∉ (F).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_F, not_false_eq_true])
  have dv_cache_0002 : f ∉ ((Wff.classMem F (synCfuns))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfuns, Finset.mem_union,
          fresh_f_not_F, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : f ∉ ((synWfun F)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, fresh_f_not_F,
          not_false_eq_true])
  have p0000 := @gEleq1 (.cv f) F (synCfuns)
  have p0001 := @gFuneq (.cv f) F
  have p0002 := @gVex f
  have p0003 := @gElfuns (.cv f) p0002
  have p0004 :=
    @gVtoclbg (.classMem (.cv f) (synCfuns)) (synWfun (.cv f))
      (.classMem F (synCfuns)) (synWfun F) f F V dv_cache_0001 dv_cache_0002
      dv_cache_0003 p0000 p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_elfunsi`. -/
@[expose]
noncomputable def gElfunsi (F : Class) :
    Nominal.NPrf (.imp (.classMem F (synCfuns)) (synWfun F)) :=
  by
  have p0000 := @gElfunsg F (synCfuns)
  have p0001 := @gIbi (.classMem F (synCfuns)) (synWfun F) p0000
  exact p0001


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part005`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_fnsex`. -/
@[expose]
noncomputable def gFnsex : Nominal.NPrf (.classMem (synCfns) (synCvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let f : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  have fresh_f_ne_a : f ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_f : a ≠ f := Ne.symm fresh_f_ne_a
  have dv_cache_0001 : a ≠ f := by exact (show a ≠ f from (by exact fresh_a_ne_f))
  have dv_cache_0002 :
    f ∉ ((synCin (synCxp (synCfuns) (synCvv)) (synCimage (synC1st)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfuns,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 :
    a ∉ ((synCin (synCxp (synCfuns) (synCvv)) (synCimage (synC1st)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfuns,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 : f ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show f ≠ a from (by exact fresh_f_ne_a))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFns f a
      dv_cache_0001
  have p0001 := @gVex a
  have p0002 := @gOpelxp (.cv f) (.cv a) (synCfuns) (synCvv)
  have p0003 :=
    @gMpbiran2 (.classMem (synCop (.cv f) (.cv a)) (synCxp (synCfuns) (synCvv)))
      (.classMem (.cv f) (synCfuns)) (.classMem (.cv a) (synCvv)) p0001 p0002
  have p0004 := @gVex f
  have p0005 := @gElfuns (.cv f) p0004
  have p0006 :=
    @gBitri (.classMem (synCop (.cv f) (.cv a)) (synCxp (synCfuns) (synCvv)))
      (.classMem (.cv f) (synCfuns)) (synWfun (.cv f)) p0003 p0005
  have p0007 := @gEqcom (synCima (synC1st) (.cv f)) (.cv a)
  have p0008 := @gDfdm4 (.cv f)
  have p0009 := @gEqeq1i (synCdm (.cv f)) (synCima (synC1st) (.cv f)) (.cv a) p0008
  have p0010 := (Nominal.biimpRefl (synWbr (.cv f) (synCimage (synC1st)) (.cv a)))
  have p0011 := @gBrimage (.cv f) (.cv a) (synC1st) p0004 p0001
  have p0012 :=
    @gBitr3i (.classMem (synCop (.cv f) (.cv a)) (synCimage (synC1st)))
      (synWbr (.cv f) (synCimage (synC1st)) (.cv a))
      (.classEq (.cv a) (synCima (synC1st) (.cv f))) p0010 p0011
  have p0013 :=
    @gN3bitr4ri (.classEq (synCima (synC1st) (.cv f)) (.cv a))
      (.classEq (.cv a) (synCima (synC1st) (.cv f)))
      (.classEq (synCdm (.cv f)) (.cv a))
      (.classMem (synCop (.cv f) (.cv a)) (synCimage (synC1st))) p0007 p0009 p0012
  have p0014 :=
    @gAnbi12i (.classMem (synCop (.cv f) (.cv a)) (synCxp (synCfuns) (synCvv)))
      (synWfun (.cv f)) (.classMem (synCop (.cv f) (.cv a)) (synCimage (synC1st)))
      (.classEq (synCdm (.cv f)) (.cv a)) p0006 p0013
  have p0015 :=
    @gElin (synCop (.cv f) (.cv a)) (synCxp (synCfuns) (synCvv))
      (synCimage (synC1st))
  have p0016 := (Nominal.biimpRefl (synWfn (.cv f) (.cv a)))
  have p0017 :=
    @gN3bitr4i
      (synWa (.classMem (synCop (.cv f) (.cv a)) (synCxp (synCfuns) (synCvv)))
        (.classMem (synCop (.cv f) (.cv a)) (synCimage (synC1st))))
      (synWa (synWfun (.cv f)) (.classEq (synCdm (.cv f)) (.cv a)))
      (.classMem (synCop (.cv f) (.cv a))
        (synCin (synCxp (synCfuns) (synCvv)) (synCimage (synC1st))))
      (synWfn (.cv f) (.cv a)) p0014 p0015 p0016
  have p0018 :=
    @gOpabbi2i (synWfn (.cv f) (.cv a)) f a
      (synCin (synCxp (synCfuns) (synCvv)) (synCimage (synC1st))) dv_cache_0002
      dv_cache_0003 dv_cache_0004 p0017
  have p0019 :=
    @gEqtr4i (synCfns) (synCopab f a (synWfn (.cv f) (.cv a)))
      (synCin (synCxp (synCfuns) (synCvv)) (synCimage (synC1st))) p0000 p0018
  have p0020 := @gFunsex
  have p0021 := @gVvex
  have p0022 := @gXpex (synCfuns) (synCvv) p0020 p0021
  have p0023 := @gN1stex
  have p0024 := @gImageex (synC1st) p0023
  have p0025 :=
    @gInex (synCxp (synCfuns) (synCvv)) (synCimage (synC1st)) p0022 p0024
  have p0026 :=
    @gEqeltri (synCfns)
      (synCin (synCxp (synCfuns) (synCvv)) (synCimage (synC1st))) (synCvv) p0019
      p0025
  exact p0026

/-- Checked nominal proof certificate identified upstream as `g_brfns`. -/
@[expose]
noncomputable def gBrfns (A : Class) (F : Class)
    (hyp_brfns_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf (synWb (synWbr F (synCfns) A) (synWfn F A)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ F.fv
  let a : Var := freshVar proofSupport 0
  let f : Var := freshVar proofSupport 1
  let b : Var := freshVar proofSupport 2
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (h))
  have fresh_a_not_F : a ∉ F.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_f_not_F : f ∉ F.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_b_not_F : b ∉ F.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_a_ne_f : a ≠ f :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_f_ne_a : f ≠ a := Ne.symm fresh_a_ne_f
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_b_ne_a : b ≠ a := Ne.symm fresh_a_ne_b
  have fresh_f_ne_b : f ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_b_ne_f : b ≠ f := Ne.symm fresh_f_ne_b
  have dv_cache_0001 : b ≠ f := by exact (show b ≠ f from (by exact fresh_b_ne_f))
  have dv_cache_0002 : f ∉ (F).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_F, not_false_eq_true])
  have dv_cache_0003 : b ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_F, not_false_eq_true])
  have dv_cache_0004 : f ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_f_ne_a, not_false_eq_true])
  have dv_cache_0005 : b ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_a, not_false_eq_true])
  have dv_cache_0006 : f ∉ ((synWfn F (.cv a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_f_not_F, fresh_f_ne_a, or_false, not_false_eq_true])
  have dv_cache_0007 : b ∉ ((synWfn F (.cv a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_b_not_F, fresh_b_ne_a, or_false, not_false_eq_true])
  have dv_cache_0008 : f ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show f ≠ b from (by exact fresh_f_ne_b))
  have dv_cache_0009 : a ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_A, not_false_eq_true])
  have dv_cache_0010 : a ∉ ((synWbr F (synCfns) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfns, Finset.mem_union,
          fresh_a_not_F, fresh_a_not_A, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0011 : a ∉ ((synWfn F A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn, Finset.mem_union,
          fresh_a_not_F, fresh_a_not_A, or_false, not_false_eq_true])
  have p0000 := @gBrex F A (synCfns)
  have p0001 :=
    @gSimprd (synWbr F (synCfns) A) (.classMem F (synCvv)) (.classMem A (synCvv))
      p0000
  have p0002 := @gFndm A F
  have p0003 := @gEqcomd (synWfn F A) (synCdm F) A p0002
  have p0004 := @gDmexg F (synCvv)
  have p0005 := Nominal.mp hyp_brfns_1 p0004
  have p0006 := @gSyl6eqel (synWfn F A) A (synCdm F) (synCvv) p0003 p0005
  have p0007 := @gBreq2 (.cv a) A F (synCfns)
  have p0008 := @gFneq2 (.cv a) A F
  have p0009 := @gVex a
  have p0010 := @gFneq1 (.cv b) (.cv f) F
  have p0011 := @gFneq2 (.cv b) (.cv a) F
  have p0012 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFns f b
      dv_cache_0001
  have p0013 :=
    @gBrab (synWfn (.cv f) (.cv b)) (synWfn F (.cv b)) (synWfn F (.cv a)) f b F
      (.cv a) (synCfns) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 hyp_brfns_1 p0009 p0010 p0011 p0012
  have p0014 :=
    @gVtoclbg (synWbr F (synCfns) (.cv a)) (synWfn F (.cv a)) (synWbr F (synCfns) A)
      (synWfn F A) a A (synCvv) dv_cache_0009 dv_cache_0010 dv_cache_0011 p0007 p0008
      p0013
  have p0015 :=
    @gPm521nii (synWbr F (synCfns) A) (.classMem A (synCvv)) (synWfn F A) p0001
      p0006 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_pprodeq2`. -/
@[expose]
noncomputable def gPprodeq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCpprod C A) (synCpprod C B))) :=
  by
  have p0000 := @gCoeq1 A B (synC2nd)
  have p0001 :=
    @gTxpeq2 (synCcom A (synC2nd)) (synCcom B (synC2nd)) (synCcom C (synC1st))
  have p0002 :=
    @gSyl (.classEq A B) (.classEq (synCcom A (synC2nd)) (synCcom B (synC2nd)))
      (.classEq (synCtxp (synCcom C (synC1st)) (synCcom A (synC2nd)))
        (synCtxp (synCcom C (synC1st)) (synCcom B (synC2nd))))
      p0000 p0001
  have p0003 := (Nominal.classEqRefl (synCpprod C A))
  have p0004 := (Nominal.classEqRefl (synCpprod C B))
  have p0005 :=
    @gN3eqtr4g (.classEq A B) (synCtxp (synCcom C (synC1st)) (synCcom A (synC2nd)))
      (synCtxp (synCcom C (synC1st)) (synCcom B (synC2nd))) (synCpprod C A)
      (synCpprod C B) p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_qrpprod`. -/
@[expose]
noncomputable def gQrpprod (A : Class) (B : Class) (C : Class) (D : Class) (R : Class)
    (S : Class) :
    Nominal.NPrf
      (synWb (synWbr (synCop A B) (synCpprod R S) (synCop C D))
        (synWa (synWbr A R C) (synWbr B S D))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv ∪ S.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  let a : Var := freshVar proofSupport 4
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_S : z ∉ S.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_w_not_C : w ∉ C.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_not_D : w ∉ D.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_R : w ∉ R.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_S : w ∉ S.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_S : a ∉ S.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_y_ne_a : y ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_a_ne_y : a ≠ y := Ne.symm fresh_y_ne_a
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_z_ne_a : z ≠ a :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_a_ne_z : a ≠ z := Ne.symm fresh_z_ne_a
  have fresh_w_ne_a : w ≠ a :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_a_ne_w : a ≠ w := Ne.symm fresh_w_ne_a
  have dv_cache_0001 : a ∉ ((synCop (.cv x) (.cv y))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_x, fresh_a_ne_y, or_false, not_false_eq_true])
  have dv_cache_0002 : a ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_z, not_false_eq_true])
  have dv_cache_0003 : a ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_R, not_false_eq_true])
  have dv_cache_0004 : a ∉ ((synC1st)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0005 : a ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_x, not_false_eq_true])
  have dv_cache_0006 : a ∉ ((synWbr (.cv x) R (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_x, fresh_a_ne_z, fresh_a_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0007 : a ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_w, not_false_eq_true])
  have dv_cache_0008 : a ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_S, not_false_eq_true])
  have dv_cache_0009 : a ∉ ((synC2nd)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0010 : a ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_y, not_false_eq_true])
  have dv_cache_0011 : a ∉ ((synWbr (.cv y) S (.cv w))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_y, fresh_a_ne_w, fresh_a_not_S, or_false,
          not_false_eq_true])
  have dv_cache_0012 : z ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_C, not_false_eq_true])
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
  have dv_cache_0014 : w ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_D, not_false_eq_true])
  have dv_cache_0015 :
    w ∉
      ((synWb (synWbr (synCop (.cv x) (.cv y)) (synCpprod R S) (synCop C D))
          (synWa (synWbr (.cv x) R C) (synWbr (.cv y) S D)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_not_C, fresh_w_not_D,
          fresh_w_not_R, fresh_w_not_S, or_false, not_false_eq_true])
  have dv_cache_0016 :
    z ∉
      ((synWb (synWbr (synCop (.cv x) (.cv y)) (synCpprod R S) (synCop C (.cv w)))
          (synWa (synWbr (.cv x) R C) (synWbr (.cv y) S (.cv w))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_C, fresh_z_ne_w,
          fresh_z_not_R, fresh_z_not_S, or_false, not_false_eq_true])
  have dv_cache_0017 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0018 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0019 : y ∉ (B).fv :=
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
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0020 :
    y ∉
      ((Wff.imp (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
          (synWb (synWbr (synCop A B) (synCpprod R S) (synCop C D))
            (synWa (synWbr A R C) (synWbr B S D))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod, Finset.mem_union,
          fresh_y_not_C, fresh_y_not_D, fresh_y_not_A, fresh_y_not_B, fresh_y_not_R,
          fresh_y_not_S, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0021 :
    x ∉
      ((Wff.imp (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
          (synWb (synWbr (synCop A (.cv y)) (synCpprod R S) (synCop C D))
            (synWa (synWbr A R C) (synWbr (.cv y) S D))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_C, fresh_x_not_D, fresh_x_not_A, fresh_x_ne_y,
          fresh_x_not_R, fresh_x_not_S, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @gBrex (synCop A B) (synCop C D) (synCpprod R S)
  have p0001 := @gOpexb A B
  have p0002 := @gOpexb C D
  have p0003 :=
    @gAnbi12i (.classMem (synCop A B) (synCvv))
      (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (.classMem (synCop C D) (synCvv))
      (synWa (.classMem C (synCvv)) (.classMem D (synCvv))) p0001 p0002
  have p0004 :=
    @gSylib (synWbr (synCop A B) (synCpprod R S) (synCop C D))
      (synWa (.classMem (synCop A B) (synCvv)) (.classMem (synCop C D) (synCvv)))
      (synWa (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
        (synWa (.classMem C (synCvv)) (.classMem D (synCvv))))
      p0000 p0003
  have p0005 := @gBrex A C R
  have p0006 := @gBrex B D S
  have p0007 :=
    @gAnim12i (synWbr A R C) (synWa (.classMem A (synCvv)) (.classMem C (synCvv)))
      (synWbr B S D) (synWa (.classMem B (synCvv)) (.classMem D (synCvv))) p0005 p0006
  have p0008 :=
    @gAn4 (.classMem A (synCvv)) (.classMem B (synCvv)) (.classMem C (synCvv))
      (.classMem D (synCvv))
  have p0009 :=
    @gSylibr (synWa (synWbr A R C) (synWbr B S D))
      (synWa (synWa (.classMem A (synCvv)) (.classMem C (synCvv)))
        (synWa (.classMem B (synCvv)) (.classMem D (synCvv))))
      (synWa (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
        (synWa (.classMem C (synCvv)) (.classMem D (synCvv))))
      p0007 p0008
  have p0010 := @gOpeq1 (.cv x) A (.cv y)
  have p0011 :=
    @gBreq1d (.classEq (.cv x) A) (synCop (.cv x) (.cv y)) (synCop A (.cv y))
      (synCop C D) (synCpprod R S) p0010
  have p0012 := @gBreq1 (.cv x) A C R
  have p0013 :=
    @gAnbi1d (.classEq (.cv x) A) (synWbr (.cv x) R C) (synWbr A R C)
      (synWbr (.cv y) S D) p0012
  have p0014 :=
    @gBibi12d (.classEq (.cv x) A)
      (synWbr (synCop (.cv x) (.cv y)) (synCpprod R S) (synCop C D))
      (synWbr (synCop A (.cv y)) (synCpprod R S) (synCop C D))
      (synWa (synWbr (.cv x) R C) (synWbr (.cv y) S D))
      (synWa (synWbr A R C) (synWbr (.cv y) S D)) p0011 p0013
  have p0015 :=
    @gImbi2d (.classEq (.cv x) A)
      (synWb (synWbr (synCop (.cv x) (.cv y)) (synCpprod R S) (synCop C D))
        (synWa (synWbr (.cv x) R C) (synWbr (.cv y) S D)))
      (synWb (synWbr (synCop A (.cv y)) (synCpprod R S) (synCop C D))
        (synWa (synWbr A R C) (synWbr (.cv y) S D)))
      (synWa (.classMem C (synCvv)) (.classMem D (synCvv))) p0014
  have p0016 := @gOpeq2 (.cv y) B A
  have p0017 :=
    @gBreq1d (.classEq (.cv y) B) (synCop A (.cv y)) (synCop A B) (synCop C D)
      (synCpprod R S) p0016
  have p0018 := @gBreq1 (.cv y) B D S
  have p0019 :=
    @gAnbi2d (.classEq (.cv y) B) (synWbr (.cv y) S D) (synWbr B S D) (synWbr A R C)
      p0018
  have p0020 :=
    @gBibi12d (.classEq (.cv y) B)
      (synWbr (synCop A (.cv y)) (synCpprod R S) (synCop C D))
      (synWbr (synCop A B) (synCpprod R S) (synCop C D))
      (synWa (synWbr A R C) (synWbr (.cv y) S D))
      (synWa (synWbr A R C) (synWbr B S D)) p0017 p0019
  have p0021 :=
    @gImbi2d (.classEq (.cv y) B)
      (synWb (synWbr (synCop A (.cv y)) (synCpprod R S) (synCop C D))
        (synWa (synWbr A R C) (synWbr (.cv y) S D)))
      (synWb (synWbr (synCop A B) (synCpprod R S) (synCop C D))
        (synWa (synWbr A R C) (synWbr B S D)))
      (synWa (.classMem C (synCvv)) (.classMem D (synCvv))) p0020
  have p0022 := @gOpeq1 (.cv z) C (.cv w)
  have p0023 :=
    @gBreq2d (.classEq (.cv z) C) (synCop (.cv z) (.cv w)) (synCop C (.cv w))
      (synCop (.cv x) (.cv y)) (synCpprod R S) p0022
  have p0024 := @gBreq2 (.cv z) C (.cv x) R
  have p0025 :=
    @gAnbi1d (.classEq (.cv z) C) (synWbr (.cv x) R (.cv z)) (synWbr (.cv x) R C)
      (synWbr (.cv y) S (.cv w)) p0024
  have p0026 :=
    @gBibi12d (.classEq (.cv z) C)
      (synWbr (synCop (.cv x) (.cv y)) (synCpprod R S) (synCop (.cv z) (.cv w)))
      (synWbr (synCop (.cv x) (.cv y)) (synCpprod R S) (synCop C (.cv w)))
      (synWa (synWbr (.cv x) R (.cv z)) (synWbr (.cv y) S (.cv w)))
      (synWa (synWbr (.cv x) R C) (synWbr (.cv y) S (.cv w))) p0023 p0025
  have p0027 := @gOpeq2 (.cv w) D C
  have p0028 :=
    @gBreq2d (.classEq (.cv w) D) (synCop C (.cv w)) (synCop C D)
      (synCop (.cv x) (.cv y)) (synCpprod R S) p0027
  have p0029 := @gBreq2 (.cv w) D (.cv y) S
  have p0030 :=
    @gAnbi2d (.classEq (.cv w) D) (synWbr (.cv y) S (.cv w)) (synWbr (.cv y) S D)
      (synWbr (.cv x) R C) p0029
  have p0031 :=
    @gBibi12d (.classEq (.cv w) D)
      (synWbr (synCop (.cv x) (.cv y)) (synCpprod R S) (synCop C (.cv w)))
      (synWbr (synCop (.cv x) (.cv y)) (synCpprod R S) (synCop C D))
      (synWa (synWbr (.cv x) R C) (synWbr (.cv y) S (.cv w)))
      (synWa (synWbr (.cv x) R C) (synWbr (.cv y) S D)) p0028 p0030
  have p0032 := (Nominal.classEqRefl (synCpprod R S))
  have p0033 :=
    @gBreqi (synCop (.cv x) (.cv y)) (synCop (.cv z) (.cv w)) (synCpprod R S)
      (synCtxp (synCcom R (synC1st)) (synCcom S (synC2nd))) p0032
  have p0034 :=
    @gTrtxp (synCop (.cv x) (.cv y)) (.cv z) (.cv w) (synCcom R (synC1st))
      (synCcom S (synC2nd))
  have p0035 :=
    @gBitri
      (synWbr (synCop (.cv x) (.cv y)) (synCpprod R S) (synCop (.cv z) (.cv w)))
      (synWbr (synCop (.cv x) (.cv y))
        (synCtxp (synCcom R (synC1st)) (synCcom S (synC2nd))) (synCop (.cv z) (.cv w)))
      (synWa (synWbr (synCop (.cv x) (.cv y)) (synCcom R (synC1st)) (.cv z))
        (synWbr (synCop (.cv x) (.cv y)) (synCcom S (synC2nd)) (.cv w)))
      p0033 p0034
  have p0036 :=
    @gBrco a (synCop (.cv x) (.cv y)) (.cv z) R (synC1st) dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004
  have p0037 := @gVex x
  have p0038 := @gVex y
  have p0039 := @gOpbr1st (.cv x) (.cv y) (.cv a) p0037 p0038
  have p0040 := @gEqcom (.cv x) (.cv a)
  have p0041_e00_recanon :
    Nominal.NPrf
      (synWb (synWbr (synCop (.cv x) (.cv y)) (synC1st) (.cv a)) (.objEq x a)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synC1st synCopab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0039
  have p0041_e01_recanon : Nominal.NPrf (synWb (.objEq x a) (.objEq a x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0040
  have p0041 :=
    @gBitri (synWbr (synCop (.cv x) (.cv y)) (synC1st) (.cv a)) (.objEq x a)
      (.objEq a x) p0041_e00_recanon p0041_e01_recanon
  have p0042 :=
    @gAnbi1i (synWbr (synCop (.cv x) (.cv y)) (synC1st) (.cv a)) (.objEq a x)
      (synWbr (.cv a) R (.cv z)) p0041
  have p0043 :=
    @gExbii
      (synWa (synWbr (synCop (.cv x) (.cv y)) (synC1st) (.cv a))
        (synWbr (.cv a) R (.cv z)))
      (synWa (.objEq a x) (synWbr (.cv a) R (.cv z))) a p0042
  have p0044 :=
    @gBitri (synWbr (synCop (.cv x) (.cv y)) (synCcom R (synC1st)) (.cv z))
      (synWex a (synWa (synWbr (synCop (.cv x) (.cv y)) (synC1st) (.cv a))
          (synWbr (.cv a) R (.cv z))))
      (synWex a (synWa (.objEq a x) (synWbr (.cv a) R (.cv z)))) p0036 p0043
  have p0045 := @gBreq1 (.cv a) (.cv x) (.cv z) R
  have p0046 :=
    @gCeqsexv (synWbr (.cv a) R (.cv z)) (synWbr (.cv x) R (.cv z)) a (.cv x)
      dv_cache_0005 dv_cache_0006 p0037 p0045
  have p0047_e01_recanon :
    Nominal.NPrf
      (synWb (synWex a (synWa (.objEq a x) (synWbr (.cv a) R (.cv z))))
        (synWbr (.cv x) R (.cv z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWex synWa synWbr synCop synCun synCnin synWnan synCcompl
          synWrex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0046
  have p0047 :=
    @gBitri (synWbr (synCop (.cv x) (.cv y)) (synCcom R (synC1st)) (.cv z))
      (synWex a (synWa (.objEq a x) (synWbr (.cv a) R (.cv z))))
      (synWbr (.cv x) R (.cv z)) p0044 p0047_e01_recanon
  have p0048 :=
    @gBrco a (synCop (.cv x) (.cv y)) (.cv w) S (synC2nd) dv_cache_0001 dv_cache_0007
      dv_cache_0008 dv_cache_0009
  have p0049 := @gOpbr2nd (.cv x) (.cv y) (.cv a) p0037 p0038
  have p0050 := @gEqcom (.cv y) (.cv a)
  have p0051_e00_recanon :
    Nominal.NPrf
      (synWb (synWbr (synCop (.cv x) (.cv y)) (synC2nd) (.cv a)) (.objEq y a)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synC2nd synCopab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0049
  have p0051_e01_recanon : Nominal.NPrf (synWb (.objEq y a) (.objEq a y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0050
  have p0051 :=
    @gBitri (synWbr (synCop (.cv x) (.cv y)) (synC2nd) (.cv a)) (.objEq y a)
      (.objEq a y) p0051_e00_recanon p0051_e01_recanon
  have p0052 :=
    @gAnbi1i (synWbr (synCop (.cv x) (.cv y)) (synC2nd) (.cv a)) (.objEq a y)
      (synWbr (.cv a) S (.cv w)) p0051
  have p0053 :=
    @gExbii
      (synWa (synWbr (synCop (.cv x) (.cv y)) (synC2nd) (.cv a))
        (synWbr (.cv a) S (.cv w)))
      (synWa (.objEq a y) (synWbr (.cv a) S (.cv w))) a p0052
  have p0054 :=
    @gBitri (synWbr (synCop (.cv x) (.cv y)) (synCcom S (synC2nd)) (.cv w))
      (synWex a (synWa (synWbr (synCop (.cv x) (.cv y)) (synC2nd) (.cv a))
          (synWbr (.cv a) S (.cv w))))
      (synWex a (synWa (.objEq a y) (synWbr (.cv a) S (.cv w)))) p0048 p0053
  have p0055 := @gBreq1 (.cv a) (.cv y) (.cv w) S
  have p0056 :=
    @gCeqsexv (synWbr (.cv a) S (.cv w)) (synWbr (.cv y) S (.cv w)) a (.cv y)
      dv_cache_0010 dv_cache_0011 p0038 p0055
  have p0057_e01_recanon :
    Nominal.NPrf
      (synWb (synWex a (synWa (.objEq a y) (synWbr (.cv a) S (.cv w))))
        (synWbr (.cv y) S (.cv w))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWex synWa synWbr synCop synCun synCnin synWnan synCcompl
          synWrex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0056
  have p0057 :=
    @gBitri (synWbr (synCop (.cv x) (.cv y)) (synCcom S (synC2nd)) (.cv w))
      (synWex a (synWa (.objEq a y) (synWbr (.cv a) S (.cv w))))
      (synWbr (.cv y) S (.cv w)) p0054 p0057_e01_recanon
  have p0058 :=
    @gAnbi12i (synWbr (synCop (.cv x) (.cv y)) (synCcom R (synC1st)) (.cv z))
      (synWbr (.cv x) R (.cv z))
      (synWbr (synCop (.cv x) (.cv y)) (synCcom S (synC2nd)) (.cv w))
      (synWbr (.cv y) S (.cv w)) p0047 p0057
  have p0059 :=
    @gBitri
      (synWbr (synCop (.cv x) (.cv y)) (synCpprod R S) (synCop (.cv z) (.cv w)))
      (synWa (synWbr (synCop (.cv x) (.cv y)) (synCcom R (synC1st)) (.cv z))
        (synWbr (synCop (.cv x) (.cv y)) (synCcom S (synC2nd)) (.cv w)))
      (synWa (synWbr (.cv x) R (.cv z)) (synWbr (.cv y) S (.cv w))) p0035 p0058
  have p0060 :=
    @gVtocl2g
      (synWb (synWbr (synCop (.cv x) (.cv y)) (synCpprod R S) (synCop (.cv z) (.cv w)))
        (synWa (synWbr (.cv x) R (.cv z)) (synWbr (.cv y) S (.cv w))))
      (synWb (synWbr (synCop (.cv x) (.cv y)) (synCpprod R S) (synCop C (.cv w)))
        (synWa (synWbr (.cv x) R C) (synWbr (.cv y) S (.cv w))))
      (synWb (synWbr (synCop (.cv x) (.cv y)) (synCpprod R S) (synCop C D))
        (synWa (synWbr (.cv x) R C) (synWbr (.cv y) S D)))
      z w C D (synCvv) (synCvv) dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
      dv_cache_0016 p0026 p0031 p0059
  have p0061 :=
    @gVtocl2g
      (.imp (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
        (synWb (synWbr (synCop (.cv x) (.cv y)) (synCpprod R S) (synCop C D))
          (synWa (synWbr (.cv x) R C) (synWbr (.cv y) S D))))
      (.imp (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
        (synWb (synWbr (synCop A (.cv y)) (synCpprod R S) (synCop C D))
          (synWa (synWbr A R C) (synWbr (.cv y) S D))))
      (.imp (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
        (synWb (synWbr (synCop A B) (synCpprod R S) (synCop C D))
          (synWa (synWbr A R C) (synWbr B S D))))
      x y A B (synCvv) (synCvv) dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
      dv_cache_0021 p0015 p0021 p0060
  have p0062 :=
    @gImp (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (synWb (synWbr (synCop A B) (synCpprod R S) (synCop C D))
        (synWa (synWbr A R C) (synWbr B S D)))
      p0061
  have p0063 :=
    @gPm521nii (synWbr (synCop A B) (synCpprod R S) (synCop C D))
      (synWa (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
        (synWa (.classMem C (synCvv)) (.classMem D (synCvv))))
      (synWa (synWbr A R C) (synWbr B S D)) p0004 p0009 p0062
  exact p0063

/-- Checked nominal proof certificate identified upstream as `g_pprodexg`. -/
@[expose]
noncomputable def gPprodexg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W)) (.classMem (synCpprod A B) (synCvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCpprod A B))
  have p0001 := @gN1stex
  have p0002 := @gCoexg A (synC1st) V (synCvv)
  have p0003 :=
    @gMpan2 (.classMem A V) (.classMem (synC1st) (synCvv))
      (.classMem (synCcom A (synC1st)) (synCvv)) p0001 p0002
  have p0004 := @gN2ndex
  have p0005 := @gCoexg B (synC2nd) W (synCvv)
  have p0006 :=
    @gMpan2 (.classMem B W) (.classMem (synC2nd) (synCvv))
      (.classMem (synCcom B (synC2nd)) (synCvv)) p0004 p0005
  have p0007 :=
    @gTxpexg (synCcom A (synC1st)) (synCcom B (synC2nd)) (synCvv) (synCvv)
  have p0008 :=
    @gSyl2an (.classMem A V) (.classMem (synCcom A (synC1st)) (synCvv))
      (.classMem (synCcom B (synC2nd)) (synCvv))
      (.classMem (synCtxp (synCcom A (synC1st)) (synCcom B (synC2nd))) (synCvv))
      (.classMem B W) p0003 p0006 p0007
  have p0009 :=
    @gSyl5eqel (synWa (.classMem A V) (.classMem B W)) (synCpprod A B)
      (synCtxp (synCcom A (synC1st)) (synCcom B (synC2nd))) (synCvv) p0000 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_pprodex`. -/
@[expose]
noncomputable def gPprodex (A : Class) (B : Class)
    (hyp_pprodex_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_pprodex_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classMem (synCpprod A B) (synCvv)) :=
  by
  have p0000 := @gPprodexg A B (synCvv) (synCvv)
  have p0001 :=
    @gMp2an (.classMem A (synCvv)) (.classMem B (synCvv))
      (.classMem (synCpprod A B) (synCvv)) hyp_pprodex_1 hyp_pprodex_2 p0000
  exact p0001


end NFChoice.DirectNominalPrf.WPPReplay

end
