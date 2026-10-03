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

@[expose]
noncomputable def g_brdisj (A : Class) (B : Class)
    (hyp_brdisj_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_brdisj_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (syn_wbr A (syn_cdisj) B) (.classEq (syn_cin A B) (syn_c0))) :=
  by
  have p0000 := @g_brdisjg A B (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (syn_wb (syn_wbr A (syn_cdisj) B) (.classEq (syn_cin A B) (syn_c0))) hyp_brdisj_1
      hyp_brdisj_2 p0000
  exact p0001

@[expose]
noncomputable def g_disjex : Nominal.NPrf (.classMem (syn_cdisj) (syn_cvv)) :=
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
  have dv_cache_0002 : z ∉ ((syn_cop (.cv x) (.cv y))).fv :=
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
  have dv_cache_0003 : z ∉ ((syn_ctxp (syn_csset) (syn_csset))).fv :=
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
    x ∉ ((syn_ccompl (syn_cima (syn_ctxp (syn_csset) (syn_csset)) (syn_c1c)))).fv :=
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
    y ∉ ((syn_ccompl (syn_cima (syn_ctxp (syn_csset) (syn_csset)) (syn_c1c)))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_disj x y
      dv_cache_0001
  have p0001 := @g_oteltxp (syn_csn (.cv z)) (.cv x) (.cv y) (syn_csset) (syn_csset)
  have p0002 := @g_vex z
  have p0003 := @g_vex x
  have p0004 := @g_opelssetsn (.cv z) (.cv x) p0002 p0003
  have p0005 := @g_vex y
  have p0006 := @g_opelssetsn (.cv z) (.cv y) p0002 p0005
  have p0007_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv z)) (.cv x)) (syn_csset)) (.objMem z x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
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
      (syn_wb (.classMem (syn_cop (syn_csn (.cv z)) (.cv y)) (syn_csset)) (.objMem z y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
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
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv z)) (.cv x)) (syn_csset)) (.objMem z x)
      (.classMem (syn_cop (syn_csn (.cv z)) (.cv y)) (syn_csset)) (.objMem z y)
      p0007_e00_recanon p0007_e01_recanon
  have p0008 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))
        (syn_ctxp (syn_csset) (syn_csset)))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv z)) (.cv x)) (syn_csset))
        (.classMem (syn_cop (syn_csn (.cv z)) (.cv y)) (syn_csset)))
      (syn_wa (.objMem z x) (.objMem z y)) p0001 p0007
  have p0009 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))
        (syn_ctxp (syn_csset) (syn_csset)))
      (syn_wa (.objMem z x) (.objMem z y)) z p0008
  have p0010 :=
    @g_elima1c z (syn_cop (.cv x) (.cv y)) (syn_ctxp (syn_csset) (syn_csset))
      dv_cache_0002 dv_cache_0003
  have p0011 := (Nominal.biimpRefl (syn_wrex z (.cv x) (.objMem z y)))
  have p0012_e02_recanon :
    Nominal.NPrf
      (syn_wb (syn_wrex z (.cv x) (.objMem z y))
        (syn_wex z (syn_wa (.objMem z x) (.objMem z y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa]
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
    @g_n_3bitr4i
      (syn_wex z (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))
          (syn_ctxp (syn_csset) (syn_csset))))
      (syn_wex z (syn_wa (.objMem z x) (.objMem z y)))
      (.classMem (syn_cop (.cv x) (.cv y))
        (syn_cima (syn_ctxp (syn_csset) (syn_csset)) (syn_c1c)))
      (syn_wrex z (.cv x) (.objMem z y)) p0009 p0010 p0012_e02_recanon
  have p0013 := @g_dfrex2 (.objMem z y) z (.cv x)
  have p0014 :=
    @g_bitri
      (.classMem (syn_cop (.cv x) (.cv y))
        (syn_cima (syn_ctxp (syn_csset) (syn_csset)) (syn_c1c)))
      (syn_wrex z (.cv x) (.objMem z y)) (.neg (syn_wral z (.cv x) (.neg (.objMem z y))))
      p0012 p0013
  have p0015 :=
    @g_con2bii
      (.classMem (syn_cop (.cv x) (.cv y))
        (syn_cima (syn_ctxp (syn_csset) (syn_csset)) (syn_c1c)))
      (syn_wral z (.cv x) (.neg (.objMem z y))) p0014
  have p0016 := @g_disj z (.cv x) (.cv y) dv_cache_0004 dv_cache_0005
  have p0017 := @g_opex (.cv x) (.cv y) p0003 p0005
  have p0018 :=
    @g_elcompl (syn_cop (.cv x) (.cv y))
      (syn_cima (syn_ctxp (syn_csset) (syn_csset)) (syn_c1c)) p0017
  have p0019_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0))
        (syn_wral z (.cv x) (.neg (.objMem z y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_c0 syn_cdif syn_cvv
          syn_wral
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
    @g_n_3bitr4ri (syn_wral z (.cv x) (.neg (.objMem z y)))
      (.neg (.classMem (syn_cop (.cv x) (.cv y))
          (syn_cima (syn_ctxp (syn_csset) (syn_csset)) (syn_c1c))))
      (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0))
      (.classMem (syn_cop (.cv x) (.cv y))
        (syn_ccompl (syn_cima (syn_ctxp (syn_csset) (syn_csset)) (syn_c1c))))
      p0015 p0019_e01_recanon p0018
  have p0020 :=
    @g_opabbi2i (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0)) x y
      (syn_ccompl (syn_cima (syn_ctxp (syn_csset) (syn_csset)) (syn_c1c))) dv_cache_0006
      dv_cache_0007 dv_cache_0001 p0019
  have p0021 :=
    @g_eqtr4i (syn_cdisj) (syn_copab x y (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0)))
      (syn_ccompl (syn_cima (syn_ctxp (syn_csset) (syn_csset)) (syn_c1c))) p0000 p0020
  have p0022 := @g_ssetex
  have p0024 := @g_txpex (syn_csset) (syn_csset) p0022 p0022
  have p0025 := @g_n_1cex
  have p0026 := @g_imaex (syn_ctxp (syn_csset) (syn_csset)) (syn_c1c) p0024 p0025
  have p0027 := @g_complex (syn_cima (syn_ctxp (syn_csset) (syn_csset)) (syn_c1c)) p0026
  have p0028 :=
    @g_eqeltri (syn_cdisj)
      (syn_ccompl (syn_cima (syn_ctxp (syn_csset) (syn_csset)) (syn_c1c))) (syn_cvv) p0021
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

@[expose]
noncomputable def g_addcfnex : Nominal.NPrf (.classMem (syn_caddcfn) (syn_cvv)) :=
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
  have dv_cache_0004 : x ∉ ((syn_c1st)).fv :=
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
  have dv_cache_0007 : y ∉ ((syn_wbr (.cv p) (syn_c1st) (.cv x))).fv :=
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
  have dv_cache_0008 : x ∉ ((syn_cop (.cv a) (.cv y))).fv :=
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
  have dv_cache_0009 : x ∉ ((syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y)))).fv :=
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
    y ∉ ((syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b))).fv :=
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
  have dv_cache_0012 : z ∉ ((syn_cop (.cv a) (.cv y))).fv :=
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
      ((syn_wb (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b)) (.objEq y b))).fv :=
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
  have dv_cache_0015 : y ∉ ((syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv b)))).fv :=
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
  have dv_cache_0016 : p ∉ ((syn_cop (.cv a) (syn_cop (.cv b) (.cv z)))).fv :=
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
      ((syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))).fv :=
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
  have dv_cache_0018 : p ∉ ((syn_ccup)).fv :=
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
  have dv_cache_0019 : p ∉ ((syn_cop (syn_cop (.cv a) (.cv b)) (.cv z))).fv :=
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
    a ∉ ((syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)))).fv :=
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
      ((syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
              (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
                  (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                  (syn_ccup))))))).fv :=
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
  have dv_cache_0022 : b ∉ ((syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))).fv :=
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
      ((syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima
              (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                    (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
                        (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                        (syn_ccup)))))) (syn_c1c))))).fv :=
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
  have dv_cache_0031 : x ∉ ((syn_cvv)).fv :=
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
  have dv_cache_0032 : y ∉ ((syn_cvv)).fv :=
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
      ((syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima
                (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                      (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
                          (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                            (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                          (syn_ccup)))))) (syn_c1c)))) (syn_c1c))).fv :=
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
      ((syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima
                (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                      (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
                          (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                            (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                          (syn_ccup)))))) (syn_c1c)))) (syn_c1c))).fv :=
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
      ((syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima
                (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                      (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
                          (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                            (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                          (syn_ccup)))))) (syn_c1c)))) (syn_c1c))).fv :=
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
  have dv_cache_0036 : z ∉ ((syn_cplc (.cv x) (.cv y))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_addcfn x y
      dv_cache_0001
  have p0001 :=
    @g_elin
      (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))
      (syn_cins2 (syn_cins2 (syn_csset)))
      (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
                    (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))))))
          (syn_c1c)))
  have p0002 := @g_snex (.cv z)
  have p0003 :=
    @g_otelins2 (syn_csn (.cv b)) (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))
      (syn_cins2 (syn_csset)) p0002
  have p0004 := @g_vex x
  have p0005 := @g_otelins2 (syn_csn (.cv b)) (.cv x) (.cv y) (syn_csset) p0004
  have p0006 := @g_vex b
  have p0007 := @g_vex y
  have p0008 := @g_opelssetsn (.cv b) (.cv y) p0006 p0007
  have p0009_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv b)) (.cv y)) (syn_csset)) (.objMem b y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
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
    @g_n_3bitri
      (.classMem
        (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (.classMem (syn_cop (syn_csn (.cv b)) (syn_cop (.cv x) (.cv y))) (syn_cins2 (syn_csset)))
      (.classMem (syn_cop (syn_csn (.cv b)) (.cv y)) (syn_csset)) (.objMem b y) p0003
      p0005 p0009_e02_recanon
  have p0010 :=
    @g_oqelins4 (syn_csn (.cv b)) (syn_csn (.cv z)) (.cv x) (.cv y)
      (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
              (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
                  (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))))))
        (syn_c1c))
      p0007
  have p0011 :=
    @g_elin
      (syn_cop (syn_csn (.cv a))
        (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x))))
      (syn_cins2 (syn_cins2 (syn_csset)))
      (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
              (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))
  have p0012 := @g_snex (.cv b)
  have p0013 :=
    @g_otelins2 (syn_csn (.cv a)) (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x))
      (syn_cins2 (syn_csset)) p0012
  have p0014 := @g_otelins2 (syn_csn (.cv a)) (syn_csn (.cv z)) (.cv x) (syn_csset) p0002
  have p0015 := @g_vex a
  have p0016 := @g_opelssetsn (.cv a) (.cv x) p0015 p0004
  have p0017_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv a)) (.cv x)) (syn_csset)) (.objMem a x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
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
    @g_n_3bitri
      (.classMem (syn_cop (syn_csn (.cv a))
          (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (.classMem (syn_cop (syn_csn (.cv a)) (syn_cop (syn_csn (.cv z)) (.cv x)))
        (syn_cins2 (syn_csset)))
      (.classMem (syn_cop (syn_csn (.cv a)) (.cv x)) (syn_csset)) (.objMem a x) p0013
      p0014 p0017_e02_recanon
  have p0018 :=
    @g_oqelins4 (syn_csn (.cv a)) (syn_csn (.cv b)) (syn_csn (.cv z)) (.cv x)
      (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
            (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
              (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))))
      p0004
  have p0019 := @g_vex z
  have p0020 :=
    @g_otsnelsi3 (.cv a) (.cv b) (.cv z)
      (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
            (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))
      p0015 p0006 p0019
  have p0021 :=
    @g_elin (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_cins3 (syn_cdisj))
      (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))
  have p0022 := @g_otelins3 (.cv a) (.cv b) (.cv z) (syn_cdisj) p0019
  have p0023 := (Nominal.biimpRefl (syn_wbr (.cv a) (syn_cdisj) (.cv b)))
  have p0024 := @g_brdisj (.cv a) (.cv b) p0015 p0006
  have p0025 :=
    @g_n_3bitr2i
      (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_cins3 (syn_cdisj)))
      (.classMem (syn_cop (.cv a) (.cv b)) (syn_cdisj))
      (syn_wbr (.cv a) (syn_cdisj) (.cv b)) (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
      p0022 p0023 p0024
  have p0026 :=
    @g_trtxp (.cv p) (.cv b) (.cv z) (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)
  have p0027 :=
    @g_anbi2i
      (syn_wbr (.cv p) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))
        (syn_cop (.cv b) (.cv z)))
      (syn_wa (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b))
        (syn_wbr (.cv p) (syn_c2nd) (.cv z)))
      (syn_wbr (.cv p) (syn_ccom (syn_c1st) (syn_c1st)) (.cv a)) p0026
  have p0028 :=
    @g_trtxp (.cv p) (.cv a) (syn_cop (.cv b) (.cv z)) (syn_ccom (syn_c1st) (syn_c1st))
      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))
  have p0029 :=
    @g_anass (syn_wbr (.cv p) (syn_ccom (syn_c1st) (syn_c1st)) (.cv a))
      (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b))
      (syn_wbr (.cv p) (syn_c2nd) (.cv z))
  have p0030 :=
    @g_n_3bitr4i
      (syn_wa (syn_wbr (.cv p) (syn_ccom (syn_c1st) (syn_c1st)) (.cv a))
        (syn_wbr (.cv p) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))
          (syn_cop (.cv b) (.cv z))))
      (syn_wa (syn_wbr (.cv p) (syn_ccom (syn_c1st) (syn_c1st)) (.cv a))
        (syn_wa (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b))
          (syn_wbr (.cv p) (syn_c2nd) (.cv z))))
      (syn_wbr (.cv p) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
        (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))))
      (syn_wa (syn_wa (syn_wbr (.cv p) (syn_ccom (syn_c1st) (syn_c1st)) (.cv a))
          (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b)))
        (syn_wbr (.cv p) (syn_c2nd) (.cv z)))
      p0027 p0028 p0029
  have p0031 :=
    @g_brco x (.cv p) (.cv a) (syn_c1st) (syn_c1st) dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0004
  have p0032 := @g_br1st y (.cv x) (.cv a) dv_cache_0005 dv_cache_0006 p0015
  have p0033 :=
    @g_anbi2i (syn_wbr (.cv x) (syn_c1st) (.cv a))
      (syn_wex y (.classEq (.cv x) (syn_cop (.cv a) (.cv y))))
      (syn_wbr (.cv p) (syn_c1st) (.cv x)) p0032
  have p0034 :=
    @g_n_19_42v (syn_wbr (.cv p) (syn_c1st) (.cv x))
      (.classEq (.cv x) (syn_cop (.cv a) (.cv y))) y dv_cache_0007
  have p0035 :=
    @g_bitr4i
      (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x)) (syn_wbr (.cv x) (syn_c1st) (.cv a)))
      (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x))
        (syn_wex y (.classEq (.cv x) (syn_cop (.cv a) (.cv y)))))
      (syn_wex y (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x))
          (.classEq (.cv x) (syn_cop (.cv a) (.cv y)))))
      p0033 p0034
  have p0036 :=
    @g_exbii
      (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x)) (syn_wbr (.cv x) (syn_c1st) (.cv a)))
      (syn_wex y (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x))
          (.classEq (.cv x) (syn_cop (.cv a) (.cv y)))))
      x p0035
  have p0037 :=
    @g_excom
      (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x)) (.classEq (.cv x) (syn_cop (.cv a) (.cv y))))
      x y
  have p0038 :=
    @g_exancom (syn_wbr (.cv p) (syn_c1st) (.cv x))
      (.classEq (.cv x) (syn_cop (.cv a) (.cv y))) x
  have p0039 := @g_opex (.cv a) (.cv y) p0015 p0007
  have p0040 := @g_breq2 (.cv x) (syn_cop (.cv a) (.cv y)) (.cv p) (syn_c1st)
  have p0041 :=
    @g_ceqsexv (syn_wbr (.cv p) (syn_c1st) (.cv x))
      (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y))) x (syn_cop (.cv a) (.cv y))
      dv_cache_0008 dv_cache_0009 p0039 p0040
  have p0042 :=
    @g_bitri
      (syn_wex x (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x))
          (.classEq (.cv x) (syn_cop (.cv a) (.cv y)))))
      (syn_wex x (syn_wa (.classEq (.cv x) (syn_cop (.cv a) (.cv y)))
          (syn_wbr (.cv p) (syn_c1st) (.cv x))))
      (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y))) p0038 p0041
  have p0043 :=
    @g_exbii
      (syn_wex x (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x))
          (.classEq (.cv x) (syn_cop (.cv a) (.cv y)))))
      (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y))) y p0042
  have p0044 :=
    @g_bitri
      (syn_wex x (syn_wex y (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x))
            (.classEq (.cv x) (syn_cop (.cv a) (.cv y))))))
      (syn_wex y (syn_wex x (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x))
            (.classEq (.cv x) (syn_cop (.cv a) (.cv y))))))
      (syn_wex y (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y)))) p0037 p0043
  have p0045 :=
    @g_n_3bitri (syn_wbr (.cv p) (syn_ccom (syn_c1st) (syn_c1st)) (.cv a))
      (syn_wex x (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x))
          (syn_wbr (.cv x) (syn_c1st) (.cv a))))
      (syn_wex x (syn_wex y (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x))
            (.classEq (.cv x) (syn_cop (.cv a) (.cv y))))))
      (syn_wex y (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y)))) p0031 p0036 p0044
  have p0046 :=
    @g_anbi1i (syn_wbr (.cv p) (syn_ccom (syn_c1st) (syn_c1st)) (.cv a))
      (syn_wex y (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y))))
      (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b)) p0045
  have p0047 :=
    @g_n_19_41v (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y)))
      (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b)) y dv_cache_0010
  have p0048 :=
    @g_br1st z (.cv p) (syn_cop (.cv a) (.cv y)) dv_cache_0011 dv_cache_0012 p0039
  have p0049 :=
    @g_breq1 (.cv p) (syn_cop (syn_cop (.cv a) (.cv y)) (.cv z)) (.cv b)
      (syn_ccom (syn_c2nd) (syn_c1st))
  have p0050 :=
    @g_brco1st (syn_cop (.cv a) (.cv y)) (.cv z) (.cv b) (syn_c2nd) p0039 p0019
  have p0051 := @g_opbr2nd (.cv a) (.cv y) (.cv b) p0015 p0007
  have p0052_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wbr (syn_cop (.cv a) (.cv y)) (syn_c2nd) (.cv b)) (.objEq y b)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_c2nd syn_copab
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
    @g_bitri
      (syn_wbr (syn_cop (syn_cop (.cv a) (.cv y)) (.cv z))
        (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b))
      (syn_wbr (syn_cop (.cv a) (.cv y)) (syn_c2nd) (.cv b)) (.objEq y b) p0050
      p0052_e01_recanon
  have p0053 :=
    @g_syl6bb (.classEq (.cv p) (syn_cop (syn_cop (.cv a) (.cv y)) (.cv z)))
      (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b))
      (syn_wbr (syn_cop (syn_cop (.cv a) (.cv y)) (.cv z))
        (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b))
      (.objEq y b) p0049 p0052
  have p0054 :=
    @g_exlimiv (.classEq (.cv p) (syn_cop (syn_cop (.cv a) (.cv y)) (.cv z)))
      (syn_wb (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b)) (.objEq y b)) z
      dv_cache_0013 p0053
  have p0055 :=
    @g_sylbi (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y)))
      (syn_wex z (.classEq (.cv p) (syn_cop (syn_cop (.cv a) (.cv y)) (.cv z))))
      (syn_wb (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b)) (.objEq y b))
      p0048 p0054
  have p0056 :=
    @g_pm5_32i (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y)))
      (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b)) (.objEq y b) p0055
  have p0057 :=
    @g_exbii
      (syn_wa (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y)))
        (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b)))
      (syn_wa (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y))) (.objEq y b)) y p0056
  have p0058 :=
    @g_exancom (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y))) (.objEq y b) y
  have p0059 :=
    @g_bitri
      (syn_wex y (syn_wa (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y)))
          (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b))))
      (syn_wex y (syn_wa (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y))) (.objEq y b)))
      (syn_wex y (syn_wa (.objEq y b) (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y)))))
      p0057 p0058
  have p0060 :=
    @g_n_3bitr2i
      (syn_wa (syn_wbr (.cv p) (syn_ccom (syn_c1st) (syn_c1st)) (.cv a))
        (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b)))
      (syn_wa (syn_wex y (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y))))
        (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b)))
      (syn_wex y (syn_wa (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y)))
          (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b))))
      (syn_wex y (syn_wa (.objEq y b) (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y)))))
      p0046 p0047 p0059
  have p0061 := @g_opeq2 (.cv y) (.cv b) (.cv a)
  have p0062_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y b) (.classEq (syn_cop (.cv a) (.cv y)) (syn_cop (.cv a) (.cv b)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0061
  have p0062 :=
    @g_breq2d (.objEq y b) (syn_cop (.cv a) (.cv y)) (syn_cop (.cv a) (.cv b)) (.cv p)
      (syn_c1st) p0062_e00_recanon
  have p0063_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv y) (.cv b))
        (syn_wb (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y)))
          (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv b))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_c1st syn_copab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0062
  have p0063 :=
    @g_ceqsexv (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y)))
      (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv b))) y (.cv b) dv_cache_0014
      dv_cache_0015 p0006 p0063_e01_recanon
  have p0064_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wex y
          (syn_wa (.objEq y b) (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y)))))
        (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv b)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl
          syn_wrex syn_cphi syn_c1st syn_copab
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
    @g_bitri
      (syn_wa (syn_wbr (.cv p) (syn_ccom (syn_c1st) (syn_c1st)) (.cv a))
        (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b)))
      (syn_wex y (syn_wa (.objEq y b) (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y)))))
      (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv b))) p0060 p0064_e01_recanon
  have p0065 :=
    @g_anbi1i
      (syn_wa (syn_wbr (.cv p) (syn_ccom (syn_c1st) (syn_c1st)) (.cv a))
        (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b)))
      (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv b)))
      (syn_wbr (.cv p) (syn_c2nd) (.cv z)) p0064
  have p0066 := @g_opex (.cv a) (.cv b) p0015 p0006
  have p0067 := @g_op1st2nd (syn_cop (.cv a) (.cv b)) (.cv z) (.cv p) p0066 p0019
  have p0068 :=
    @g_n_3bitri
      (syn_wbr (.cv p) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
        (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))))
      (syn_wa (syn_wa (syn_wbr (.cv p) (syn_ccom (syn_c1st) (syn_c1st)) (.cv a))
          (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b)))
        (syn_wbr (.cv p) (syn_c2nd) (.cv z)))
      (syn_wa (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv b)))
        (syn_wbr (.cv p) (syn_c2nd) (.cv z)))
      (.classEq (.cv p) (syn_cop (syn_cop (.cv a) (.cv b)) (.cv z))) p0030 p0065 p0067
  have p0069 :=
    @g_rexbii
      (syn_wbr (.cv p) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
        (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))))
      (.classEq (.cv p) (syn_cop (syn_cop (.cv a) (.cv b)) (.cv z))) p (syn_ccup) p0068
  have p0070 :=
    @g_elima p (syn_cop (.cv a) (syn_cop (.cv b) (.cv z)))
      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
      (syn_ccup) dv_cache_0016 dv_cache_0017 dv_cache_0018
  have p0071 :=
    @g_risset p (syn_cop (syn_cop (.cv a) (.cv b)) (.cv z)) (syn_ccup) dv_cache_0019
      dv_cache_0018
  have p0072 :=
    @g_n_3bitr4i
      (syn_wrex p (syn_ccup) (syn_wbr (.cv p) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
            (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
          (syn_cop (.cv a) (syn_cop (.cv b) (.cv z)))))
      (syn_wrex p (syn_ccup) (.classEq (.cv p) (syn_cop (syn_cop (.cv a) (.cv b)) (.cv z))))
      (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_cima
          (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
            (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))
      (.classMem (syn_cop (syn_cop (.cv a) (.cv b)) (.cv z)) (syn_ccup)) p0069 p0070 p0071
  have p0073 := (Nominal.biimpRefl (syn_wbr (syn_cop (.cv a) (.cv b)) (syn_ccup) (.cv z)))
  have p0074 := @g_brcup (.cv a) (.cv b) (.cv z) p0015 p0006
  have p0075 :=
    @g_n_3bitr2i
      (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_cima
          (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
            (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))
      (.classMem (syn_cop (syn_cop (.cv a) (.cv b)) (.cv z)) (syn_ccup))
      (syn_wbr (syn_cop (.cv a) (.cv b)) (syn_ccup) (.cv z))
      (.classEq (.cv z) (syn_cun (.cv a) (.cv b))) p0072 p0073 p0074
  have p0076 :=
    @g_anbi12i
      (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_cins3 (syn_cdisj)))
      (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
      (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_cima
          (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
            (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))
      (.classEq (.cv z) (syn_cun (.cv a) (.cv b))) p0025 p0075
  have p0077 :=
    @g_bitri
      (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_cin (syn_cins3 (syn_cdisj))
          (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
              (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))))
      (syn_wa (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_cins3 (syn_cdisj)))
        (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_cima
            (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
              (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))))
      (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
        (.classEq (.cv z) (syn_cun (.cv a) (.cv b))))
      p0021 p0076
  have p0078 :=
    @g_n_3bitri
      (.classMem (syn_cop (syn_csn (.cv a))
          (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)))) (syn_cins4 (syn_csi3
            (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
                (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                  (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))))))
      (.classMem (syn_cop (syn_csn (.cv a)) (syn_cop (syn_csn (.cv b)) (syn_csn (.cv z))))
        (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
              (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))
      (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_cin (syn_cins3 (syn_cdisj))
          (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
              (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))))
      (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
        (.classEq (.cv z) (syn_cun (.cv a) (.cv b))))
      p0018 p0020 p0077
  have p0079 :=
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (.cv a))
          (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (.objMem a x)
      (.classMem (syn_cop (syn_csn (.cv a))
          (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)))) (syn_cins4 (syn_csi3
            (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
                (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                  (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))))))
      (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
        (.classEq (.cv z) (syn_cun (.cv a) (.cv b))))
      p0017 p0078
  have p0080 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv a))
          (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x))))
        (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
              (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
                  (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv a))
            (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x))))
          (syn_cins2 (syn_cins2 (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv a))
            (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)))) (syn_cins4
            (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
                  (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))))
      (syn_wa (.objMem a x) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
          (.classEq (.cv z) (syn_cun (.cv a) (.cv b)))))
      p0011 p0079
  have p0081 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv a))
          (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x))))
        (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
              (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
                  (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))))
      (syn_wa (.objMem a x) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
          (.classEq (.cv z) (syn_cun (.cv a) (.cv b)))))
      a p0080
  have p0082 :=
    @g_elima1c a (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)))
      (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
            (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
                (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                  (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))))))
      dv_cache_0020 dv_cache_0021
  have p0083 :=
    (Nominal.biimpRefl (syn_wrex a (.cv x) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
          (.classEq (.cv z) (syn_cun (.cv a) (.cv b))))))
  have p0084_e02_recanon :
    Nominal.NPrf
      (syn_wb (syn_wrex a (.cv x) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
            (.classEq (.cv z) (syn_cun (.cv a) (.cv b))))) (syn_wex a (syn_wa (.objMem a x)
            (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
              (.classEq (.cv z) (syn_cun (.cv a) (.cv b))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa]
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
    @g_n_3bitr4i
      (syn_wex a (.classMem (syn_cop (syn_csn (.cv a))
            (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x))))
          (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
                    (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))))))))
      (syn_wex a (syn_wa (.objMem a x) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
            (.classEq (.cv z) (syn_cun (.cv a) (.cv b))))))
      (.classMem (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x))) (syn_cima
          (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
                    (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))))))
          (syn_c1c)))
      (syn_wrex a (.cv x) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
          (.classEq (.cv z) (syn_cun (.cv a) (.cv b)))))
      p0081 p0082 p0084_e02_recanon
  have p0085 :=
    @g_bitri
      (.classMem
        (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))
        (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                  (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
                      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))))))
            (syn_c1c))))
      (.classMem (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x))) (syn_cima
          (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
                    (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))))))
          (syn_c1c)))
      (syn_wrex a (.cv x) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
          (.classEq (.cv z) (syn_cun (.cv a) (.cv b)))))
      p0010 p0084
  have p0086 :=
    @g_anbi12i
      (.classMem
        (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (.objMem b y)
      (.classMem
        (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))
        (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                  (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
                      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))))))
            (syn_c1c))))
      (syn_wrex a (.cv x) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
          (.classEq (.cv z) (syn_cun (.cv a) (.cv b)))))
      p0009 p0085
  have p0087 :=
    @g_bitri
      (.classMem
        (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))
        (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima
              (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                    (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
                        (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                        (syn_ccup)))))) (syn_c1c)))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv b))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))
          (syn_cins2 (syn_cins2 (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv b))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_cins4 (syn_cima
              (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                    (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
                        (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                        (syn_ccup)))))) (syn_c1c)))))
      (syn_wa (.objMem b y) (syn_wrex a (.cv x)
          (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
            (.classEq (.cv z) (syn_cun (.cv a) (.cv b))))))
      p0001 p0086
  have p0088 :=
    @g_exbii
      (.classMem
        (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))
        (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima
              (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                    (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
                        (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                        (syn_ccup)))))) (syn_c1c)))))
      (syn_wa (.objMem b y) (syn_wrex a (.cv x)
          (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
            (.classEq (.cv z) (syn_cun (.cv a) (.cv b))))))
      b p0087
  have p0089 :=
    @g_elima1c b (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))
      (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima
            (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                  (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
                      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))))))
            (syn_c1c))))
      dv_cache_0022 dv_cache_0023
  have p0090 :=
    (Nominal.biimpRefl (syn_wrex b (.cv y) (syn_wrex a (.cv x)
          (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
            (.classEq (.cv z) (syn_cun (.cv a) (.cv b)))))))
  have p0091_e02_recanon :
    Nominal.NPrf
      (syn_wb (syn_wrex b (.cv y) (syn_wrex a (.cv x)
            (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
              (.classEq (.cv z) (syn_cun (.cv a) (.cv b)))))) (syn_wex b (syn_wa (.objMem b y)
            (syn_wrex a (.cv x) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
                (.classEq (.cv z) (syn_cun (.cv a) (.cv b)))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa]
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
    @g_n_3bitr4i
      (syn_wex b (.classMem (syn_cop (syn_csn (.cv b))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))
          (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima
                (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                      (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
                          (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                            (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                          (syn_ccup)))))) (syn_c1c))))))
      (syn_wex b (syn_wa (.objMem b y) (syn_wrex a (.cv x)
            (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
              (.classEq (.cv z) (syn_cun (.cv a) (.cv b)))))))
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cima
          (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima
                (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                      (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
                          (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                            (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                          (syn_ccup)))))) (syn_c1c)))) (syn_c1c)))
      (syn_wrex b (.cv y) (syn_wrex a (.cv x)
          (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
            (.classEq (.cv z) (syn_cun (.cv a) (.cv b))))))
      p0088 p0089 p0091_e02_recanon
  have p0092 :=
    @g_eladdc (.cv z) (.cv x) (.cv y) a b dv_cache_0024 dv_cache_0025 dv_cache_0026
      dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
  have p0093 :=
    @g_rexcom
      (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
        (.classEq (.cv z) (syn_cun (.cv a) (.cv b))))
      a b (.cv x) (.cv y) dv_cache_0027 dv_cache_0028 dv_cache_0030
  have p0094 :=
    @g_bitri (.classMem (.cv z) (syn_cplc (.cv x) (.cv y)))
      (syn_wrex a (.cv x) (syn_wrex b (.cv y)
          (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
            (.classEq (.cv z) (syn_cun (.cv a) (.cv b))))))
      (syn_wrex b (.cv y) (syn_wrex a (.cv x)
          (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
            (.classEq (.cv z) (syn_cun (.cv a) (.cv b))))))
      p0092 p0093
  have p0095 :=
    @g_bitr4i
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cima
          (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima
                (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                      (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
                          (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                            (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                          (syn_ccup)))))) (syn_c1c)))) (syn_c1c)))
      (syn_wrex b (.cv y) (syn_wrex a (.cv x)
          (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
            (.classEq (.cv z) (syn_cun (.cv a) (.cv b))))))
      (.classMem (.cv z) (syn_cplc (.cv x) (.cv y))) p0091 p0094
  have p0096 :=
    @g_releqmpt2 x y z (syn_cvv) (syn_cvv)
      (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima
              (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                    (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
                        (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                        (syn_ccup)))))) (syn_c1c)))) (syn_c1c))
      (syn_cplc (.cv x) (.cv y)) dv_cache_0031 dv_cache_0032 dv_cache_0031 dv_cache_0032
      dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0001 dv_cache_0037
      dv_cache_0038 p0095
  have p0097 :=
    @g_eqtr4i (syn_caddcfn) (syn_cmpt2 x (syn_cvv) y (syn_cvv) (syn_cplc (.cv x) (.cv y)))
      (syn_cdif (syn_cxp (syn_cxp (syn_cvv) (syn_cvv)) (syn_cvv)) (syn_cima
          (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_cima
                (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima
                      (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                            (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
                                (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                                  (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                                (syn_ccup)))))) (syn_c1c)))) (syn_c1c)))) (syn_c1c)))
      p0000 p0096
  have p0098 := @g_vvex
  have p0100 := @g_ssetex
  have p0101 := @g_ins2ex (syn_csset) p0100
  have p0102 := @g_ins2ex (syn_cins2 (syn_csset)) p0101
  have p0103 := @g_disjex
  have p0104 := @g_ins3ex (syn_cdisj) p0103
  have p0105 := @g_n_1stex
  have p0107 := @g_coex (syn_c1st) (syn_c1st) p0105 p0105
  have p0108 := @g_n_2ndex
  have p0110 := @g_coex (syn_c2nd) (syn_c1st) p0108 p0105
  have p0112 := @g_txpex (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd) p0110 p0108
  have p0113 :=
    @g_txpex (syn_ccom (syn_c1st) (syn_c1st))
      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)) p0107 p0112
  have p0114 := @g_cupex
  have p0115 :=
    @g_imaex
      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
      (syn_ccup) p0113 p0114
  have p0116 :=
    @g_inex (syn_cins3 (syn_cdisj))
      (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))
      p0104 p0115
  have p0117 :=
    @g_si3ex
      (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
            (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))
      p0116
  have p0118 :=
    @g_ins4ex
      (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
            (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
              (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))))
      p0117
  have p0119 :=
    @g_inex (syn_cins2 (syn_cins2 (syn_csset)))
      (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
              (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))
      p0102 p0118
  have p0120 := @g_n_1cex
  have p0121 :=
    @g_imaex
      (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
            (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
                (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                  (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))))))
      (syn_c1c) p0119 p0120
  have p0122 :=
    @g_ins4ex
      (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
              (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
                  (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))))))
        (syn_c1c))
      p0121
  have p0123 :=
    @g_inex (syn_cins2 (syn_cins2 (syn_csset)))
      (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
                    (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))))))
          (syn_c1c)))
      p0102 p0122
  have p0125 :=
    @g_imaex
      (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima
            (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                  (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
                      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))))))
            (syn_c1c))))
      (syn_c1c) p0123 p0120
  have p0126 :=
    @g_mpt2exlem (syn_cvv) (syn_cvv)
      (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima
              (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                    (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
                        (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                        (syn_ccup)))))) (syn_c1c)))) (syn_c1c))
      p0098 p0098 p0125
  have p0127 :=
    @g_eqeltri (syn_caddcfn)
      (syn_cdif (syn_cxp (syn_cxp (syn_cvv) (syn_cvv)) (syn_cvv)) (syn_cima
          (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_cima
                (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima
                      (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                            (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima
                                (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                                  (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                                (syn_ccup)))))) (syn_c1c)))) (syn_c1c)))) (syn_c1c)))
      (syn_cvv) p0097 p0126
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

@[expose]
noncomputable def g_addcfn : Nominal.NPrf (syn_wfn (syn_caddcfn) (syn_cvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0002 : x ∉ ((syn_cvv)).fv :=
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
  have dv_cache_0003 : y ∉ ((syn_cvv)).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_addcfn x y
      dv_cache_0001
  have p0001 := @g_vex x
  have p0002 := @g_vex y
  have p0003 := @g_addcex (.cv x) (.cv y) p0001 p0002
  have p0004 :=
    @g_fnmpt2i x y (syn_cvv) (syn_cvv) (syn_cplc (.cv x) (.cv y)) (syn_caddcfn)
      dv_cache_0002 dv_cache_0003 dv_cache_0002 dv_cache_0003 dv_cache_0001 p0000 p0003
  have p0005 := @g_xpvv
  have p0006 := @g_fneq2i (syn_cxp (syn_cvv) (syn_cvv)) (syn_cvv) (syn_caddcfn) p0005
  have p0007 :=
    @g_mpbi (syn_wfn (syn_caddcfn) (syn_cxp (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_caddcfn) (syn_cvv)) p0004 p0006
  exact p0007

@[expose]
noncomputable def g_braddcfn (A : Class) (B : Class) (C : Class)
    (hyp_braddcfn_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_braddcfn_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (syn_wbr (syn_cop A B) (syn_caddcfn) C) (.classEq (syn_cplc A B) C)) :=
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
  have dv_cache_0006 : x ∉ ((syn_cvv)).fv :=
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
  have dv_cache_0007 : y ∉ ((syn_cvv)).fv :=
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
  have dv_cache_0008 : x ∉ ((syn_cplc A (.cv y))).fv :=
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
  have dv_cache_0009 : x ∉ ((syn_cplc A B)).fv :=
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
  have dv_cache_0010 : y ∉ ((syn_cplc A B)).fv :=
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
  have p0000 := @g_addcfn
  have p0001 := @g_opex A B hyp_braddcfn_1 hyp_braddcfn_2
  have p0002 := @g_fnbrfvb (syn_cvv) (syn_cop A B) C (syn_caddcfn)
  have p0003 :=
    @g_mp2an (syn_wfn (syn_caddcfn) (syn_cvv)) (.classMem (syn_cop A B) (syn_cvv))
      (syn_wb (.classEq (syn_cfv (syn_caddcfn) (syn_cop A B)) C)
        (syn_wbr (syn_cop A B) (syn_caddcfn) C))
      p0000 p0001 p0002
  have p0004 := (Nominal.classEqRefl (syn_co A (syn_caddcfn) B))
  have p0005 := @g_addceq1 (.cv x) A (.cv y)
  have p0006 := @g_addceq2 (.cv y) B A
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_addcfn x y
      dv_cache_0001
  have p0008 := @g_addcex A B hyp_braddcfn_1 hyp_braddcfn_2
  have p0009 :=
    @g_ovmpt2 x y A B (syn_cvv) (syn_cvv) (syn_cplc (.cv x) (.cv y)) (syn_cplc A B)
      (syn_caddcfn) (syn_cplc A (.cv y)) dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0001 p0005 p0006 p0007 p0008
  have p0010 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (.classEq (syn_co A (syn_caddcfn) B) (syn_cplc A B)) hyp_braddcfn_1 hyp_braddcfn_2
      p0009
  have p0011 :=
    @g_eqtr3i (syn_co A (syn_caddcfn) B) (syn_cfv (syn_caddcfn) (syn_cop A B))
      (syn_cplc A B) p0004 p0010
  have p0012 := @g_eqeq1i (syn_cfv (syn_caddcfn) (syn_cop A B)) (syn_cplc A B) C p0011
  have p0013 :=
    @g_bitr3i (syn_wbr (syn_cop A B) (syn_caddcfn) C)
      (.classEq (syn_cfv (syn_caddcfn) (syn_cop A B)) C) (.classEq (syn_cplc A B) C) p0003
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

@[expose]
noncomputable def g_funsex : Nominal.NPrf (.classMem (syn_cfuns) (syn_cvv)) :=
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
      ((syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin
                        (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st))
                              (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                        (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid)))
                (syn_c1c))) (syn_c1c)))).fv :=
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
  have dv_cache_0003 : z ∉ ((syn_cop (syn_csn (.cv x)) (.cv f))).fv :=
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
      ((syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima
                        (syn_ctxp (syn_ccnv (syn_c1st))
                          (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                    (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid)))
            (syn_c1c)))).fv :=
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
    y ∉ ((syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f)))).fv :=
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
      ((syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima
                    (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                    (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset)))
          (syn_cins3 (syn_cid)))).fv :=
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
    q ∉ ((syn_cop (.cv p) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x))))).fv :=
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
      ((syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))).fv :=
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
  have dv_cache_0009 : q ∉ ((syn_cop (.cv x) (.cv y))).fv :=
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
    q ∉ ((syn_wbr (.cv p) (syn_c1st) (syn_csn (syn_cop (.cv x) (.cv y))))).fv :=
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
    p ∉ ((syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f)))).fv :=
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
      ((syn_cin (syn_cins4 (syn_cima
              (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
              (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd))))).fv :=
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
  have dv_cache_0013 : p ∉ ((syn_csset)).fv :=
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
  have dv_cache_0014 : p ∉ ((syn_cop (syn_csn (syn_cop (.cv x) (.cv y))) (.cv f))).fv :=
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
      ((syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_cdif (syn_cins2
                        (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st))
                                  (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                            (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset)))
                      (syn_cins3 (syn_cid))) (syn_c1c))) (syn_c1c))) (syn_c1c)))).fv :=
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
  have p0000 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_funs f
  have p0001 :=
    @g_elima1c x (.cv f)
      (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin
                      (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st))
                            (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                      (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid)))
              (syn_c1c))) (syn_c1c)))
      dv_cache_0001 dv_cache_0002
  have p0002 := @g_snex (.cv x)
  have p0003 := @g_vex f
  have p0004 := @g_opex (syn_csn (.cv x)) (.cv f) p0002 p0003
  have p0005 :=
    @g_elcompl (syn_cop (syn_csn (.cv x)) (.cv f))
      (syn_cima (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4
                      (syn_cima (syn_ctxp (syn_ccnv (syn_c1st))
                          (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                    (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid)))
            (syn_c1c))) (syn_c1c))
      p0004
  have p0006 :=
    @g_elima1c z (syn_cop (syn_csn (.cv x)) (.cv f))
      (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima
                      (syn_ctxp (syn_ccnv (syn_c1st))
                        (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                  (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid)))
          (syn_c1c)))
      dv_cache_0003 dv_cache_0004
  have p0007 :=
    @g_elima1c y (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f)))
      (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima
                  (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                  (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset)))
        (syn_cins3 (syn_cid)))
      dv_cache_0005 dv_cache_0006
  have p0008 :=
    @g_eldif
      (syn_cop (syn_csn (.cv y))
        (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f))))
      (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st))
                  (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
            (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset)))
      (syn_cins3 (syn_cid))
  have p0009 := @g_snex (.cv z)
  have p0010 :=
    @g_otelins2 (syn_csn (.cv y)) (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f))
      (syn_cima (syn_cin (syn_cins4 (syn_cima
              (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
              (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))
      p0009
  have p0011 := @g_vex x
  have p0012 := @g_vex y
  have p0013 := @g_opex (.cv x) (.cv y) p0011 p0012
  have p0014 := @g_opelssetsn (syn_cop (.cv x) (.cv y)) (.cv f) p0013 p0003
  have p0015 :=
    (Nominal.biimpRefl (syn_wbr (.cv p) (syn_cin (syn_cins4 (syn_cima
              (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
              (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd))))
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f)))))
  have p0016 :=
    @g_elin
      (syn_cop (.cv p) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f))))
      (syn_cins4 (syn_cima
          (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
          (syn_c1c)))
      (syn_cins2 (syn_cins2 (syn_c2nd)))
  have p0017 :=
    @g_oqelins4 (.cv p) (syn_csn (.cv y)) (syn_csn (.cv x)) (.cv f)
      (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
        (syn_c1c))
      p0003
  have p0018 :=
    @g_elima1c q (syn_cop (.cv p) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x))))
      (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
      dv_cache_0007 dv_cache_0008
  have p0019 :=
    @g_oteltxp (syn_csn (.cv q)) (.cv p) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x)))
      (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))
  have p0020 := @g_opelcnv (syn_csn (.cv q)) (.cv p) (syn_c1st)
  have p0021 := (Nominal.biimpRefl (syn_wbr (.cv p) (syn_c1st) (syn_csn (.cv q))))
  have p0022 :=
    @g_bitr4i (.classMem (syn_cop (syn_csn (.cv q)) (.cv p)) (syn_ccnv (syn_c1st)))
      (.classMem (syn_cop (.cv p) (syn_csn (.cv q))) (syn_c1st))
      (syn_wbr (.cv p) (syn_c1st) (syn_csn (.cv q))) p0020 p0021
  have p0023 := @g_vex q
  have p0024 :=
    @g_otsnelsi3 (.cv q) (.cv y) (.cv x) (syn_ctxp (syn_c2nd) (syn_c1st)) p0023 p0012
      p0011
  have p0025 := @g_oteltxp (.cv q) (.cv y) (.cv x) (syn_c2nd) (syn_c1st)
  have p0026 := (Nominal.biimpRefl (syn_wbr (.cv q) (syn_c1st) (.cv x)))
  have p0027 := (Nominal.biimpRefl (syn_wbr (.cv q) (syn_c2nd) (.cv y)))
  have p0028 :=
    @g_anbi12i (syn_wbr (.cv q) (syn_c1st) (.cv x))
      (.classMem (syn_cop (.cv q) (.cv x)) (syn_c1st))
      (syn_wbr (.cv q) (syn_c2nd) (.cv y))
      (.classMem (syn_cop (.cv q) (.cv y)) (syn_c2nd)) p0026 p0027
  have p0029 :=
    @g_ancom (.classMem (syn_cop (.cv q) (.cv x)) (syn_c1st))
      (.classMem (syn_cop (.cv q) (.cv y)) (syn_c2nd))
  have p0030 :=
    @g_bitr2i
      (syn_wa (syn_wbr (.cv q) (syn_c1st) (.cv x)) (syn_wbr (.cv q) (syn_c2nd) (.cv y)))
      (syn_wa (.classMem (syn_cop (.cv q) (.cv x)) (syn_c1st))
        (.classMem (syn_cop (.cv q) (.cv y)) (syn_c2nd)))
      (syn_wa (.classMem (syn_cop (.cv q) (.cv y)) (syn_c2nd))
        (.classMem (syn_cop (.cv q) (.cv x)) (syn_c1st)))
      p0028 p0029
  have p0031 := @g_op1st2nd (.cv x) (.cv y) (.cv q) p0011 p0012
  have p0032 :=
    @g_n_3bitri
      (.classMem (syn_cop (.cv q) (syn_cop (.cv y) (.cv x))) (syn_ctxp (syn_c2nd) (syn_c1st)))
      (syn_wa (.classMem (syn_cop (.cv q) (.cv y)) (syn_c2nd))
        (.classMem (syn_cop (.cv q) (.cv x)) (syn_c1st)))
      (syn_wa (syn_wbr (.cv q) (syn_c1st) (.cv x)) (syn_wbr (.cv q) (syn_c2nd) (.cv y)))
      (.classEq (.cv q) (syn_cop (.cv x) (.cv y))) p0025 p0030 p0031
  have p0033 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x))))
        (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
      (.classMem (syn_cop (.cv q) (syn_cop (.cv y) (.cv x))) (syn_ctxp (syn_c2nd) (syn_c1st)))
      (.classEq (.cv q) (syn_cop (.cv x) (.cv y))) p0024 p0032
  have p0034 :=
    @g_anbi12ci (.classMem (syn_cop (syn_csn (.cv q)) (.cv p)) (syn_ccnv (syn_c1st)))
      (syn_wbr (.cv p) (syn_c1st) (syn_csn (.cv q)))
      (.classMem (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x))))
        (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
      (.classEq (.cv q) (syn_cop (.cv x) (.cv y))) p0022 p0033
  have p0035 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv q))
          (syn_cop (.cv p) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x)))))
        (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv q)) (.cv p)) (syn_ccnv (syn_c1st))) (.classMem
          (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x))))
          (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))))
      (syn_wa (.classEq (.cv q) (syn_cop (.cv x) (.cv y)))
        (syn_wbr (.cv p) (syn_c1st) (syn_csn (.cv q))))
      p0019 p0034
  have p0036 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv q))
          (syn_cop (.cv p) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x)))))
        (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))))
      (syn_wa (.classEq (.cv q) (syn_cop (.cv x) (.cv y)))
        (syn_wbr (.cv p) (syn_c1st) (syn_csn (.cv q))))
      q p0035
  have p0037 := @g_sneq (.cv q) (syn_cop (.cv x) (.cv y))
  have p0038 :=
    @g_breq2d (.classEq (.cv q) (syn_cop (.cv x) (.cv y))) (syn_csn (.cv q))
      (syn_csn (syn_cop (.cv x) (.cv y))) (.cv p) (syn_c1st) p0037
  have p0039 :=
    @g_ceqsexv (syn_wbr (.cv p) (syn_c1st) (syn_csn (.cv q)))
      (syn_wbr (.cv p) (syn_c1st) (syn_csn (syn_cop (.cv x) (.cv y)))) q
      (syn_cop (.cv x) (.cv y)) dv_cache_0009 dv_cache_0010 p0013 p0038
  have p0040 :=
    @g_n_3bitri
      (.classMem (syn_cop (.cv p) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x)))) (syn_cima
          (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
          (syn_c1c)))
      (syn_wex q (.classMem (syn_cop (syn_csn (.cv q))
            (syn_cop (.cv p) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x)))))
          (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))))
      (syn_wex q (syn_wa (.classEq (.cv q) (syn_cop (.cv x) (.cv y)))
          (syn_wbr (.cv p) (syn_c1st) (syn_csn (.cv q)))))
      (syn_wbr (.cv p) (syn_c1st) (syn_csn (syn_cop (.cv x) (.cv y)))) p0018 p0036 p0039
  have p0041 :=
    @g_bitri
      (.classMem
        (syn_cop (.cv p) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f))))
        (syn_cins4 (syn_cima
            (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
            (syn_c1c))))
      (.classMem (syn_cop (.cv p) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x)))) (syn_cima
          (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
          (syn_c1c)))
      (syn_wbr (.cv p) (syn_c1st) (syn_csn (syn_cop (.cv x) (.cv y)))) p0017 p0040
  have p0042 := @g_otelins2 (.cv p) (syn_csn (.cv x)) (.cv f) (syn_c2nd) p0002
  have p0043 := @g_snex (.cv y)
  have p0044 :=
    @g_otelins2 (.cv p) (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f))
      (syn_cins2 (syn_c2nd)) p0043
  have p0045 := (Nominal.biimpRefl (syn_wbr (.cv p) (syn_c2nd) (.cv f)))
  have p0046 :=
    @g_n_3bitr4i
      (.classMem (syn_cop (.cv p) (syn_cop (syn_csn (.cv x)) (.cv f))) (syn_cins2 (syn_c2nd)))
      (.classMem (syn_cop (.cv p) (.cv f)) (syn_c2nd))
      (.classMem
        (syn_cop (.cv p) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f))))
        (syn_cins2 (syn_cins2 (syn_c2nd))))
      (syn_wbr (.cv p) (syn_c2nd) (.cv f)) p0042 p0044 p0045
  have p0047 :=
    @g_anbi12i
      (.classMem
        (syn_cop (.cv p) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f))))
        (syn_cins4 (syn_cima
            (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
            (syn_c1c))))
      (syn_wbr (.cv p) (syn_c1st) (syn_csn (syn_cop (.cv x) (.cv y))))
      (.classMem
        (syn_cop (.cv p) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f))))
        (syn_cins2 (syn_cins2 (syn_c2nd))))
      (syn_wbr (.cv p) (syn_c2nd) (.cv f)) p0041 p0046
  have p0048 :=
    @g_bitri
      (.classMem
        (syn_cop (.cv p) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f))))
        (syn_cin (syn_cins4 (syn_cima
              (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
              (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))))
      (syn_wa (.classMem (syn_cop (.cv p)
            (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f)))) (syn_cins4
            (syn_cima
              (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
              (syn_c1c)))) (.classMem (syn_cop (.cv p)
            (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f))))
          (syn_cins2 (syn_cins2 (syn_c2nd)))))
      (syn_wa (syn_wbr (.cv p) (syn_c1st) (syn_csn (syn_cop (.cv x) (.cv y))))
        (syn_wbr (.cv p) (syn_c2nd) (.cv f)))
      p0016 p0047
  have p0049 := @g_snex (syn_cop (.cv x) (.cv y))
  have p0050 :=
    @g_op1st2nd (syn_csn (syn_cop (.cv x) (.cv y))) (.cv f) (.cv p) p0049 p0003
  have p0051 :=
    @g_n_3bitri
      (syn_wbr (.cv p) (syn_cin (syn_cins4 (syn_cima
              (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
              (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd))))
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f))))
      (.classMem
        (syn_cop (.cv p) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f))))
        (syn_cin (syn_cins4 (syn_cima
              (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
              (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))))
      (syn_wa (syn_wbr (.cv p) (syn_c1st) (syn_csn (syn_cop (.cv x) (.cv y))))
        (syn_wbr (.cv p) (syn_c2nd) (.cv f)))
      (.classEq (.cv p) (syn_cop (syn_csn (syn_cop (.cv x) (.cv y))) (.cv f))) p0015 p0048
      p0050
  have p0052 :=
    @g_rexbii
      (syn_wbr (.cv p) (syn_cin (syn_cins4 (syn_cima
              (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
              (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd))))
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f))))
      (.classEq (.cv p) (syn_cop (syn_csn (syn_cop (.cv x) (.cv y))) (.cv f))) p
      (syn_csset) p0051
  have p0053 :=
    @g_elima p (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f)))
      (syn_cin (syn_cins4 (syn_cima
            (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
            (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd))))
      (syn_csset) dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0054 :=
    @g_risset p (syn_cop (syn_csn (syn_cop (.cv x) (.cv y))) (.cv f)) (syn_csset)
      dv_cache_0014 dv_cache_0013
  have p0055 :=
    @g_n_3bitr4i
      (syn_wrex p (syn_csset) (syn_wbr (.cv p) (syn_cin (syn_cins4 (syn_cima
                (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd))))
          (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f)))))
      (syn_wrex p (syn_csset)
        (.classEq (.cv p) (syn_cop (syn_csn (syn_cop (.cv x) (.cv y))) (.cv f))))
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f))) (syn_cima
          (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st))
                  (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
            (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset)))
      (.classMem (syn_cop (syn_csn (syn_cop (.cv x) (.cv y))) (.cv f)) (syn_csset)) p0052
      p0053 p0054
  have p0056 := (Nominal.biimpRefl (syn_wbr (.cv x) (.cv f) (.cv y)))
  have p0057 :=
    @g_n_3bitr4i
      (.classMem (syn_cop (syn_csn (syn_cop (.cv x) (.cv y))) (.cv f)) (syn_csset))
      (.classMem (syn_cop (.cv x) (.cv y)) (.cv f))
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f))) (syn_cima
          (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st))
                  (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
            (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset)))
      (syn_wbr (.cv x) (.cv f) (.cv y)) p0014 p0055 p0056
  have p0058 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv y))
          (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f)))) (syn_cins2 (syn_cima
            (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st))
                    (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
              (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))))
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f))) (syn_cima
          (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st))
                  (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
            (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset)))
      (syn_wbr (.cv x) (.cv f) (.cv y)) p0010 p0057
  have p0059 :=
    @g_otelins3 (syn_csn (.cv y)) (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f))
      (syn_cid) p0004
  have p0060 := @g_ideq (syn_csn (.cv y)) (syn_csn (.cv z)) p0009
  have p0061 :=
    (Nominal.biimpRefl (syn_wbr (syn_csn (.cv y)) (syn_cid) (syn_csn (.cv z))))
  have p0062 := @g_sneqb (.cv y) (.cv z) p0012
  have p0063_e02_recanon :
    Nominal.NPrf (syn_wb (.classEq (syn_csn (.cv y)) (syn_csn (.cv z))) (.objEq y z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn
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
    @g_n_3bitr3i (syn_wbr (syn_csn (.cv y)) (syn_cid) (syn_csn (.cv z)))
      (.classEq (syn_csn (.cv y)) (syn_csn (.cv z)))
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_csn (.cv z))) (syn_cid)) (.objEq y z)
      p0060 p0061 p0063_e02_recanon
  have p0064 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv y))
          (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f))))
        (syn_cins3 (syn_cid)))
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_csn (.cv z))) (syn_cid)) (.objEq y z)
      p0059 p0063
  have p0065 :=
    @g_notbii
      (.classMem (syn_cop (syn_csn (.cv y))
          (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f))))
        (syn_cins3 (syn_cid)))
      (.objEq y z) p0064
  have p0066 :=
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (.cv y))
          (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f)))) (syn_cins2 (syn_cima
            (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st))
                    (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
              (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))))
      (syn_wbr (.cv x) (.cv f) (.cv y))
      (.neg (.classMem (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f))))
          (syn_cins3 (syn_cid))))
      (.neg (.objEq y z)) p0058 p0065
  have p0067 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv y))
          (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f)))) (syn_cdif (syn_cins2
            (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st))
                      (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f)))) (syn_cins2
            (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st))
                      (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset)))) (.neg (.classMem
            (syn_cop (syn_csn (.cv y))
              (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f))))
            (syn_cins3 (syn_cid)))))
      (syn_wa (syn_wbr (.cv x) (.cv f) (.cv y)) (.neg (.objEq y z))) p0008 p0066
  have p0068 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv y))
          (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f)))) (syn_cdif (syn_cins2
            (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st))
                      (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))))
      (syn_wa (syn_wbr (.cv x) (.cv f) (.cv y)) (.neg (.objEq y z))) y p0067
  have p0069 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f))) (syn_cima
          (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima
                      (syn_ctxp (syn_ccnv (syn_c1st))
                        (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                  (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid)))
          (syn_c1c)))
      (syn_wex y (.classMem (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f)))) (syn_cdif
            (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st))
                        (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                  (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid)))))
      (syn_wex y (syn_wa (syn_wbr (.cv x) (.cv f) (.cv y)) (.neg (.objEq y z)))) p0007
      p0068
  have p0070 :=
    @g_notbii
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f))) (syn_cima
          (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima
                      (syn_ctxp (syn_ccnv (syn_c1st))
                        (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                  (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid)))
          (syn_c1c)))
      (syn_wex y (syn_wa (syn_wbr (.cv x) (.cv f) (.cv y)) (.neg (.objEq y z)))) p0069
  have p0071 := @g_opex (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f)) p0009 p0004
  have p0072 :=
    @g_elcompl (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f)))
      (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima
                    (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                    (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset)))
          (syn_cins3 (syn_cid))) (syn_c1c))
      p0071
  have p0073 := @g_exanali (syn_wbr (.cv x) (.cv f) (.cv y)) (.objEq y z) y
  have p0074 :=
    @g_con2bii (syn_wex y (syn_wa (syn_wbr (.cv x) (.cv f) (.cv y)) (.neg (.objEq y z))))
      (.all y (.imp (syn_wbr (.cv x) (.cv f) (.cv y)) (.objEq y z))) p0073
  have p0075 :=
    @g_n_3bitr4i
      (.neg (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f))) (syn_cima
            (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima
                        (syn_ctxp (syn_ccnv (syn_c1st))
                          (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                    (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid)))
            (syn_c1c))))
      (.neg (syn_wex y (syn_wa (syn_wbr (.cv x) (.cv f) (.cv y)) (.neg (.objEq y z)))))
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f))) (syn_ccompl
          (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima
                        (syn_ctxp (syn_ccnv (syn_c1st))
                          (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                    (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid)))
            (syn_c1c))))
      (.all y (.imp (syn_wbr (.cv x) (.cv f) (.cv y)) (.objEq y z))) p0070 p0072 p0074
  have p0076 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f))) (syn_ccompl
          (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima
                        (syn_ctxp (syn_ccnv (syn_c1st))
                          (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                    (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid)))
            (syn_c1c))))
      (.all y (.imp (syn_wbr (.cv x) (.cv f) (.cv y)) (.objEq y z))) z p0075
  have p0077 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv x)) (.cv f)) (syn_cima (syn_ccompl (syn_cima (syn_cdif
                (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima
                          (syn_ctxp (syn_ccnv (syn_c1st))
                            (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                      (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid)))
              (syn_c1c))) (syn_c1c)))
      (syn_wex z (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f)))
          (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima
                          (syn_ctxp (syn_ccnv (syn_c1st))
                            (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                      (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid)))
              (syn_c1c)))))
      (syn_wex z (.all y (.imp (syn_wbr (.cv x) (.cv f) (.cv y)) (.objEq y z)))) p0006
      p0076
  have p0078 :=
    @g_notbii
      (.classMem (syn_cop (syn_csn (.cv x)) (.cv f)) (syn_cima (syn_ccompl (syn_cima (syn_cdif
                (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima
                          (syn_ctxp (syn_ccnv (syn_c1st))
                            (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                      (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid)))
              (syn_c1c))) (syn_c1c)))
      (syn_wex z (.all y (.imp (syn_wbr (.cv x) (.cv f) (.cv y)) (.objEq y z)))) p0077
  have p0079 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv x)) (.cv f)) (syn_ccompl (syn_cima (syn_ccompl (syn_cima
                (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima
                            (syn_ctxp (syn_ccnv (syn_c1st))
                              (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                        (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid)))
                (syn_c1c))) (syn_c1c))))
      (.neg (.classMem (syn_cop (syn_csn (.cv x)) (.cv f)) (syn_cima (syn_ccompl (syn_cima
                (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima
                            (syn_ctxp (syn_ccnv (syn_c1st))
                              (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                        (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid)))
                (syn_c1c))) (syn_c1c))))
      (.neg (syn_wex z (.all y (.imp (syn_wbr (.cv x) (.cv f) (.cv y)) (.objEq y z)))))
      p0005 p0078
  have p0080 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv x)) (.cv f)) (syn_ccompl (syn_cima (syn_ccompl (syn_cima
                (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima
                            (syn_ctxp (syn_ccnv (syn_c1st))
                              (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                        (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid)))
                (syn_c1c))) (syn_c1c))))
      (.neg (syn_wex z (.all y (.imp (syn_wbr (.cv x) (.cv f) (.cv y)) (.objEq y z))))) x
      p0079
  have p0081 :=
    @g_bitri
      (.classMem (.cv f) (syn_cima (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_cdif
                    (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima
                              (syn_ctxp (syn_ccnv (syn_c1st))
                                (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                          (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset)))
                    (syn_cins3 (syn_cid))) (syn_c1c))) (syn_c1c))) (syn_c1c)))
      (syn_wex x (.classMem (syn_cop (syn_csn (.cv x)) (.cv f)) (syn_ccompl (syn_cima
              (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima
                              (syn_ctxp (syn_ccnv (syn_c1st))
                                (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                          (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset)))
                    (syn_cins3 (syn_cid))) (syn_c1c))) (syn_c1c)))))
      (syn_wex x
        (.neg (syn_wex z (.all y (.imp (syn_wbr (.cv x) (.cv f) (.cv y)) (.objEq y z))))))
      p0001 p0080
  have p0082 :=
    @g_notbii
      (.classMem (.cv f) (syn_cima (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_cdif
                    (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima
                              (syn_ctxp (syn_ccnv (syn_c1st))
                                (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                          (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset)))
                    (syn_cins3 (syn_cid))) (syn_c1c))) (syn_c1c))) (syn_c1c)))
      (syn_wex x
        (.neg (syn_wex z (.all y (.imp (syn_wbr (.cv x) (.cv f) (.cv y)) (.objEq y z))))))
      p0081
  have p0083 :=
    @g_elcompl (.cv f)
      (syn_cima (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima
                      (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st))
                              (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                        (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid)))
                (syn_c1c))) (syn_c1c))) (syn_c1c))
      p0003
  have p0084 :=
    @g_alex (syn_wex z (.all y (.imp (syn_wbr (.cv x) (.cv f) (.cv y)) (.objEq y z)))) x
  have p0085 :=
    @g_n_3bitr4i
      (.neg (.classMem (.cv f) (syn_cima (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_cdif
                      (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima
                                (syn_ctxp (syn_ccnv (syn_c1st))
                                  (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                            (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset)))
                      (syn_cins3 (syn_cid))) (syn_c1c))) (syn_c1c))) (syn_c1c))))
      (.neg (syn_wex x (.neg
            (syn_wex z (.all y (.imp (syn_wbr (.cv x) (.cv f) (.cv y)) (.objEq y z)))))))
      (.classMem (.cv f) (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_ccompl (syn_cima
                    (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima
                                (syn_ctxp (syn_ccnv (syn_c1st))
                                  (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                            (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset)))
                      (syn_cins3 (syn_cid))) (syn_c1c))) (syn_c1c))) (syn_c1c))))
      (.all x (syn_wex z (.all y (.imp (syn_wbr (.cv x) (.cv f) (.cv y)) (.objEq y z)))))
      p0082 p0083 p0084
  have p0086 :=
    @g_dffun3 x y z (.cv f) dv_cache_0001 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
  have p0087 :=
    @g_bitr4i
      (.classMem (.cv f) (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_ccompl (syn_cima
                    (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima
                                (syn_ctxp (syn_ccnv (syn_c1st))
                                  (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                            (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset)))
                      (syn_cins3 (syn_cid))) (syn_c1c))) (syn_c1c))) (syn_c1c))))
      (.all x (syn_wex z (.all y (.imp (syn_wbr (.cv x) (.cv f) (.cv y)) (.objEq y z)))))
      (syn_wfun (.cv f)) p0085 p0086
  have p0088 :=
    @g_eqabi (syn_wfun (.cv f)) f
      (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_cdif (syn_cins2
                      (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st))
                                (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                          (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset)))
                    (syn_cins3 (syn_cid))) (syn_c1c))) (syn_c1c))) (syn_c1c)))
      dv_cache_0020 p0087
  have p0089 :=
    @g_eqtr4i (syn_cfuns) (.cab f (syn_wfun (.cv f)))
      (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_cdif (syn_cins2
                      (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st))
                                (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                          (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset)))
                    (syn_cins3 (syn_cid))) (syn_c1c))) (syn_c1c))) (syn_c1c)))
      p0000 p0088
  have p0090 := @g_n_1stex
  have p0091 := @g_cnvex (syn_c1st) p0090
  have p0092 := @g_n_2ndex
  have p0094 := @g_txpex (syn_c2nd) (syn_c1st) p0092 p0090
  have p0095 := @g_si3ex (syn_ctxp (syn_c2nd) (syn_c1st)) p0094
  have p0096 :=
    @g_txpex (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))) p0091 p0095
  have p0097 := @g_n_1cex
  have p0098 :=
    @g_imaex (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
      (syn_c1c) p0096 p0097
  have p0099 :=
    @g_ins4ex
      (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
        (syn_c1c))
      p0098
  have p0101 := @g_ins2ex (syn_c2nd) p0092
  have p0102 := @g_ins2ex (syn_cins2 (syn_c2nd)) p0101
  have p0103 :=
    @g_inex
      (syn_cins4 (syn_cima
          (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
          (syn_c1c)))
      (syn_cins2 (syn_cins2 (syn_c2nd))) p0099 p0102
  have p0104 := @g_ssetex
  have p0105 :=
    @g_imaex
      (syn_cin (syn_cins4 (syn_cima
            (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
            (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd))))
      (syn_csset) p0103 p0104
  have p0106 :=
    @g_ins2ex
      (syn_cima (syn_cin (syn_cins4 (syn_cima
              (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
              (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))
      p0105
  have p0107 := @g_idex
  have p0108 := @g_ins3ex (syn_cid) p0107
  have p0109 :=
    @g_difex
      (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st))
                  (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
            (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset)))
      (syn_cins3 (syn_cid)) p0106 p0108
  have p0111 :=
    @g_imaex
      (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima
                  (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                  (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset)))
        (syn_cins3 (syn_cid)))
      (syn_c1c) p0109 p0097
  have p0112 :=
    @g_complex
      (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima
                    (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                    (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset)))
          (syn_cins3 (syn_cid))) (syn_c1c))
      p0111
  have p0114 :=
    @g_imaex
      (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima
                      (syn_ctxp (syn_ccnv (syn_c1st))
                        (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                  (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid)))
          (syn_c1c)))
      (syn_c1c) p0112 p0097
  have p0115 :=
    @g_complex
      (syn_cima (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4
                      (syn_cima (syn_ctxp (syn_ccnv (syn_c1st))
                          (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                    (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid)))
            (syn_c1c))) (syn_c1c))
      p0114
  have p0117 :=
    @g_imaex
      (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin
                      (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st))
                            (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                      (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid)))
              (syn_c1c))) (syn_c1c)))
      (syn_c1c) p0115 p0097
  have p0118 :=
    @g_complex
      (syn_cima (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima
                      (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st))
                              (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                        (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid)))
                (syn_c1c))) (syn_c1c))) (syn_c1c))
      p0117
  have p0119 :=
    @g_eqeltri (syn_cfuns)
      (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_cdif (syn_cins2
                      (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st))
                                (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))
                          (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset)))
                    (syn_cins3 (syn_cid))) (syn_c1c))) (syn_c1c))) (syn_c1c)))
      (syn_cvv) p0089 p0118
  exact p0119

@[expose]
noncomputable def g_elfuns (F : Class)
    (hyp_elfuns_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem F (syn_cfuns)) (syn_wfun F)) :=
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
  have dv_cache_0002 : f ∉ ((syn_wfun F)).fv :=
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
  have p0000 := @g_funeq (.cv f) F
  have p0001 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_funs f
  have p0002 :=
    @g_elab2 (syn_wfun (.cv f)) (syn_wfun F) f F (syn_cfuns) dv_cache_0001 dv_cache_0002
      hyp_elfuns_1 p0000 p0001
  exact p0002

@[expose]
noncomputable def g_elfunsg (F : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem F V) (syn_wb (.classMem F (syn_cfuns)) (syn_wfun F))) :=
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
  have dv_cache_0002 : f ∉ ((Wff.classMem F (syn_cfuns))).fv :=
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
  have dv_cache_0003 : f ∉ ((syn_wfun F)).fv :=
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
  have p0000 := @g_eleq1 (.cv f) F (syn_cfuns)
  have p0001 := @g_funeq (.cv f) F
  have p0002 := @g_vex f
  have p0003 := @g_elfuns (.cv f) p0002
  have p0004 :=
    @g_vtoclbg (.classMem (.cv f) (syn_cfuns)) (syn_wfun (.cv f))
      (.classMem F (syn_cfuns)) (syn_wfun F) f F V dv_cache_0001 dv_cache_0002
      dv_cache_0003 p0000 p0001 p0003
  exact p0004

@[expose]
noncomputable def g_elfunsi (F : Class) :
    Nominal.NPrf (.imp (.classMem F (syn_cfuns)) (syn_wfun F)) :=
  by
  have p0000 := @g_elfunsg F (syn_cfuns)
  have p0001 := @g_ibi (.classMem F (syn_cfuns)) (syn_wfun F) p0000
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

@[expose]
noncomputable def g_fnsex : Nominal.NPrf (.classMem (syn_cfns) (syn_cvv)) :=
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
    f ∉ ((syn_cin (syn_cxp (syn_cfuns) (syn_cvv)) (syn_cimage (syn_c1st)))).fv :=
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
    a ∉ ((syn_cin (syn_cxp (syn_cfuns) (syn_cvv)) (syn_cimage (syn_c1st)))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fns f a
      dv_cache_0001
  have p0001 := @g_vex a
  have p0002 := @g_opelxp (.cv f) (.cv a) (syn_cfuns) (syn_cvv)
  have p0003 :=
    @g_mpbiran2 (.classMem (syn_cop (.cv f) (.cv a)) (syn_cxp (syn_cfuns) (syn_cvv)))
      (.classMem (.cv f) (syn_cfuns)) (.classMem (.cv a) (syn_cvv)) p0001 p0002
  have p0004 := @g_vex f
  have p0005 := @g_elfuns (.cv f) p0004
  have p0006 :=
    @g_bitri (.classMem (syn_cop (.cv f) (.cv a)) (syn_cxp (syn_cfuns) (syn_cvv)))
      (.classMem (.cv f) (syn_cfuns)) (syn_wfun (.cv f)) p0003 p0005
  have p0007 := @g_eqcom (syn_cima (syn_c1st) (.cv f)) (.cv a)
  have p0008 := @g_dfdm4 (.cv f)
  have p0009 := @g_eqeq1i (syn_cdm (.cv f)) (syn_cima (syn_c1st) (.cv f)) (.cv a) p0008
  have p0010 := (Nominal.biimpRefl (syn_wbr (.cv f) (syn_cimage (syn_c1st)) (.cv a)))
  have p0011 := @g_brimage (.cv f) (.cv a) (syn_c1st) p0004 p0001
  have p0012 :=
    @g_bitr3i (.classMem (syn_cop (.cv f) (.cv a)) (syn_cimage (syn_c1st)))
      (syn_wbr (.cv f) (syn_cimage (syn_c1st)) (.cv a))
      (.classEq (.cv a) (syn_cima (syn_c1st) (.cv f))) p0010 p0011
  have p0013 :=
    @g_n_3bitr4ri (.classEq (syn_cima (syn_c1st) (.cv f)) (.cv a))
      (.classEq (.cv a) (syn_cima (syn_c1st) (.cv f)))
      (.classEq (syn_cdm (.cv f)) (.cv a))
      (.classMem (syn_cop (.cv f) (.cv a)) (syn_cimage (syn_c1st))) p0007 p0009 p0012
  have p0014 :=
    @g_anbi12i (.classMem (syn_cop (.cv f) (.cv a)) (syn_cxp (syn_cfuns) (syn_cvv)))
      (syn_wfun (.cv f)) (.classMem (syn_cop (.cv f) (.cv a)) (syn_cimage (syn_c1st)))
      (.classEq (syn_cdm (.cv f)) (.cv a)) p0006 p0013
  have p0015 :=
    @g_elin (syn_cop (.cv f) (.cv a)) (syn_cxp (syn_cfuns) (syn_cvv))
      (syn_cimage (syn_c1st))
  have p0016 := (Nominal.biimpRefl (syn_wfn (.cv f) (.cv a)))
  have p0017 :=
    @g_n_3bitr4i
      (syn_wa (.classMem (syn_cop (.cv f) (.cv a)) (syn_cxp (syn_cfuns) (syn_cvv)))
        (.classMem (syn_cop (.cv f) (.cv a)) (syn_cimage (syn_c1st))))
      (syn_wa (syn_wfun (.cv f)) (.classEq (syn_cdm (.cv f)) (.cv a)))
      (.classMem (syn_cop (.cv f) (.cv a))
        (syn_cin (syn_cxp (syn_cfuns) (syn_cvv)) (syn_cimage (syn_c1st))))
      (syn_wfn (.cv f) (.cv a)) p0014 p0015 p0016
  have p0018 :=
    @g_opabbi2i (syn_wfn (.cv f) (.cv a)) f a
      (syn_cin (syn_cxp (syn_cfuns) (syn_cvv)) (syn_cimage (syn_c1st))) dv_cache_0002
      dv_cache_0003 dv_cache_0004 p0017
  have p0019 :=
    @g_eqtr4i (syn_cfns) (syn_copab f a (syn_wfn (.cv f) (.cv a)))
      (syn_cin (syn_cxp (syn_cfuns) (syn_cvv)) (syn_cimage (syn_c1st))) p0000 p0018
  have p0020 := @g_funsex
  have p0021 := @g_vvex
  have p0022 := @g_xpex (syn_cfuns) (syn_cvv) p0020 p0021
  have p0023 := @g_n_1stex
  have p0024 := @g_imageex (syn_c1st) p0023
  have p0025 :=
    @g_inex (syn_cxp (syn_cfuns) (syn_cvv)) (syn_cimage (syn_c1st)) p0022 p0024
  have p0026 :=
    @g_eqeltri (syn_cfns)
      (syn_cin (syn_cxp (syn_cfuns) (syn_cvv)) (syn_cimage (syn_c1st))) (syn_cvv) p0019
      p0025
  exact p0026

@[expose]
noncomputable def g_brfns (A : Class) (F : Class)
    (hyp_brfns_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (syn_wb (syn_wbr F (syn_cfns) A) (syn_wfn F A)) :=
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
  have dv_cache_0006 : f ∉ ((syn_wfn F (.cv a))).fv :=
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
  have dv_cache_0007 : b ∉ ((syn_wfn F (.cv a))).fv :=
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
  have dv_cache_0010 : a ∉ ((syn_wbr F (syn_cfns) A)).fv :=
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
  have dv_cache_0011 : a ∉ ((syn_wfn F A)).fv :=
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
  have p0000 := @g_brex F A (syn_cfns)
  have p0001 :=
    @g_simprd (syn_wbr F (syn_cfns) A) (.classMem F (syn_cvv)) (.classMem A (syn_cvv))
      p0000
  have p0002 := @g_fndm A F
  have p0003 := @g_eqcomd (syn_wfn F A) (syn_cdm F) A p0002
  have p0004 := @g_dmexg F (syn_cvv)
  have p0005 := Nominal.mp hyp_brfns_1 p0004
  have p0006 := @g_syl6eqel (syn_wfn F A) A (syn_cdm F) (syn_cvv) p0003 p0005
  have p0007 := @g_breq2 (.cv a) A F (syn_cfns)
  have p0008 := @g_fneq2 (.cv a) A F
  have p0009 := @g_vex a
  have p0010 := @g_fneq1 (.cv b) (.cv f) F
  have p0011 := @g_fneq2 (.cv b) (.cv a) F
  have p0012 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fns f b
      dv_cache_0001
  have p0013 :=
    @g_brab (syn_wfn (.cv f) (.cv b)) (syn_wfn F (.cv b)) (syn_wfn F (.cv a)) f b F
      (.cv a) (syn_cfns) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 hyp_brfns_1 p0009 p0010 p0011 p0012
  have p0014 :=
    @g_vtoclbg (syn_wbr F (syn_cfns) (.cv a)) (syn_wfn F (.cv a)) (syn_wbr F (syn_cfns) A)
      (syn_wfn F A) a A (syn_cvv) dv_cache_0009 dv_cache_0010 dv_cache_0011 p0007 p0008
      p0013
  have p0015 :=
    @g_pm5_21nii (syn_wbr F (syn_cfns) A) (.classMem A (syn_cvv)) (syn_wfn F A) p0001
      p0006 p0014
  exact p0015

@[expose]
noncomputable def g_pprodeq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cpprod C A) (syn_cpprod C B))) :=
  by
  have p0000 := @g_coeq1 A B (syn_c2nd)
  have p0001 :=
    @g_txpeq2 (syn_ccom A (syn_c2nd)) (syn_ccom B (syn_c2nd)) (syn_ccom C (syn_c1st))
  have p0002 :=
    @g_syl (.classEq A B) (.classEq (syn_ccom A (syn_c2nd)) (syn_ccom B (syn_c2nd)))
      (.classEq (syn_ctxp (syn_ccom C (syn_c1st)) (syn_ccom A (syn_c2nd)))
        (syn_ctxp (syn_ccom C (syn_c1st)) (syn_ccom B (syn_c2nd))))
      p0000 p0001
  have p0003 := (Nominal.classEqRefl (syn_cpprod C A))
  have p0004 := (Nominal.classEqRefl (syn_cpprod C B))
  have p0005 :=
    @g_n_3eqtr4g (.classEq A B) (syn_ctxp (syn_ccom C (syn_c1st)) (syn_ccom A (syn_c2nd)))
      (syn_ctxp (syn_ccom C (syn_c1st)) (syn_ccom B (syn_c2nd))) (syn_cpprod C A)
      (syn_cpprod C B) p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_qrpprod (A : Class) (B : Class) (C : Class) (D : Class) (R : Class)
    (S : Class) :
    Nominal.NPrf
      (syn_wb (syn_wbr (syn_cop A B) (syn_cpprod R S) (syn_cop C D))
        (syn_wa (syn_wbr A R C) (syn_wbr B S D))) :=
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
  have dv_cache_0001 : a ∉ ((syn_cop (.cv x) (.cv y))).fv := by
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
  have dv_cache_0004 : a ∉ ((syn_c1st)).fv :=
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
  have dv_cache_0006 : a ∉ ((syn_wbr (.cv x) R (.cv z))).fv :=
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
  have dv_cache_0009 : a ∉ ((syn_c2nd)).fv :=
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
  have dv_cache_0011 : a ∉ ((syn_wbr (.cv y) S (.cv w))).fv :=
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
      ((syn_wb (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod R S) (syn_cop C D))
          (syn_wa (syn_wbr (.cv x) R C) (syn_wbr (.cv y) S D)))).fv :=
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
      ((syn_wb (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod R S) (syn_cop C (.cv w)))
          (syn_wa (syn_wbr (.cv x) R C) (syn_wbr (.cv y) S (.cv w))))).fv :=
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
      ((Wff.imp (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
          (syn_wb (syn_wbr (syn_cop A B) (syn_cpprod R S) (syn_cop C D))
            (syn_wa (syn_wbr A R C) (syn_wbr B S D))))).fv :=
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
      ((Wff.imp (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
          (syn_wb (syn_wbr (syn_cop A (.cv y)) (syn_cpprod R S) (syn_cop C D))
            (syn_wa (syn_wbr A R C) (syn_wbr (.cv y) S D))))).fv :=
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
  have p0000 := @g_brex (syn_cop A B) (syn_cop C D) (syn_cpprod R S)
  have p0001 := @g_opexb A B
  have p0002 := @g_opexb C D
  have p0003 :=
    @g_anbi12i (.classMem (syn_cop A B) (syn_cvv))
      (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (.classMem (syn_cop C D) (syn_cvv))
      (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) p0001 p0002
  have p0004 :=
    @g_sylib (syn_wbr (syn_cop A B) (syn_cpprod R S) (syn_cop C D))
      (syn_wa (.classMem (syn_cop A B) (syn_cvv)) (.classMem (syn_cop C D) (syn_cvv)))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
        (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))))
      p0000 p0003
  have p0005 := @g_brex A C R
  have p0006 := @g_brex B D S
  have p0007 :=
    @g_anim12i (syn_wbr A R C) (syn_wa (.classMem A (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wbr B S D) (syn_wa (.classMem B (syn_cvv)) (.classMem D (syn_cvv))) p0005 p0006
  have p0008 :=
    @g_an4 (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv))
      (.classMem D (syn_cvv))
  have p0009 :=
    @g_sylibr (syn_wa (syn_wbr A R C) (syn_wbr B S D))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem C (syn_cvv)))
        (syn_wa (.classMem B (syn_cvv)) (.classMem D (syn_cvv))))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
        (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))))
      p0007 p0008
  have p0010 := @g_opeq1 (.cv x) A (.cv y)
  have p0011 :=
    @g_breq1d (.classEq (.cv x) A) (syn_cop (.cv x) (.cv y)) (syn_cop A (.cv y))
      (syn_cop C D) (syn_cpprod R S) p0010
  have p0012 := @g_breq1 (.cv x) A C R
  have p0013 :=
    @g_anbi1d (.classEq (.cv x) A) (syn_wbr (.cv x) R C) (syn_wbr A R C)
      (syn_wbr (.cv y) S D) p0012
  have p0014 :=
    @g_bibi12d (.classEq (.cv x) A)
      (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod R S) (syn_cop C D))
      (syn_wbr (syn_cop A (.cv y)) (syn_cpprod R S) (syn_cop C D))
      (syn_wa (syn_wbr (.cv x) R C) (syn_wbr (.cv y) S D))
      (syn_wa (syn_wbr A R C) (syn_wbr (.cv y) S D)) p0011 p0013
  have p0015 :=
    @g_imbi2d (.classEq (.cv x) A)
      (syn_wb (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod R S) (syn_cop C D))
        (syn_wa (syn_wbr (.cv x) R C) (syn_wbr (.cv y) S D)))
      (syn_wb (syn_wbr (syn_cop A (.cv y)) (syn_cpprod R S) (syn_cop C D))
        (syn_wa (syn_wbr A R C) (syn_wbr (.cv y) S D)))
      (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) p0014
  have p0016 := @g_opeq2 (.cv y) B A
  have p0017 :=
    @g_breq1d (.classEq (.cv y) B) (syn_cop A (.cv y)) (syn_cop A B) (syn_cop C D)
      (syn_cpprod R S) p0016
  have p0018 := @g_breq1 (.cv y) B D S
  have p0019 :=
    @g_anbi2d (.classEq (.cv y) B) (syn_wbr (.cv y) S D) (syn_wbr B S D) (syn_wbr A R C)
      p0018
  have p0020 :=
    @g_bibi12d (.classEq (.cv y) B)
      (syn_wbr (syn_cop A (.cv y)) (syn_cpprod R S) (syn_cop C D))
      (syn_wbr (syn_cop A B) (syn_cpprod R S) (syn_cop C D))
      (syn_wa (syn_wbr A R C) (syn_wbr (.cv y) S D))
      (syn_wa (syn_wbr A R C) (syn_wbr B S D)) p0017 p0019
  have p0021 :=
    @g_imbi2d (.classEq (.cv y) B)
      (syn_wb (syn_wbr (syn_cop A (.cv y)) (syn_cpprod R S) (syn_cop C D))
        (syn_wa (syn_wbr A R C) (syn_wbr (.cv y) S D)))
      (syn_wb (syn_wbr (syn_cop A B) (syn_cpprod R S) (syn_cop C D))
        (syn_wa (syn_wbr A R C) (syn_wbr B S D)))
      (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) p0020
  have p0022 := @g_opeq1 (.cv z) C (.cv w)
  have p0023 :=
    @g_breq2d (.classEq (.cv z) C) (syn_cop (.cv z) (.cv w)) (syn_cop C (.cv w))
      (syn_cop (.cv x) (.cv y)) (syn_cpprod R S) p0022
  have p0024 := @g_breq2 (.cv z) C (.cv x) R
  have p0025 :=
    @g_anbi1d (.classEq (.cv z) C) (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv x) R C)
      (syn_wbr (.cv y) S (.cv w)) p0024
  have p0026 :=
    @g_bibi12d (.classEq (.cv z) C)
      (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod R S) (syn_cop (.cv z) (.cv w)))
      (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod R S) (syn_cop C (.cv w)))
      (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w)))
      (syn_wa (syn_wbr (.cv x) R C) (syn_wbr (.cv y) S (.cv w))) p0023 p0025
  have p0027 := @g_opeq2 (.cv w) D C
  have p0028 :=
    @g_breq2d (.classEq (.cv w) D) (syn_cop C (.cv w)) (syn_cop C D)
      (syn_cop (.cv x) (.cv y)) (syn_cpprod R S) p0027
  have p0029 := @g_breq2 (.cv w) D (.cv y) S
  have p0030 :=
    @g_anbi2d (.classEq (.cv w) D) (syn_wbr (.cv y) S (.cv w)) (syn_wbr (.cv y) S D)
      (syn_wbr (.cv x) R C) p0029
  have p0031 :=
    @g_bibi12d (.classEq (.cv w) D)
      (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod R S) (syn_cop C (.cv w)))
      (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod R S) (syn_cop C D))
      (syn_wa (syn_wbr (.cv x) R C) (syn_wbr (.cv y) S (.cv w)))
      (syn_wa (syn_wbr (.cv x) R C) (syn_wbr (.cv y) S D)) p0028 p0030
  have p0032 := (Nominal.classEqRefl (syn_cpprod R S))
  have p0033 :=
    @g_breqi (syn_cop (.cv x) (.cv y)) (syn_cop (.cv z) (.cv w)) (syn_cpprod R S)
      (syn_ctxp (syn_ccom R (syn_c1st)) (syn_ccom S (syn_c2nd))) p0032
  have p0034 :=
    @g_trtxp (syn_cop (.cv x) (.cv y)) (.cv z) (.cv w) (syn_ccom R (syn_c1st))
      (syn_ccom S (syn_c2nd))
  have p0035 :=
    @g_bitri
      (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod R S) (syn_cop (.cv z) (.cv w)))
      (syn_wbr (syn_cop (.cv x) (.cv y))
        (syn_ctxp (syn_ccom R (syn_c1st)) (syn_ccom S (syn_c2nd))) (syn_cop (.cv z) (.cv w)))
      (syn_wa (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_ccom R (syn_c1st)) (.cv z))
        (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_ccom S (syn_c2nd)) (.cv w)))
      p0033 p0034
  have p0036 :=
    @g_brco a (syn_cop (.cv x) (.cv y)) (.cv z) R (syn_c1st) dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004
  have p0037 := @g_vex x
  have p0038 := @g_vex y
  have p0039 := @g_opbr1st (.cv x) (.cv y) (.cv a) p0037 p0038
  have p0040 := @g_eqcom (.cv x) (.cv a)
  have p0041_e00_recanon :
    Nominal.NPrf
      (syn_wb (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_c1st) (.cv a)) (.objEq x a)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_c1st syn_copab
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
  have p0041_e01_recanon : Nominal.NPrf (syn_wb (.objEq x a) (.objEq a x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
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
    @g_bitri (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_c1st) (.cv a)) (.objEq x a)
      (.objEq a x) p0041_e00_recanon p0041_e01_recanon
  have p0042 :=
    @g_anbi1i (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_c1st) (.cv a)) (.objEq a x)
      (syn_wbr (.cv a) R (.cv z)) p0041
  have p0043 :=
    @g_exbii
      (syn_wa (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_c1st) (.cv a))
        (syn_wbr (.cv a) R (.cv z)))
      (syn_wa (.objEq a x) (syn_wbr (.cv a) R (.cv z))) a p0042
  have p0044 :=
    @g_bitri (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_ccom R (syn_c1st)) (.cv z))
      (syn_wex a (syn_wa (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_c1st) (.cv a))
          (syn_wbr (.cv a) R (.cv z))))
      (syn_wex a (syn_wa (.objEq a x) (syn_wbr (.cv a) R (.cv z)))) p0036 p0043
  have p0045 := @g_breq1 (.cv a) (.cv x) (.cv z) R
  have p0046 :=
    @g_ceqsexv (syn_wbr (.cv a) R (.cv z)) (syn_wbr (.cv x) R (.cv z)) a (.cv x)
      dv_cache_0005 dv_cache_0006 p0037 p0045
  have p0047_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wex a (syn_wa (.objEq a x) (syn_wbr (.cv a) R (.cv z))))
        (syn_wbr (.cv x) R (.cv z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl
          syn_wrex syn_cphi
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
    @g_bitri (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_ccom R (syn_c1st)) (.cv z))
      (syn_wex a (syn_wa (.objEq a x) (syn_wbr (.cv a) R (.cv z))))
      (syn_wbr (.cv x) R (.cv z)) p0044 p0047_e01_recanon
  have p0048 :=
    @g_brco a (syn_cop (.cv x) (.cv y)) (.cv w) S (syn_c2nd) dv_cache_0001 dv_cache_0007
      dv_cache_0008 dv_cache_0009
  have p0049 := @g_opbr2nd (.cv x) (.cv y) (.cv a) p0037 p0038
  have p0050 := @g_eqcom (.cv y) (.cv a)
  have p0051_e00_recanon :
    Nominal.NPrf
      (syn_wb (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_c2nd) (.cv a)) (.objEq y a)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_c2nd syn_copab
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
  have p0051_e01_recanon : Nominal.NPrf (syn_wb (.objEq y a) (.objEq a y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
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
    @g_bitri (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_c2nd) (.cv a)) (.objEq y a)
      (.objEq a y) p0051_e00_recanon p0051_e01_recanon
  have p0052 :=
    @g_anbi1i (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_c2nd) (.cv a)) (.objEq a y)
      (syn_wbr (.cv a) S (.cv w)) p0051
  have p0053 :=
    @g_exbii
      (syn_wa (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_c2nd) (.cv a))
        (syn_wbr (.cv a) S (.cv w)))
      (syn_wa (.objEq a y) (syn_wbr (.cv a) S (.cv w))) a p0052
  have p0054 :=
    @g_bitri (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_ccom S (syn_c2nd)) (.cv w))
      (syn_wex a (syn_wa (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_c2nd) (.cv a))
          (syn_wbr (.cv a) S (.cv w))))
      (syn_wex a (syn_wa (.objEq a y) (syn_wbr (.cv a) S (.cv w)))) p0048 p0053
  have p0055 := @g_breq1 (.cv a) (.cv y) (.cv w) S
  have p0056 :=
    @g_ceqsexv (syn_wbr (.cv a) S (.cv w)) (syn_wbr (.cv y) S (.cv w)) a (.cv y)
      dv_cache_0010 dv_cache_0011 p0038 p0055
  have p0057_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wex a (syn_wa (.objEq a y) (syn_wbr (.cv a) S (.cv w))))
        (syn_wbr (.cv y) S (.cv w))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl
          syn_wrex syn_cphi
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
    @g_bitri (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_ccom S (syn_c2nd)) (.cv w))
      (syn_wex a (syn_wa (.objEq a y) (syn_wbr (.cv a) S (.cv w))))
      (syn_wbr (.cv y) S (.cv w)) p0054 p0057_e01_recanon
  have p0058 :=
    @g_anbi12i (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_ccom R (syn_c1st)) (.cv z))
      (syn_wbr (.cv x) R (.cv z))
      (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_ccom S (syn_c2nd)) (.cv w))
      (syn_wbr (.cv y) S (.cv w)) p0047 p0057
  have p0059 :=
    @g_bitri
      (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod R S) (syn_cop (.cv z) (.cv w)))
      (syn_wa (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_ccom R (syn_c1st)) (.cv z))
        (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_ccom S (syn_c2nd)) (.cv w)))
      (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w))) p0035 p0058
  have p0060 :=
    @g_vtocl2g
      (syn_wb (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod R S) (syn_cop (.cv z) (.cv w)))
        (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w))))
      (syn_wb (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod R S) (syn_cop C (.cv w)))
        (syn_wa (syn_wbr (.cv x) R C) (syn_wbr (.cv y) S (.cv w))))
      (syn_wb (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod R S) (syn_cop C D))
        (syn_wa (syn_wbr (.cv x) R C) (syn_wbr (.cv y) S D)))
      z w C D (syn_cvv) (syn_cvv) dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
      dv_cache_0016 p0026 p0031 p0059
  have p0061 :=
    @g_vtocl2g
      (.imp (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
        (syn_wb (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_cpprod R S) (syn_cop C D))
          (syn_wa (syn_wbr (.cv x) R C) (syn_wbr (.cv y) S D))))
      (.imp (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
        (syn_wb (syn_wbr (syn_cop A (.cv y)) (syn_cpprod R S) (syn_cop C D))
          (syn_wa (syn_wbr A R C) (syn_wbr (.cv y) S D))))
      (.imp (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
        (syn_wb (syn_wbr (syn_cop A B) (syn_cpprod R S) (syn_cop C D))
          (syn_wa (syn_wbr A R C) (syn_wbr B S D))))
      x y A B (syn_cvv) (syn_cvv) dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
      dv_cache_0021 p0015 p0021 p0060
  have p0062 :=
    @g_imp (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (syn_wb (syn_wbr (syn_cop A B) (syn_cpprod R S) (syn_cop C D))
        (syn_wa (syn_wbr A R C) (syn_wbr B S D)))
      p0061
  have p0063 :=
    @g_pm5_21nii (syn_wbr (syn_cop A B) (syn_cpprod R S) (syn_cop C D))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
        (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))))
      (syn_wa (syn_wbr A R C) (syn_wbr B S D)) p0004 p0009 p0062
  exact p0063

@[expose]
noncomputable def g_pprodexg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_cpprod A B) (syn_cvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cpprod A B))
  have p0001 := @g_n_1stex
  have p0002 := @g_coexg A (syn_c1st) V (syn_cvv)
  have p0003 :=
    @g_mpan2 (.classMem A V) (.classMem (syn_c1st) (syn_cvv))
      (.classMem (syn_ccom A (syn_c1st)) (syn_cvv)) p0001 p0002
  have p0004 := @g_n_2ndex
  have p0005 := @g_coexg B (syn_c2nd) W (syn_cvv)
  have p0006 :=
    @g_mpan2 (.classMem B W) (.classMem (syn_c2nd) (syn_cvv))
      (.classMem (syn_ccom B (syn_c2nd)) (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_txpexg (syn_ccom A (syn_c1st)) (syn_ccom B (syn_c2nd)) (syn_cvv) (syn_cvv)
  have p0008 :=
    @g_syl2an (.classMem A V) (.classMem (syn_ccom A (syn_c1st)) (syn_cvv))
      (.classMem (syn_ccom B (syn_c2nd)) (syn_cvv))
      (.classMem (syn_ctxp (syn_ccom A (syn_c1st)) (syn_ccom B (syn_c2nd))) (syn_cvv))
      (.classMem B W) p0003 p0006 p0007
  have p0009 :=
    @g_syl5eqel (syn_wa (.classMem A V) (.classMem B W)) (syn_cpprod A B)
      (syn_ctxp (syn_ccom A (syn_c1st)) (syn_ccom B (syn_c2nd))) (syn_cvv) p0000 p0008
  exact p0009

@[expose]
noncomputable def g_pprodex (A : Class) (B : Class)
    (hyp_pprodex_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_pprodex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cpprod A B) (syn_cvv)) :=
  by
  have p0000 := @g_pprodexg A B (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (.classMem (syn_cpprod A B) (syn_cvv)) hyp_pprodex_1 hyp_pprodex_2 p0000
  exact p0001


end NFChoice.DirectNominalPrf.WPPReplay

end
