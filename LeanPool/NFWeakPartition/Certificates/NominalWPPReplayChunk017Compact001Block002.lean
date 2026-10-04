/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk017Compact001Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk017Compact001Part006`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_siecsnndv`. -/
@[expose]
noncomputable def gSiecsnndv (u : Var) (R : Class) (_dv_R_u : u ∉ R.fv) :
    Nominal.NPrf
      (.classEq (synCec (synCsn (.cv u)) (synCsi R)) (synCpw1 (synCec (.cv u) R))) :=
  by
  let proofSupport : Finset Var := ({ u } : Finset Var) ∪ R.fv
  let p : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let z : Var := freshVar proofSupport 3
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_ne_u : p ≠ u := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_ne_u : x ≠ u := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_ne_u : y ≠ u := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_z_ne_u : z ≠ u := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_p_ne_x : p ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_p : x ≠ p := Ne.symm fresh_p_ne_x
  have fresh_p_ne_y : p ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_p : y ≠ p := Ne.symm fresh_p_ne_y
  have fresh_p_ne_z : p ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_z_ne_p : z ≠ p := Ne.symm fresh_p_ne_z
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have dv_cache_0001 : x ∉ ((synCsn (.cv u))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_u,
          not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCsn (.cv u))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_u,
          not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_p, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_p, not_false_eq_true])
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
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0008 : z ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((synCec (.cv u) R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_u, fresh_z_not_R, or_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ ((Wff.classEq (.cv p) (synCsn (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_p, fresh_z_ne_y, or_false, not_false_eq_true])
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
  have dv_cache_0012 : x ∉ ((Wff.classMem (.cv p) (synCpw1 (synCec (.cv u) R)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_p, fresh_x_ne_u, fresh_x_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0013 : y ∉ ((Wff.classMem (.cv p) (synCpw1 (synCec (.cv u) R)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_p, fresh_y_ne_u, fresh_y_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0014 : y ∉ ((synCec (.cv u) R)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_u, fresh_y_not_R, or_false, not_false_eq_true])
  have dv_cache_0015 :
    y ∉ ((Wff.classMem (.cv p) (synCec (synCsn (.cv u)) (synCsi R)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_p, fresh_y_ne_u, fresh_y_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0016 : p ∉ ((synCec (synCsn (.cv u)) (synCsi R))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_u, fresh_p_not_R, or_false, not_false_eq_true])
  have dv_cache_0017 : p ∉ ((synCpw1 (synCec (.cv u) R))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_u, fresh_p_not_R, or_false, not_false_eq_true])
  have p0000 := @gElec (.cv p) (synCsn (.cv u)) (synCsi R)
  have p0001 :=
    @gBiimpi (.classMem (.cv p) (synCec (synCsn (.cv u)) (synCsi R)))
      (synWbr (synCsn (.cv u)) (synCsi R) (.cv p)) p0000
  have p0002 :=
    @gBrsi x y (synCsn (.cv u)) (.cv p) R dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0003 :=
    @gSylib (.classMem (.cv p) (synCec (synCsn (.cv u)) (synCsi R)))
      (synWbr (synCsn (.cv u)) (synCsi R) (.cv p))
      (synWex x (synWex y (synW3a (.classEq (synCsn (.cv u)) (synCsn (.cv x)))
            (.classEq (.cv p) (synCsn (.cv y))) (synWbr (.cv x) R (.cv y)))))
      p0001 p0002
  have p0004 :=
    @gSimp3 (.classEq (synCsn (.cv u)) (synCsn (.cv x)))
      (.classEq (.cv p) (synCsn (.cv y))) (synWbr (.cv x) R (.cv y))
  have p0005 :=
    @gSimp1 (.classEq (synCsn (.cv u)) (synCsn (.cv x)))
      (.classEq (.cv p) (synCsn (.cv y))) (synWbr (.cv x) R (.cv y))
  have p0006 := @gVex u
  have p0007 := @gSneqr (.cv u) (.cv x) p0006
  have p0008 :=
    @gSyl
      (synW3a (.classEq (synCsn (.cv u)) (synCsn (.cv x)))
        (.classEq (.cv p) (synCsn (.cv y))) (synWbr (.cv x) R (.cv y)))
      (.classEq (synCsn (.cv u)) (synCsn (.cv x))) (.classEq (.cv u) (.cv x)) p0005
      p0007
  have p0009 :=
    @gBreq1d
      (synW3a (.classEq (synCsn (.cv u)) (synCsn (.cv x)))
        (.classEq (.cv p) (synCsn (.cv y))) (synWbr (.cv x) R (.cv y)))
      (.cv u) (.cv x) (.cv y) R p0008
  have p0010 :=
    @gMpbird
      (synW3a (.classEq (synCsn (.cv u)) (synCsn (.cv x)))
        (.classEq (.cv p) (synCsn (.cv y))) (synWbr (.cv x) R (.cv y)))
      (synWbr (.cv u) R (.cv y)) (synWbr (.cv x) R (.cv y)) p0004 p0009
  have p0011 := @gElec (.cv y) (.cv u) R
  have p0012 :=
    @gSylibr
      (synW3a (.classEq (synCsn (.cv u)) (synCsn (.cv x)))
        (.classEq (.cv p) (synCsn (.cv y))) (synWbr (.cv x) R (.cv y)))
      (synWbr (.cv u) R (.cv y)) (.classMem (.cv y) (synCec (.cv u) R)) p0010 p0011
  have p0013 :=
    @gSimp2 (.classEq (synCsn (.cv u)) (synCsn (.cv x)))
      (.classEq (.cv p) (synCsn (.cv y))) (synWbr (.cv x) R (.cv y))
  have p0014 :=
    @gJca
      (synW3a (.classEq (synCsn (.cv u)) (synCsn (.cv x)))
        (.classEq (.cv p) (synCsn (.cv y))) (synWbr (.cv x) R (.cv y)))
      (.classMem (.cv y) (synCec (.cv u) R)) (.classEq (.cv p) (synCsn (.cv y))) p0012
      p0013
  have p0015 := @gId (.classEq (.cv z) (.cv y))
  have p0016 := @gSneqd (.classEq (.cv z) (.cv y)) (.cv z) (.cv y) p0015
  have p0017 :=
    @gEqeq2d (.classEq (.cv z) (.cv y)) (synCsn (.cv z)) (synCsn (.cv y)) (.cv p) p0016
  have p0018 :=
    @gRspcev (.classEq (.cv p) (synCsn (.cv z))) (.classEq (.cv p) (synCsn (.cv y))) z
      (.cv y) (synCec (.cv u) R) dv_cache_0008 dv_cache_0009 dv_cache_0010 p0017
  have p0019 :=
    @gSyl
      (synW3a (.classEq (synCsn (.cv u)) (synCsn (.cv x)))
        (.classEq (.cv p) (synCsn (.cv y))) (synWbr (.cv x) R (.cv y)))
      (synWa (.classMem (.cv y) (synCec (.cv u) R)) (.classEq (.cv p) (synCsn (.cv y))))
      (synWrex z (synCec (.cv u) R) (.classEq (.cv p) (synCsn (.cv z)))) p0014 p0018
  have p0020 := @gElpw1 z (.cv p) (synCec (.cv u) R) dv_cache_0011 dv_cache_0009
  have p0021 :=
    @gSylibr
      (synW3a (.classEq (synCsn (.cv u)) (synCsn (.cv x)))
        (.classEq (.cv p) (synCsn (.cv y))) (synWbr (.cv x) R (.cv y)))
      (synWrex z (synCec (.cv u) R) (.classEq (.cv p) (synCsn (.cv z))))
      (.classMem (.cv p) (synCpw1 (synCec (.cv u) R))) p0019 p0020
  have p0022 :=
    @gExlimivv
      (synW3a (.classEq (synCsn (.cv u)) (synCsn (.cv x)))
        (.classEq (.cv p) (synCsn (.cv y))) (synWbr (.cv x) R (.cv y)))
      (.classMem (.cv p) (synCpw1 (synCec (.cv u) R))) x y dv_cache_0012 dv_cache_0013
      p0021
  have p0023 :=
    @gSyl (.classMem (.cv p) (synCec (synCsn (.cv u)) (synCsi R)))
      (synWex x (synWex y (synW3a (.classEq (synCsn (.cv u)) (synCsn (.cv x)))
            (.classEq (.cv p) (synCsn (.cv y))) (synWbr (.cv x) R (.cv y)))))
      (.classMem (.cv p) (synCpw1 (synCec (.cv u) R))) p0003 p0022
  have p0024 := @gElpw1 y (.cv p) (synCec (.cv u) R) dv_cache_0004 dv_cache_0014
  have p0025 :=
    @gBiimpi (.classMem (.cv p) (synCpw1 (synCec (.cv u) R)))
      (synWrex y (synCec (.cv u) R) (.classEq (.cv p) (synCsn (.cv y)))) p0024
  have p0026 :=
    @gSimpl (.classMem (.cv y) (synCec (.cv u) R)) (.classEq (.cv p) (synCsn (.cv y)))
  have p0028 :=
    @gSylib
      (synWa (.classMem (.cv y) (synCec (.cv u) R)) (.classEq (.cv p) (synCsn (.cv y))))
      (.classMem (.cv y) (synCec (.cv u) R)) (synWbr (.cv u) R (.cv y)) p0026 p0011
  have p0030 := @gVex y
  have p0031 := @gBrsnsi (.cv u) (.cv y) R p0006 p0030
  have p0032 :=
    @gSylibr
      (synWa (.classMem (.cv y) (synCec (.cv u) R)) (.classEq (.cv p) (synCsn (.cv y))))
      (synWbr (.cv u) R (.cv y))
      (synWbr (synCsn (.cv u)) (synCsi R) (synCsn (.cv y))) p0028 p0031
  have p0033 :=
    @gSimpr (.classMem (.cv y) (synCec (.cv u) R)) (.classEq (.cv p) (synCsn (.cv y)))
  have p0034 :=
    @gBreq2d
      (synWa (.classMem (.cv y) (synCec (.cv u) R)) (.classEq (.cv p) (synCsn (.cv y))))
      (.cv p) (synCsn (.cv y)) (synCsn (.cv u)) (synCsi R) p0033
  have p0035 :=
    @gMpbird
      (synWa (.classMem (.cv y) (synCec (.cv u) R)) (.classEq (.cv p) (synCsn (.cv y))))
      (synWbr (synCsn (.cv u)) (synCsi R) (.cv p))
      (synWbr (synCsn (.cv u)) (synCsi R) (synCsn (.cv y))) p0032 p0034
  have p0037 :=
    @gSylibr
      (synWa (.classMem (.cv y) (synCec (.cv u) R)) (.classEq (.cv p) (synCsn (.cv y))))
      (synWbr (synCsn (.cv u)) (synCsi R) (.cv p))
      (.classMem (.cv p) (synCec (synCsn (.cv u)) (synCsi R))) p0035 p0000
  have p0038 :=
    @gRexlimiva (.classEq (.cv p) (synCsn (.cv y)))
      (.classMem (.cv p) (synCec (synCsn (.cv u)) (synCsi R))) y (synCec (.cv u) R)
      dv_cache_0015 p0037
  have p0039 :=
    @gSyl (.classMem (.cv p) (synCpw1 (synCec (.cv u) R)))
      (synWrex y (synCec (.cv u) R) (.classEq (.cv p) (synCsn (.cv y))))
      (.classMem (.cv p) (synCec (synCsn (.cv u)) (synCsi R))) p0025 p0038
  have p0040 :=
    @gImpbii (.classMem (.cv p) (synCec (synCsn (.cv u)) (synCsi R)))
      (.classMem (.cv p) (synCpw1 (synCec (.cv u) R))) p0023 p0039
  have p0041 :=
    @gEqriv p (synCec (synCsn (.cv u)) (synCsi R)) (synCpw1 (synCec (.cv u) R))
      dv_cache_0016 dv_cache_0017 p0040
  exact p0041

/-- Checked nominal proof certificate identified upstream as `g_siecsnclndv`. -/
@[expose]
noncomputable def gSiecsnclndv (C : Class) (R : Class) :
    Nominal.NPrf
      (.imp (.classMem C (synCvv))
        (.classEq (synCec (synCsn C) (synCsi R)) (synCpw1 (synCec C R)))) :=
  by
  let proofSupport : Finset Var := C.fv ∪ R.fv
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have dv_cache_0001 : u ∉ (R).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_R, not_false_eq_true])
  have dv_cache_0002 : u ∉ (C).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_C, not_false_eq_true])
  have dv_cache_0003 :
    u ∉ ((Wff.classEq (synCec (synCsn C) (synCsi R)) (synCpw1 (synCec C R)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          fresh_u_not_C, fresh_u_not_R, or_false, not_false_eq_true])
  have dv_cache_0004 : u ∉ ((Wff.classMem C (synCvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_u_not_C, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @gId (.classMem C (synCvv))
  have p0001 := @gSimpr (.classMem C (synCvv)) (.classEq (.cv u) C)
  have p0002 := @gSneq (.cv u) C
  have p0003 :=
    @gSyl (synWa (.classMem C (synCvv)) (.classEq (.cv u) C)) (.classEq (.cv u) C)
      (.classEq (synCsn (.cv u)) (synCsn C)) p0001 p0002
  have p0004 := @gEceq1 (synCsn (.cv u)) (synCsn C) (synCsi R)
  have p0005 :=
    @gSyl (synWa (.classMem C (synCvv)) (.classEq (.cv u) C))
      (.classEq (synCsn (.cv u)) (synCsn C))
      (.classEq (synCec (synCsn (.cv u)) (synCsi R)) (synCec (synCsn C) (synCsi R)))
      p0003 p0004
  have p0007 := @gEceq1 (.cv u) C R
  have p0008 :=
    @gSyl (synWa (.classMem C (synCvv)) (.classEq (.cv u) C)) (.classEq (.cv u) C)
      (.classEq (synCec (.cv u) R) (synCec C R)) p0001 p0007
  have p0009 := @gPw1eq (synCec (.cv u) R) (synCec C R)
  have p0010 :=
    @gSyl (synWa (.classMem C (synCvv)) (.classEq (.cv u) C))
      (.classEq (synCec (.cv u) R) (synCec C R))
      (.classEq (synCpw1 (synCec (.cv u) R)) (synCpw1 (synCec C R))) p0008 p0009
  have p0011 :=
    @gEqeq12d (synWa (.classMem C (synCvv)) (.classEq (.cv u) C))
      (synCec (synCsn (.cv u)) (synCsi R)) (synCec (synCsn C) (synCsi R))
      (synCpw1 (synCec (.cv u) R)) (synCpw1 (synCec C R)) p0005 p0010
  have p0012 := @gSiecsnndv u R dv_cache_0001
  have p0013 :=
    @gA1i
      (.classEq (synCec (synCsn (.cv u)) (synCsi R)) (synCpw1 (synCec (.cv u) R)))
      (.classMem C (synCvv)) p0012
  have p0014 :=
    @gVtocld (.classMem C (synCvv))
      (.classEq (synCec (synCsn (.cv u)) (synCsi R)) (synCpw1 (synCec (.cv u) R)))
      (.classEq (synCec (synCsn C) (synCsi R)) (synCpw1 (synCec C R))) u C (synCvv)
      dv_cache_0002 dv_cache_0003 dv_cache_0004 p0000 p0011 p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_f1oclassimfreeclndv`. -/
@[expose]
noncomputable def gF1oclassimfreeclndv (v : Var) (A : Class) (B : Class) (Q : Class)
    (S : Class) (T : Class) (F : Class) (dv_A_v : v ∉ A.fv) (_dv_B_v : v ∉ B.fv)
    (dv_F_v : v ∉ F.fv) (dv_Q_v : v ∉ Q.fv) (dv_S_v : v ∉ S.fv) (dv_T_v : v ∉ T.fv)
    (hyp_f1oclassimfreeclndv_1 : Nominal.NPrf (synWf1o F A B))
    (hyp_f1oclassimfreeclndv_2 : Nominal.NPrf (synWss (synCec Q T) A))
    (hyp_f1oclassimfreeclndv_3 : Nominal.NPrf (synWss (synCec (synCfv F Q) S) B))
    (hyp_f1oclassimfreeclndv_4 : Nominal.NPrf (synWral v A
          (synWb (synWbr Q T (.cv v)) (synWbr (synCfv F Q) S (synCfv F (.cv v))))))
    (_hyp_f1oclassimfreeclndv_5 : Nominal.NPrf (.classMem Q A)) :
    Nominal.NPrf (.classEq (synCima F (synCec Q T)) (synCec (synCfv F Q) S)) :=
  by
  let proofSupport : Finset Var :=
    ({ v } : Finset Var) ∪ A.fv ∪ B.fv ∪ Q.fv ∪ S.fv ∪ T.fv ∪ F.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_v : z ≠ v := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_v_ne_z : v ≠ z := Ne.symm fresh_z_ne_v
  have fresh_z_not_Q : z ∉ Q.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_S : z ∉ S.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_T : z ∉ T.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : v ∉ ((synCfv (synCcnv F) (.cv z))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_z, dv_F_v, or_false, not_false_eq_true])
  have dv_cache_0002 : v ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_v, not_false_eq_true])
  have dv_cache_0003 :
    v ∉
      ((synWb (synWbr Q T (synCfv (synCcnv F) (.cv z)))
          (synWbr (synCfv F Q) S (synCfv F (synCfv (synCcnv F) (.cv z)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_Q_v, fresh_v_ne_z, dv_F_v, dv_T_v, dv_S_v, or_false,
          not_false_eq_true])
  have dv_cache_0004 : z ∉ ((synCima F (synCec Q T))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, Finset.mem_union,
          fresh_z_not_F, fresh_z_not_Q, fresh_z_not_T, or_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((synCec (synCfv F Q) S)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          fresh_z_not_Q, fresh_z_not_F, fresh_z_not_S, or_false, not_false_eq_true])
  have p0000 := @gId (.classMem (.cv z) (synCima F (synCec Q T)))
  have p0001 := @gImassrn F (synCec Q T)
  have p0002 := @gF1of A B F
  have p0003 := Nominal.mp hyp_f1oclassimfreeclndv_1 p0002
  have p0004 := @gFrn A B F
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @gPm32i (synWss (synCima F (synCec Q T)) (synCrn F)) (synWss (synCrn F) B)
      p0001 p0005
  have p0007 := @gSstr (synCima F (synCec Q T)) (synCrn F) B
  have p0008 := Nominal.mp p0006 p0007
  have p0009 := @gSseli (synCima F (synCec Q T)) B (.cv z) p0008
  have p0010 := @gA1i (synWf1o F A B) (.classMem (.cv z) B) hyp_f1oclassimfreeclndv_1
  have p0011 := @gId (.classMem (.cv z) B)
  have p0012 :=
    @gJca (.classMem (.cv z) B) (synWf1o F A B) (.classMem (.cv z) B) p0010 p0011
  have p0013 := @gF1ocnvfv2 A B (.cv z) F
  have p0014 :=
    @gSyl (.classMem (.cv z) B) (synWa (synWf1o F A B) (.classMem (.cv z) B))
      (.classEq (synCfv F (synCfv (synCcnv F) (.cv z))) (.cv z)) p0012 p0013
  have p0015 :=
    @gEleq1d (.classMem (.cv z) B) (synCfv F (synCfv (synCcnv F) (.cv z))) (.cv z)
      (synCima F (synCec Q T)) p0014
  have p0016 := @gF1of1 A B F
  have p0017 := Nominal.mp hyp_f1oclassimfreeclndv_1 p0016
  have p0018 := @gA1i (synWf1 F A B) (.classMem (.cv z) B) p0017
  have p0022 := @gF1ocnvdm A B (.cv z) F
  have p0023 :=
    @gSyl (.classMem (.cv z) B) (synWa (synWf1o F A B) (.classMem (.cv z) B))
      (.classMem (synCfv (synCcnv F) (.cv z)) A) p0012 p0022
  have p0024 :=
    @gA1i (synWss (synCec Q T) A) (.classMem (.cv z) B) hyp_f1oclassimfreeclndv_2
  have p0025 :=
    @gN3jca (.classMem (.cv z) B) (synWf1 F A B)
      (.classMem (synCfv (synCcnv F) (.cv z)) A) (synWss (synCec Q T) A) p0018 p0023
      p0024
  have p0026 := @gF1elima A B F (synCfv (synCcnv F) (.cv z)) (synCec Q T)
  have p0027 :=
    @gSyl (.classMem (.cv z) B)
      (synW3a (synWf1 F A B) (.classMem (synCfv (synCcnv F) (.cv z)) A)
        (synWss (synCec Q T) A))
      (synWb (.classMem (synCfv F (synCfv (synCcnv F) (.cv z))) (synCima F (synCec Q T)))
        (.classMem (synCfv (synCcnv F) (.cv z)) (synCec Q T)))
      p0025 p0026
  have p0028 :=
    @gBitr3d (.classMem (.cv z) B)
      (.classMem (synCfv F (synCfv (synCcnv F) (.cv z))) (synCima F (synCec Q T)))
      (.classMem (.cv z) (synCima F (synCec Q T)))
      (.classMem (synCfv (synCcnv F) (.cv z)) (synCec Q T)) p0015 p0027
  have p0029 := @gElec (synCfv (synCcnv F) (.cv z)) Q T
  have p0030 :=
    @gA1i
      (synWb (.classMem (synCfv (synCcnv F) (.cv z)) (synCec Q T))
        (synWbr Q T (synCfv (synCcnv F) (.cv z))))
      (.classMem (.cv z) B) p0029
  have p0031 :=
    @gBitrd (.classMem (.cv z) B) (.classMem (.cv z) (synCima F (synCec Q T)))
      (.classMem (synCfv (synCcnv F) (.cv z)) (synCec Q T))
      (synWbr Q T (synCfv (synCcnv F) (.cv z))) p0028 p0030
  have p0032 :=
    @gA1i
      (synWral v A
        (synWb (synWbr Q T (.cv v)) (synWbr (synCfv F Q) S (synCfv F (.cv v)))))
      (.classMem (.cv z) B) hyp_f1oclassimfreeclndv_4
  have p0038 :=
    @gJca (.classMem (.cv z) B)
      (synWral v A
        (synWb (synWbr Q T (.cv v)) (synWbr (synCfv F Q) S (synCfv F (.cv v)))))
      (.classMem (synCfv (synCcnv F) (.cv z)) A) p0032 p0023
  have p0039 := @gId (.classEq (.cv v) (synCfv (synCcnv F) (.cv z)))
  have p0040 :=
    @gBreq2d (.classEq (.cv v) (synCfv (synCcnv F) (.cv z))) (.cv v)
      (synCfv (synCcnv F) (.cv z)) Q T p0039
  have p0042 :=
    @gFveq2d (.classEq (.cv v) (synCfv (synCcnv F) (.cv z))) (.cv v)
      (synCfv (synCcnv F) (.cv z)) F p0039
  have p0043 :=
    @gBreq2d (.classEq (.cv v) (synCfv (synCcnv F) (.cv z))) (synCfv F (.cv v))
      (synCfv F (synCfv (synCcnv F) (.cv z))) (synCfv F Q) S p0042
  have p0044 :=
    @gBibi12d (.classEq (.cv v) (synCfv (synCcnv F) (.cv z))) (synWbr Q T (.cv v))
      (synWbr Q T (synCfv (synCcnv F) (.cv z)))
      (synWbr (synCfv F Q) S (synCfv F (.cv v)))
      (synWbr (synCfv F Q) S (synCfv F (synCfv (synCcnv F) (.cv z)))) p0040 p0043
  have p0045 :=
    @gRspccva
      (synWb (synWbr Q T (.cv v)) (synWbr (synCfv F Q) S (synCfv F (.cv v))))
      (synWb (synWbr Q T (synCfv (synCcnv F) (.cv z)))
        (synWbr (synCfv F Q) S (synCfv F (synCfv (synCcnv F) (.cv z)))))
      v (synCfv (synCcnv F) (.cv z)) A dv_cache_0001 dv_cache_0002 dv_cache_0003 p0044
  have p0046 :=
    @gSyl (.classMem (.cv z) B)
      (synWa (synWral v A
          (synWb (synWbr Q T (.cv v)) (synWbr (synCfv F Q) S (synCfv F (.cv v)))))
        (.classMem (synCfv (synCcnv F) (.cv z)) A))
      (synWb (synWbr Q T (synCfv (synCcnv F) (.cv z)))
        (synWbr (synCfv F Q) S (synCfv F (synCfv (synCcnv F) (.cv z)))))
      p0038 p0045
  have p0047 :=
    @gBitrd (.classMem (.cv z) B) (.classMem (.cv z) (synCima F (synCec Q T)))
      (synWbr Q T (synCfv (synCcnv F) (.cv z)))
      (synWbr (synCfv F Q) S (synCfv F (synCfv (synCcnv F) (.cv z)))) p0031 p0046
  have p0053 :=
    @gBreq2d (.classMem (.cv z) B) (synCfv F (synCfv (synCcnv F) (.cv z))) (.cv z)
      (synCfv F Q) S p0014
  have p0054 :=
    @gBitrd (.classMem (.cv z) B) (.classMem (.cv z) (synCima F (synCec Q T)))
      (synWbr (synCfv F Q) S (synCfv F (synCfv (synCcnv F) (.cv z))))
      (synWbr (synCfv F Q) S (.cv z)) p0047 p0053
  have p0055 := @gElec (.cv z) (synCfv F Q) S
  have p0056 :=
    @gA1i
      (synWb (.classMem (.cv z) (synCec (synCfv F Q) S)) (synWbr (synCfv F Q) S (.cv z)))
      (.classMem (.cv z) B) p0055
  have p0057 :=
    @gBicomd (.classMem (.cv z) B) (.classMem (.cv z) (synCec (synCfv F Q) S))
      (synWbr (synCfv F Q) S (.cv z)) p0056
  have p0058 :=
    @gBitrd (.classMem (.cv z) B) (.classMem (.cv z) (synCima F (synCec Q T)))
      (synWbr (synCfv F Q) S (.cv z)) (.classMem (.cv z) (synCec (synCfv F Q) S))
      p0054 p0057
  have p0059 :=
    @gSyl (.classMem (.cv z) (synCima F (synCec Q T))) (.classMem (.cv z) B)
      (synWb (.classMem (.cv z) (synCima F (synCec Q T)))
        (.classMem (.cv z) (synCec (synCfv F Q) S)))
      p0009 p0058
  have p0060 :=
    @gMpbid (.classMem (.cv z) (synCima F (synCec Q T)))
      (.classMem (.cv z) (synCima F (synCec Q T)))
      (.classMem (.cv z) (synCec (synCfv F Q) S)) p0000 p0059
  have p0061 := @gId (.classMem (.cv z) (synCec (synCfv F Q) S))
  have p0062 := @gSseli (synCec (synCfv F Q) S) B (.cv z) hyp_f1oclassimfreeclndv_3
  have p0112 :=
    @gSyl (.classMem (.cv z) (synCec (synCfv F Q) S)) (.classMem (.cv z) B)
      (synWb (.classMem (.cv z) (synCima F (synCec Q T)))
        (.classMem (.cv z) (synCec (synCfv F Q) S)))
      p0062 p0058
  have p0113 :=
    @gMpbird (.classMem (.cv z) (synCec (synCfv F Q) S))
      (.classMem (.cv z) (synCima F (synCec Q T)))
      (.classMem (.cv z) (synCec (synCfv F Q) S)) p0061 p0112
  have p0114 :=
    @gImpbii (.classMem (.cv z) (synCima F (synCec Q T)))
      (.classMem (.cv z) (synCec (synCfv F Q) S)) p0060 p0113
  have p0115 :=
    @gEqriv z (synCima F (synCec Q T)) (synCec (synCfv F Q) S) dv_cache_0004
      dv_cache_0005 p0114
  exact p0115

/-- Checked nominal proof certificate identified upstream as `g_hnsicodemapkernelclndv`. -/
@[expose]
noncomputable def gHnsicodemapkernelclndv (A : Class) (Q : Class) (r : Var)
    (dv_A_r : r ∉ A.fv) (_dv_Q_r : r ∉ Q.fv) :
    Nominal.NPrf
      (.imp (.classMem Q (synCpw1 (synChwcn A)))
        (.imp (.classMem (.cv r) (synCpw1 (synChwcn A)))
          (synWb (synWbr Q (synCsi (synChwniso A)) (.cv r))
            (synWbr (synCfv (synChnsicodemap A) Q) (synChwniso (synCpw1 A))
              (synCfv (synChnsicodemap A) (.cv r)))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ Q.fv ∪ ({ r } : Finset Var)
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_q_not_Q : q ∉ Q.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_ne_r : q ≠ r := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have dv_cache_0001 : q ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_A, not_false_eq_true])
  have dv_cache_0002 : r ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_r, not_false_eq_true])
  have dv_cache_0003 : q ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show q ≠ r from (by exact fresh_q_ne_r))
  have dv_cache_0004 : q ∉ (Q).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_Q, not_false_eq_true])
  have dv_cache_0005 : q ∉ ((synCpw1 (synChwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, fresh_q_not_A,
          not_false_eq_true])
  have dv_cache_0006 :
    q ∉
      ((Wff.imp (.classMem (.cv r) (synCpw1 (synChwcn A)))
          (synWb (synWbr Q (synCsi (synChwniso A)) (.cv r))
            (synWbr (synCfv (synChnsicodemap A) Q) (synChwniso (synCpw1 A))
              (synCfv (synChnsicodemap A) (.cv r)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap,
          Finset.mem_union, Finset.mem_singleton, fresh_q_ne_r, fresh_q_not_A,
          fresh_q_not_Q, or_false, not_false_eq_true])
  have p0000 := @gBiid (.classMem (.cv r) (synCpw1 (synChwcn A)))
  have p0001 :=
    @gA1i
      (synWb (.classMem (.cv r) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (.classEq (.cv q) Q) p0000
  have p0002 := @gId (.classEq (.cv q) Q)
  have p0003 :=
    @gBreq1d (.classEq (.cv q) Q) (.cv q) Q (.cv r) (synCsi (synChwniso A)) p0002
  have p0005 := @gFveq2d (.classEq (.cv q) Q) (.cv q) Q (synChnsicodemap A) p0002
  have p0006 :=
    @gBreq1d (.classEq (.cv q) Q) (synCfv (synChnsicodemap A) (.cv q))
      (synCfv (synChnsicodemap A) Q) (synCfv (synChnsicodemap A) (.cv r))
      (synChwniso (synCpw1 A)) p0005
  have p0007 :=
    @gBibi12d (.classEq (.cv q) Q) (synWbr (.cv q) (synCsi (synChwniso A)) (.cv r))
      (synWbr Q (synCsi (synChwniso A)) (.cv r))
      (synWbr (synCfv (synChnsicodemap A) (.cv q)) (synChwniso (synCpw1 A))
        (synCfv (synChnsicodemap A) (.cv r)))
      (synWbr (synCfv (synChnsicodemap A) Q) (synChwniso (synCpw1 A))
        (synCfv (synChnsicodemap A) (.cv r)))
      p0003 p0006
  have p0008 :=
    @gImbi12d (.classEq (.cv q) Q) (.classMem (.cv r) (synCpw1 (synChwcn A)))
      (.classMem (.cv r) (synCpw1 (synChwcn A)))
      (synWb (synWbr (.cv q) (synCsi (synChwniso A)) (.cv r))
        (synWbr (synCfv (synChnsicodemap A) (.cv q)) (synChwniso (synCpw1 A))
          (synCfv (synChnsicodemap A) (.cv r))))
      (synWb (synWbr Q (synCsi (synChwniso A)) (.cv r))
        (synWbr (synCfv (synChnsicodemap A) Q) (synChwniso (synCpw1 A))
          (synCfv (synChnsicodemap A) (.cv r))))
      p0001 p0007
  have p0009 := @gHnsicodemapkernelndv A r q dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0010 :=
    @gEx (.classMem (.cv q) (synCpw1 (synChwcn A)))
      (.classMem (.cv r) (synCpw1 (synChwcn A)))
      (synWb (synWbr (.cv q) (synCsi (synChwniso A)) (.cv r))
        (synWbr (synCfv (synChnsicodemap A) (.cv q)) (synChwniso (synCpw1 A))
          (synCfv (synChnsicodemap A) (.cv r))))
      p0009
  have p0011 :=
    @gVtoclga
      (.imp (.classMem (.cv r) (synCpw1 (synChwcn A)))
        (synWb (synWbr (.cv q) (synCsi (synChwniso A)) (.cv r))
          (synWbr (synCfv (synChnsicodemap A) (.cv q)) (synChwniso (synCpw1 A))
            (synCfv (synChnsicodemap A) (.cv r)))))
      (.imp (.classMem (.cv r) (synCpw1 (synChwcn A)))
        (synWb (synWbr Q (synCsi (synChwniso A)) (.cv r))
          (synWbr (synCfv (synChnsicodemap A) Q) (synChwniso (synCpw1 A))
            (synCfv (synChnsicodemap A) (.cv r)))))
      q Q (synCpw1 (synChwcn A)) dv_cache_0004 dv_cache_0005 dv_cache_0006 p0008 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_hnsicodemapclassimclndv`. -/
@[expose]
noncomputable def gHnsicodemapclassimclndv (A : Class) (Q : Class)
    (hyp_hnsicodemapclassimclndv_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_hnsicodemapclassimclndv_2 : Nominal.NPrf (.classMem Q (synCpw1 (synChwcn A)))) :
    Nominal.NPrf
      (.classEq (synCima (synChnsicodemap A) (synCec Q (synCsi (synChwniso A))))
        (synCec (synCfv (synChnsicodemap A) Q) (synChwniso (synCpw1 A)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ Q.fv
  let r : Var := freshVar proofSupport 0
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (h))
  have fresh_r_not_Q : r ∉ Q.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have dv_cache_0001 : r ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_A, not_false_eq_true])
  have dv_cache_0002 : r ∉ (Q).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_Q, not_false_eq_true])
  have dv_cache_0003 : r ∉ ((synCpw1 (synChwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, fresh_r_not_A,
          not_false_eq_true])
  have dv_cache_0004 : r ∉ ((synChwcn (synCpw1 A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_r_not_A,
          not_false_eq_true])
  have dv_cache_0005 : r ∉ ((synChnsicodemap A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap,
          fresh_r_not_A, not_false_eq_true])
  have dv_cache_0006 : r ∉ ((synChwniso (synCpw1 A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_r_not_A,
          not_false_eq_true])
  have dv_cache_0007 : r ∉ ((synCsi (synChwniso A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, fresh_r_not_A,
          not_false_eq_true])
  have p0000 := @gHnsicodemapf1ondv A
  have p0001 := @gPw1argclcl (synChwcn A) Q
  have p0002 := Nominal.mp hyp_hnsicodemapclassimclndv_2 p0001
  have p0003 :=
    @gSimpr (.classMem (synCuni Q) (synChwcn A)) (.classEq Q (synCsn (synCuni Q)))
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := @gEceq1 Q (synCsn (synCuni Q)) (synCsi (synChwniso A))
  have p0006 := Nominal.mp p0004 p0005
  have p0009 :=
    @gSimpl (.classMem (synCuni Q) (synChwcn A)) (.classEq Q (synCsn (synCuni Q)))
  have p0010 := Nominal.mp p0002 p0009
  have p0011 := @gElex (synCuni Q) (synChwcn A)
  have p0012 := Nominal.mp p0010 p0011
  have p0013 := @gSiecsnclndv (synCuni Q) (synChwniso A)
  have p0014 := Nominal.mp p0012 p0013
  have p0015 :=
    @gEqtri (synCec Q (synCsi (synChwniso A)))
      (synCec (synCsn (synCuni Q)) (synCsi (synChwniso A)))
      (synCpw1 (synCec (synCuni Q) (synChwniso A))) p0006 p0014
  have p0016 := @gHwnisoerv A
  have p0017 := @gHwnisodm A
  have p0018 :=
    @gA1i (.classEq (synCdm (synChwniso A)) (synChwcn A)) (.classMem A (synCvv))
      p0017
  have p0019 :=
    @gEcss (.classMem A (synCvv)) (synCuni Q) (synChwniso A) (synChwcn A) p0016 p0018
  have p0020 := Nominal.mp hyp_hnsicodemapclassimclndv_1 p0019
  have p0021 := @gPw1ss (synCec (synCuni Q) (synChwniso A)) (synChwcn A)
  have p0022 := Nominal.mp p0020 p0021
  have p0023 :=
    @gEqsstri (synCec Q (synCsi (synChwniso A)))
      (synCpw1 (synCec (synCuni Q) (synChwniso A))) (synCpw1 (synChwcn A)) p0015
      p0022
  have p0024 := @gPw1exg A (synCvv)
  have p0025 := Nominal.mp hyp_hnsicodemapclassimclndv_1 p0024
  have p0026 := @gHwnisoerv (synCpw1 A)
  have p0027 := @gHwnisodm (synCpw1 A)
  have p0028 :=
    @gA1i (.classEq (synCdm (synChwniso (synCpw1 A))) (synChwcn (synCpw1 A)))
      (.classMem (synCpw1 A) (synCvv)) p0027
  have p0029 :=
    @gEcss (.classMem (synCpw1 A) (synCvv)) (synCfv (synChnsicodemap A) Q)
      (synChwniso (synCpw1 A)) (synChwcn (synCpw1 A)) p0026 p0028
  have p0030 := Nominal.mp p0025 p0029
  have p0031 := @gHnsicodemapkernelclndv A Q r dv_cache_0001 dv_cache_0002
  have p0032 := Nominal.mp hyp_hnsicodemapclassimclndv_2 p0031
  have p0033 :=
    @gRgen
      (synWb (synWbr Q (synCsi (synChwniso A)) (.cv r))
        (synWbr (synCfv (synChnsicodemap A) Q) (synChwniso (synCpw1 A))
          (synCfv (synChnsicodemap A) (.cv r))))
      r (synCpw1 (synChwcn A)) p0032
  have p0034 :=
    @gF1oclassimfreeclndv r (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)) Q
      (synChwniso (synCpw1 A)) (synCsi (synChwniso A)) (synChnsicodemap A)
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0002 dv_cache_0006 dv_cache_0007
      p0000 p0023 p0030 p0033 hyp_hnsicodemapclassimclndv_2
  exact p0034


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part007`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hnsicodemapclassimdndv`. -/
@[expose]
noncomputable def gHnsicodemapclassimdndv (A : Class) (q : Var) (_dv_A_q : q ∉ A.fv)
    (hyp_hnsicodemapclassimdndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (synCpw1 (synChwcn A))) (.classEq
          (synCima (synChnsicodemap A) (synCec (.cv q) (synCsi (synChwniso A))))
          (synCec (synCfv (synChnsicodemap A) (.cv q)) (synChwniso (synCpw1 A))))) :=
  by
  have dv_cache_0001 :
    Disjoint (A).fv
      ((synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))).fv :=
    by
    exact
      (show Disjoint (A).fv ((synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))).fv
        from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
          exact
            (show
              Disjoint ((A).fv)
                ((((synCkqrel (synClefin))).fv) ∪ (((synCxp (synC0) (synC0))).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint ((A).fv) (((synCkqrel (synClefin))).fv) from
                    (by
                      rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel];
                      exact
                        (show Disjoint ((A).fv) (((synClefin)).fv) from
                          (by
                            rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin];
                            exact
                              (show Disjoint ((A).fv) ((∅ : Finset Var)) from
                                (by simp)))))),
                  (show Disjoint ((A).fv) (((synCxp (synC0) (synC0))).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp];
                      exact
                        (show Disjoint ((A).fv) ((((synC0)).fv) ∪ (((synC0)).fv)) from
                          (Finset.disjoint_union_right.mpr
                            ⟨(show Disjoint ((A).fv) (((synC0)).fv) from
                                (by
                                  rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
                                  exact
                                    (show Disjoint ((A).fv) ((∅ : Finset Var)) from
                                      (by simp)))),
                              (show Disjoint ((A).fv) (((synC0)).fv) from
                                (by
                                  rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
                                  exact
                                    (show Disjoint ((A).fv) ((∅ : Finset Var)) from
                                      (by simp))))⟩))))⟩))))
  have p0000 :=
    @gEceq1 (.cv q)
      (synCif (.classMem (.cv q) (synCpw1 (synChwcn A))) (.cv q) (synCsn
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCsi (synChwniso A))
  have p0001 :=
    @gImaeq2d
      (.classEq (.cv q) (synCif (.classMem (.cv q) (synCpw1 (synChwcn A))) (.cv q) (synCsn
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (synCec (.cv q) (synCsi (synChwniso A)))
      (synCec (synCif (.classMem (.cv q) (synCpw1 (synChwcn A))) (.cv q) (synCsn
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCsi (synChwniso A)))
      (synChnsicodemap A) p0000
  have p0002 :=
    @gId
      (.classEq (.cv q) (synCif (.classMem (.cv q) (synCpw1 (synChwcn A))) (.cv q) (synCsn
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
  have p0003 :=
    @gFveq2d
      (.classEq (.cv q) (synCif (.classMem (.cv q) (synCpw1 (synChwcn A))) (.cv q) (synCsn
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (.cv q)
      (synCif (.classMem (.cv q) (synCpw1 (synChwcn A))) (.cv q) (synCsn
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synChnsicodemap A) p0002
  have p0004 :=
    @gEceq1 (synCfv (synChnsicodemap A) (.cv q))
      (synCfv (synChnsicodemap A)
        (synCif (.classMem (.cv q) (synCpw1 (synChwcn A))) (.cv q) (synCsn
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (synChwniso (synCpw1 A))
  have p0005 :=
    @gSyl
      (.classEq (.cv q) (synCif (.classMem (.cv q) (synCpw1 (synChwcn A))) (.cv q) (synCsn
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (.classEq (synCfv (synChnsicodemap A) (.cv q)) (synCfv (synChnsicodemap A)
          (synCif (.classMem (.cv q) (synCpw1 (synChwcn A))) (.cv q) (synCsn
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))))))
      (.classEq (synCec (synCfv (synChnsicodemap A) (.cv q)) (synChwniso (synCpw1 A)))
        (synCec (synCfv (synChnsicodemap A)
            (synCif (.classMem (.cv q) (synCpw1 (synChwcn A))) (.cv q) (synCsn
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0))))) (synChwniso (synCpw1 A))))
      p0003 p0004
  have p0006 :=
    @gEqeq12d
      (.classEq (.cv q) (synCif (.classMem (.cv q) (synCpw1 (synChwcn A))) (.cv q) (synCsn
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (synCima (synChnsicodemap A) (synCec (.cv q) (synCsi (synChwniso A))))
      (synCima (synChnsicodemap A) (synCec
          (synCif (.classMem (.cv q) (synCpw1 (synChwcn A))) (.cv q) (synCsn
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCsi (synChwniso A))))
      (synCec (synCfv (synChnsicodemap A) (.cv q)) (synChwniso (synCpw1 A)))
      (synCec (synCfv (synChnsicodemap A)
          (synCif (.classMem (.cv q) (synCpw1 (synChwcn A))) (.cv q) (synCsn
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))))) (synChwniso (synCpw1 A)))
      p0001 p0005
  have p0007 := @gEqid (synC0)
  have p0008 :=
    @gSimpr (.classEq (synC0) (synC0)) (.classMem (.cv q) (synCpw1 (synChwcn A)))
  have p0009 := @gWecomparisondefaultemptywe
  have p0010 := @gN0ss A
  have p0011 :=
    @gPm32i
      (synWbr (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synCwe)
        (synC0))
      (synWss (synC0) A) p0009 p0010
  have p0013 :=
    @gBrex (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)
      (synCwe)
  have p0014 := Nominal.mp p0009 p0013
  have p0015 :=
    @gSimpl
      (.classMem (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synCvv))
      (.classMem (synC0) (synCvv))
  have p0016 := Nominal.mp p0014 p0015
  have p0017 := @gN0ex
  have p0018 :=
    @gElhwcodes A (synC0)
      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) dv_cache_0001 p0016
      p0017
  have p0019 :=
    @gMpbir
      (.classMem
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
        (synChwcodes A))
      (synWa (synWbr (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synCwe)
          (synC0)) (synWss (synC0) A))
      p0011 p0018
  have p0020 := @gInss2 (synCkqrel (synClefin)) (synCxp (synC0) (synC0))
  have p0027 :=
    @gOpfv1st (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)
      p0016 p0017
  have p0034 :=
    @gOpfv2nd (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)
      p0016 p0017
  have p0042 :=
    @gXpeq12i
      (synCfv (synC2nd)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
      (synC0)
      (synCfv (synC2nd)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
      (synC0) p0034 p0034
  have p0043 :=
    @gSseq12i
      (synCfv (synC1st)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
      (synCxp (synCfv (synC2nd)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synCfv (synC2nd)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCxp (synC0) (synC0)) p0027 p0042
  have p0044 :=
    @gMpbir
      (synWss (synCfv (synC1st)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synCxp (synCfv (synC2nd)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synCfv (synC2nd)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (synWss (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
        (synCxp (synC0) (synC0)))
      p0020 p0043
  have p0045 :=
    @gPm32i
      (.classMem
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
        (synChwcodes A))
      (synWss (synCfv (synC1st)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synCxp (synCfv (synC2nd)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synCfv (synC2nd)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      p0019 p0044
  have p0052 :=
    @gOpex (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0) p0016
      p0017
  have p0053 :=
    @gElhwcncl A
      (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
  have p0054 := Nominal.mp p0052 p0053
  have p0055 :=
    @gMpbir
      (.classMem
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
        (synChwcn A))
      (synWa (.classMem
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
          (synChwcodes A)) (synWss (synCfv (synC1st)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synCxp (synCfv (synC2nd)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))) (synCfv (synC2nd)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))))))
      p0045 p0054
  have p0056 :=
    @gSnelpw1
      (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
      (synChwcn A)
  have p0057 :=
    @gMpbir
      (.classMem (synCsn
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synCpw1 (synChwcn A)))
      (.classMem
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
        (synChwcn A))
      p0055 p0056
  have p0058 :=
    @gA1i
      (.classMem (synCsn
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synCpw1 (synChwcn A)))
      (synWa (.classEq (synC0) (synC0)) (.neg (.classMem (.cv q) (synCpw1 (synChwcn A)))))
      p0057
  have p0059 :=
    @gIfclda (.classEq (synC0) (synC0)) (.classMem (.cv q) (synCpw1 (synChwcn A)))
      (.cv q)
      (synCsn (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
          (synC0)))
      (synCpw1 (synChwcn A)) p0008 p0058
  have p0060 := Nominal.mp p0007 p0059
  have p0061 :=
    @gHnsicodemapclassimclndv A
      (synCif (.classMem (.cv q) (synCpw1 (synChwcn A))) (.cv q) (synCsn
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      hyp_hnsicodemapclassimdndv_1 p0060
  have p0062 :=
    @gDedth (.classMem (.cv q) (synCpw1 (synChwcn A)))
      (.classEq (synCima (synChnsicodemap A) (synCec (.cv q) (synCsi (synChwniso A))))
        (synCec (synCfv (synChnsicodemap A) (.cv q)) (synChwniso (synCpw1 A))))
      (.classEq (synCima (synChnsicodemap A) (synCec
            (synCif (.classMem (.cv q) (synCpw1 (synChwcn A))) (.cv q) (synCsn
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCsi (synChwniso A)))) (synCec (synCfv (synChnsicodemap A)
            (synCif (.classMem (.cv q) (synCpw1 (synChwcn A))) (.cv q) (synCsn
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0))))) (synChwniso (synCpw1 A))))
      (.cv q)
      (synCsn (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
          (synC0)))
      p0006 p0061
  exact p0062

/-- Checked nominal proof certificate identified upstream as `g_hnsicodemapclassimcldndv`. -/
@[expose]
noncomputable def gHnsicodemapclassimcldndv (A : Class) (Q : Class)
    (hyp_hnsicodemapclassimcldndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem Q (synCpw1 (synChwcn A)))
        (.classEq (synCima (synChnsicodemap A) (synCec Q (synCsi (synChwniso A))))
          (synCec (synCfv (synChnsicodemap A) Q) (synChwniso (synCpw1 A))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ Q.fv
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_not_Q : q ∉ Q.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have dv_cache_0001 : q ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_A, not_false_eq_true])
  have dv_cache_0002 : q ∉ (Q).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_Q, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((synCpw1 (synChwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, fresh_q_not_A,
          not_false_eq_true])
  have dv_cache_0004 :
    q ∉
      ((Wff.classEq (synCima (synChnsicodemap A) (synCec Q (synCsi (synChwniso A))))
          (synCec (synCfv (synChnsicodemap A) Q) (synChwniso (synCpw1 A))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          fresh_q_not_A, fresh_q_not_Q, or_false, not_false_eq_true])
  have p0000 := @gEceq1 (.cv q) Q (synCsi (synChwniso A))
  have p0001 :=
    @gImaeq2d (.classEq (.cv q) Q) (synCec (.cv q) (synCsi (synChwniso A)))
      (synCec Q (synCsi (synChwniso A))) (synChnsicodemap A) p0000
  have p0002 := @gId (.classEq (.cv q) Q)
  have p0003 := @gFveq2d (.classEq (.cv q) Q) (.cv q) Q (synChnsicodemap A) p0002
  have p0004 :=
    @gEceq1 (synCfv (synChnsicodemap A) (.cv q)) (synCfv (synChnsicodemap A) Q)
      (synChwniso (synCpw1 A))
  have p0005 :=
    @gSyl (.classEq (.cv q) Q)
      (.classEq (synCfv (synChnsicodemap A) (.cv q)) (synCfv (synChnsicodemap A) Q))
      (.classEq (synCec (synCfv (synChnsicodemap A) (.cv q)) (synChwniso (synCpw1 A)))
        (synCec (synCfv (synChnsicodemap A) Q) (synChwniso (synCpw1 A))))
      p0003 p0004
  have p0006 :=
    @gEqeq12d (.classEq (.cv q) Q)
      (synCima (synChnsicodemap A) (synCec (.cv q) (synCsi (synChwniso A))))
      (synCima (synChnsicodemap A) (synCec Q (synCsi (synChwniso A))))
      (synCec (synCfv (synChnsicodemap A) (.cv q)) (synChwniso (synCpw1 A)))
      (synCec (synCfv (synChnsicodemap A) Q) (synChwniso (synCpw1 A))) p0001 p0005
  have p0007 := @gHnsicodemapclassimdndv A q dv_cache_0001 hyp_hnsicodemapclassimcldndv_1
  have p0008 :=
    @gVtoclga
      (.classEq (synCima (synChnsicodemap A) (synCec (.cv q) (synCsi (synChwniso A))))
        (synCec (synCfv (synChnsicodemap A) (.cv q)) (synChwniso (synCpw1 A))))
      (.classEq (synCima (synChnsicodemap A) (synCec Q (synCsi (synChwniso A))))
        (synCec (synCfv (synChnsicodemap A) Q) (synChwniso (synCpw1 A))))
      q Q (synCpw1 (synChwcn A)) dv_cache_0002 dv_cache_0003 dv_cache_0004 p0006 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_elhnordclndv`. -/
@[expose]
noncomputable def gElhnordclndv (u : Var) (A : Class) (X : Class) (dv_A_u : u ∉ A.fv)
    (dv_X_u : u ∉ X.fv) :
    Nominal.NPrf
      (.imp (.classMem X (synCvv)) (synWb (.classMem X (synChnord A))
          (synWrex u (synChwcn A) (.classEq X (synCec (.cv u) (synChwniso A)))))) :=
  by
  let proofSupport : Finset Var := ({ u } : Finset Var) ∪ A.fv ∪ X.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_u : x ≠ u := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_x : u ≠ x := Ne.symm fresh_x_ne_u
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_X : x ∉ X.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : u ∉ ((Wff.classEq (.cv x) X)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_x, dv_X_u, or_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0004 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0005 : x ∉ (X).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_X, not_false_eq_true])
  have dv_cache_0006 :
    x ∉
      ((synWb (.classMem X (synChnord A)) (synWrex u (synChwcn A)
            (.classEq X (synCec (.cv u) (synChwniso A)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_not_X, fresh_x_not_A,
          fresh_x_ne_u, or_false, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Wff.classMem X (synCvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_x_not_X, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @gId (.classMem X (synCvv))
  have p0001 := @gSimpr (.classMem X (synCvv)) (.classEq (.cv x) X)
  have p0002 := @gEleq1 (.cv x) X (synChnord A)
  have p0003 := @gId (.classEq (.cv x) X)
  have p0004 :=
    @gEqeq1d (.classEq (.cv x) X) (.cv x) X (synCec (.cv u) (synChwniso A)) p0003
  have p0005 :=
    @gRexbidv (.classEq (.cv x) X) (.classEq (.cv x) (synCec (.cv u) (synChwniso A)))
      (.classEq X (synCec (.cv u) (synChwniso A))) u (synChwcn A) dv_cache_0001 p0004
  have p0006 :=
    @gBibi12d (.classEq (.cv x) X) (.classMem (.cv x) (synChnord A))
      (.classMem X (synChnord A))
      (synWrex u (synChwcn A) (.classEq (.cv x) (synCec (.cv u) (synChwniso A))))
      (synWrex u (synChwcn A) (.classEq X (synCec (.cv u) (synChwniso A)))) p0002
      p0005
  have p0007 :=
    @gSyl (synWa (.classMem X (synCvv)) (.classEq (.cv x) X)) (.classEq (.cv x) X)
      (synWb (synWb (.classMem (.cv x) (synChnord A))
          (synWrex u (synChwcn A) (.classEq (.cv x) (synCec (.cv u) (synChwniso A)))))
        (synWb (.classMem X (synChnord A))
          (synWrex u (synChwcn A) (.classEq X (synCec (.cv u) (synChwniso A))))))
      p0001 p0006
  have p0008 := @gVex x
  have p0009 := @gElhnord x u A dv_cache_0002 dv_cache_0003 dv_cache_0004 p0008
  have p0010 :=
    @gA1i
      (synWb (.classMem (.cv x) (synChnord A))
        (synWrex u (synChwcn A) (.classEq (.cv x) (synCec (.cv u) (synChwniso A)))))
      (.classMem X (synCvv)) p0009
  have p0011 :=
    @gVtocld (.classMem X (synCvv))
      (synWb (.classMem (.cv x) (synChnord A))
        (synWrex u (synChwcn A) (.classEq (.cv x) (synCec (.cv u) (synChwniso A)))))
      (synWb (.classMem X (synChnord A))
        (synWrex u (synChwcn A) (.classEq X (synCec (.cv u) (synChwniso A)))))
      x X (synCvv) dv_cache_0005 dv_cache_0006 dv_cache_0007 p0000 p0007 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_hnsiquomapfvhnordndv`. -/
@[expose]
noncomputable def gHnsiquomapfvhnordndv (A : Class) (q : Var) (dv_A_q : q ∉ A.fv)
    (hyp_hnsiquomapfvhnordndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (synCpw1 (synChnord A)))
        (.classMem (synCfv (synChnsiquomap A) (.cv q)) (synChnord (synCpw1 A)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ ({ q } : Finset Var)
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_ne_q : u ≠ q := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have dv_cache_0001 : u ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((synCuni (.cv q))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_u_ne_q,
          not_false_eq_true])
  have dv_cache_0003 : q ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_q, not_false_eq_true])
  have dv_cache_0004 : u ∉ ((synChwniso A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          fresh_u_not_A, not_false_eq_true])
  have dv_cache_0005 :
    u ∉
      ((Wff.classMem (synCfv (synChnsiquomap A) (.cv q)) (synChnord (synCpw1 A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_q, fresh_u_not_A, or_false, not_false_eq_true])
  have dv_cache_0006 : u ∉ ((Wff.classMem (.cv q) (synCpw1 (synChnord A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_q, fresh_u_not_A, or_false, not_false_eq_true])
  have p0000 := @gPw1argclcl (synChnord A) (.cv q)
  have p0001 :=
    @gSimpl (.classMem (synCuni (.cv q)) (synChnord A))
      (.classEq (.cv q) (synCsn (synCuni (.cv q))))
  have p0002 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synChnord A)))
      (synWa (.classMem (synCuni (.cv q)) (synChnord A))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      (.classMem (synCuni (.cv q)) (synChnord A)) p0000 p0001
  have p0006 := @gElex (synCuni (.cv q)) (synChnord A)
  have p0007 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synChnord A)))
      (.classMem (synCuni (.cv q)) (synChnord A))
      (.classMem (synCuni (.cv q)) (synCvv)) p0002 p0006
  have p0008 := @gElhnordclndv u A (synCuni (.cv q)) dv_cache_0001 dv_cache_0002
  have p0009 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synChnord A)))
      (.classMem (synCuni (.cv q)) (synCvv))
      (synWb (.classMem (synCuni (.cv q)) (synChnord A)) (synWrex u (synChwcn A)
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      p0007 p0008
  have p0010 :=
    @gMpbid (.classMem (.cv q) (synCpw1 (synChnord A)))
      (.classMem (synCuni (.cv q)) (synChnord A))
      (synWrex u (synChwcn A) (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A))))
      p0002 p0009
  have p0011 :=
    @gSimpl (.classMem (.cv q) (synCpw1 (synChnord A)))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A))))
  have p0012 := @gHnsiquomapvalndv A q dv_cache_0003 hyp_hnsiquomapfvhnordndv_1
  have p0013 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (.classMem (.cv q) (synCpw1 (synChnord A)))
      (.classEq (synCfv (synChnsiquomap A) (.cv q))
        (synCima (synChnsicodemap A) (synCpw1 (synCuni (.cv q)))))
      p0011 p0012
  have p0014 :=
    @gSimpr (.classMem (.cv q) (synCpw1 (synChnord A)))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A))))
  have p0015 :=
    @gSimpr (.classMem (.cv u) (synChwcn A))
      (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))
  have p0016 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A))))
      (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A))) p0014 p0015
  have p0017 := @gPw1eq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A))
  have p0018 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))
      (.classEq (synCpw1 (synCuni (.cv q))) (synCpw1 (synCec (.cv u) (synChwniso A))))
      p0016 p0017
  have p0019 := @gSiecsnndv u (synChwniso A) dv_cache_0004
  have p0020 :=
    @gEqcomi (synCec (synCsn (.cv u)) (synCsi (synChwniso A)))
      (synCpw1 (synCec (.cv u) (synChwniso A))) p0019
  have p0021 :=
    @gA1i
      (.classEq (synCpw1 (synCec (.cv u) (synChwniso A)))
        (synCec (synCsn (.cv u)) (synCsi (synChwniso A))))
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      p0020
  have p0022 :=
    @gEqtrd
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (synCpw1 (synCuni (.cv q))) (synCpw1 (synCec (.cv u) (synChwniso A)))
      (synCec (synCsn (.cv u)) (synCsi (synChwniso A))) p0018 p0021
  have p0023 :=
    @gImaeq2d
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (synCpw1 (synCuni (.cv q))) (synCec (synCsn (.cv u)) (synCsi (synChwniso A)))
      (synChnsicodemap A) p0022
  have p0024 :=
    @gEqtrd
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (synCfv (synChnsiquomap A) (.cv q))
      (synCima (synChnsicodemap A) (synCpw1 (synCuni (.cv q))))
      (synCima (synChnsicodemap A) (synCec (synCsn (.cv u)) (synCsi (synChwniso A))))
      p0013 p0023
  have p0026 :=
    @gSimpl (.classMem (.cv u) (synChwcn A))
      (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))
  have p0027 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A))))
      (.classMem (.cv u) (synChwcn A)) p0014 p0026
  have p0028 := @gSnelpw1 (.cv u) (synChwcn A)
  have p0029 :=
    @gSylibr
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (.classMem (.cv u) (synChwcn A))
      (.classMem (synCsn (.cv u)) (synCpw1 (synChwcn A))) p0027 p0028
  have p0030 := @gHnsicodemapclassimcldndv A (synCsn (.cv u)) hyp_hnsiquomapfvhnordndv_1
  have p0031 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (.classMem (synCsn (.cv u)) (synCpw1 (synChwcn A)))
      (.classEq (synCima (synChnsicodemap A)
          (synCec (synCsn (.cv u)) (synCsi (synChwniso A))))
        (synCec (synCfv (synChnsicodemap A) (synCsn (.cv u))) (synChwniso (synCpw1 A))))
      p0029 p0030
  have p0032 :=
    @gEqtrd
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (synCfv (synChnsiquomap A) (.cv q))
      (synCima (synChnsicodemap A) (synCec (synCsn (.cv u)) (synCsi (synChwniso A))))
      (synCec (synCfv (synChnsicodemap A) (synCsn (.cv u))) (synChwniso (synCpw1 A)))
      p0024 p0031
  have p0038 := @gHnsicodemapfndv A
  have p0039 :=
    @gFfvelrni (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)) (synCsn (.cv u))
      (synChnsicodemap A) p0038
  have p0040 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (.classMem (synCsn (.cv u)) (synCpw1 (synChwcn A)))
      (.classMem (synCfv (synChnsicodemap A) (synCsn (.cv u))) (synChwcn (synCpw1 A)))
      p0029 p0039
  have p0041 := @gPw1exg A (synCvv)
  have p0042 := Nominal.mp hyp_hnsiquomapfvhnordndv_1 p0041
  have p0043 :=
    @gHwnisoclasselhnordcl (synCpw1 A) (synCfv (synChnsicodemap A) (synCsn (.cv u)))
      p0042
  have p0044 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (.classMem (synCfv (synChnsicodemap A) (synCsn (.cv u))) (synChwcn (synCpw1 A)))
      (.classMem (synCec (synCfv (synChnsicodemap A) (synCsn (.cv u)))
          (synChwniso (synCpw1 A))) (synChnord (synCpw1 A)))
      p0040 p0043
  have p0045 :=
    @gEqeltrd
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (synCfv (synChnsiquomap A) (.cv q))
      (synCec (synCfv (synChnsicodemap A) (synCsn (.cv u))) (synChwniso (synCpw1 A)))
      (synChnord (synCpw1 A)) p0032 p0044
  have p0046 :=
    @gRexlimddv (.classMem (.cv q) (synCpw1 (synChnord A)))
      (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))
      (.classMem (synCfv (synChnsiquomap A) (.cv q)) (synChnord (synCpw1 A))) u
      (synChwcn A) dv_cache_0005 dv_cache_0006 p0010 p0045
  exact p0046

/-- Checked nominal proof certificate identified upstream as `g_hnsiquomapvalclndv`. -/
@[expose]
noncomputable def gHnsiquomapvalclndv (A : Class) (Q : Class)
    (hyp_hnsiquomapvalclndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem Q (synCpw1 (synChnord A))) (.classEq (synCfv (synChnsiquomap A) Q)
          (synCima (synChnsicodemap A) (synCpw1 (synCuni Q))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ Q.fv
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_not_Q : q ∉ Q.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have dv_cache_0001 : q ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_A, not_false_eq_true])
  have dv_cache_0002 : q ∉ (Q).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_Q, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((synCpw1 (synChnord A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, fresh_q_not_A,
          not_false_eq_true])
  have dv_cache_0004 :
    q ∉
      ((Wff.classEq (synCfv (synChnsiquomap A) Q)
          (synCima (synChnsicodemap A) (synCpw1 (synCuni Q))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union,
          fresh_q_not_Q, fresh_q_not_A, or_false, not_false_eq_true])
  have p0000 := @gId (.classEq (.cv q) Q)
  have p0001 := @gFveq2d (.classEq (.cv q) Q) (.cv q) Q (synChnsiquomap A) p0000
  have p0003 := @gUnieqd (.classEq (.cv q) Q) (.cv q) Q p0000
  have p0004 := @gPw1eq (synCuni (.cv q)) (synCuni Q)
  have p0005 :=
    @gSyl (.classEq (.cv q) Q) (.classEq (synCuni (.cv q)) (synCuni Q))
      (.classEq (synCpw1 (synCuni (.cv q))) (synCpw1 (synCuni Q))) p0003 p0004
  have p0006 :=
    @gImaeq2d (.classEq (.cv q) Q) (synCpw1 (synCuni (.cv q))) (synCpw1 (synCuni Q))
      (synChnsicodemap A) p0005
  have p0007 :=
    @gEqeq12d (.classEq (.cv q) Q) (synCfv (synChnsiquomap A) (.cv q))
      (synCfv (synChnsiquomap A) Q)
      (synCima (synChnsicodemap A) (synCpw1 (synCuni (.cv q))))
      (synCima (synChnsicodemap A) (synCpw1 (synCuni Q))) p0001 p0006
  have p0008 := @gHnsiquomapvalndv A q dv_cache_0001 hyp_hnsiquomapvalclndv_1
  have p0009 :=
    @gVtoclga
      (.classEq (synCfv (synChnsiquomap A) (.cv q))
        (synCima (synChnsicodemap A) (synCpw1 (synCuni (.cv q)))))
      (.classEq (synCfv (synChnsiquomap A) Q)
        (synCima (synChnsicodemap A) (synCpw1 (synCuni Q))))
      q Q (synCpw1 (synChnord A)) dv_cache_0002 dv_cache_0003 dv_cache_0004 p0007 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_hnsiquomapfndv`. -/
@[expose]
noncomputable def gHnsiquomapfndv (A : Class)
    (hyp_hnsiquomapfndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (synWf (synChnsiquomap A) (synCpw1 (synChnord A)) (synChnord (synCpw1 A))) :=
  by
  let proofSupport : Finset Var := A.fv
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (h)
  have dv_cache_0001 : q ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_A, not_false_eq_true])
  have dv_cache_0002 : q ∉ ((synCpw1 (synChnord A))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, fresh_q_not_A,
          not_false_eq_true])
  have dv_cache_0003 : q ∉ ((synChnord (synCpw1 A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_q_not_A,
          not_false_eq_true])
  have dv_cache_0004 : q ∉ ((synChnsiquomap A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap,
          fresh_q_not_A, not_false_eq_true])
  have p0000 := @gHnsiquomapfnndv A hyp_hnsiquomapfndv_1
  have p0001 := @gHnsiquomapfvhnordndv A q dv_cache_0001 hyp_hnsiquomapfndv_1
  have p0002 :=
    @gRgen (.classMem (synCfv (synChnsiquomap A) (.cv q)) (synChnord (synCpw1 A))) q
      (synCpw1 (synChnord A)) p0001
  have p0003 :=
    @gPm32i (synWfn (synChnsiquomap A) (synCpw1 (synChnord A)))
      (synWral q (synCpw1 (synChnord A))
        (.classMem (synCfv (synChnsiquomap A) (.cv q)) (synChnord (synCpw1 A))))
      p0000 p0002
  have p0004 :=
    @gFfnfv q (synCpw1 (synChnord A)) (synChnord (synCpw1 A)) (synChnsiquomap A)
      dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0005 :=
    @gMpbir
      (synWf (synChnsiquomap A) (synCpw1 (synChnord A)) (synChnord (synCpw1 A)))
      (synWa (synWfn (synChnsiquomap A) (synCpw1 (synChnord A)))
        (synWral q (synCpw1 (synChnord A))
          (.classMem (synCfv (synChnsiquomap A) (.cv q)) (synChnord (synCpw1 A)))))
      p0003 p0004
  exact p0005


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part008`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hnsiquomappreexndv`. -/
@[expose]
noncomputable def gHnsiquomappreexndv (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (_dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y)
    (hyp_hnsiquomappreexndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv y) (synChnord (synCpw1 A))) (synWrex x (synCpw1 (synChnord A))
          (.classEq (.cv y) (synCfv (synChnsiquomap A) (.cv x))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  let w : Var := freshVar proofSupport 0
  let r : Var := freshVar proofSupport 1
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_r_ne_x : r ≠ x := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_r : x ≠ r := Ne.symm fresh_r_ne_x
  have fresh_r_ne_y : r ≠ y := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_w_ne_r : w ≠ r :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_r_ne_w : r ≠ w := Ne.symm fresh_w_ne_r
  have dv_cache_0001 : w ∉ ((synCpw1 A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_w_not_A,
          not_false_eq_true])
  have dv_cache_0002 : w ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_y, not_false_eq_true])
  have dv_cache_0003 : r ∉ ((synCpw1 (synChwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, fresh_r_not_A,
          not_false_eq_true])
  have dv_cache_0004 : r ∉ ((synChwcn (synCpw1 A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_r_not_A,
          not_false_eq_true])
  have dv_cache_0005 : r ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_r_ne_w, not_false_eq_true])
  have dv_cache_0006 : r ∉ ((synChnsicodemap A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap,
          fresh_r_not_A, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((synCsn (synCec (synCuni (.cv r)) (synChwniso A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_r, dv_A_x, or_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((synCpw1 (synChnord A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, dv_A_x,
          not_false_eq_true])
  have dv_cache_0009 :
    x ∉
      ((Wff.classEq (.cv y) (synCfv (synChnsiquomap A)
            (synCsn (synCec (synCuni (.cv r)) (synChwniso A)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, dv_x_y, fresh_x_ne_r, dv_A_x, or_false,
          not_false_eq_true])
  have dv_cache_0010 :
    r ∉
      ((synWrex x (synCpw1 (synChnord A))
          (.classEq (.cv y) (synCfv (synChnsiquomap A) (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap,
          Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, fresh_r_not_A,
          fresh_r_ne_y, fresh_r_ne_x, or_false, and_false, not_false_eq_true])
  have dv_cache_0011 :
    r ∉
      ((synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
          (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
            (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_y, fresh_r_not_A, fresh_r_ne_w, or_false,
          not_false_eq_true])
  have dv_cache_0012 :
    w ∉
      ((synWrex x (synCpw1 (synChnord A))
          (.classEq (.cv y) (synCfv (synChnsiquomap A) (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap,
          Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, fresh_w_not_A,
          fresh_w_ne_y, fresh_w_ne_x, or_false, and_false, not_false_eq_true])
  have dv_cache_0013 : w ∉ ((Wff.classMem (.cv y) (synChnord (synCpw1 A)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_y, fresh_w_not_A, or_false, not_false_eq_true])
  have p0000 := @gId (.classMem (.cv y) (synChnord (synCpw1 A)))
  have p0002 := @gElex (.cv y) (synChnord (synCpw1 A))
  have p0003 :=
    @gSyl (.classMem (.cv y) (synChnord (synCpw1 A)))
      (.classMem (.cv y) (synChnord (synCpw1 A))) (.classMem (.cv y) (synCvv)) p0000
      p0002
  have p0004 := @gElhnordclndv w (synCpw1 A) (.cv y) dv_cache_0001 dv_cache_0002
  have p0005 :=
    @gSyl (.classMem (.cv y) (synChnord (synCpw1 A))) (.classMem (.cv y) (synCvv))
      (synWb (.classMem (.cv y) (synChnord (synCpw1 A))) (synWrex w (synChwcn (synCpw1 A))
          (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
      p0003 p0004
  have p0006 :=
    @gMpbid (.classMem (.cv y) (synChnord (synCpw1 A)))
      (.classMem (.cv y) (synChnord (synCpw1 A)))
      (synWrex w (synChwcn (synCpw1 A))
        (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A)))))
      p0000 p0005
  have p0007 := @gHnsicodemapfondv A
  have p0008 :=
    @gA1i
      (synWfo (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)))
      (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
        (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
          (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
      p0007
  have p0009 :=
    @gSimpr (.classMem (.cv y) (synChnord (synCpw1 A)))
      (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
        (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A)))))
  have p0010 :=
    @gSimpl (.classMem (.cv w) (synChwcn (synCpw1 A)))
      (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))
  have p0011 :=
    @gSyl
      (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
        (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
          (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
      (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
        (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A)))))
      (.classMem (.cv w) (synChwcn (synCpw1 A))) p0009 p0010
  have p0012 :=
    @gJca
      (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
        (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
          (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
      (synWfo (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)))
      (.classMem (.cv w) (synChwcn (synCpw1 A))) p0008 p0011
  have p0013 :=
    @gFoelrn r (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)) (.cv w)
      (synChnsicodemap A) dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0014 :=
    @gSyl
      (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
        (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
          (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
      (synWa (synWfo (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)))
        (.classMem (.cv w) (synChwcn (synCpw1 A))))
      (synWrex r (synCpw1 (synChwcn A))
        (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r))))
      p0012 p0013
  have p0015 :=
    @gSimpr
      (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
        (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
          (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
      (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
        (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r))))
  have p0016 :=
    @gSimpl (.classMem (.cv r) (synCpw1 (synChwcn A)))
      (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))
  have p0017 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
          (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
            (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
        (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
          (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))))
      (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
        (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r))))
      (.classMem (.cv r) (synCpw1 (synChwcn A))) p0015 p0016
  have p0018 := @gPw1argclcl (synChwcn A) (.cv r)
  have p0019 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
          (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
            (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
        (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
          (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))))
      (.classMem (.cv r) (synCpw1 (synChwcn A)))
      (synWa (.classMem (synCuni (.cv r)) (synChwcn A))
        (.classEq (.cv r) (synCsn (synCuni (.cv r)))))
      p0017 p0018
  have p0020 :=
    @gSimpl (.classMem (synCuni (.cv r)) (synChwcn A))
      (.classEq (.cv r) (synCsn (synCuni (.cv r))))
  have p0021 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
          (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
            (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
        (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
          (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))))
      (synWa (.classMem (synCuni (.cv r)) (synChwcn A))
        (.classEq (.cv r) (synCsn (synCuni (.cv r)))))
      (.classMem (synCuni (.cv r)) (synChwcn A)) p0019 p0020
  have p0022 := @gHwnisoclasselhnordcl A (synCuni (.cv r)) hyp_hnsiquomappreexndv_1
  have p0023 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
          (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
            (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
        (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
          (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))))
      (.classMem (synCuni (.cv r)) (synChwcn A))
      (.classMem (synCec (synCuni (.cv r)) (synChwniso A)) (synChnord A)) p0021 p0022
  have p0024 := @gSnelpw1 (synCec (synCuni (.cv r)) (synChwniso A)) (synChnord A)
  have p0025 :=
    @gSylibr
      (synWa (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
          (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
            (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
        (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
          (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))))
      (.classMem (synCec (synCuni (.cv r)) (synChwniso A)) (synChnord A))
      (.classMem (synCsn (synCec (synCuni (.cv r)) (synChwniso A)))
        (synCpw1 (synChnord A)))
      p0023 p0024
  have p0026 :=
    @gSimpl
      (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
        (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
          (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
      (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
        (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r))))
  have p0028 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
          (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
            (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
        (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
          (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))))
      (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
        (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
          (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
      (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
        (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A)))))
      p0026 p0009
  have p0029 :=
    @gSimpr (.classMem (.cv w) (synChwcn (synCpw1 A)))
      (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))
  have p0030 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
          (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
            (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
        (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
          (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))))
      (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
        (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A)))))
      (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A)))) p0028 p0029
  have p0032 :=
    @gSimpr (.classMem (.cv r) (synCpw1 (synChwcn A)))
      (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))
  have p0033 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
          (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
            (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
        (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
          (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))))
      (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
        (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r))))
      (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r))) p0015 p0032
  have p0034 :=
    @gEceq1 (.cv w) (synCfv (synChnsicodemap A) (.cv r)) (synChwniso (synCpw1 A))
  have p0035 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
          (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
            (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
        (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
          (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))))
      (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))
      (.classEq (synCec (.cv w) (synChwniso (synCpw1 A)))
        (synCec (synCfv (synChnsicodemap A) (.cv r)) (synChwniso (synCpw1 A))))
      p0033 p0034
  have p0036 :=
    @gEqtrd
      (synWa (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
          (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
            (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
        (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
          (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))))
      (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A)))
      (synCec (synCfv (synChnsicodemap A) (.cv r)) (synChwniso (synCpw1 A))) p0030
      p0035
  have p0048 :=
    @gHnsiquomapvalclndv A (synCsn (synCec (synCuni (.cv r)) (synChwniso A)))
      hyp_hnsiquomappreexndv_1
  have p0049 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
          (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
            (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
        (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
          (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))))
      (.classMem (synCsn (synCec (synCuni (.cv r)) (synChwniso A)))
        (synCpw1 (synChnord A)))
      (.classEq (synCfv (synChnsiquomap A)
          (synCsn (synCec (synCuni (.cv r)) (synChwniso A)))) (synCima (synChnsicodemap A)
          (synCpw1 (synCuni (synCsn (synCec (synCuni (.cv r)) (synChwniso A)))))))
      p0025 p0048
  have p0059 := @gElex (synCec (synCuni (.cv r)) (synChwniso A)) (synChnord A)
  have p0060 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
          (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
            (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
        (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
          (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))))
      (.classMem (synCec (synCuni (.cv r)) (synChwniso A)) (synChnord A))
      (.classMem (synCec (synCuni (.cv r)) (synChwniso A)) (synCvv)) p0023 p0059
  have p0061 := @gUnisng (synCec (synCuni (.cv r)) (synChwniso A)) (synCvv)
  have p0062 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
          (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
            (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
        (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
          (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))))
      (.classMem (synCec (synCuni (.cv r)) (synChwniso A)) (synCvv))
      (.classEq (synCuni (synCsn (synCec (synCuni (.cv r)) (synChwniso A))))
        (synCec (synCuni (.cv r)) (synChwniso A)))
      p0060 p0061
  have p0063 :=
    @gPw1eq (synCuni (synCsn (synCec (synCuni (.cv r)) (synChwniso A))))
      (synCec (synCuni (.cv r)) (synChwniso A))
  have p0064 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
          (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
            (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
        (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
          (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))))
      (.classEq (synCuni (synCsn (synCec (synCuni (.cv r)) (synChwniso A))))
        (synCec (synCuni (.cv r)) (synChwniso A)))
      (.classEq (synCpw1 (synCuni (synCsn (synCec (synCuni (.cv r)) (synChwniso A)))))
        (synCpw1 (synCec (synCuni (.cv r)) (synChwniso A))))
      p0062 p0063
  have p0065 :=
    @gImaeq2d
      (synWa (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
          (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
            (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
        (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
          (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))))
      (synCpw1 (synCuni (synCsn (synCec (synCuni (.cv r)) (synChwniso A)))))
      (synCpw1 (synCec (synCuni (.cv r)) (synChwniso A))) (synChnsicodemap A) p0064
  have p0066 :=
    @gEqtrd
      (synWa (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
          (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
            (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
        (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
          (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))))
      (synCfv (synChnsiquomap A) (synCsn (synCec (synCuni (.cv r)) (synChwniso A))))
      (synCima (synChnsicodemap A)
        (synCpw1 (synCuni (synCsn (synCec (synCuni (.cv r)) (synChwniso A))))))
      (synCima (synChnsicodemap A) (synCpw1 (synCec (synCuni (.cv r)) (synChwniso A))))
      p0049 p0065
  have p0072 :=
    @gSimpr (.classMem (synCuni (.cv r)) (synChwcn A))
      (.classEq (.cv r) (synCsn (synCuni (.cv r))))
  have p0073 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
          (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
            (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
        (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
          (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))))
      (synWa (.classMem (synCuni (.cv r)) (synChwcn A))
        (.classEq (.cv r) (synCsn (synCuni (.cv r)))))
      (.classEq (.cv r) (synCsn (synCuni (.cv r)))) p0019 p0072
  have p0074 := @gEceq1 (.cv r) (synCsn (synCuni (.cv r))) (synCsi (synChwniso A))
  have p0075 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
          (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
            (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
        (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
          (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))))
      (.classEq (.cv r) (synCsn (synCuni (.cv r))))
      (.classEq (synCec (.cv r) (synCsi (synChwniso A)))
        (synCec (synCsn (synCuni (.cv r))) (synCsi (synChwniso A))))
      p0073 p0074
  have p0083 := @gElex (synCuni (.cv r)) (synChwcn A)
  have p0084 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
          (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
            (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
        (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
          (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))))
      (.classMem (synCuni (.cv r)) (synChwcn A))
      (.classMem (synCuni (.cv r)) (synCvv)) p0021 p0083
  have p0085 := @gSiecsnclndv (synCuni (.cv r)) (synChwniso A)
  have p0086 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
          (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
            (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
        (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
          (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))))
      (.classMem (synCuni (.cv r)) (synCvv))
      (.classEq (synCec (synCsn (synCuni (.cv r))) (synCsi (synChwniso A)))
        (synCpw1 (synCec (synCuni (.cv r)) (synChwniso A))))
      p0084 p0085
  have p0087 :=
    @gEqtrd
      (synWa (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
          (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
            (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
        (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
          (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))))
      (synCec (.cv r) (synCsi (synChwniso A)))
      (synCec (synCsn (synCuni (.cv r))) (synCsi (synChwniso A)))
      (synCpw1 (synCec (synCuni (.cv r)) (synChwniso A))) p0075 p0086
  have p0088 :=
    @gEqcomd
      (synWa (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
          (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
            (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
        (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
          (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))))
      (synCec (.cv r) (synCsi (synChwniso A)))
      (synCpw1 (synCec (synCuni (.cv r)) (synChwniso A))) p0087
  have p0089 :=
    @gImaeq2d
      (synWa (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
          (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
            (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
        (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
          (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))))
      (synCpw1 (synCec (synCuni (.cv r)) (synChwniso A)))
      (synCec (.cv r) (synCsi (synChwniso A))) (synChnsicodemap A) p0088
  have p0090 :=
    @gEqtrd
      (synWa (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
          (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
            (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
        (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
          (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))))
      (synCfv (synChnsiquomap A) (synCsn (synCec (synCuni (.cv r)) (synChwniso A))))
      (synCima (synChnsicodemap A) (synCpw1 (synCec (synCuni (.cv r)) (synChwniso A))))
      (synCima (synChnsicodemap A) (synCec (.cv r) (synCsi (synChwniso A)))) p0066
      p0089
  have p0094 := @gHnsicodemapclassimcldndv A (.cv r) hyp_hnsiquomappreexndv_1
  have p0095 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
          (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
            (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
        (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
          (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))))
      (.classMem (.cv r) (synCpw1 (synChwcn A)))
      (.classEq (synCima (synChnsicodemap A) (synCec (.cv r) (synCsi (synChwniso A))))
        (synCec (synCfv (synChnsicodemap A) (.cv r)) (synChwniso (synCpw1 A))))
      p0017 p0094
  have p0096 :=
    @gEqtrd
      (synWa (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
          (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
            (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
        (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
          (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))))
      (synCfv (synChnsiquomap A) (synCsn (synCec (synCuni (.cv r)) (synChwniso A))))
      (synCima (synChnsicodemap A) (synCec (.cv r) (synCsi (synChwniso A))))
      (synCec (synCfv (synChnsicodemap A) (.cv r)) (synChwniso (synCpw1 A))) p0090
      p0095
  have p0097 :=
    @gEqcomd
      (synWa (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
          (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
            (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
        (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
          (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))))
      (synCfv (synChnsiquomap A) (synCsn (synCec (synCuni (.cv r)) (synChwniso A))))
      (synCec (synCfv (synChnsicodemap A) (.cv r)) (synChwniso (synCpw1 A))) p0096
  have p0098 :=
    @gEqtrd
      (synWa (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
          (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
            (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
        (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
          (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))))
      (.cv y) (synCec (synCfv (synChnsicodemap A) (.cv r)) (synChwniso (synCpw1 A)))
      (synCfv (synChnsiquomap A) (synCsn (synCec (synCuni (.cv r)) (synChwniso A))))
      p0036 p0097
  have p0099 :=
    @gJca
      (synWa (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
          (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
            (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
        (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
          (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))))
      (.classMem (synCsn (synCec (synCuni (.cv r)) (synChwniso A)))
        (synCpw1 (synChnord A)))
      (.classEq (.cv y) (synCfv (synChnsiquomap A)
          (synCsn (synCec (synCuni (.cv r)) (synChwniso A)))))
      p0025 p0098
  have p0100 :=
    @gId (.classEq (.cv x) (synCsn (synCec (synCuni (.cv r)) (synChwniso A))))
  have p0101 :=
    @gFveq2d (.classEq (.cv x) (synCsn (synCec (synCuni (.cv r)) (synChwniso A))))
      (.cv x) (synCsn (synCec (synCuni (.cv r)) (synChwniso A))) (synChnsiquomap A)
      p0100
  have p0102 :=
    @gEqeq2d (.classEq (.cv x) (synCsn (synCec (synCuni (.cv r)) (synChwniso A))))
      (synCfv (synChnsiquomap A) (.cv x))
      (synCfv (synChnsiquomap A) (synCsn (synCec (synCuni (.cv r)) (synChwniso A))))
      (.cv y) p0101
  have p0103 :=
    @gRspcev (.classEq (.cv y) (synCfv (synChnsiquomap A) (.cv x)))
      (.classEq (.cv y) (synCfv (synChnsiquomap A)
          (synCsn (synCec (synCuni (.cv r)) (synChwniso A)))))
      x (synCsn (synCec (synCuni (.cv r)) (synChwniso A))) (synCpw1 (synChnord A))
      dv_cache_0007 dv_cache_0008 dv_cache_0009 p0102
  have p0104 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
          (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
            (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
        (synWa (.classMem (.cv r) (synCpw1 (synChwcn A)))
          (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))))
      (synWa (.classMem (synCsn (synCec (synCuni (.cv r)) (synChwniso A)))
          (synCpw1 (synChnord A))) (.classEq (.cv y) (synCfv (synChnsiquomap A)
            (synCsn (synCec (synCuni (.cv r)) (synChwniso A))))))
      (synWrex x (synCpw1 (synChnord A))
        (.classEq (.cv y) (synCfv (synChnsiquomap A) (.cv x))))
      p0099 p0103
  have p0105 :=
    @gRexlimddv
      (synWa (.classMem (.cv y) (synChnord (synCpw1 A)))
        (synWa (.classMem (.cv w) (synChwcn (synCpw1 A)))
          (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))))
      (.classEq (.cv w) (synCfv (synChnsicodemap A) (.cv r)))
      (synWrex x (synCpw1 (synChnord A))
        (.classEq (.cv y) (synCfv (synChnsiquomap A) (.cv x))))
      r (synCpw1 (synChwcn A)) dv_cache_0010 dv_cache_0011 p0014 p0104
  have p0106 :=
    @gRexlimddv (.classMem (.cv y) (synChnord (synCpw1 A)))
      (.classEq (.cv y) (synCec (.cv w) (synChwniso (synCpw1 A))))
      (synWrex x (synCpw1 (synChnord A))
        (.classEq (.cv y) (synCfv (synChnsiquomap A) (.cv x))))
      w (synChwcn (synCpw1 A)) dv_cache_0012 dv_cache_0013 p0006 p0105
  exact p0106

/-- Checked nominal proof certificate identified upstream as `g_hnsiquomapfondv`. -/
@[expose]
noncomputable def gHnsiquomapfondv (A : Class)
    (hyp_hnsiquomapfondv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (synWfo (synChnsiquomap A) (synCpw1 (synChnord A)) (synChnord (synCpw1 A))) :=
  by
  let proofSupport : Finset Var := A.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0003 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0004 : x ∉ ((synCpw1 (synChnord A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0005 : y ∉ ((synCpw1 (synChnord A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, fresh_y_not_A,
          not_false_eq_true])
  have dv_cache_0006 : x ∉ ((synChnord (synCpw1 A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0007 : y ∉ ((synChnord (synCpw1 A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_y_not_A,
          not_false_eq_true])
  have dv_cache_0008 : x ∉ ((synChnsiquomap A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap,
          fresh_x_not_A, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((synChnsiquomap A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap,
          fresh_y_not_A, not_false_eq_true])
  have p0000 := @gHnsiquomapfndv A hyp_hnsiquomapfondv_1
  have p0001 :=
    @gHnsiquomappreexndv x y A dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_hnsiquomapfondv_1
  have p0002 :=
    @gRgen
      (synWrex x (synCpw1 (synChnord A))
        (.classEq (.cv y) (synCfv (synChnsiquomap A) (.cv x))))
      y (synChnord (synCpw1 A)) p0001
  have p0003 :=
    @gPm32i
      (synWf (synChnsiquomap A) (synCpw1 (synChnord A)) (synChnord (synCpw1 A)))
      (synWral y (synChnord (synCpw1 A)) (synWrex x (synCpw1 (synChnord A))
          (.classEq (.cv y) (synCfv (synChnsiquomap A) (.cv x)))))
      p0000 p0002
  have p0004 :=
    @gDffo3 x y (synCpw1 (synChnord A)) (synChnord (synCpw1 A)) (synChnsiquomap A)
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0003
  have p0005 :=
    @gMpbir
      (synWfo (synChnsiquomap A) (synCpw1 (synChnord A)) (synChnord (synCpw1 A)))
      (synWa (synWf (synChnsiquomap A) (synCpw1 (synChnord A)) (synChnord (synCpw1 A)))
        (synWral y (synChnord (synCpw1 A)) (synWrex x (synCpw1 (synChnord A))
            (.classEq (.cv y) (synCfv (synChnsiquomap A) (.cv x))))))
      p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_hnsicodemapkernelcl2ndv`. -/
@[expose]
noncomputable def gHnsicodemapkernelcl2ndv (A : Class) (P : Class) (Q : Class) :
    Nominal.NPrf
      (.imp (.classMem Q (synCpw1 (synChwcn A))) (.imp (.classMem P (synCpw1 (synChwcn A)))
          (synWb (synWbr Q (synCsi (synChwniso A)) P)
            (synWbr (synCfv (synChnsicodemap A) Q) (synChwniso (synCpw1 A))
              (synCfv (synChnsicodemap A) P))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ P.fv ∪ Q.fv
  let r : Var := freshVar proofSupport 0
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_r_not_P : r ∉ P.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_not_Q : r ∉ Q.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have dv_cache_0001 : r ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_A, not_false_eq_true])
  have dv_cache_0002 : r ∉ (Q).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_Q, not_false_eq_true])
  have dv_cache_0003 : r ∉ (P).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_P, not_false_eq_true])
  have dv_cache_0004 : r ∉ ((synCpw1 (synChwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, fresh_r_not_A,
          not_false_eq_true])
  have dv_cache_0005 :
    r ∉
      ((Wff.imp (.classMem Q (synCpw1 (synChwcn A)))
          (synWb (synWbr Q (synCsi (synChwniso A)) P)
            (synWbr (synCfv (synChnsicodemap A) Q) (synChwniso (synCpw1 A))
              (synCfv (synChnsicodemap A) P))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap,
          Finset.mem_union, fresh_r_not_Q, fresh_r_not_A, fresh_r_not_P, or_false,
          not_false_eq_true])
  have p0000 := @gBiid (.classMem Q (synCpw1 (synChwcn A)))
  have p0001 :=
    @gA1i
      (synWb (.classMem Q (synCpw1 (synChwcn A))) (.classMem Q (synCpw1 (synChwcn A))))
      (.classEq (.cv r) P) p0000
  have p0002 := @gId (.classEq (.cv r) P)
  have p0003 := @gBreq2d (.classEq (.cv r) P) (.cv r) P Q (synCsi (synChwniso A)) p0002
  have p0005 := @gFveq2d (.classEq (.cv r) P) (.cv r) P (synChnsicodemap A) p0002
  have p0006 :=
    @gBreq2d (.classEq (.cv r) P) (synCfv (synChnsicodemap A) (.cv r))
      (synCfv (synChnsicodemap A) P) (synCfv (synChnsicodemap A) Q)
      (synChwniso (synCpw1 A)) p0005
  have p0007 :=
    @gBibi12d (.classEq (.cv r) P) (synWbr Q (synCsi (synChwniso A)) (.cv r))
      (synWbr Q (synCsi (synChwniso A)) P)
      (synWbr (synCfv (synChnsicodemap A) Q) (synChwniso (synCpw1 A))
        (synCfv (synChnsicodemap A) (.cv r)))
      (synWbr (synCfv (synChnsicodemap A) Q) (synChwniso (synCpw1 A))
        (synCfv (synChnsicodemap A) P))
      p0003 p0006
  have p0008 :=
    @gImbi12d (.classEq (.cv r) P) (.classMem Q (synCpw1 (synChwcn A)))
      (.classMem Q (synCpw1 (synChwcn A)))
      (synWb (synWbr Q (synCsi (synChwniso A)) (.cv r))
        (synWbr (synCfv (synChnsicodemap A) Q) (synChwniso (synCpw1 A))
          (synCfv (synChnsicodemap A) (.cv r))))
      (synWb (synWbr Q (synCsi (synChwniso A)) P)
        (synWbr (synCfv (synChnsicodemap A) Q) (synChwniso (synCpw1 A))
          (synCfv (synChnsicodemap A) P)))
      p0001 p0007
  have p0009 := @gHnsicodemapkernelclndv A Q r dv_cache_0001 dv_cache_0002
  have p0010 :=
    @gCom12 (.classMem Q (synCpw1 (synChwcn A)))
      (.classMem (.cv r) (synCpw1 (synChwcn A)))
      (synWb (synWbr Q (synCsi (synChwniso A)) (.cv r))
        (synWbr (synCfv (synChnsicodemap A) Q) (synChwniso (synCpw1 A))
          (synCfv (synChnsicodemap A) (.cv r))))
      p0009
  have p0011 :=
    @gVtoclga
      (.imp (.classMem Q (synCpw1 (synChwcn A)))
        (synWb (synWbr Q (synCsi (synChwniso A)) (.cv r))
          (synWbr (synCfv (synChnsicodemap A) Q) (synChwniso (synCpw1 A))
            (synCfv (synChnsicodemap A) (.cv r)))))
      (.imp (.classMem Q (synCpw1 (synChwcn A)))
        (synWb (synWbr Q (synCsi (synChwniso A)) P)
          (synWbr (synCfv (synChnsicodemap A) Q) (synChwniso (synCpw1 A))
            (synCfv (synChnsicodemap A) P))))
      r P (synCpw1 (synChwcn A)) dv_cache_0003 dv_cache_0004 dv_cache_0005 p0008 p0010
  have p0012 :=
    @gCom12 (.classMem P (synCpw1 (synChwcn A))) (.classMem Q (synCpw1 (synChwcn A)))
      (synWb (synWbr Q (synCsi (synChwniso A)) P)
        (synWbr (synCfv (synChnsicodemap A) Q) (synChwniso (synCpw1 A))
          (synCfv (synChnsicodemap A) P)))
      p0011
  exact p0012


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part009`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hnsiquomaprepvalndv`. -/
@[expose]
noncomputable def gHnsiquomaprepvalndv (u : Var) (A : Class) (q : Var)
    (dv_A_q : q ∉ A.fv) (dv_A_u : u ∉ A.fv) (_dv_q_u : q ≠ u)
    (hyp_hnsiquomaprepvalndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (synWa (.classMem (.cv u) (synChwcn A))
            (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q))
          (synCec (synCfv (synChnsicodemap A) (synCsn (.cv u)))
            (synChwniso (synCpw1 A))))) :=
  by
  have dv_cache_0001 : q ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_q, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((synChwniso A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, dv_A_u,
          not_false_eq_true])
  have p0000 :=
    @gSimpl (.classMem (.cv q) (synCpw1 (synChnord A)))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A))))
  have p0001 := @gHnsiquomapvalndv A q dv_cache_0001 hyp_hnsiquomaprepvalndv_1
  have p0002 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (.classMem (.cv q) (synCpw1 (synChnord A)))
      (.classEq (synCfv (synChnsiquomap A) (.cv q))
        (synCima (synChnsicodemap A) (synCpw1 (synCuni (.cv q)))))
      p0000 p0001
  have p0003 :=
    @gSimpr (.classMem (.cv q) (synCpw1 (synChnord A)))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A))))
  have p0004 :=
    @gSimpr (.classMem (.cv u) (synChwcn A))
      (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))
  have p0005 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A))))
      (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A))) p0003 p0004
  have p0006 := @gPw1eq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A))
  have p0007 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))
      (.classEq (synCpw1 (synCuni (.cv q))) (synCpw1 (synCec (.cv u) (synChwniso A))))
      p0005 p0006
  have p0008 := @gSiecsnndv u (synChwniso A) dv_cache_0002
  have p0009 :=
    @gEqcomi (synCec (synCsn (.cv u)) (synCsi (synChwniso A)))
      (synCpw1 (synCec (.cv u) (synChwniso A))) p0008
  have p0010 :=
    @gA1i
      (.classEq (synCpw1 (synCec (.cv u) (synChwniso A)))
        (synCec (synCsn (.cv u)) (synCsi (synChwniso A))))
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      p0009
  have p0011 :=
    @gEqtrd
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (synCpw1 (synCuni (.cv q))) (synCpw1 (synCec (.cv u) (synChwniso A)))
      (synCec (synCsn (.cv u)) (synCsi (synChwniso A))) p0007 p0010
  have p0012 :=
    @gImaeq2d
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (synCpw1 (synCuni (.cv q))) (synCec (synCsn (.cv u)) (synCsi (synChwniso A)))
      (synChnsicodemap A) p0011
  have p0013 :=
    @gEqtrd
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (synCfv (synChnsiquomap A) (.cv q))
      (synCima (synChnsicodemap A) (synCpw1 (synCuni (.cv q))))
      (synCima (synChnsicodemap A) (synCec (synCsn (.cv u)) (synCsi (synChwniso A))))
      p0002 p0012
  have p0015 :=
    @gSimpl (.classMem (.cv u) (synChwcn A))
      (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))
  have p0016 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A))))
      (.classMem (.cv u) (synChwcn A)) p0003 p0015
  have p0017 := @gSnelpw1 (.cv u) (synChwcn A)
  have p0018 :=
    @gSylibr
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (.classMem (.cv u) (synChwcn A))
      (.classMem (synCsn (.cv u)) (synCpw1 (synChwcn A))) p0016 p0017
  have p0019 := @gHnsicodemapclassimcldndv A (synCsn (.cv u)) hyp_hnsiquomaprepvalndv_1
  have p0020 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (.classMem (synCsn (.cv u)) (synCpw1 (synChwcn A)))
      (.classEq (synCima (synChnsicodemap A)
          (synCec (synCsn (.cv u)) (synCsi (synChwniso A))))
        (synCec (synCfv (synChnsicodemap A) (synCsn (.cv u))) (synChwniso (synCpw1 A))))
      p0018 p0019
  have p0021 :=
    @gEqtrd
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (synCfv (synChnsiquomap A) (.cv q))
      (synCima (synChnsicodemap A) (synCec (synCsn (.cv u)) (synCsi (synChwniso A))))
      (synCec (synCfv (synChnsicodemap A) (synCsn (.cv u))) (synChwniso (synCpw1 A)))
      p0013 p0020
  exact p0021

/-- Checked nominal proof certificate identified upstream as `g_hnordpw1repndv`. -/
@[expose]
noncomputable def gHnordpw1repndv (u : Var) (A : Class) (q : Var) (_dv_A_q : q ∉ A.fv)
    (_dv_A_u : u ∉ A.fv) (_dv_q_u : q ≠ u) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (synWa (.classMem (.cv u) (synChwcn A))
            (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
        (.classEq (.cv q) (synCsn (synCec (.cv u) (synChwniso A))))) :=
  by
  have p0000 :=
    @gSimpl (.classMem (.cv q) (synCpw1 (synChnord A)))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A))))
  have p0001 := @gPw1argclcl (synChnord A) (.cv q)
  have p0002 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (.classMem (.cv q) (synCpw1 (synChnord A)))
      (synWa (.classMem (synCuni (.cv q)) (synChnord A))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      p0000 p0001
  have p0003 :=
    @gSimpr (.classMem (synCuni (.cv q)) (synChnord A))
      (.classEq (.cv q) (synCsn (synCuni (.cv q))))
  have p0004 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (synWa (.classMem (synCuni (.cv q)) (synChnord A))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0002 p0003
  have p0005 :=
    @gSimpr (.classMem (.cv q) (synCpw1 (synChnord A)))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A))))
  have p0006 :=
    @gSimpr (.classMem (.cv u) (synChwcn A))
      (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))
  have p0007 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A))))
      (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A))) p0005 p0006
  have p0008 := @gSneq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A))
  have p0009 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))
      (.classEq (synCsn (synCuni (.cv q))) (synCsn (synCec (.cv u) (synChwniso A))))
      p0007 p0008
  have p0010 :=
    @gEqtrd
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (.cv q) (synCsn (synCuni (.cv q))) (synCsn (synCec (.cv u) (synChwniso A)))
      p0004 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_brsnsiandv`. -/
@[expose]
noncomputable def gBrsnsiandv (A : Class) (B : Class) (R : Class)
    (_dv_A_R : Disjoint A.fv R.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
        (synWb (synWbr (synCsn A) (synCsi R) (synCsn B)) (synWbr A R B))) :=
  by
  have p0000 := @gId (.classEq A (synCif (.classMem A (synCvv)) A (synC0)))
  have p0001 := @gSneq A (synCif (.classMem A (synCvv)) A (synC0))
  have p0002 :=
    @gSyl (.classEq A (synCif (.classMem A (synCvv)) A (synC0)))
      (.classEq A (synCif (.classMem A (synCvv)) A (synC0)))
      (.classEq (synCsn A) (synCsn (synCif (.classMem A (synCvv)) A (synC0)))) p0000
      p0001
  have p0003 :=
    @gBreq1d (.classEq A (synCif (.classMem A (synCvv)) A (synC0))) (synCsn A)
      (synCsn (synCif (.classMem A (synCvv)) A (synC0))) (synCsn B) (synCsi R) p0002
  have p0005 :=
    @gBreq1d (.classEq A (synCif (.classMem A (synCvv)) A (synC0))) A
      (synCif (.classMem A (synCvv)) A (synC0)) B R p0000
  have p0006 :=
    @gBibi12d (.classEq A (synCif (.classMem A (synCvv)) A (synC0)))
      (synWbr (synCsn A) (synCsi R) (synCsn B))
      (synWbr (synCsn (synCif (.classMem A (synCvv)) A (synC0))) (synCsi R) (synCsn B))
      (synWbr A R B) (synWbr (synCif (.classMem A (synCvv)) A (synC0)) R B) p0003
      p0005
  have p0007 := @gId (.classEq B (synCif (.classMem B (synCvv)) B (synC0)))
  have p0008 := @gSneq B (synCif (.classMem B (synCvv)) B (synC0))
  have p0009 :=
    @gSyl (.classEq B (synCif (.classMem B (synCvv)) B (synC0)))
      (.classEq B (synCif (.classMem B (synCvv)) B (synC0)))
      (.classEq (synCsn B) (synCsn (synCif (.classMem B (synCvv)) B (synC0)))) p0007
      p0008
  have p0010 :=
    @gBreq2d (.classEq B (synCif (.classMem B (synCvv)) B (synC0))) (synCsn B)
      (synCsn (synCif (.classMem B (synCvv)) B (synC0)))
      (synCsn (synCif (.classMem A (synCvv)) A (synC0))) (synCsi R) p0009
  have p0012 :=
    @gBreq2d (.classEq B (synCif (.classMem B (synCvv)) B (synC0))) B
      (synCif (.classMem B (synCvv)) B (synC0))
      (synCif (.classMem A (synCvv)) A (synC0)) R p0007
  have p0013 :=
    @gBibi12d (.classEq B (synCif (.classMem B (synCvv)) B (synC0)))
      (synWbr (synCsn (synCif (.classMem A (synCvv)) A (synC0))) (synCsi R) (synCsn B))
      (synWbr (synCsn (synCif (.classMem A (synCvv)) A (synC0))) (synCsi R)
        (synCsn (synCif (.classMem B (synCvv)) B (synC0))))
      (synWbr (synCif (.classMem A (synCvv)) A (synC0)) R B)
      (synWbr (synCif (.classMem A (synCvv)) A (synC0)) R
        (synCif (.classMem B (synCvv)) B (synC0)))
      p0010 p0012
  have p0014 := @gEqid (synC0)
  have p0015 := @gSimpr (.classEq (synC0) (synC0)) (.classMem A (synCvv))
  have p0016 := @gN0ex
  have p0017 :=
    @gA1i (.classMem (synC0) (synCvv))
      (synWa (.classEq (synC0) (synC0)) (.neg (.classMem A (synCvv)))) p0016
  have p0018 :=
    @gIfclda (.classEq (synC0) (synC0)) (.classMem A (synCvv)) A (synC0) (synCvv)
      p0015 p0017
  have p0019 := Nominal.mp p0014 p0018
  have p0021 := @gSimpr (.classEq (synC0) (synC0)) (.classMem B (synCvv))
  have p0023 :=
    @gA1i (.classMem (synC0) (synCvv))
      (synWa (.classEq (synC0) (synC0)) (.neg (.classMem B (synCvv)))) p0016
  have p0024 :=
    @gIfclda (.classEq (synC0) (synC0)) (.classMem B (synCvv)) B (synC0) (synCvv)
      p0021 p0023
  have p0025 := Nominal.mp p0014 p0024
  have p0026 :=
    @gBrsnsi (synCif (.classMem A (synCvv)) A (synC0))
      (synCif (.classMem B (synCvv)) B (synC0)) R p0019 p0025
  have p0027 :=
    @gDedth2h (.classMem A (synCvv)) (.classMem B (synCvv))
      (synWb (synWbr (synCsn A) (synCsi R) (synCsn B)) (synWbr A R B))
      (synWb (synWbr (synCsn (synCif (.classMem A (synCvv)) A (synC0))) (synCsi R)
          (synCsn B)) (synWbr (synCif (.classMem A (synCvv)) A (synC0)) R B))
      (synWb (synWbr (synCsn (synCif (.classMem A (synCvv)) A (synC0))) (synCsi R)
          (synCsn (synCif (.classMem B (synCvv)) B (synC0))))
        (synWbr (synCif (.classMem A (synCvv)) A (synC0)) R
          (synCif (.classMem B (synCvv)) B (synC0))))
      A B (synC0) (synC0) p0006 p0013 p0026
  exact p0027


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part010`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hnsiquomapfvineqndv`. -/
@[expose]
noncomputable def gHnsiquomapfvineqndv (A : Class) (s : Var) (q : Var)
    (dv_A_q : q ∉ A.fv) (dv_A_s : s ∉ A.fv) (_dv_q_s : q ≠ s)
    (hyp_hnsiquomapfvineqndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.classMem (.cv s) (synCpw1 (synChnord A)))) (.imp
          (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s)))
          (.classEq (.cv q) (.cv s)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ ({ s } : Finset Var) ∪ ({ q } : Finset Var)
  let u : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_u_ne_s : u ≠ s := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_q : u ≠ q := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_u : q ≠ u := Ne.symm fresh_u_ne_q
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_v_ne_s : v ≠ s := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_s_ne_v : s ≠ v := Ne.symm fresh_v_ne_s
  have fresh_v_ne_q : v ≠ q := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_u_ne_v : u ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_v_ne_u : v ≠ u := Ne.symm fresh_u_ne_v
  have dv_cache_0001 : u ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((synCuni (.cv q))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_u_ne_q,
          not_false_eq_true])
  have dv_cache_0003 : v ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_A, not_false_eq_true])
  have dv_cache_0004 : v ∉ ((synCuni (.cv s))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_v_ne_s,
          not_false_eq_true])
  have dv_cache_0005 : q ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_q, not_false_eq_true])
  have dv_cache_0006 : q ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show q ≠ u from (by exact fresh_q_ne_u))
  have dv_cache_0007 : s ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_s, not_false_eq_true])
  have dv_cache_0008 : s ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show s ≠ v from (by exact fresh_s_ne_v))
  have dv_cache_0009 : Disjoint ((Class.cv u)).fv ((synChwniso A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (show Disjoint ((Class.cv u)).fv ((synChwniso A)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso];
          exact
            (show Disjoint (({ u } : Finset Var)) ((A).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show u ∉ (A).fv from (by exact fresh_u_not_A))))))
  have dv_cache_0010 :
    v ∉
      ((Wff.imp (.classEq (synCfv (synChnsiquomap A) (.cv q))
            (synCfv (synChnsiquomap A) (.cv s))) (.classEq (.cv q) (.cv s)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_q, fresh_v_not_A, fresh_v_ne_s, or_false,
          not_false_eq_true])
  have dv_cache_0011 :
    v ∉
      ((synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classMem (.cv s) (synCpw1 (synChnord A))))
          (synWa (.classMem (.cv u) (synChwcn A))
            (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_q, fresh_v_not_A, fresh_v_ne_s, fresh_v_ne_u,
          or_false, not_false_eq_true])
  have dv_cache_0012 :
    u ∉
      ((Wff.imp (.classEq (synCfv (synChnsiquomap A) (.cv q))
            (synCfv (synChnsiquomap A) (.cv s))) (.classEq (.cv q) (.cv s)))).fv :=
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
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_q, fresh_u_not_A, fresh_u_ne_s, or_false,
          not_false_eq_true])
  have dv_cache_0013 :
    u ∉
      ((synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.classMem (.cv s) (synCpw1 (synChnord A))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_q, fresh_u_not_A, fresh_u_ne_s, or_false,
          not_false_eq_true])
  have p0000 :=
    @gSimpl (.classMem (.cv q) (synCpw1 (synChnord A)))
      (.classMem (.cv s) (synCpw1 (synChnord A)))
  have p0001 := @gPw1argclcl (synChnord A) (.cv q)
  have p0002 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (.classMem (.cv s) (synCpw1 (synChnord A))))
      (.classMem (.cv q) (synCpw1 (synChnord A)))
      (synWa (.classMem (synCuni (.cv q)) (synChnord A))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      p0000 p0001
  have p0003 :=
    @gSimpl (.classMem (synCuni (.cv q)) (synChnord A))
      (.classEq (.cv q) (synCsn (synCuni (.cv q))))
  have p0004 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (.classMem (.cv s) (synCpw1 (synChnord A))))
      (synWa (.classMem (synCuni (.cv q)) (synChnord A))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      (.classMem (synCuni (.cv q)) (synChnord A)) p0002 p0003
  have p0010 := @gElex (synCuni (.cv q)) (synChnord A)
  have p0011 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (.classMem (.cv s) (synCpw1 (synChnord A))))
      (.classMem (synCuni (.cv q)) (synChnord A))
      (.classMem (synCuni (.cv q)) (synCvv)) p0004 p0010
  have p0012 := @gElhnordclndv u A (synCuni (.cv q)) dv_cache_0001 dv_cache_0002
  have p0013 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (.classMem (.cv s) (synCpw1 (synChnord A))))
      (.classMem (synCuni (.cv q)) (synCvv))
      (synWb (.classMem (synCuni (.cv q)) (synChnord A)) (synWrex u (synChwcn A)
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      p0011 p0012
  have p0014 :=
    @gMpbid
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (.classMem (.cv s) (synCpw1 (synChnord A))))
      (.classMem (synCuni (.cv q)) (synChnord A))
      (synWrex u (synChwcn A) (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A))))
      p0004 p0013
  have p0015 :=
    @gSimpl
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (.classMem (.cv s) (synCpw1 (synChnord A))))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A))))
  have p0016 :=
    @gSimpr (.classMem (.cv q) (synCpw1 (synChnord A)))
      (.classMem (.cv s) (synCpw1 (synChnord A)))
  have p0017 := @gPw1argclcl (synChnord A) (.cv s)
  have p0018 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (.classMem (.cv s) (synCpw1 (synChnord A))))
      (.classMem (.cv s) (synCpw1 (synChnord A)))
      (synWa (.classMem (synCuni (.cv s)) (synChnord A))
        (.classEq (.cv s) (synCsn (synCuni (.cv s)))))
      p0016 p0017
  have p0019 :=
    @gSimpl (.classMem (synCuni (.cv s)) (synChnord A))
      (.classEq (.cv s) (synCsn (synCuni (.cv s))))
  have p0020 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (.classMem (.cv s) (synCpw1 (synChnord A))))
      (synWa (.classMem (synCuni (.cv s)) (synChnord A))
        (.classEq (.cv s) (synCsn (synCuni (.cv s)))))
      (.classMem (synCuni (.cv s)) (synChnord A)) p0018 p0019
  have p0026 := @gElex (synCuni (.cv s)) (synChnord A)
  have p0027 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (.classMem (.cv s) (synCpw1 (synChnord A))))
      (.classMem (synCuni (.cv s)) (synChnord A))
      (.classMem (synCuni (.cv s)) (synCvv)) p0020 p0026
  have p0028 := @gElhnordclndv v A (synCuni (.cv s)) dv_cache_0003 dv_cache_0004
  have p0029 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (.classMem (.cv s) (synCpw1 (synChnord A))))
      (.classMem (synCuni (.cv s)) (synCvv))
      (synWb (.classMem (synCuni (.cv s)) (synChnord A)) (synWrex v (synChwcn A)
          (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
      p0027 p0028
  have p0030 :=
    @gMpbid
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (.classMem (.cv s) (synCpw1 (synChnord A))))
      (.classMem (synCuni (.cv s)) (synChnord A))
      (synWrex v (synChwcn A) (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A))))
      p0020 p0029
  have p0031 :=
    @gSyl
      (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.classMem (.cv s) (synCpw1 (synChnord A))))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (.classMem (.cv s) (synCpw1 (synChnord A))))
      (synWrex v (synChwcn A) (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A))))
      p0015 p0030
  have p0032 :=
    @gSimpl
      (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classMem (.cv s) (synCpw1 (synChnord A))))
          (synWa (.classMem (.cv u) (synChwcn A))
            (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
      (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s)))
  have p0033 :=
    @gSimpl
      (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.classMem (.cv s) (synCpw1 (synChnord A))))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A))))
  have p0034 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classMem (.cv s) (synCpw1 (synChnord A))))
          (synWa (.classMem (.cv u) (synChwcn A))
            (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
      (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.classMem (.cv s) (synCpw1 (synChnord A))))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      p0032 p0033
  have p0036 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.classMem (.cv s) (synCpw1 (synChnord A))))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (.classMem (.cv s) (synCpw1 (synChnord A))))
      p0034 p0015
  have p0038 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (.classMem (.cv s) (synCpw1 (synChnord A))))
      (.classMem (.cv q) (synCpw1 (synChnord A))) p0036 p0000
  have p0042 :=
    @gSimpr
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (.classMem (.cv s) (synCpw1 (synChnord A))))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A))))
  have p0043 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.classMem (.cv s) (synCpw1 (synChnord A))))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A))))
      p0034 p0042
  have p0044 :=
    @gSimpl (.classMem (.cv u) (synChwcn A))
      (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))
  have p0045 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A))))
      (.classMem (.cv u) (synChwcn A)) p0043 p0044
  have p0051 :=
    @gSimpr (.classMem (.cv u) (synChwcn A))
      (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))
  have p0052 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A))))
      (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A))) p0043 p0051
  have p0053 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (.classMem (.cv u) (synChwcn A))
      (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A))) p0045 p0052
  have p0054 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (.classMem (.cv q) (synCpw1 (synChnord A)))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A))))
      p0038 p0053
  have p0055 := @gHnordpw1repndv u A q dv_cache_0005 dv_cache_0001 dv_cache_0006
  have p0056 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (.classEq (.cv q) (synCsn (synCec (.cv u) (synChwniso A)))) p0054 p0055
  have p0080 :=
    @gHnsiquomaprepvalndv u A q dv_cache_0005 dv_cache_0001 dv_cache_0006
      hyp_hnsiquomapfvineqndv_1
  have p0081 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (.classEq (synCfv (synChnsiquomap A) (.cv q))
        (synCec (synCfv (synChnsicodemap A) (synCsn (.cv u))) (synChwniso (synCpw1 A))))
      p0054 p0080
  have p0082 :=
    @gEqcomd
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (synCfv (synChnsiquomap A) (.cv q))
      (synCec (synCfv (synChnsicodemap A) (synCsn (.cv u))) (synChwniso (synCpw1 A)))
      p0081
  have p0083 :=
    @gSimpr
      (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classMem (.cv s) (synCpw1 (synChnord A))))
          (synWa (.classMem (.cv u) (synChwcn A))
            (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
      (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s)))
  have p0084 :=
    @gEqtrd
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (synCec (synCfv (synChnsicodemap A) (synCsn (.cv u))) (synChwniso (synCpw1 A)))
      (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s)) p0082
      p0083
  have p0091 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (.classMem (.cv s) (synCpw1 (synChnord A))))
      (.classMem (.cv s) (synCpw1 (synChnord A))) p0036 p0016
  have p0093 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.classMem (.cv s) (synCpw1 (synChnord A))))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A))))
  have p0094 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classMem (.cv s) (synCpw1 (synChnord A))))
          (synWa (.classMem (.cv u) (synChwcn A))
            (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A))))
      p0032 p0093
  have p0095 :=
    @gSimpl (.classMem (.cv v) (synChwcn A))
      (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))
  have p0096 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A))))
      (.classMem (.cv v) (synChwcn A)) p0094 p0095
  have p0100 :=
    @gSimpr (.classMem (.cv v) (synChwcn A))
      (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))
  have p0101 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A))))
      (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A))) p0094 p0100
  have p0102 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (.classMem (.cv v) (synChwcn A))
      (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A))) p0096 p0101
  have p0103 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (.classMem (.cv s) (synCpw1 (synChnord A)))
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A))))
      p0091 p0102
  have p0104 :=
    @gHnsiquomaprepvalndv v A s dv_cache_0007 dv_cache_0003 dv_cache_0008
      hyp_hnsiquomapfvineqndv_1
  have p0105 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (synWa (.classMem (.cv s) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv v) (synChwcn A))
          (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
      (.classEq (synCfv (synChnsiquomap A) (.cv s))
        (synCec (synCfv (synChnsicodemap A) (synCsn (.cv v))) (synChwniso (synCpw1 A))))
      p0103 p0104
  have p0106 :=
    @gEqtrd
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (synCec (synCfv (synChnsicodemap A) (synCsn (.cv u))) (synChwniso (synCpw1 A)))
      (synCfv (synChnsiquomap A) (.cv s))
      (synCec (synCfv (synChnsicodemap A) (synCsn (.cv v))) (synChwniso (synCpw1 A)))
      p0084 p0105
  have p0114 := @gSnelpw1 (.cv u) (synChwcn A)
  have p0115 :=
    @gSylibr
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (.classMem (.cv u) (synChwcn A))
      (.classMem (synCsn (.cv u)) (synCpw1 (synChwcn A))) p0045 p0114
  have p0116 := @gHnsicodemapfndv A
  have p0117 :=
    @gFfvelrni (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)) (synCsn (.cv u))
      (synChnsicodemap A) p0116
  have p0118 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (.classMem (synCsn (.cv u)) (synCpw1 (synChwcn A)))
      (.classMem (synCfv (synChnsicodemap A) (synCsn (.cv u))) (synChwcn (synCpw1 A)))
      p0115 p0117
  have p0124 := @gSnelpw1 (.cv v) (synChwcn A)
  have p0125 :=
    @gSylibr
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (.classMem (.cv v) (synChwcn A))
      (.classMem (synCsn (.cv v)) (synCpw1 (synChwcn A))) p0096 p0124
  have p0127 :=
    @gFfvelrni (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)) (synCsn (.cv v))
      (synChnsicodemap A) p0116
  have p0128 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (.classMem (synCsn (.cv v)) (synCpw1 (synChwcn A)))
      (.classMem (synCfv (synChnsicodemap A) (synCsn (.cv v))) (synChwcn (synCpw1 A)))
      p0125 p0127
  have p0129 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (.classMem (synCfv (synChnsicodemap A) (synCsn (.cv u))) (synChwcn (synCpw1 A)))
      (.classMem (synCfv (synChnsicodemap A) (synCsn (.cv v))) (synChwcn (synCpw1 A)))
      p0118 p0128
  have p0130 := @gPw1exg A (synCvv)
  have p0131 := Nominal.mp hyp_hnsiquomapfvineqndv_1 p0130
  have p0132 :=
    @gHwnisoclasseqbcl (synCpw1 A) (synCfv (synChnsicodemap A) (synCsn (.cv u)))
      (synCfv (synChnsicodemap A) (synCsn (.cv v))) p0131
  have p0133 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (synWa (.classMem (synCfv (synChnsicodemap A) (synCsn (.cv u)))
          (synChwcn (synCpw1 A))) (.classMem (synCfv (synChnsicodemap A) (synCsn (.cv v)))
          (synChwcn (synCpw1 A))))
      (synWb (.classEq (synCec (synCfv (synChnsicodemap A) (synCsn (.cv u)))
            (synChwniso (synCpw1 A)))
          (synCec (synCfv (synChnsicodemap A) (synCsn (.cv v))) (synChwniso (synCpw1 A))))
        (synWbr (synCfv (synChnsicodemap A) (synCsn (.cv u)))
          (synChwniso (synCpw1 A)) (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
      p0129 p0132
  have p0134 :=
    @gMpbid
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (.classEq (synCec (synCfv (synChnsicodemap A) (synCsn (.cv u)))
          (synChwniso (synCpw1 A))) (synCec (synCfv (synChnsicodemap A) (synCsn (.cv v)))
          (synChwniso (synCpw1 A))))
      (synWbr (synCfv (synChnsicodemap A) (synCsn (.cv u))) (synChwniso (synCpw1 A))
        (synCfv (synChnsicodemap A) (synCsn (.cv v))))
      p0106 p0133
  have p0151 := @gHnsicodemapkernelcl2ndv A (synCsn (.cv v)) (synCsn (.cv u))
  have p0152 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (.classMem (synCsn (.cv u)) (synCpw1 (synChwcn A)))
      (.imp (.classMem (synCsn (.cv v)) (synCpw1 (synChwcn A)))
        (synWb (synWbr (synCsn (.cv u)) (synCsi (synChwniso A)) (synCsn (.cv v)))
          (synWbr (synCfv (synChnsicodemap A) (synCsn (.cv u)))
            (synChwniso (synCpw1 A)) (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
      p0115 p0151
  have p0153 :=
    @gMpd
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (.classMem (synCsn (.cv v)) (synCpw1 (synChwcn A)))
      (synWb (synWbr (synCsn (.cv u)) (synCsi (synChwniso A)) (synCsn (.cv v)))
        (synWbr (synCfv (synChnsicodemap A) (synCsn (.cv u)))
          (synChwniso (synCpw1 A)) (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
      p0125 p0152
  have p0154 :=
    @gMpbird
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (synWbr (synCsn (.cv u)) (synCsi (synChwniso A)) (synCsn (.cv v)))
      (synWbr (synCfv (synChnsicodemap A) (synCsn (.cv u))) (synChwniso (synCpw1 A))
        (synCfv (synChnsicodemap A) (synCsn (.cv v))))
      p0134 p0153
  have p0162 := @gElex (.cv u) (synChwcn A)
  have p0163 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synCvv)) p0045 p0162
  have p0169 := @gElex (.cv v) (synChwcn A)
  have p0170 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (.classMem (.cv v) (synChwcn A)) (.classMem (.cv v) (synCvv)) p0096 p0169
  have p0171 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (.classMem (.cv u) (synCvv)) (.classMem (.cv v) (synCvv)) p0163 p0170
  have p0172 := @gBrsnsiandv (.cv u) (.cv v) (synChwniso A) dv_cache_0009
  have p0173 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (synWa (.classMem (.cv u) (synCvv)) (.classMem (.cv v) (synCvv)))
      (synWb (synWbr (synCsn (.cv u)) (synCsi (synChwniso A)) (synCsn (.cv v)))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      p0171 p0172
  have p0174 :=
    @gMpbid
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (synWbr (synCsn (.cv u)) (synCsi (synChwniso A)) (synCsn (.cv v)))
      (synWbr (.cv u) (synChwniso A) (.cv v)) p0154 p0173
  have p0187 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0045 p0096
  have p0188 := @gHwnisoclasseqbcl A (.cv u) (.cv v) hyp_hnsiquomapfvineqndv_1
  have p0189 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWb (.classEq (synCec (.cv u) (synChwniso A)) (synCec (.cv v) (synChwniso A)))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      p0187 p0188
  have p0190 :=
    @gMpbird
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (.classEq (synCec (.cv u) (synChwniso A)) (synCec (.cv v) (synChwniso A)))
      (synWbr (.cv u) (synChwniso A) (.cv v)) p0174 p0189
  have p0191 :=
    @gSneq (synCec (.cv u) (synChwniso A)) (synCec (.cv v) (synChwniso A))
  have p0192 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (.classEq (synCec (.cv u) (synChwniso A)) (synCec (.cv v) (synChwniso A)))
      (.classEq (synCsn (synCec (.cv u) (synChwniso A)))
        (synCsn (synCec (.cv v) (synChwniso A))))
      p0190 p0191
  have p0193 :=
    @gEqtrd
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (.cv q) (synCsn (synCec (.cv u) (synChwniso A)))
      (synCsn (synCec (.cv v) (synChwniso A))) p0056 p0192
  have p0213 := @gHnordpw1repndv v A s dv_cache_0007 dv_cache_0003 dv_cache_0008
  have p0214 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (synWa (.classMem (.cv s) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv v) (synChwcn A))
          (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
      (.classEq (.cv s) (synCsn (synCec (.cv v) (synChwniso A)))) p0103 p0213
  have p0215 :=
    @gEqcomd
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (.cv s) (synCsn (synCec (.cv v) (synChwniso A))) p0214
  have p0216 :=
    @gEqtrd
      (synWa (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classMem (.cv s) (synCpw1 (synChnord A))))
            (synWa (.classMem (.cv u) (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s))))
      (.cv q) (synCsn (synCec (.cv v) (synChwniso A))) (.cv s) p0193 p0215
  have p0217 :=
    @gEx
      (synWa (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classMem (.cv s) (synCpw1 (synChnord A))))
          (synWa (.classMem (.cv u) (synChwcn A))
            (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))))
      (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s)))
      (.classEq (.cv q) (.cv s)) p0216
  have p0218 :=
    @gRexlimddv
      (synWa (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.classMem (.cv s) (synCpw1 (synChnord A))))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (.classEq (synCuni (.cv s)) (synCec (.cv v) (synChwniso A)))
      (.imp (.classEq (synCfv (synChnsiquomap A) (.cv q))
          (synCfv (synChnsiquomap A) (.cv s))) (.classEq (.cv q) (.cv s)))
      v (synChwcn A) dv_cache_0010 dv_cache_0011 p0031 p0217
  have p0219 :=
    @gRexlimddv
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (.classMem (.cv s) (synCpw1 (synChnord A))))
      (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))
      (.imp (.classEq (synCfv (synChnsiquomap A) (.cv q))
          (synCfv (synChnsiquomap A) (.cv s))) (.classEq (.cv q) (.cv s)))
      u (synChwcn A) dv_cache_0012 dv_cache_0013 p0014 p0218
  exact p0219


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part011`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hnsiquomapf1ndv`. -/
@[expose]
noncomputable def gHnsiquomapf1ndv (A : Class)
    (hyp_hnsiquomapf1ndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (synWf1 (synChnsiquomap A) (synCpw1 (synChnord A)) (synChnord (synCpw1 A))) :=
  by
  let proofSupport : Finset Var := A.fv
  let q : Var := freshVar proofSupport 0
  let s : Var := freshVar proofSupport 1
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (h)
  have fresh_s : s ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_s_not_A : s ∉ A.fv := by
    intro h
    exact fresh_s (h)
  have fresh_q_ne_s : q ≠ s :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_s_ne_q : s ≠ q := Ne.symm fresh_q_ne_s
  have dv_cache_0001 : q ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_A, not_false_eq_true])
  have dv_cache_0002 : s ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_s_not_A, not_false_eq_true])
  have dv_cache_0003 : q ≠ s :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show q ≠ s from (by exact fresh_q_ne_s))
  have dv_cache_0004 : s ∉ ((Wff.classMem (.cv q) (synCpw1 (synChnord A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          Finset.mem_singleton, fresh_s_ne_q, fresh_s_not_A, or_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ ((synCpw1 (synChnord A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, fresh_q_not_A,
          not_false_eq_true])
  have dv_cache_0006 : s ∉ ((synCpw1 (synChnord A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, fresh_s_not_A,
          not_false_eq_true])
  have dv_cache_0007 : q ∉ ((synChnsiquomap A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap,
          fresh_q_not_A, not_false_eq_true])
  have dv_cache_0008 : s ∉ ((synChnsiquomap A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap,
          fresh_s_not_A, not_false_eq_true])
  have p0000 := @gHnsiquomapfndv A hyp_hnsiquomapf1ndv_1
  have p0001 :=
    @gHnsiquomapfvineqndv A s q dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_hnsiquomapf1ndv_1
  have p0002 :=
    @gEx (.classMem (.cv q) (synCpw1 (synChnord A)))
      (.classMem (.cv s) (synCpw1 (synChnord A)))
      (.imp (.classEq (synCfv (synChnsiquomap A) (.cv q))
          (synCfv (synChnsiquomap A) (.cv s))) (.classEq (.cv q) (.cv s)))
      p0001
  have p0003 :=
    @gRalrimiv (.classMem (.cv q) (synCpw1 (synChnord A)))
      (.imp (.classEq (synCfv (synChnsiquomap A) (.cv q))
          (synCfv (synChnsiquomap A) (.cv s))) (.classEq (.cv q) (.cv s)))
      s (synCpw1 (synChnord A)) dv_cache_0004 p0002
  have p0004 :=
    @gRgen
      (synWral s (synCpw1 (synChnord A)) (.imp
          (.classEq (synCfv (synChnsiquomap A) (.cv q)) (synCfv (synChnsiquomap A) (.cv s)))
          (.classEq (.cv q) (.cv s))))
      q (synCpw1 (synChnord A)) p0003
  have p0005 :=
    @gPm32i
      (synWf (synChnsiquomap A) (synCpw1 (synChnord A)) (synChnord (synCpw1 A)))
      (synWral q (synCpw1 (synChnord A)) (synWral s (synCpw1 (synChnord A)) (.imp
            (.classEq (synCfv (synChnsiquomap A) (.cv q))
              (synCfv (synChnsiquomap A) (.cv s))) (.classEq (.cv q) (.cv s)))))
      p0000 p0004
  have p0006 :=
    @gDff13 q s (synCpw1 (synChnord A)) (synChnord (synCpw1 A)) (synChnsiquomap A)
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0003
  have p0007_e01_recanon :
    Nominal.NPrf
      (synWb (synWf1 (synChnsiquomap A) (synCpw1 (synChnord A)) (synChnord (synCpw1 A)))
        (synWa (synWf (synChnsiquomap A) (synCpw1 (synChnord A)) (synChnord (synCpw1 A)))
          (synWral q (synCpw1 (synChnord A)) (synWral s (synCpw1 (synChnord A)) (.imp
                (.classEq (synCfv (synChnsiquomap A) (.cv q))
                  (synCfv (synChnsiquomap A) (.cv s))) (.classEq (.cv q) (.cv s))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWf1 synWa synWf synWfun synWss synCin synCcompl synCnin
          synWnan synCcom synCopab synWex synCcnv synCid synChnsiquomap synCres
          synCpw1 synChnord synCqs synWrex synCec synCima synCsn synChwcn
          synChwniso
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0007 :=
    @gMpbir
      (synWf1 (synChnsiquomap A) (synCpw1 (synChnord A)) (synChnord (synCpw1 A)))
      (synWa (synWf (synChnsiquomap A) (synCpw1 (synChnord A)) (synChnord (synCpw1 A)))
        (synWral q (synCpw1 (synChnord A)) (synWral s (synCpw1 (synChnord A)) (.imp
              (.classEq (synCfv (synChnsiquomap A) (.cv q))
                (synCfv (synChnsiquomap A) (.cv s))) (.classEq (.cv q) (.cv s))))))
      p0005 p0007_e01_recanon
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_hnsiquomapf1ondv`. -/
@[expose]
noncomputable def gHnsiquomapf1ondv (A : Class)
    (hyp_hnsiquomapf1ondv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (synWf1o (synChnsiquomap A) (synCpw1 (synChnord A)) (synChnord (synCpw1 A))) :=
  by
  have p0000 := @gHnsiquomapf1ndv A hyp_hnsiquomapf1ondv_1
  have p0001 := @gHnsiquomapfondv A hyp_hnsiquomapf1ondv_1
  have p0002 :=
    @gPm32i
      (synWf1 (synChnsiquomap A) (synCpw1 (synChnord A)) (synChnord (synCpw1 A)))
      (synWfo (synChnsiquomap A) (synCpw1 (synChnord A)) (synChnord (synCpw1 A)))
      p0000 p0001
  have p0003 :=
    (Nominal.biimpRefl
      (synWf1o (synChnsiquomap A) (synCpw1 (synChnord A)) (synChnord (synCpw1 A))))
  have p0004 :=
    @gMpbir
      (synWf1o (synChnsiquomap A) (synCpw1 (synChnord A)) (synChnord (synCpw1 A)))
      (synWa (synWf1 (synChnsiquomap A) (synCpw1 (synChnord A)) (synChnord (synCpw1 A)))
        (synWfo (synChnsiquomap A) (synCpw1 (synChnord A)) (synChnord (synCpw1 A))))
      p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_hnordpw1shiftenndv`. -/
@[expose]
noncomputable def gHnordpw1shiftenndv (A : Class)
    (hyp_hnordpw1shiftenndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (synWbr (synCpw1 (synChnord A)) (synCen) (synChnord (synCpw1 A))) :=
  by
  have p0000 := @gHnsiquomapf1ondv A hyp_hnordpw1shiftenndv_1
  have p0001 := @gHnsiquomapexgndv A
  have p0002 := Nominal.mp hyp_hnordpw1shiftenndv_1 p0001
  have p0003 :=
    @gF1oen (synCpw1 (synChnord A)) (synChnord (synCpw1 A)) (synChnsiquomap A) p0002
  have p0004 := Nominal.mp p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_hncardtcshiftndv`. -/
@[expose]
noncomputable def gHncardtcshiftndv (A : Class)
    (hyp_hncardtcshiftndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classEq (synCtc (synChncard A)) (synChncard (synCpw1 A))) :=
  by
  have p0000 := @gHnordpw1shiftenndv A hyp_hncardtcshiftndv_1
  have p0001 := @gHncardtcshiftcondndv A hyp_hncardtcshiftndv_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_wppconcrete6fntc7hncard1valndv`. -/
@[expose]
noncomputable def gWppconcrete6fntc7hncard1valndv :
    Nominal.NPrf
      (.classEq (synCfv (synCwppconcrete6fn) (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
        (synChncard (synChnord (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))))) :=
  by
  have p0000 := @gN1cex
  have p0001 := @gHncardtcshiftndv (synC1c) p0000
  have p0002 := (Nominal.classEqRefl (synChncard (synCpw1 (synC1c))))
  have p0003 :=
    @gEqtri (synCtc (synChncard (synC1c))) (synChncard (synCpw1 (synC1c)))
      (synCnc (synChnord (synCpw1 (synC1c)))) p0001 p0002
  have p0004 :=
    @gTceq (synCtc (synChncard (synC1c))) (synCnc (synChnord (synCpw1 (synC1c))))
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @gTceq (synCtc (synCtc (synChncard (synC1c))))
      (synCtc (synCnc (synChnord (synCpw1 (synC1c)))))
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @gTceq (synCtc (synCtc (synCtc (synChncard (synC1c)))))
      (synCtc (synCtc (synCnc (synChnord (synCpw1 (synC1c))))))
  have p0009 := Nominal.mp p0007 p0008
  have p0010 :=
    @gTceq (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))
      (synCtc (synCtc (synCtc (synCnc (synChnord (synCpw1 (synC1c)))))))
  have p0011 := Nominal.mp p0009 p0010
  have p0012 :=
    @gTceq (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))
      (synCtc (synCtc (synCtc (synCtc (synCnc (synChnord (synCpw1 (synC1c))))))))
  have p0013 := Nominal.mp p0011 p0012
  have p0014 :=
    @gTceq
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
      (synCtc (synCtc
          (synCtc (synCtc (synCtc (synCnc (synChnord (synCpw1 (synC1c)))))))))
  have p0015 := Nominal.mp p0013 p0014
  have p0016 :=
    @gFveq2i
      (synCtc (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (synCtc (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCnc (synChnord (synCpw1 (synC1c))))))))))
      (synCwppconcrete6fn) p0015
  have p0018 := @gPw1ex (synC1c) p0000
  have p0019 := @gHnordexg (synCpw1 (synC1c))
  have p0020 := Nominal.mp p0018 p0019
  have p0021 := @gWppconcrete6fnvalndv (synChnord (synCpw1 (synC1c))) p0020
  have p0022 :=
    @gEqtri
      (synCfv (synCwppconcrete6fn) (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
      (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc (synCtc
                (synCtc (synCtc (synCnc (synChnord (synCpw1 (synC1c)))))))))))
      (synChncard (synChnord (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))))
      p0016 p0021
  exact p0022


end NFChoice.DirectNominalPrf.WPPReplay

end
