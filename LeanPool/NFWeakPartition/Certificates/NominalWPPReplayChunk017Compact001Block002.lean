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

@[expose]
noncomputable def g_siecsnndv (u : Var) (R : Class) (_dv_R_u : u ∉ R.fv) :
    Nominal.NPrf
      (.classEq (syn_cec (syn_csn (.cv u)) (syn_csi R)) (syn_cpw1 (syn_cec (.cv u) R))) :=
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
  have dv_cache_0001 : x ∉ ((syn_csn (.cv u))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_u,
          not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_csn (.cv u))).fv :=
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
  have dv_cache_0009 : z ∉ ((syn_cec (.cv u) R)).fv :=
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
  have dv_cache_0010 : z ∉ ((Wff.classEq (.cv p) (syn_csn (.cv y)))).fv :=
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
  have dv_cache_0012 : x ∉ ((Wff.classMem (.cv p) (syn_cpw1 (syn_cec (.cv u) R)))).fv :=
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
  have dv_cache_0013 : y ∉ ((Wff.classMem (.cv p) (syn_cpw1 (syn_cec (.cv u) R)))).fv :=
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
  have dv_cache_0014 : y ∉ ((syn_cec (.cv u) R)).fv :=
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
    y ∉ ((Wff.classMem (.cv p) (syn_cec (syn_csn (.cv u)) (syn_csi R)))).fv :=
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
  have dv_cache_0016 : p ∉ ((syn_cec (syn_csn (.cv u)) (syn_csi R))).fv :=
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
  have dv_cache_0017 : p ∉ ((syn_cpw1 (syn_cec (.cv u) R))).fv :=
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
  have p0000 := @g_elec (.cv p) (syn_csn (.cv u)) (syn_csi R)
  have p0001 :=
    @g_biimpi (.classMem (.cv p) (syn_cec (syn_csn (.cv u)) (syn_csi R)))
      (syn_wbr (syn_csn (.cv u)) (syn_csi R) (.cv p)) p0000
  have p0002 :=
    @g_brsi x y (syn_csn (.cv u)) (.cv p) R dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0003 :=
    @g_sylib (.classMem (.cv p) (syn_cec (syn_csn (.cv u)) (syn_csi R)))
      (syn_wbr (syn_csn (.cv u)) (syn_csi R) (.cv p))
      (syn_wex x (syn_wex y (syn_w3a (.classEq (syn_csn (.cv u)) (syn_csn (.cv x)))
            (.classEq (.cv p) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y)))))
      p0001 p0002
  have p0004 :=
    @g_simp3 (.classEq (syn_csn (.cv u)) (syn_csn (.cv x)))
      (.classEq (.cv p) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))
  have p0005 :=
    @g_simp1 (.classEq (syn_csn (.cv u)) (syn_csn (.cv x)))
      (.classEq (.cv p) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))
  have p0006 := @g_vex u
  have p0007 := @g_sneqr (.cv u) (.cv x) p0006
  have p0008 :=
    @g_syl
      (syn_w3a (.classEq (syn_csn (.cv u)) (syn_csn (.cv x)))
        (.classEq (.cv p) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (.classEq (syn_csn (.cv u)) (syn_csn (.cv x))) (.classEq (.cv u) (.cv x)) p0005
      p0007
  have p0009 :=
    @g_breq1d
      (syn_w3a (.classEq (syn_csn (.cv u)) (syn_csn (.cv x)))
        (.classEq (.cv p) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (.cv u) (.cv x) (.cv y) R p0008
  have p0010 :=
    @g_mpbird
      (syn_w3a (.classEq (syn_csn (.cv u)) (syn_csn (.cv x)))
        (.classEq (.cv p) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wbr (.cv u) R (.cv y)) (syn_wbr (.cv x) R (.cv y)) p0004 p0009
  have p0011 := @g_elec (.cv y) (.cv u) R
  have p0012 :=
    @g_sylibr
      (syn_w3a (.classEq (syn_csn (.cv u)) (syn_csn (.cv x)))
        (.classEq (.cv p) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wbr (.cv u) R (.cv y)) (.classMem (.cv y) (syn_cec (.cv u) R)) p0010 p0011
  have p0013 :=
    @g_simp2 (.classEq (syn_csn (.cv u)) (syn_csn (.cv x)))
      (.classEq (.cv p) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))
  have p0014 :=
    @g_jca
      (syn_w3a (.classEq (syn_csn (.cv u)) (syn_csn (.cv x)))
        (.classEq (.cv p) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (.classMem (.cv y) (syn_cec (.cv u) R)) (.classEq (.cv p) (syn_csn (.cv y))) p0012
      p0013
  have p0015 := @g_id (.classEq (.cv z) (.cv y))
  have p0016 := @g_sneqd (.classEq (.cv z) (.cv y)) (.cv z) (.cv y) p0015
  have p0017 :=
    @g_eqeq2d (.classEq (.cv z) (.cv y)) (syn_csn (.cv z)) (syn_csn (.cv y)) (.cv p) p0016
  have p0018 :=
    @g_rspcev (.classEq (.cv p) (syn_csn (.cv z))) (.classEq (.cv p) (syn_csn (.cv y))) z
      (.cv y) (syn_cec (.cv u) R) dv_cache_0008 dv_cache_0009 dv_cache_0010 p0017
  have p0019 :=
    @g_syl
      (syn_w3a (.classEq (syn_csn (.cv u)) (syn_csn (.cv x)))
        (.classEq (.cv p) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (.classMem (.cv y) (syn_cec (.cv u) R)) (.classEq (.cv p) (syn_csn (.cv y))))
      (syn_wrex z (syn_cec (.cv u) R) (.classEq (.cv p) (syn_csn (.cv z)))) p0014 p0018
  have p0020 := @g_elpw1 z (.cv p) (syn_cec (.cv u) R) dv_cache_0011 dv_cache_0009
  have p0021 :=
    @g_sylibr
      (syn_w3a (.classEq (syn_csn (.cv u)) (syn_csn (.cv x)))
        (.classEq (.cv p) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wrex z (syn_cec (.cv u) R) (.classEq (.cv p) (syn_csn (.cv z))))
      (.classMem (.cv p) (syn_cpw1 (syn_cec (.cv u) R))) p0019 p0020
  have p0022 :=
    @g_exlimivv
      (syn_w3a (.classEq (syn_csn (.cv u)) (syn_csn (.cv x)))
        (.classEq (.cv p) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (.classMem (.cv p) (syn_cpw1 (syn_cec (.cv u) R))) x y dv_cache_0012 dv_cache_0013
      p0021
  have p0023 :=
    @g_syl (.classMem (.cv p) (syn_cec (syn_csn (.cv u)) (syn_csi R)))
      (syn_wex x (syn_wex y (syn_w3a (.classEq (syn_csn (.cv u)) (syn_csn (.cv x)))
            (.classEq (.cv p) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y)))))
      (.classMem (.cv p) (syn_cpw1 (syn_cec (.cv u) R))) p0003 p0022
  have p0024 := @g_elpw1 y (.cv p) (syn_cec (.cv u) R) dv_cache_0004 dv_cache_0014
  have p0025 :=
    @g_biimpi (.classMem (.cv p) (syn_cpw1 (syn_cec (.cv u) R)))
      (syn_wrex y (syn_cec (.cv u) R) (.classEq (.cv p) (syn_csn (.cv y)))) p0024
  have p0026 :=
    @g_simpl (.classMem (.cv y) (syn_cec (.cv u) R)) (.classEq (.cv p) (syn_csn (.cv y)))
  have p0028 :=
    @g_sylib
      (syn_wa (.classMem (.cv y) (syn_cec (.cv u) R)) (.classEq (.cv p) (syn_csn (.cv y))))
      (.classMem (.cv y) (syn_cec (.cv u) R)) (syn_wbr (.cv u) R (.cv y)) p0026 p0011
  have p0030 := @g_vex y
  have p0031 := @g_brsnsi (.cv u) (.cv y) R p0006 p0030
  have p0032 :=
    @g_sylibr
      (syn_wa (.classMem (.cv y) (syn_cec (.cv u) R)) (.classEq (.cv p) (syn_csn (.cv y))))
      (syn_wbr (.cv u) R (.cv y))
      (syn_wbr (syn_csn (.cv u)) (syn_csi R) (syn_csn (.cv y))) p0028 p0031
  have p0033 :=
    @g_simpr (.classMem (.cv y) (syn_cec (.cv u) R)) (.classEq (.cv p) (syn_csn (.cv y)))
  have p0034 :=
    @g_breq2d
      (syn_wa (.classMem (.cv y) (syn_cec (.cv u) R)) (.classEq (.cv p) (syn_csn (.cv y))))
      (.cv p) (syn_csn (.cv y)) (syn_csn (.cv u)) (syn_csi R) p0033
  have p0035 :=
    @g_mpbird
      (syn_wa (.classMem (.cv y) (syn_cec (.cv u) R)) (.classEq (.cv p) (syn_csn (.cv y))))
      (syn_wbr (syn_csn (.cv u)) (syn_csi R) (.cv p))
      (syn_wbr (syn_csn (.cv u)) (syn_csi R) (syn_csn (.cv y))) p0032 p0034
  have p0037 :=
    @g_sylibr
      (syn_wa (.classMem (.cv y) (syn_cec (.cv u) R)) (.classEq (.cv p) (syn_csn (.cv y))))
      (syn_wbr (syn_csn (.cv u)) (syn_csi R) (.cv p))
      (.classMem (.cv p) (syn_cec (syn_csn (.cv u)) (syn_csi R))) p0035 p0000
  have p0038 :=
    @g_rexlimiva (.classEq (.cv p) (syn_csn (.cv y)))
      (.classMem (.cv p) (syn_cec (syn_csn (.cv u)) (syn_csi R))) y (syn_cec (.cv u) R)
      dv_cache_0015 p0037
  have p0039 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cec (.cv u) R)))
      (syn_wrex y (syn_cec (.cv u) R) (.classEq (.cv p) (syn_csn (.cv y))))
      (.classMem (.cv p) (syn_cec (syn_csn (.cv u)) (syn_csi R))) p0025 p0038
  have p0040 :=
    @g_impbii (.classMem (.cv p) (syn_cec (syn_csn (.cv u)) (syn_csi R)))
      (.classMem (.cv p) (syn_cpw1 (syn_cec (.cv u) R))) p0023 p0039
  have p0041 :=
    @g_eqriv p (syn_cec (syn_csn (.cv u)) (syn_csi R)) (syn_cpw1 (syn_cec (.cv u) R))
      dv_cache_0016 dv_cache_0017 p0040
  exact p0041

@[expose]
noncomputable def g_siecsnclndv (C : Class) (R : Class) :
    Nominal.NPrf
      (.imp (.classMem C (syn_cvv))
        (.classEq (syn_cec (syn_csn C) (syn_csi R)) (syn_cpw1 (syn_cec C R)))) :=
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
    u ∉ ((Wff.classEq (syn_cec (syn_csn C) (syn_csi R)) (syn_cpw1 (syn_cec C R)))).fv :=
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
  have dv_cache_0004 : u ∉ ((Wff.classMem C (syn_cvv))).fv :=
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
  have p0000 := @g_id (.classMem C (syn_cvv))
  have p0001 := @g_simpr (.classMem C (syn_cvv)) (.classEq (.cv u) C)
  have p0002 := @g_sneq (.cv u) C
  have p0003 :=
    @g_syl (syn_wa (.classMem C (syn_cvv)) (.classEq (.cv u) C)) (.classEq (.cv u) C)
      (.classEq (syn_csn (.cv u)) (syn_csn C)) p0001 p0002
  have p0004 := @g_eceq1 (syn_csn (.cv u)) (syn_csn C) (syn_csi R)
  have p0005 :=
    @g_syl (syn_wa (.classMem C (syn_cvv)) (.classEq (.cv u) C))
      (.classEq (syn_csn (.cv u)) (syn_csn C))
      (.classEq (syn_cec (syn_csn (.cv u)) (syn_csi R)) (syn_cec (syn_csn C) (syn_csi R)))
      p0003 p0004
  have p0007 := @g_eceq1 (.cv u) C R
  have p0008 :=
    @g_syl (syn_wa (.classMem C (syn_cvv)) (.classEq (.cv u) C)) (.classEq (.cv u) C)
      (.classEq (syn_cec (.cv u) R) (syn_cec C R)) p0001 p0007
  have p0009 := @g_pw1eq (syn_cec (.cv u) R) (syn_cec C R)
  have p0010 :=
    @g_syl (syn_wa (.classMem C (syn_cvv)) (.classEq (.cv u) C))
      (.classEq (syn_cec (.cv u) R) (syn_cec C R))
      (.classEq (syn_cpw1 (syn_cec (.cv u) R)) (syn_cpw1 (syn_cec C R))) p0008 p0009
  have p0011 :=
    @g_eqeq12d (syn_wa (.classMem C (syn_cvv)) (.classEq (.cv u) C))
      (syn_cec (syn_csn (.cv u)) (syn_csi R)) (syn_cec (syn_csn C) (syn_csi R))
      (syn_cpw1 (syn_cec (.cv u) R)) (syn_cpw1 (syn_cec C R)) p0005 p0010
  have p0012 := @g_siecsnndv u R dv_cache_0001
  have p0013 :=
    @g_a1i
      (.classEq (syn_cec (syn_csn (.cv u)) (syn_csi R)) (syn_cpw1 (syn_cec (.cv u) R)))
      (.classMem C (syn_cvv)) p0012
  have p0014 :=
    @g_vtocld (.classMem C (syn_cvv))
      (.classEq (syn_cec (syn_csn (.cv u)) (syn_csi R)) (syn_cpw1 (syn_cec (.cv u) R)))
      (.classEq (syn_cec (syn_csn C) (syn_csi R)) (syn_cpw1 (syn_cec C R))) u C (syn_cvv)
      dv_cache_0002 dv_cache_0003 dv_cache_0004 p0000 p0011 p0013
  exact p0014

@[expose]
noncomputable def g_f1oclassimfreeclndv (v : Var) (A : Class) (B : Class) (Q : Class)
    (S : Class) (T : Class) (F : Class) (dv_A_v : v ∉ A.fv) (_dv_B_v : v ∉ B.fv)
    (dv_F_v : v ∉ F.fv) (dv_Q_v : v ∉ Q.fv) (dv_S_v : v ∉ S.fv) (dv_T_v : v ∉ T.fv)
    (hyp_f1oclassimfreeclndv_1 : Nominal.NPrf (syn_wf1o F A B))
    (hyp_f1oclassimfreeclndv_2 : Nominal.NPrf (syn_wss (syn_cec Q T) A))
    (hyp_f1oclassimfreeclndv_3 : Nominal.NPrf (syn_wss (syn_cec (syn_cfv F Q) S) B))
    (hyp_f1oclassimfreeclndv_4 : Nominal.NPrf (syn_wral v A
          (syn_wb (syn_wbr Q T (.cv v)) (syn_wbr (syn_cfv F Q) S (syn_cfv F (.cv v))))))
    (_hyp_f1oclassimfreeclndv_5 : Nominal.NPrf (.classMem Q A)) :
    Nominal.NPrf (.classEq (syn_cima F (syn_cec Q T)) (syn_cec (syn_cfv F Q) S)) :=
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
  have dv_cache_0001 : v ∉ ((syn_cfv (syn_ccnv F) (.cv z))).fv := by
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
      ((syn_wb (syn_wbr Q T (syn_cfv (syn_ccnv F) (.cv z)))
          (syn_wbr (syn_cfv F Q) S (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z)))))).fv :=
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
  have dv_cache_0004 : z ∉ ((syn_cima F (syn_cec Q T))).fv :=
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
  have dv_cache_0005 : z ∉ ((syn_cec (syn_cfv F Q) S)).fv :=
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
  have p0000 := @g_id (.classMem (.cv z) (syn_cima F (syn_cec Q T)))
  have p0001 := @g_imassrn F (syn_cec Q T)
  have p0002 := @g_f1of A B F
  have p0003 := Nominal.mp hyp_f1oclassimfreeclndv_1 p0002
  have p0004 := @g_frn A B F
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @g_pm3_2i (syn_wss (syn_cima F (syn_cec Q T)) (syn_crn F)) (syn_wss (syn_crn F) B)
      p0001 p0005
  have p0007 := @g_sstr (syn_cima F (syn_cec Q T)) (syn_crn F) B
  have p0008 := Nominal.mp p0006 p0007
  have p0009 := @g_sseli (syn_cima F (syn_cec Q T)) B (.cv z) p0008
  have p0010 := @g_a1i (syn_wf1o F A B) (.classMem (.cv z) B) hyp_f1oclassimfreeclndv_1
  have p0011 := @g_id (.classMem (.cv z) B)
  have p0012 :=
    @g_jca (.classMem (.cv z) B) (syn_wf1o F A B) (.classMem (.cv z) B) p0010 p0011
  have p0013 := @g_f1ocnvfv2 A B (.cv z) F
  have p0014 :=
    @g_syl (.classMem (.cv z) B) (syn_wa (syn_wf1o F A B) (.classMem (.cv z) B))
      (.classEq (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z))) (.cv z)) p0012 p0013
  have p0015 :=
    @g_eleq1d (.classMem (.cv z) B) (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z))) (.cv z)
      (syn_cima F (syn_cec Q T)) p0014
  have p0016 := @g_f1of1 A B F
  have p0017 := Nominal.mp hyp_f1oclassimfreeclndv_1 p0016
  have p0018 := @g_a1i (syn_wf1 F A B) (.classMem (.cv z) B) p0017
  have p0022 := @g_f1ocnvdm A B (.cv z) F
  have p0023 :=
    @g_syl (.classMem (.cv z) B) (syn_wa (syn_wf1o F A B) (.classMem (.cv z) B))
      (.classMem (syn_cfv (syn_ccnv F) (.cv z)) A) p0012 p0022
  have p0024 :=
    @g_a1i (syn_wss (syn_cec Q T) A) (.classMem (.cv z) B) hyp_f1oclassimfreeclndv_2
  have p0025 :=
    @g_n_3jca (.classMem (.cv z) B) (syn_wf1 F A B)
      (.classMem (syn_cfv (syn_ccnv F) (.cv z)) A) (syn_wss (syn_cec Q T) A) p0018 p0023
      p0024
  have p0026 := @g_f1elima A B F (syn_cfv (syn_ccnv F) (.cv z)) (syn_cec Q T)
  have p0027 :=
    @g_syl (.classMem (.cv z) B)
      (syn_w3a (syn_wf1 F A B) (.classMem (syn_cfv (syn_ccnv F) (.cv z)) A)
        (syn_wss (syn_cec Q T) A))
      (syn_wb (.classMem (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z))) (syn_cima F (syn_cec Q T)))
        (.classMem (syn_cfv (syn_ccnv F) (.cv z)) (syn_cec Q T)))
      p0025 p0026
  have p0028 :=
    @g_bitr3d (.classMem (.cv z) B)
      (.classMem (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z))) (syn_cima F (syn_cec Q T)))
      (.classMem (.cv z) (syn_cima F (syn_cec Q T)))
      (.classMem (syn_cfv (syn_ccnv F) (.cv z)) (syn_cec Q T)) p0015 p0027
  have p0029 := @g_elec (syn_cfv (syn_ccnv F) (.cv z)) Q T
  have p0030 :=
    @g_a1i
      (syn_wb (.classMem (syn_cfv (syn_ccnv F) (.cv z)) (syn_cec Q T))
        (syn_wbr Q T (syn_cfv (syn_ccnv F) (.cv z))))
      (.classMem (.cv z) B) p0029
  have p0031 :=
    @g_bitrd (.classMem (.cv z) B) (.classMem (.cv z) (syn_cima F (syn_cec Q T)))
      (.classMem (syn_cfv (syn_ccnv F) (.cv z)) (syn_cec Q T))
      (syn_wbr Q T (syn_cfv (syn_ccnv F) (.cv z))) p0028 p0030
  have p0032 :=
    @g_a1i
      (syn_wral v A
        (syn_wb (syn_wbr Q T (.cv v)) (syn_wbr (syn_cfv F Q) S (syn_cfv F (.cv v)))))
      (.classMem (.cv z) B) hyp_f1oclassimfreeclndv_4
  have p0038 :=
    @g_jca (.classMem (.cv z) B)
      (syn_wral v A
        (syn_wb (syn_wbr Q T (.cv v)) (syn_wbr (syn_cfv F Q) S (syn_cfv F (.cv v)))))
      (.classMem (syn_cfv (syn_ccnv F) (.cv z)) A) p0032 p0023
  have p0039 := @g_id (.classEq (.cv v) (syn_cfv (syn_ccnv F) (.cv z)))
  have p0040 :=
    @g_breq2d (.classEq (.cv v) (syn_cfv (syn_ccnv F) (.cv z))) (.cv v)
      (syn_cfv (syn_ccnv F) (.cv z)) Q T p0039
  have p0042 :=
    @g_fveq2d (.classEq (.cv v) (syn_cfv (syn_ccnv F) (.cv z))) (.cv v)
      (syn_cfv (syn_ccnv F) (.cv z)) F p0039
  have p0043 :=
    @g_breq2d (.classEq (.cv v) (syn_cfv (syn_ccnv F) (.cv z))) (syn_cfv F (.cv v))
      (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z))) (syn_cfv F Q) S p0042
  have p0044 :=
    @g_bibi12d (.classEq (.cv v) (syn_cfv (syn_ccnv F) (.cv z))) (syn_wbr Q T (.cv v))
      (syn_wbr Q T (syn_cfv (syn_ccnv F) (.cv z)))
      (syn_wbr (syn_cfv F Q) S (syn_cfv F (.cv v)))
      (syn_wbr (syn_cfv F Q) S (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z)))) p0040 p0043
  have p0045 :=
    @g_rspccva
      (syn_wb (syn_wbr Q T (.cv v)) (syn_wbr (syn_cfv F Q) S (syn_cfv F (.cv v))))
      (syn_wb (syn_wbr Q T (syn_cfv (syn_ccnv F) (.cv z)))
        (syn_wbr (syn_cfv F Q) S (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z)))))
      v (syn_cfv (syn_ccnv F) (.cv z)) A dv_cache_0001 dv_cache_0002 dv_cache_0003 p0044
  have p0046 :=
    @g_syl (.classMem (.cv z) B)
      (syn_wa (syn_wral v A
          (syn_wb (syn_wbr Q T (.cv v)) (syn_wbr (syn_cfv F Q) S (syn_cfv F (.cv v)))))
        (.classMem (syn_cfv (syn_ccnv F) (.cv z)) A))
      (syn_wb (syn_wbr Q T (syn_cfv (syn_ccnv F) (.cv z)))
        (syn_wbr (syn_cfv F Q) S (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z)))))
      p0038 p0045
  have p0047 :=
    @g_bitrd (.classMem (.cv z) B) (.classMem (.cv z) (syn_cima F (syn_cec Q T)))
      (syn_wbr Q T (syn_cfv (syn_ccnv F) (.cv z)))
      (syn_wbr (syn_cfv F Q) S (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z)))) p0031 p0046
  have p0053 :=
    @g_breq2d (.classMem (.cv z) B) (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z))) (.cv z)
      (syn_cfv F Q) S p0014
  have p0054 :=
    @g_bitrd (.classMem (.cv z) B) (.classMem (.cv z) (syn_cima F (syn_cec Q T)))
      (syn_wbr (syn_cfv F Q) S (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z))))
      (syn_wbr (syn_cfv F Q) S (.cv z)) p0047 p0053
  have p0055 := @g_elec (.cv z) (syn_cfv F Q) S
  have p0056 :=
    @g_a1i
      (syn_wb (.classMem (.cv z) (syn_cec (syn_cfv F Q) S)) (syn_wbr (syn_cfv F Q) S (.cv z)))
      (.classMem (.cv z) B) p0055
  have p0057 :=
    @g_bicomd (.classMem (.cv z) B) (.classMem (.cv z) (syn_cec (syn_cfv F Q) S))
      (syn_wbr (syn_cfv F Q) S (.cv z)) p0056
  have p0058 :=
    @g_bitrd (.classMem (.cv z) B) (.classMem (.cv z) (syn_cima F (syn_cec Q T)))
      (syn_wbr (syn_cfv F Q) S (.cv z)) (.classMem (.cv z) (syn_cec (syn_cfv F Q) S))
      p0054 p0057
  have p0059 :=
    @g_syl (.classMem (.cv z) (syn_cima F (syn_cec Q T))) (.classMem (.cv z) B)
      (syn_wb (.classMem (.cv z) (syn_cima F (syn_cec Q T)))
        (.classMem (.cv z) (syn_cec (syn_cfv F Q) S)))
      p0009 p0058
  have p0060 :=
    @g_mpbid (.classMem (.cv z) (syn_cima F (syn_cec Q T)))
      (.classMem (.cv z) (syn_cima F (syn_cec Q T)))
      (.classMem (.cv z) (syn_cec (syn_cfv F Q) S)) p0000 p0059
  have p0061 := @g_id (.classMem (.cv z) (syn_cec (syn_cfv F Q) S))
  have p0062 := @g_sseli (syn_cec (syn_cfv F Q) S) B (.cv z) hyp_f1oclassimfreeclndv_3
  have p0112 :=
    @g_syl (.classMem (.cv z) (syn_cec (syn_cfv F Q) S)) (.classMem (.cv z) B)
      (syn_wb (.classMem (.cv z) (syn_cima F (syn_cec Q T)))
        (.classMem (.cv z) (syn_cec (syn_cfv F Q) S)))
      p0062 p0058
  have p0113 :=
    @g_mpbird (.classMem (.cv z) (syn_cec (syn_cfv F Q) S))
      (.classMem (.cv z) (syn_cima F (syn_cec Q T)))
      (.classMem (.cv z) (syn_cec (syn_cfv F Q) S)) p0061 p0112
  have p0114 :=
    @g_impbii (.classMem (.cv z) (syn_cima F (syn_cec Q T)))
      (.classMem (.cv z) (syn_cec (syn_cfv F Q) S)) p0060 p0113
  have p0115 :=
    @g_eqriv z (syn_cima F (syn_cec Q T)) (syn_cec (syn_cfv F Q) S) dv_cache_0004
      dv_cache_0005 p0114
  exact p0115

@[expose]
noncomputable def g_hnsicodemapkernelclndv (A : Class) (Q : Class) (r : Var)
    (dv_A_r : r ∉ A.fv) (_dv_Q_r : r ∉ Q.fv) :
    Nominal.NPrf
      (.imp (.classMem Q (syn_cpw1 (syn_chwcn A)))
        (.imp (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
          (syn_wb (syn_wbr Q (syn_csi (syn_chwniso A)) (.cv r))
            (syn_wbr (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A))
              (syn_cfv (syn_chnsicodemap A) (.cv r)))))) :=
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
  have dv_cache_0005 : q ∉ ((syn_cpw1 (syn_chwcn A))).fv :=
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
      ((Wff.imp (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
          (syn_wb (syn_wbr Q (syn_csi (syn_chwniso A)) (.cv r))
            (syn_wbr (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A))
              (syn_cfv (syn_chnsicodemap A) (.cv r)))))).fv :=
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
  have p0000 := @g_biid (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
  have p0001 :=
    @g_a1i
      (syn_wb (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (.classEq (.cv q) Q) p0000
  have p0002 := @g_id (.classEq (.cv q) Q)
  have p0003 :=
    @g_breq1d (.classEq (.cv q) Q) (.cv q) Q (.cv r) (syn_csi (syn_chwniso A)) p0002
  have p0005 := @g_fveq2d (.classEq (.cv q) Q) (.cv q) Q (syn_chnsicodemap A) p0002
  have p0006 :=
    @g_breq1d (.classEq (.cv q) Q) (syn_cfv (syn_chnsicodemap A) (.cv q))
      (syn_cfv (syn_chnsicodemap A) Q) (syn_cfv (syn_chnsicodemap A) (.cv r))
      (syn_chwniso (syn_cpw1 A)) p0005
  have p0007 :=
    @g_bibi12d (.classEq (.cv q) Q) (syn_wbr (.cv q) (syn_csi (syn_chwniso A)) (.cv r))
      (syn_wbr Q (syn_csi (syn_chwniso A)) (.cv r))
      (syn_wbr (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwniso (syn_cpw1 A))
        (syn_cfv (syn_chnsicodemap A) (.cv r)))
      (syn_wbr (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A))
        (syn_cfv (syn_chnsicodemap A) (.cv r)))
      p0003 p0006
  have p0008 :=
    @g_imbi12d (.classEq (.cv q) Q) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
      (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
      (syn_wb (syn_wbr (.cv q) (syn_csi (syn_chwniso A)) (.cv r))
        (syn_wbr (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwniso (syn_cpw1 A))
          (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (syn_wb (syn_wbr Q (syn_csi (syn_chwniso A)) (.cv r))
        (syn_wbr (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A))
          (syn_cfv (syn_chnsicodemap A) (.cv r))))
      p0001 p0007
  have p0009 := @g_hnsicodemapkernelndv A r q dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0010 :=
    @g_ex (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
      (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
      (syn_wb (syn_wbr (.cv q) (syn_csi (syn_chwniso A)) (.cv r))
        (syn_wbr (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwniso (syn_cpw1 A))
          (syn_cfv (syn_chnsicodemap A) (.cv r))))
      p0009
  have p0011 :=
    @g_vtoclga
      (.imp (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
        (syn_wb (syn_wbr (.cv q) (syn_csi (syn_chwniso A)) (.cv r))
          (syn_wbr (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwniso (syn_cpw1 A))
            (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      (.imp (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
        (syn_wb (syn_wbr Q (syn_csi (syn_chwniso A)) (.cv r))
          (syn_wbr (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A))
            (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      q Q (syn_cpw1 (syn_chwcn A)) dv_cache_0004 dv_cache_0005 dv_cache_0006 p0008 p0010
  exact p0011

@[expose]
noncomputable def g_hnsicodemapclassimclndv (A : Class) (Q : Class)
    (hyp_hnsicodemapclassimclndv_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_hnsicodemapclassimclndv_2 : Nominal.NPrf (.classMem Q (syn_cpw1 (syn_chwcn A)))) :
    Nominal.NPrf
      (.classEq (syn_cima (syn_chnsicodemap A) (syn_cec Q (syn_csi (syn_chwniso A))))
        (syn_cec (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A)))) :=
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
  have dv_cache_0003 : r ∉ ((syn_cpw1 (syn_chwcn A))).fv :=
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
  have dv_cache_0004 : r ∉ ((syn_chwcn (syn_cpw1 A))).fv :=
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
  have dv_cache_0005 : r ∉ ((syn_chnsicodemap A)).fv :=
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
  have dv_cache_0006 : r ∉ ((syn_chwniso (syn_cpw1 A))).fv :=
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
  have dv_cache_0007 : r ∉ ((syn_csi (syn_chwniso A))).fv :=
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
  have p0000 := @g_hnsicodemapf1ondv A
  have p0001 := @g_pw1argclcl (syn_chwcn A) Q
  have p0002 := Nominal.mp hyp_hnsicodemapclassimclndv_2 p0001
  have p0003 :=
    @g_simpr (.classMem (syn_cuni Q) (syn_chwcn A)) (.classEq Q (syn_csn (syn_cuni Q)))
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := @g_eceq1 Q (syn_csn (syn_cuni Q)) (syn_csi (syn_chwniso A))
  have p0006 := Nominal.mp p0004 p0005
  have p0009 :=
    @g_simpl (.classMem (syn_cuni Q) (syn_chwcn A)) (.classEq Q (syn_csn (syn_cuni Q)))
  have p0010 := Nominal.mp p0002 p0009
  have p0011 := @g_elex (syn_cuni Q) (syn_chwcn A)
  have p0012 := Nominal.mp p0010 p0011
  have p0013 := @g_siecsnclndv (syn_cuni Q) (syn_chwniso A)
  have p0014 := Nominal.mp p0012 p0013
  have p0015 :=
    @g_eqtri (syn_cec Q (syn_csi (syn_chwniso A)))
      (syn_cec (syn_csn (syn_cuni Q)) (syn_csi (syn_chwniso A)))
      (syn_cpw1 (syn_cec (syn_cuni Q) (syn_chwniso A))) p0006 p0014
  have p0016 := @g_hwnisoerv A
  have p0017 := @g_hwnisodm A
  have p0018 :=
    @g_a1i (.classEq (syn_cdm (syn_chwniso A)) (syn_chwcn A)) (.classMem A (syn_cvv))
      p0017
  have p0019 :=
    @g_ecss (.classMem A (syn_cvv)) (syn_cuni Q) (syn_chwniso A) (syn_chwcn A) p0016 p0018
  have p0020 := Nominal.mp hyp_hnsicodemapclassimclndv_1 p0019
  have p0021 := @g_pw1ss (syn_cec (syn_cuni Q) (syn_chwniso A)) (syn_chwcn A)
  have p0022 := Nominal.mp p0020 p0021
  have p0023 :=
    @g_eqsstri (syn_cec Q (syn_csi (syn_chwniso A)))
      (syn_cpw1 (syn_cec (syn_cuni Q) (syn_chwniso A))) (syn_cpw1 (syn_chwcn A)) p0015
      p0022
  have p0024 := @g_pw1exg A (syn_cvv)
  have p0025 := Nominal.mp hyp_hnsicodemapclassimclndv_1 p0024
  have p0026 := @g_hwnisoerv (syn_cpw1 A)
  have p0027 := @g_hwnisodm (syn_cpw1 A)
  have p0028 :=
    @g_a1i (.classEq (syn_cdm (syn_chwniso (syn_cpw1 A))) (syn_chwcn (syn_cpw1 A)))
      (.classMem (syn_cpw1 A) (syn_cvv)) p0027
  have p0029 :=
    @g_ecss (.classMem (syn_cpw1 A) (syn_cvv)) (syn_cfv (syn_chnsicodemap A) Q)
      (syn_chwniso (syn_cpw1 A)) (syn_chwcn (syn_cpw1 A)) p0026 p0028
  have p0030 := Nominal.mp p0025 p0029
  have p0031 := @g_hnsicodemapkernelclndv A Q r dv_cache_0001 dv_cache_0002
  have p0032 := Nominal.mp hyp_hnsicodemapclassimclndv_2 p0031
  have p0033 :=
    @g_rgen
      (syn_wb (syn_wbr Q (syn_csi (syn_chwniso A)) (.cv r))
        (syn_wbr (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A))
          (syn_cfv (syn_chnsicodemap A) (.cv r))))
      r (syn_cpw1 (syn_chwcn A)) p0032
  have p0034 :=
    @g_f1oclassimfreeclndv r (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)) Q
      (syn_chwniso (syn_cpw1 A)) (syn_csi (syn_chwniso A)) (syn_chnsicodemap A)
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

@[expose]
noncomputable def g_hnsicodemapclassimdndv (A : Class) (q : Var) (_dv_A_q : q ∉ A.fv)
    (hyp_hnsicodemapclassimdndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classEq
          (syn_cima (syn_chnsicodemap A) (syn_cec (.cv q) (syn_csi (syn_chwniso A))))
          (syn_cec (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwniso (syn_cpw1 A))))) :=
  by
  have dv_cache_0001 :
    Disjoint (A).fv
      ((syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))).fv :=
    by
    exact
      (show Disjoint (A).fv ((syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))).fv
        from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
          exact
            (show
              Disjoint ((A).fv)
                ((((syn_ckqrel (syn_clefin))).fv) ∪ (((syn_cxp (syn_c0) (syn_c0))).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint ((A).fv) (((syn_ckqrel (syn_clefin))).fv) from
                    (by
                      rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel];
                      exact
                        (show Disjoint ((A).fv) (((syn_clefin)).fv) from
                          (by
                            rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin];
                            exact
                              (show Disjoint ((A).fv) ((∅ : Finset Var)) from
                                (by simp)))))),
                  (show Disjoint ((A).fv) (((syn_cxp (syn_c0) (syn_c0))).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp];
                      exact
                        (show Disjoint ((A).fv) ((((syn_c0)).fv) ∪ (((syn_c0)).fv)) from
                          (Finset.disjoint_union_right.mpr
                            ⟨(show Disjoint ((A).fv) (((syn_c0)).fv) from
                                (by
                                  rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
                                  exact
                                    (show Disjoint ((A).fv) ((∅ : Finset Var)) from
                                      (by simp)))),
                              (show Disjoint ((A).fv) (((syn_c0)).fv) from
                                (by
                                  rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
                                  exact
                                    (show Disjoint ((A).fv) ((∅ : Finset Var)) from
                                      (by simp))))⟩))))⟩))))
  have p0000 :=
    @g_eceq1 (.cv q)
      (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_csi (syn_chwniso A))
  have p0001 :=
    @g_imaeq2d
      (.classEq (.cv q) (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (syn_cec (.cv q) (syn_csi (syn_chwniso A)))
      (syn_cec (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_csi (syn_chwniso A)))
      (syn_chnsicodemap A) p0000
  have p0002 :=
    @g_id
      (.classEq (.cv q) (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
  have p0003 :=
    @g_fveq2d
      (.classEq (.cv q) (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (.cv q)
      (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_chnsicodemap A) p0002
  have p0004 :=
    @g_eceq1 (syn_cfv (syn_chnsicodemap A) (.cv q))
      (syn_cfv (syn_chnsicodemap A)
        (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (syn_chwniso (syn_cpw1 A))
  have p0005 :=
    @g_syl
      (.classEq (.cv q) (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A)
          (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))))))
      (.classEq (syn_cec (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwniso (syn_cpw1 A)))
        (syn_cec (syn_cfv (syn_chnsicodemap A)
            (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0))))) (syn_chwniso (syn_cpw1 A))))
      p0003 p0004
  have p0006 :=
    @g_eqeq12d
      (.classEq (.cv q) (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (syn_cima (syn_chnsicodemap A) (syn_cec (.cv q) (syn_csi (syn_chwniso A))))
      (syn_cima (syn_chnsicodemap A) (syn_cec
          (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_csi (syn_chwniso A))))
      (syn_cec (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwniso (syn_cpw1 A)))
      (syn_cec (syn_cfv (syn_chnsicodemap A)
          (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))))) (syn_chwniso (syn_cpw1 A)))
      p0001 p0005
  have p0007 := @g_eqid (syn_c0)
  have p0008 :=
    @g_simpr (.classEq (syn_c0) (syn_c0)) (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
  have p0009 := @g_wecomparisondefaultemptywe
  have p0010 := @g_n_0ss A
  have p0011 :=
    @g_pm3_2i
      (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe)
        (syn_c0))
      (syn_wss (syn_c0) A) p0009 p0010
  have p0013 :=
    @g_brex (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)
      (syn_cwe)
  have p0014 := Nominal.mp p0009 p0013
  have p0015 :=
    @g_simpl
      (.classMem (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cvv))
      (.classMem (syn_c0) (syn_cvv))
  have p0016 := Nominal.mp p0014 p0015
  have p0017 := @g_n_0ex
  have p0018 :=
    @g_elhwcodes A (syn_c0)
      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) dv_cache_0001 p0016
      p0017
  have p0019 :=
    @g_mpbir
      (.classMem
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
        (syn_chwcodes A))
      (syn_wa (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe)
          (syn_c0)) (syn_wss (syn_c0) A))
      p0011 p0018
  have p0020 := @g_inss2 (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))
  have p0027 :=
    @g_opfv1st (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)
      p0016 p0017
  have p0034 :=
    @g_opfv2nd (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)
      p0016 p0017
  have p0042 :=
    @g_xpeq12i
      (syn_cfv (syn_c2nd)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
      (syn_c0)
      (syn_cfv (syn_c2nd)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
      (syn_c0) p0034 p0034
  have p0043 :=
    @g_sseq12i
      (syn_cfv (syn_c1st)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
      (syn_cxp (syn_cfv (syn_c2nd)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_cfv (syn_c2nd)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cxp (syn_c0) (syn_c0)) p0027 p0042
  have p0044 :=
    @g_mpbir
      (syn_wss (syn_cfv (syn_c1st)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_cxp (syn_cfv (syn_c2nd)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_cfv (syn_c2nd)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (syn_wss (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
        (syn_cxp (syn_c0) (syn_c0)))
      p0020 p0043
  have p0045 :=
    @g_pm3_2i
      (.classMem
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
        (syn_chwcodes A))
      (syn_wss (syn_cfv (syn_c1st)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_cxp (syn_cfv (syn_c2nd)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_cfv (syn_c2nd)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      p0019 p0044
  have p0052 :=
    @g_opex (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0) p0016
      p0017
  have p0053 :=
    @g_elhwcncl A
      (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
  have p0054 := Nominal.mp p0052 p0053
  have p0055 :=
    @g_mpbir
      (.classMem
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
        (syn_chwcn A))
      (syn_wa (.classMem
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
          (syn_chwcodes A)) (syn_wss (syn_cfv (syn_c1st)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_cxp (syn_cfv (syn_c2nd)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))) (syn_cfv (syn_c2nd)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))))))
      p0045 p0054
  have p0056 :=
    @g_snelpw1
      (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
      (syn_chwcn A)
  have p0057 :=
    @g_mpbir
      (.classMem (syn_csn
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_cpw1 (syn_chwcn A)))
      (.classMem
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
        (syn_chwcn A))
      p0055 p0056
  have p0058 :=
    @g_a1i
      (.classMem (syn_csn
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_cpw1 (syn_chwcn A)))
      (syn_wa (.classEq (syn_c0) (syn_c0)) (.neg (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))))
      p0057
  have p0059 :=
    @g_ifclda (.classEq (syn_c0) (syn_c0)) (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
      (.cv q)
      (syn_csn (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
          (syn_c0)))
      (syn_cpw1 (syn_chwcn A)) p0008 p0058
  have p0060 := Nominal.mp p0007 p0059
  have p0061 :=
    @g_hnsicodemapclassimclndv A
      (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      hyp_hnsicodemapclassimdndv_1 p0060
  have p0062 :=
    @g_dedth (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
      (.classEq (syn_cima (syn_chnsicodemap A) (syn_cec (.cv q) (syn_csi (syn_chwniso A))))
        (syn_cec (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwniso (syn_cpw1 A))))
      (.classEq (syn_cima (syn_chnsicodemap A) (syn_cec
            (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_csi (syn_chwniso A)))) (syn_cec (syn_cfv (syn_chnsicodemap A)
            (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0))))) (syn_chwniso (syn_cpw1 A))))
      (.cv q)
      (syn_csn (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
          (syn_c0)))
      p0006 p0061
  exact p0062

@[expose]
noncomputable def g_hnsicodemapclassimcldndv (A : Class) (Q : Class)
    (hyp_hnsicodemapclassimcldndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem Q (syn_cpw1 (syn_chwcn A)))
        (.classEq (syn_cima (syn_chnsicodemap A) (syn_cec Q (syn_csi (syn_chwniso A))))
          (syn_cec (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A))))) :=
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
  have dv_cache_0003 : q ∉ ((syn_cpw1 (syn_chwcn A))).fv :=
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
      ((Wff.classEq (syn_cima (syn_chnsicodemap A) (syn_cec Q (syn_csi (syn_chwniso A))))
          (syn_cec (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A))))).fv :=
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
  have p0000 := @g_eceq1 (.cv q) Q (syn_csi (syn_chwniso A))
  have p0001 :=
    @g_imaeq2d (.classEq (.cv q) Q) (syn_cec (.cv q) (syn_csi (syn_chwniso A)))
      (syn_cec Q (syn_csi (syn_chwniso A))) (syn_chnsicodemap A) p0000
  have p0002 := @g_id (.classEq (.cv q) Q)
  have p0003 := @g_fveq2d (.classEq (.cv q) Q) (.cv q) Q (syn_chnsicodemap A) p0002
  have p0004 :=
    @g_eceq1 (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) Q)
      (syn_chwniso (syn_cpw1 A))
  have p0005 :=
    @g_syl (.classEq (.cv q) Q)
      (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) Q))
      (.classEq (syn_cec (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwniso (syn_cpw1 A)))
        (syn_cec (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A))))
      p0003 p0004
  have p0006 :=
    @g_eqeq12d (.classEq (.cv q) Q)
      (syn_cima (syn_chnsicodemap A) (syn_cec (.cv q) (syn_csi (syn_chwniso A))))
      (syn_cima (syn_chnsicodemap A) (syn_cec Q (syn_csi (syn_chwniso A))))
      (syn_cec (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwniso (syn_cpw1 A)))
      (syn_cec (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A))) p0001 p0005
  have p0007 := @g_hnsicodemapclassimdndv A q dv_cache_0001 hyp_hnsicodemapclassimcldndv_1
  have p0008 :=
    @g_vtoclga
      (.classEq (syn_cima (syn_chnsicodemap A) (syn_cec (.cv q) (syn_csi (syn_chwniso A))))
        (syn_cec (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwniso (syn_cpw1 A))))
      (.classEq (syn_cima (syn_chnsicodemap A) (syn_cec Q (syn_csi (syn_chwniso A))))
        (syn_cec (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A))))
      q Q (syn_cpw1 (syn_chwcn A)) dv_cache_0002 dv_cache_0003 dv_cache_0004 p0006 p0007
  exact p0008

@[expose]
noncomputable def g_elhnordclndv (u : Var) (A : Class) (X : Class) (dv_A_u : u ∉ A.fv)
    (dv_X_u : u ∉ X.fv) :
    Nominal.NPrf
      (.imp (.classMem X (syn_cvv)) (syn_wb (.classMem X (syn_chnord A))
          (syn_wrex u (syn_chwcn A) (.classEq X (syn_cec (.cv u) (syn_chwniso A)))))) :=
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
      ((syn_wb (.classMem X (syn_chnord A)) (syn_wrex u (syn_chwcn A)
            (.classEq X (syn_cec (.cv u) (syn_chwniso A)))))).fv :=
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
  have dv_cache_0007 : x ∉ ((Wff.classMem X (syn_cvv))).fv :=
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
  have p0000 := @g_id (.classMem X (syn_cvv))
  have p0001 := @g_simpr (.classMem X (syn_cvv)) (.classEq (.cv x) X)
  have p0002 := @g_eleq1 (.cv x) X (syn_chnord A)
  have p0003 := @g_id (.classEq (.cv x) X)
  have p0004 :=
    @g_eqeq1d (.classEq (.cv x) X) (.cv x) X (syn_cec (.cv u) (syn_chwniso A)) p0003
  have p0005 :=
    @g_rexbidv (.classEq (.cv x) X) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso A)))
      (.classEq X (syn_cec (.cv u) (syn_chwniso A))) u (syn_chwcn A) dv_cache_0001 p0004
  have p0006 :=
    @g_bibi12d (.classEq (.cv x) X) (.classMem (.cv x) (syn_chnord A))
      (.classMem X (syn_chnord A))
      (syn_wrex u (syn_chwcn A) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso A))))
      (syn_wrex u (syn_chwcn A) (.classEq X (syn_cec (.cv u) (syn_chwniso A)))) p0002
      p0005
  have p0007 :=
    @g_syl (syn_wa (.classMem X (syn_cvv)) (.classEq (.cv x) X)) (.classEq (.cv x) X)
      (syn_wb (syn_wb (.classMem (.cv x) (syn_chnord A))
          (syn_wrex u (syn_chwcn A) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso A)))))
        (syn_wb (.classMem X (syn_chnord A))
          (syn_wrex u (syn_chwcn A) (.classEq X (syn_cec (.cv u) (syn_chwniso A))))))
      p0001 p0006
  have p0008 := @g_vex x
  have p0009 := @g_elhnord x u A dv_cache_0002 dv_cache_0003 dv_cache_0004 p0008
  have p0010 :=
    @g_a1i
      (syn_wb (.classMem (.cv x) (syn_chnord A))
        (syn_wrex u (syn_chwcn A) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso A)))))
      (.classMem X (syn_cvv)) p0009
  have p0011 :=
    @g_vtocld (.classMem X (syn_cvv))
      (syn_wb (.classMem (.cv x) (syn_chnord A))
        (syn_wrex u (syn_chwcn A) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso A)))))
      (syn_wb (.classMem X (syn_chnord A))
        (syn_wrex u (syn_chwcn A) (.classEq X (syn_cec (.cv u) (syn_chwniso A)))))
      x X (syn_cvv) dv_cache_0005 dv_cache_0006 dv_cache_0007 p0000 p0007 p0010
  exact p0011

@[expose]
noncomputable def g_hnsiquomapfvhnordndv (A : Class) (q : Var) (dv_A_q : q ∉ A.fv)
    (hyp_hnsiquomapfvhnordndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (.classMem (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_chnord (syn_cpw1 A)))) :=
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
  have dv_cache_0002 : u ∉ ((syn_cuni (.cv q))).fv :=
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
  have dv_cache_0004 : u ∉ ((syn_chwniso A)).fv :=
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
      ((Wff.classMem (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_chnord (syn_cpw1 A)))).fv :=
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
  have dv_cache_0006 : u ∉ ((Wff.classMem (.cv q) (syn_cpw1 (syn_chnord A)))).fv :=
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
  have p0000 := @g_pw1argclcl (syn_chnord A) (.cv q)
  have p0001 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) (syn_chnord A))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0002 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (syn_wa (.classMem (syn_cuni (.cv q)) (syn_chnord A))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      (.classMem (syn_cuni (.cv q)) (syn_chnord A)) p0000 p0001
  have p0006 := @g_elex (syn_cuni (.cv q)) (syn_chnord A)
  have p0007 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (.classMem (syn_cuni (.cv q)) (syn_chnord A))
      (.classMem (syn_cuni (.cv q)) (syn_cvv)) p0002 p0006
  have p0008 := @g_elhnordclndv u A (syn_cuni (.cv q)) dv_cache_0001 dv_cache_0002
  have p0009 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (.classMem (syn_cuni (.cv q)) (syn_cvv))
      (syn_wb (.classMem (syn_cuni (.cv q)) (syn_chnord A)) (syn_wrex u (syn_chwcn A)
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      p0007 p0008
  have p0010 :=
    @g_mpbid (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (.classMem (syn_cuni (.cv q)) (syn_chnord A))
      (syn_wrex u (syn_chwcn A) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
      p0002 p0009
  have p0011 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
  have p0012 := @g_hnsiquomapvalndv A q dv_cache_0003 hyp_hnsiquomapfvhnordndv_1
  have p0013 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q))
        (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cuni (.cv q)))))
      p0011 p0012
  have p0014 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
  have p0015 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A))
      (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))
  have p0016 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
      (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))) p0014 p0015
  have p0017 := @g_pw1eq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))
  have p0018 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))
      (.classEq (syn_cpw1 (syn_cuni (.cv q))) (syn_cpw1 (syn_cec (.cv u) (syn_chwniso A))))
      p0016 p0017
  have p0019 := @g_siecsnndv u (syn_chwniso A) dv_cache_0004
  have p0020 :=
    @g_eqcomi (syn_cec (syn_csn (.cv u)) (syn_csi (syn_chwniso A)))
      (syn_cpw1 (syn_cec (.cv u) (syn_chwniso A))) p0019
  have p0021 :=
    @g_a1i
      (.classEq (syn_cpw1 (syn_cec (.cv u) (syn_chwniso A)))
        (syn_cec (syn_csn (.cv u)) (syn_csi (syn_chwniso A))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      p0020
  have p0022 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (syn_cpw1 (syn_cuni (.cv q))) (syn_cpw1 (syn_cec (.cv u) (syn_chwniso A)))
      (syn_cec (syn_csn (.cv u)) (syn_csi (syn_chwniso A))) p0018 p0021
  have p0023 :=
    @g_imaeq2d
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (syn_cpw1 (syn_cuni (.cv q))) (syn_cec (syn_csn (.cv u)) (syn_csi (syn_chwniso A)))
      (syn_chnsicodemap A) p0022
  have p0024 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (syn_cfv (syn_chnsiquomap A) (.cv q))
      (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cuni (.cv q))))
      (syn_cima (syn_chnsicodemap A) (syn_cec (syn_csn (.cv u)) (syn_csi (syn_chwniso A))))
      p0013 p0023
  have p0026 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A))
      (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))
  have p0027 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
      (.classMem (.cv u) (syn_chwcn A)) p0014 p0026
  have p0028 := @g_snelpw1 (.cv u) (syn_chwcn A)
  have p0029 :=
    @g_sylibr
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (.classMem (.cv u) (syn_chwcn A))
      (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A))) p0027 p0028
  have p0030 := @g_hnsicodemapclassimcldndv A (syn_csn (.cv u)) hyp_hnsiquomapfvhnordndv_1
  have p0031 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A)))
      (.classEq (syn_cima (syn_chnsicodemap A)
          (syn_cec (syn_csn (.cv u)) (syn_csi (syn_chwniso A))))
        (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A))))
      p0029 p0030
  have p0032 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (syn_cfv (syn_chnsiquomap A) (.cv q))
      (syn_cima (syn_chnsicodemap A) (syn_cec (syn_csn (.cv u)) (syn_csi (syn_chwniso A))))
      (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A)))
      p0024 p0031
  have p0038 := @g_hnsicodemapfndv A
  have p0039 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)) (syn_csn (.cv u))
      (syn_chnsicodemap A) p0038
  have p0040 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A)))
      (.classMem (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwcn (syn_cpw1 A)))
      p0029 p0039
  have p0041 := @g_pw1exg A (syn_cvv)
  have p0042 := Nominal.mp hyp_hnsiquomapfvhnordndv_1 p0041
  have p0043 :=
    @g_hwnisoclasselhnordcl (syn_cpw1 A) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u)))
      p0042
  have p0044 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (.classMem (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwcn (syn_cpw1 A)))
      (.classMem (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u)))
          (syn_chwniso (syn_cpw1 A))) (syn_chnord (syn_cpw1 A)))
      p0040 p0043
  have p0045 :=
    @g_eqeltrd
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (syn_cfv (syn_chnsiquomap A) (.cv q))
      (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A)))
      (syn_chnord (syn_cpw1 A)) p0032 p0044
  have p0046 :=
    @g_rexlimddv (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))
      (.classMem (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_chnord (syn_cpw1 A))) u
      (syn_chwcn A) dv_cache_0005 dv_cache_0006 p0010 p0045
  exact p0046

@[expose]
noncomputable def g_hnsiquomapvalclndv (A : Class) (Q : Class)
    (hyp_hnsiquomapvalclndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem Q (syn_cpw1 (syn_chnord A))) (.classEq (syn_cfv (syn_chnsiquomap A) Q)
          (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cuni Q))))) :=
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
  have dv_cache_0003 : q ∉ ((syn_cpw1 (syn_chnord A))).fv :=
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
      ((Wff.classEq (syn_cfv (syn_chnsiquomap A) Q)
          (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cuni Q))))).fv :=
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
  have p0000 := @g_id (.classEq (.cv q) Q)
  have p0001 := @g_fveq2d (.classEq (.cv q) Q) (.cv q) Q (syn_chnsiquomap A) p0000
  have p0003 := @g_unieqd (.classEq (.cv q) Q) (.cv q) Q p0000
  have p0004 := @g_pw1eq (syn_cuni (.cv q)) (syn_cuni Q)
  have p0005 :=
    @g_syl (.classEq (.cv q) Q) (.classEq (syn_cuni (.cv q)) (syn_cuni Q))
      (.classEq (syn_cpw1 (syn_cuni (.cv q))) (syn_cpw1 (syn_cuni Q))) p0003 p0004
  have p0006 :=
    @g_imaeq2d (.classEq (.cv q) Q) (syn_cpw1 (syn_cuni (.cv q))) (syn_cpw1 (syn_cuni Q))
      (syn_chnsicodemap A) p0005
  have p0007 :=
    @g_eqeq12d (.classEq (.cv q) Q) (syn_cfv (syn_chnsiquomap A) (.cv q))
      (syn_cfv (syn_chnsiquomap A) Q)
      (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cuni (.cv q))))
      (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cuni Q))) p0001 p0006
  have p0008 := @g_hnsiquomapvalndv A q dv_cache_0001 hyp_hnsiquomapvalclndv_1
  have p0009 :=
    @g_vtoclga
      (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q))
        (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cuni (.cv q)))))
      (.classEq (syn_cfv (syn_chnsiquomap A) Q)
        (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cuni Q))))
      q Q (syn_cpw1 (syn_chnord A)) dv_cache_0002 dv_cache_0003 dv_cache_0004 p0007 p0008
  exact p0009

@[expose]
noncomputable def g_hnsiquomapfndv (A : Class)
    (hyp_hnsiquomapfndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (syn_wf (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A))) :=
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
  have dv_cache_0002 : q ∉ ((syn_cpw1 (syn_chnord A))).fv :=
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
  have dv_cache_0003 : q ∉ ((syn_chnord (syn_cpw1 A))).fv :=
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
  have dv_cache_0004 : q ∉ ((syn_chnsiquomap A)).fv :=
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
  have p0000 := @g_hnsiquomapfnndv A hyp_hnsiquomapfndv_1
  have p0001 := @g_hnsiquomapfvhnordndv A q dv_cache_0001 hyp_hnsiquomapfndv_1
  have p0002 :=
    @g_rgen (.classMem (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_chnord (syn_cpw1 A))) q
      (syn_cpw1 (syn_chnord A)) p0001
  have p0003 :=
    @g_pm3_2i (syn_wfn (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)))
      (syn_wral q (syn_cpw1 (syn_chnord A))
        (.classMem (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_chnord (syn_cpw1 A))))
      p0000 p0002
  have p0004 :=
    @g_ffnfv q (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A)) (syn_chnsiquomap A)
      dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0005 :=
    @g_mpbir
      (syn_wf (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A)))
      (syn_wa (syn_wfn (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)))
        (syn_wral q (syn_cpw1 (syn_chnord A))
          (.classMem (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_chnord (syn_cpw1 A)))))
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

@[expose]
noncomputable def g_hnsiquomappreexndv (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (_dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y)
    (hyp_hnsiquomappreexndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wrex x (syn_cpw1 (syn_chnord A))
          (.classEq (.cv y) (syn_cfv (syn_chnsiquomap A) (.cv x))))) :=
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
  have dv_cache_0001 : w ∉ ((syn_cpw1 A)).fv := by
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
  have dv_cache_0003 : r ∉ ((syn_cpw1 (syn_chwcn A))).fv :=
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
  have dv_cache_0004 : r ∉ ((syn_chwcn (syn_cpw1 A))).fv :=
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
  have dv_cache_0006 : r ∉ ((syn_chnsicodemap A)).fv :=
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
  have dv_cache_0007 : x ∉ ((syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))).fv :=
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
  have dv_cache_0008 : x ∉ ((syn_cpw1 (syn_chnord A))).fv :=
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
      ((Wff.classEq (.cv y) (syn_cfv (syn_chnsiquomap A)
            (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))))).fv :=
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
      ((syn_wrex x (syn_cpw1 (syn_chnord A))
          (.classEq (.cv y) (syn_cfv (syn_chnsiquomap A) (.cv x))))).fv :=
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
      ((syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
          (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
            (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))).fv :=
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
      ((syn_wrex x (syn_cpw1 (syn_chnord A))
          (.classEq (.cv y) (syn_cfv (syn_chnsiquomap A) (.cv x))))).fv :=
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
  have dv_cache_0013 : w ∉ ((Wff.classMem (.cv y) (syn_chnord (syn_cpw1 A)))).fv :=
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
  have p0000 := @g_id (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
  have p0002 := @g_elex (.cv y) (syn_chnord (syn_cpw1 A))
  have p0003 :=
    @g_syl (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
      (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (.classMem (.cv y) (syn_cvv)) p0000
      p0002
  have p0004 := @g_elhnordclndv w (syn_cpw1 A) (.cv y) dv_cache_0001 dv_cache_0002
  have p0005 :=
    @g_syl (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (.classMem (.cv y) (syn_cvv))
      (syn_wb (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wrex w (syn_chwcn (syn_cpw1 A))
          (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
      p0003 p0004
  have p0006 :=
    @g_mpbid (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
      (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
      (syn_wrex w (syn_chwcn (syn_cpw1 A))
        (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))
      p0000 p0005
  have p0007 := @g_hnsicodemapfondv A
  have p0008 :=
    @g_a1i
      (syn_wfo (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)))
      (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
        (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
          (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
      p0007
  have p0009 :=
    @g_simpr (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
      (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
        (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))
  have p0010 :=
    @g_simpl (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
      (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))
  have p0011 :=
    @g_syl
      (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
        (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
          (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
      (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
        (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))
      (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) p0009 p0010
  have p0012 :=
    @g_jca
      (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
        (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
          (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
      (syn_wfo (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)))
      (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) p0008 p0011
  have p0013 :=
    @g_foelrn r (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)) (.cv w)
      (syn_chnsicodemap A) dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0014 :=
    @g_syl
      (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
        (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
          (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
      (syn_wa (syn_wfo (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)))
        (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))))
      (syn_wrex r (syn_cpw1 (syn_chwcn A))
        (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))
      p0012 p0013
  have p0015 :=
    @g_simpr
      (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
        (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
          (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
      (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
        (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))
  have p0016 :=
    @g_simpl (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
      (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))
  have p0017 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
          (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
            (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
        (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
          (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
        (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) p0015 p0016
  have p0018 := @g_pw1argclcl (syn_chwcn A) (.cv r)
  have p0019 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
          (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
            (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
        (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
          (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
      (syn_wa (.classMem (syn_cuni (.cv r)) (syn_chwcn A))
        (.classEq (.cv r) (syn_csn (syn_cuni (.cv r)))))
      p0017 p0018
  have p0020 :=
    @g_simpl (.classMem (syn_cuni (.cv r)) (syn_chwcn A))
      (.classEq (.cv r) (syn_csn (syn_cuni (.cv r))))
  have p0021 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
          (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
            (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
        (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
          (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      (syn_wa (.classMem (syn_cuni (.cv r)) (syn_chwcn A))
        (.classEq (.cv r) (syn_csn (syn_cuni (.cv r)))))
      (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) p0019 p0020
  have p0022 := @g_hwnisoclasselhnordcl A (syn_cuni (.cv r)) hyp_hnsiquomappreexndv_1
  have p0023 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
          (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
            (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
        (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
          (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      (.classMem (syn_cuni (.cv r)) (syn_chwcn A))
      (.classMem (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)) (syn_chnord A)) p0021 p0022
  have p0024 := @g_snelpw1 (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)) (syn_chnord A)
  have p0025 :=
    @g_sylibr
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
          (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
            (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
        (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
          (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      (.classMem (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)) (syn_chnord A))
      (.classMem (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))
        (syn_cpw1 (syn_chnord A)))
      p0023 p0024
  have p0026 :=
    @g_simpl
      (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
        (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
          (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
      (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
        (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))
  have p0028 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
          (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
            (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
        (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
          (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
        (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
          (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
      (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
        (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))
      p0026 p0009
  have p0029 :=
    @g_simpr (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
      (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))
  have p0030 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
          (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
            (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
        (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
          (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
        (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))
      (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))) p0028 p0029
  have p0032 :=
    @g_simpr (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
      (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))
  have p0033 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
          (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
            (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
        (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
          (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
        (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))) p0015 p0032
  have p0034 :=
    @g_eceq1 (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)) (syn_chwniso (syn_cpw1 A))
  have p0035 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
          (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
            (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
        (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
          (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))
      (.classEq (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))
        (syn_cec (syn_cfv (syn_chnsicodemap A) (.cv r)) (syn_chwniso (syn_cpw1 A))))
      p0033 p0034
  have p0036 :=
    @g_eqtrd
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
          (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
            (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
        (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
          (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))
      (syn_cec (syn_cfv (syn_chnsicodemap A) (.cv r)) (syn_chwniso (syn_cpw1 A))) p0030
      p0035
  have p0048 :=
    @g_hnsiquomapvalclndv A (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))
      hyp_hnsiquomappreexndv_1
  have p0049 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
          (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
            (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
        (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
          (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      (.classMem (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))
        (syn_cpw1 (syn_chnord A)))
      (.classEq (syn_cfv (syn_chnsiquomap A)
          (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))) (syn_cima (syn_chnsicodemap A)
          (syn_cpw1 (syn_cuni (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))))))
      p0025 p0048
  have p0059 := @g_elex (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)) (syn_chnord A)
  have p0060 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
          (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
            (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
        (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
          (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      (.classMem (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)) (syn_chnord A))
      (.classMem (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)) (syn_cvv)) p0023 p0059
  have p0061 := @g_unisng (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)) (syn_cvv)
  have p0062 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
          (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
            (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
        (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
          (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      (.classMem (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)) (syn_cvv))
      (.classEq (syn_cuni (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))))
        (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))
      p0060 p0061
  have p0063 :=
    @g_pw1eq (syn_cuni (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))))
      (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))
  have p0064 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
          (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
            (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
        (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
          (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      (.classEq (syn_cuni (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))))
        (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))
      (.classEq (syn_cpw1 (syn_cuni (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))))
        (syn_cpw1 (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))))
      p0062 p0063
  have p0065 :=
    @g_imaeq2d
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
          (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
            (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
        (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
          (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      (syn_cpw1 (syn_cuni (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))))
      (syn_cpw1 (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))) (syn_chnsicodemap A) p0064
  have p0066 :=
    @g_eqtrd
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
          (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
            (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
        (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
          (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      (syn_cfv (syn_chnsiquomap A) (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))))
      (syn_cima (syn_chnsicodemap A)
        (syn_cpw1 (syn_cuni (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))))))
      (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))))
      p0049 p0065
  have p0072 :=
    @g_simpr (.classMem (syn_cuni (.cv r)) (syn_chwcn A))
      (.classEq (.cv r) (syn_csn (syn_cuni (.cv r))))
  have p0073 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
          (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
            (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
        (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
          (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      (syn_wa (.classMem (syn_cuni (.cv r)) (syn_chwcn A))
        (.classEq (.cv r) (syn_csn (syn_cuni (.cv r)))))
      (.classEq (.cv r) (syn_csn (syn_cuni (.cv r)))) p0019 p0072
  have p0074 := @g_eceq1 (.cv r) (syn_csn (syn_cuni (.cv r))) (syn_csi (syn_chwniso A))
  have p0075 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
          (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
            (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
        (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
          (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      (.classEq (.cv r) (syn_csn (syn_cuni (.cv r))))
      (.classEq (syn_cec (.cv r) (syn_csi (syn_chwniso A)))
        (syn_cec (syn_csn (syn_cuni (.cv r))) (syn_csi (syn_chwniso A))))
      p0073 p0074
  have p0083 := @g_elex (syn_cuni (.cv r)) (syn_chwcn A)
  have p0084 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
          (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
            (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
        (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
          (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      (.classMem (syn_cuni (.cv r)) (syn_chwcn A))
      (.classMem (syn_cuni (.cv r)) (syn_cvv)) p0021 p0083
  have p0085 := @g_siecsnclndv (syn_cuni (.cv r)) (syn_chwniso A)
  have p0086 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
          (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
            (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
        (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
          (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      (.classMem (syn_cuni (.cv r)) (syn_cvv))
      (.classEq (syn_cec (syn_csn (syn_cuni (.cv r))) (syn_csi (syn_chwniso A)))
        (syn_cpw1 (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))))
      p0084 p0085
  have p0087 :=
    @g_eqtrd
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
          (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
            (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
        (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
          (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      (syn_cec (.cv r) (syn_csi (syn_chwniso A)))
      (syn_cec (syn_csn (syn_cuni (.cv r))) (syn_csi (syn_chwniso A)))
      (syn_cpw1 (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))) p0075 p0086
  have p0088 :=
    @g_eqcomd
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
          (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
            (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
        (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
          (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      (syn_cec (.cv r) (syn_csi (syn_chwniso A)))
      (syn_cpw1 (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))) p0087
  have p0089 :=
    @g_imaeq2d
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
          (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
            (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
        (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
          (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      (syn_cpw1 (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))
      (syn_cec (.cv r) (syn_csi (syn_chwniso A))) (syn_chnsicodemap A) p0088
  have p0090 :=
    @g_eqtrd
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
          (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
            (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
        (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
          (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      (syn_cfv (syn_chnsiquomap A) (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))))
      (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))))
      (syn_cima (syn_chnsicodemap A) (syn_cec (.cv r) (syn_csi (syn_chwniso A)))) p0066
      p0089
  have p0094 := @g_hnsicodemapclassimcldndv A (.cv r) hyp_hnsiquomappreexndv_1
  have p0095 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
          (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
            (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
        (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
          (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
      (.classEq (syn_cima (syn_chnsicodemap A) (syn_cec (.cv r) (syn_csi (syn_chwniso A))))
        (syn_cec (syn_cfv (syn_chnsicodemap A) (.cv r)) (syn_chwniso (syn_cpw1 A))))
      p0017 p0094
  have p0096 :=
    @g_eqtrd
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
          (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
            (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
        (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
          (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      (syn_cfv (syn_chnsiquomap A) (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))))
      (syn_cima (syn_chnsicodemap A) (syn_cec (.cv r) (syn_csi (syn_chwniso A))))
      (syn_cec (syn_cfv (syn_chnsicodemap A) (.cv r)) (syn_chwniso (syn_cpw1 A))) p0090
      p0095
  have p0097 :=
    @g_eqcomd
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
          (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
            (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
        (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
          (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      (syn_cfv (syn_chnsiquomap A) (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))))
      (syn_cec (syn_cfv (syn_chnsicodemap A) (.cv r)) (syn_chwniso (syn_cpw1 A))) p0096
  have p0098 :=
    @g_eqtrd
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
          (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
            (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
        (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
          (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      (.cv y) (syn_cec (syn_cfv (syn_chnsicodemap A) (.cv r)) (syn_chwniso (syn_cpw1 A)))
      (syn_cfv (syn_chnsiquomap A) (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))))
      p0036 p0097
  have p0099 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
          (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
            (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
        (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
          (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      (.classMem (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))
        (syn_cpw1 (syn_chnord A)))
      (.classEq (.cv y) (syn_cfv (syn_chnsiquomap A)
          (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))))
      p0025 p0098
  have p0100 :=
    @g_id (.classEq (.cv x) (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))))
  have p0101 :=
    @g_fveq2d (.classEq (.cv x) (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))))
      (.cv x) (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))) (syn_chnsiquomap A)
      p0100
  have p0102 :=
    @g_eqeq2d (.classEq (.cv x) (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))))
      (syn_cfv (syn_chnsiquomap A) (.cv x))
      (syn_cfv (syn_chnsiquomap A) (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))))
      (.cv y) p0101
  have p0103 :=
    @g_rspcev (.classEq (.cv y) (syn_cfv (syn_chnsiquomap A) (.cv x)))
      (.classEq (.cv y) (syn_cfv (syn_chnsiquomap A)
          (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))))
      x (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))) (syn_cpw1 (syn_chnord A))
      dv_cache_0007 dv_cache_0008 dv_cache_0009 p0102
  have p0104 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
          (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
            (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
        (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
          (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      (syn_wa (.classMem (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))
          (syn_cpw1 (syn_chnord A))) (.classEq (.cv y) (syn_cfv (syn_chnsiquomap A)
            (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))))))
      (syn_wrex x (syn_cpw1 (syn_chnord A))
        (.classEq (.cv y) (syn_cfv (syn_chnsiquomap A) (.cv x))))
      p0099 p0103
  have p0105 :=
    @g_rexlimddv
      (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
        (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))
          (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))
      (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))
      (syn_wrex x (syn_cpw1 (syn_chnord A))
        (.classEq (.cv y) (syn_cfv (syn_chnsiquomap A) (.cv x))))
      r (syn_cpw1 (syn_chwcn A)) dv_cache_0010 dv_cache_0011 p0014 p0104
  have p0106 :=
    @g_rexlimddv (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
      (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))
      (syn_wrex x (syn_cpw1 (syn_chnord A))
        (.classEq (.cv y) (syn_cfv (syn_chnsiquomap A) (.cv x))))
      w (syn_chwcn (syn_cpw1 A)) dv_cache_0012 dv_cache_0013 p0006 p0105
  exact p0106

@[expose]
noncomputable def g_hnsiquomapfondv (A : Class)
    (hyp_hnsiquomapfondv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (syn_wfo (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A))) :=
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
  have dv_cache_0004 : x ∉ ((syn_cpw1 (syn_chnord A))).fv :=
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
  have dv_cache_0005 : y ∉ ((syn_cpw1 (syn_chnord A))).fv :=
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
  have dv_cache_0006 : x ∉ ((syn_chnord (syn_cpw1 A))).fv :=
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
  have dv_cache_0007 : y ∉ ((syn_chnord (syn_cpw1 A))).fv :=
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
  have dv_cache_0008 : x ∉ ((syn_chnsiquomap A)).fv :=
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
  have dv_cache_0009 : y ∉ ((syn_chnsiquomap A)).fv :=
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
  have p0000 := @g_hnsiquomapfndv A hyp_hnsiquomapfondv_1
  have p0001 :=
    @g_hnsiquomappreexndv x y A dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_hnsiquomapfondv_1
  have p0002 :=
    @g_rgen
      (syn_wrex x (syn_cpw1 (syn_chnord A))
        (.classEq (.cv y) (syn_cfv (syn_chnsiquomap A) (.cv x))))
      y (syn_chnord (syn_cpw1 A)) p0001
  have p0003 :=
    @g_pm3_2i
      (syn_wf (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A)))
      (syn_wral y (syn_chnord (syn_cpw1 A)) (syn_wrex x (syn_cpw1 (syn_chnord A))
          (.classEq (.cv y) (syn_cfv (syn_chnsiquomap A) (.cv x)))))
      p0000 p0002
  have p0004 :=
    @g_dffo3 x y (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A)) (syn_chnsiquomap A)
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0003
  have p0005 :=
    @g_mpbir
      (syn_wfo (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A)))
      (syn_wa (syn_wf (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A)))
        (syn_wral y (syn_chnord (syn_cpw1 A)) (syn_wrex x (syn_cpw1 (syn_chnord A))
            (.classEq (.cv y) (syn_cfv (syn_chnsiquomap A) (.cv x))))))
      p0003 p0004
  exact p0005

@[expose]
noncomputable def g_hnsicodemapkernelcl2ndv (A : Class) (P : Class) (Q : Class) :
    Nominal.NPrf
      (.imp (.classMem Q (syn_cpw1 (syn_chwcn A))) (.imp (.classMem P (syn_cpw1 (syn_chwcn A)))
          (syn_wb (syn_wbr Q (syn_csi (syn_chwniso A)) P)
            (syn_wbr (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A))
              (syn_cfv (syn_chnsicodemap A) P))))) :=
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
  have dv_cache_0004 : r ∉ ((syn_cpw1 (syn_chwcn A))).fv :=
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
      ((Wff.imp (.classMem Q (syn_cpw1 (syn_chwcn A)))
          (syn_wb (syn_wbr Q (syn_csi (syn_chwniso A)) P)
            (syn_wbr (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A))
              (syn_cfv (syn_chnsicodemap A) P))))).fv :=
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
  have p0000 := @g_biid (.classMem Q (syn_cpw1 (syn_chwcn A)))
  have p0001 :=
    @g_a1i
      (syn_wb (.classMem Q (syn_cpw1 (syn_chwcn A))) (.classMem Q (syn_cpw1 (syn_chwcn A))))
      (.classEq (.cv r) P) p0000
  have p0002 := @g_id (.classEq (.cv r) P)
  have p0003 := @g_breq2d (.classEq (.cv r) P) (.cv r) P Q (syn_csi (syn_chwniso A)) p0002
  have p0005 := @g_fveq2d (.classEq (.cv r) P) (.cv r) P (syn_chnsicodemap A) p0002
  have p0006 :=
    @g_breq2d (.classEq (.cv r) P) (syn_cfv (syn_chnsicodemap A) (.cv r))
      (syn_cfv (syn_chnsicodemap A) P) (syn_cfv (syn_chnsicodemap A) Q)
      (syn_chwniso (syn_cpw1 A)) p0005
  have p0007 :=
    @g_bibi12d (.classEq (.cv r) P) (syn_wbr Q (syn_csi (syn_chwniso A)) (.cv r))
      (syn_wbr Q (syn_csi (syn_chwniso A)) P)
      (syn_wbr (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A))
        (syn_cfv (syn_chnsicodemap A) (.cv r)))
      (syn_wbr (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A))
        (syn_cfv (syn_chnsicodemap A) P))
      p0003 p0006
  have p0008 :=
    @g_imbi12d (.classEq (.cv r) P) (.classMem Q (syn_cpw1 (syn_chwcn A)))
      (.classMem Q (syn_cpw1 (syn_chwcn A)))
      (syn_wb (syn_wbr Q (syn_csi (syn_chwniso A)) (.cv r))
        (syn_wbr (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A))
          (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (syn_wb (syn_wbr Q (syn_csi (syn_chwniso A)) P)
        (syn_wbr (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A))
          (syn_cfv (syn_chnsicodemap A) P)))
      p0001 p0007
  have p0009 := @g_hnsicodemapkernelclndv A Q r dv_cache_0001 dv_cache_0002
  have p0010 :=
    @g_com12 (.classMem Q (syn_cpw1 (syn_chwcn A)))
      (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
      (syn_wb (syn_wbr Q (syn_csi (syn_chwniso A)) (.cv r))
        (syn_wbr (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A))
          (syn_cfv (syn_chnsicodemap A) (.cv r))))
      p0009
  have p0011 :=
    @g_vtoclga
      (.imp (.classMem Q (syn_cpw1 (syn_chwcn A)))
        (syn_wb (syn_wbr Q (syn_csi (syn_chwniso A)) (.cv r))
          (syn_wbr (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A))
            (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      (.imp (.classMem Q (syn_cpw1 (syn_chwcn A)))
        (syn_wb (syn_wbr Q (syn_csi (syn_chwniso A)) P)
          (syn_wbr (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A))
            (syn_cfv (syn_chnsicodemap A) P))))
      r P (syn_cpw1 (syn_chwcn A)) dv_cache_0003 dv_cache_0004 dv_cache_0005 p0008 p0010
  have p0012 :=
    @g_com12 (.classMem P (syn_cpw1 (syn_chwcn A))) (.classMem Q (syn_cpw1 (syn_chwcn A)))
      (syn_wb (syn_wbr Q (syn_csi (syn_chwniso A)) P)
        (syn_wbr (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A))
          (syn_cfv (syn_chnsicodemap A) P)))
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

@[expose]
noncomputable def g_hnsiquomaprepvalndv (u : Var) (A : Class) (q : Var)
    (dv_A_q : q ∉ A.fv) (dv_A_u : u ∉ A.fv) (_dv_q_u : q ≠ u)
    (hyp_hnsiquomaprepvalndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q))
          (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u)))
            (syn_chwniso (syn_cpw1 A))))) :=
  by
  have dv_cache_0001 : q ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_q, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((syn_chwniso A)).fv :=
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
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
  have p0001 := @g_hnsiquomapvalndv A q dv_cache_0001 hyp_hnsiquomaprepvalndv_1
  have p0002 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q))
        (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cuni (.cv q)))))
      p0000 p0001
  have p0003 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
  have p0004 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A))
      (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))
  have p0005 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
      (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))) p0003 p0004
  have p0006 := @g_pw1eq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))
  have p0007 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))
      (.classEq (syn_cpw1 (syn_cuni (.cv q))) (syn_cpw1 (syn_cec (.cv u) (syn_chwniso A))))
      p0005 p0006
  have p0008 := @g_siecsnndv u (syn_chwniso A) dv_cache_0002
  have p0009 :=
    @g_eqcomi (syn_cec (syn_csn (.cv u)) (syn_csi (syn_chwniso A)))
      (syn_cpw1 (syn_cec (.cv u) (syn_chwniso A))) p0008
  have p0010 :=
    @g_a1i
      (.classEq (syn_cpw1 (syn_cec (.cv u) (syn_chwniso A)))
        (syn_cec (syn_csn (.cv u)) (syn_csi (syn_chwniso A))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      p0009
  have p0011 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (syn_cpw1 (syn_cuni (.cv q))) (syn_cpw1 (syn_cec (.cv u) (syn_chwniso A)))
      (syn_cec (syn_csn (.cv u)) (syn_csi (syn_chwniso A))) p0007 p0010
  have p0012 :=
    @g_imaeq2d
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (syn_cpw1 (syn_cuni (.cv q))) (syn_cec (syn_csn (.cv u)) (syn_csi (syn_chwniso A)))
      (syn_chnsicodemap A) p0011
  have p0013 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (syn_cfv (syn_chnsiquomap A) (.cv q))
      (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cuni (.cv q))))
      (syn_cima (syn_chnsicodemap A) (syn_cec (syn_csn (.cv u)) (syn_csi (syn_chwniso A))))
      p0002 p0012
  have p0015 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A))
      (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))
  have p0016 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
      (.classMem (.cv u) (syn_chwcn A)) p0003 p0015
  have p0017 := @g_snelpw1 (.cv u) (syn_chwcn A)
  have p0018 :=
    @g_sylibr
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (.classMem (.cv u) (syn_chwcn A))
      (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A))) p0016 p0017
  have p0019 := @g_hnsicodemapclassimcldndv A (syn_csn (.cv u)) hyp_hnsiquomaprepvalndv_1
  have p0020 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A)))
      (.classEq (syn_cima (syn_chnsicodemap A)
          (syn_cec (syn_csn (.cv u)) (syn_csi (syn_chwniso A))))
        (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A))))
      p0018 p0019
  have p0021 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (syn_cfv (syn_chnsiquomap A) (.cv q))
      (syn_cima (syn_chnsicodemap A) (syn_cec (syn_csn (.cv u)) (syn_csi (syn_chwniso A))))
      (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A)))
      p0013 p0020
  exact p0021

@[expose]
noncomputable def g_hnordpw1repndv (u : Var) (A : Class) (q : Var) (_dv_A_q : q ∉ A.fv)
    (_dv_A_u : u ∉ A.fv) (_dv_q_u : q ≠ u) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
        (.classEq (.cv q) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))) :=
  by
  have p0000 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
  have p0001 := @g_pw1argclcl (syn_chnord A) (.cv q)
  have p0002 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (syn_wa (.classMem (syn_cuni (.cv q)) (syn_chnord A))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      p0000 p0001
  have p0003 :=
    @g_simpr (.classMem (syn_cuni (.cv q)) (syn_chnord A))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0004 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (syn_wa (.classMem (syn_cuni (.cv q)) (syn_chnord A))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0002 p0003
  have p0005 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
  have p0006 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A))
      (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))
  have p0007 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
      (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))) p0005 p0006
  have p0008 := @g_sneq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))
  have p0009 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))
      (.classEq (syn_csn (syn_cuni (.cv q))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))
      p0007 p0008
  have p0010 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (.cv q) (syn_csn (syn_cuni (.cv q))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))
      p0004 p0009
  exact p0010

@[expose]
noncomputable def g_brsnsiandv (A : Class) (B : Class) (R : Class)
    (_dv_A_R : Disjoint A.fv R.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
        (syn_wb (syn_wbr (syn_csn A) (syn_csi R) (syn_csn B)) (syn_wbr A R B))) :=
  by
  have p0000 := @g_id (.classEq A (syn_cif (.classMem A (syn_cvv)) A (syn_c0)))
  have p0001 := @g_sneq A (syn_cif (.classMem A (syn_cvv)) A (syn_c0))
  have p0002 :=
    @g_syl (.classEq A (syn_cif (.classMem A (syn_cvv)) A (syn_c0)))
      (.classEq A (syn_cif (.classMem A (syn_cvv)) A (syn_c0)))
      (.classEq (syn_csn A) (syn_csn (syn_cif (.classMem A (syn_cvv)) A (syn_c0)))) p0000
      p0001
  have p0003 :=
    @g_breq1d (.classEq A (syn_cif (.classMem A (syn_cvv)) A (syn_c0))) (syn_csn A)
      (syn_csn (syn_cif (.classMem A (syn_cvv)) A (syn_c0))) (syn_csn B) (syn_csi R) p0002
  have p0005 :=
    @g_breq1d (.classEq A (syn_cif (.classMem A (syn_cvv)) A (syn_c0))) A
      (syn_cif (.classMem A (syn_cvv)) A (syn_c0)) B R p0000
  have p0006 :=
    @g_bibi12d (.classEq A (syn_cif (.classMem A (syn_cvv)) A (syn_c0)))
      (syn_wbr (syn_csn A) (syn_csi R) (syn_csn B))
      (syn_wbr (syn_csn (syn_cif (.classMem A (syn_cvv)) A (syn_c0))) (syn_csi R) (syn_csn B))
      (syn_wbr A R B) (syn_wbr (syn_cif (.classMem A (syn_cvv)) A (syn_c0)) R B) p0003
      p0005
  have p0007 := @g_id (.classEq B (syn_cif (.classMem B (syn_cvv)) B (syn_c0)))
  have p0008 := @g_sneq B (syn_cif (.classMem B (syn_cvv)) B (syn_c0))
  have p0009 :=
    @g_syl (.classEq B (syn_cif (.classMem B (syn_cvv)) B (syn_c0)))
      (.classEq B (syn_cif (.classMem B (syn_cvv)) B (syn_c0)))
      (.classEq (syn_csn B) (syn_csn (syn_cif (.classMem B (syn_cvv)) B (syn_c0)))) p0007
      p0008
  have p0010 :=
    @g_breq2d (.classEq B (syn_cif (.classMem B (syn_cvv)) B (syn_c0))) (syn_csn B)
      (syn_csn (syn_cif (.classMem B (syn_cvv)) B (syn_c0)))
      (syn_csn (syn_cif (.classMem A (syn_cvv)) A (syn_c0))) (syn_csi R) p0009
  have p0012 :=
    @g_breq2d (.classEq B (syn_cif (.classMem B (syn_cvv)) B (syn_c0))) B
      (syn_cif (.classMem B (syn_cvv)) B (syn_c0))
      (syn_cif (.classMem A (syn_cvv)) A (syn_c0)) R p0007
  have p0013 :=
    @g_bibi12d (.classEq B (syn_cif (.classMem B (syn_cvv)) B (syn_c0)))
      (syn_wbr (syn_csn (syn_cif (.classMem A (syn_cvv)) A (syn_c0))) (syn_csi R) (syn_csn B))
      (syn_wbr (syn_csn (syn_cif (.classMem A (syn_cvv)) A (syn_c0))) (syn_csi R)
        (syn_csn (syn_cif (.classMem B (syn_cvv)) B (syn_c0))))
      (syn_wbr (syn_cif (.classMem A (syn_cvv)) A (syn_c0)) R B)
      (syn_wbr (syn_cif (.classMem A (syn_cvv)) A (syn_c0)) R
        (syn_cif (.classMem B (syn_cvv)) B (syn_c0)))
      p0010 p0012
  have p0014 := @g_eqid (syn_c0)
  have p0015 := @g_simpr (.classEq (syn_c0) (syn_c0)) (.classMem A (syn_cvv))
  have p0016 := @g_n_0ex
  have p0017 :=
    @g_a1i (.classMem (syn_c0) (syn_cvv))
      (syn_wa (.classEq (syn_c0) (syn_c0)) (.neg (.classMem A (syn_cvv)))) p0016
  have p0018 :=
    @g_ifclda (.classEq (syn_c0) (syn_c0)) (.classMem A (syn_cvv)) A (syn_c0) (syn_cvv)
      p0015 p0017
  have p0019 := Nominal.mp p0014 p0018
  have p0021 := @g_simpr (.classEq (syn_c0) (syn_c0)) (.classMem B (syn_cvv))
  have p0023 :=
    @g_a1i (.classMem (syn_c0) (syn_cvv))
      (syn_wa (.classEq (syn_c0) (syn_c0)) (.neg (.classMem B (syn_cvv)))) p0016
  have p0024 :=
    @g_ifclda (.classEq (syn_c0) (syn_c0)) (.classMem B (syn_cvv)) B (syn_c0) (syn_cvv)
      p0021 p0023
  have p0025 := Nominal.mp p0014 p0024
  have p0026 :=
    @g_brsnsi (syn_cif (.classMem A (syn_cvv)) A (syn_c0))
      (syn_cif (.classMem B (syn_cvv)) B (syn_c0)) R p0019 p0025
  have p0027 :=
    @g_dedth2h (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (syn_wb (syn_wbr (syn_csn A) (syn_csi R) (syn_csn B)) (syn_wbr A R B))
      (syn_wb (syn_wbr (syn_csn (syn_cif (.classMem A (syn_cvv)) A (syn_c0))) (syn_csi R)
          (syn_csn B)) (syn_wbr (syn_cif (.classMem A (syn_cvv)) A (syn_c0)) R B))
      (syn_wb (syn_wbr (syn_csn (syn_cif (.classMem A (syn_cvv)) A (syn_c0))) (syn_csi R)
          (syn_csn (syn_cif (.classMem B (syn_cvv)) B (syn_c0))))
        (syn_wbr (syn_cif (.classMem A (syn_cvv)) A (syn_c0)) R
          (syn_cif (.classMem B (syn_cvv)) B (syn_c0))))
      A B (syn_c0) (syn_c0) p0006 p0013 p0026
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

@[expose]
noncomputable def g_hnsiquomapfvineqndv (A : Class) (s : Var) (q : Var)
    (dv_A_q : q ∉ A.fv) (dv_A_s : s ∉ A.fv) (_dv_q_s : q ≠ s)
    (hyp_hnsiquomapfvineqndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))) (.imp
          (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))
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
  have dv_cache_0002 : u ∉ ((syn_cuni (.cv q))).fv :=
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
  have dv_cache_0004 : v ∉ ((syn_cuni (.cv s))).fv :=
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
  have dv_cache_0009 : Disjoint ((Class.cv u)).fv ((syn_chwniso A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (show Disjoint ((Class.cv u)).fv ((syn_chwniso A)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso];
          exact
            (show Disjoint (({ u } : Finset Var)) ((A).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show u ∉ (A).fv from (by exact fresh_u_not_A))))))
  have dv_cache_0010 :
    v ∉
      ((Wff.imp (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q))
            (syn_cfv (syn_chnsiquomap A) (.cv s))) (.classEq (.cv q) (.cv s)))).fv :=
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
      ((syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
          (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))).fv :=
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
      ((Wff.imp (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q))
            (syn_cfv (syn_chnsiquomap A) (.cv s))) (.classEq (.cv q) (.cv s)))).fv :=
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
      ((syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))).fv :=
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
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))
  have p0001 := @g_pw1argclcl (syn_chnord A) (.cv q)
  have p0002 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
      (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (syn_wa (.classMem (syn_cuni (.cv q)) (syn_chnord A))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      p0000 p0001
  have p0003 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) (syn_chnord A))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0004 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
      (syn_wa (.classMem (syn_cuni (.cv q)) (syn_chnord A))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      (.classMem (syn_cuni (.cv q)) (syn_chnord A)) p0002 p0003
  have p0010 := @g_elex (syn_cuni (.cv q)) (syn_chnord A)
  have p0011 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
      (.classMem (syn_cuni (.cv q)) (syn_chnord A))
      (.classMem (syn_cuni (.cv q)) (syn_cvv)) p0004 p0010
  have p0012 := @g_elhnordclndv u A (syn_cuni (.cv q)) dv_cache_0001 dv_cache_0002
  have p0013 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
      (.classMem (syn_cuni (.cv q)) (syn_cvv))
      (syn_wb (.classMem (syn_cuni (.cv q)) (syn_chnord A)) (syn_wrex u (syn_chwcn A)
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      p0011 p0012
  have p0014 :=
    @g_mpbid
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
      (.classMem (syn_cuni (.cv q)) (syn_chnord A))
      (syn_wrex u (syn_chwcn A) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
      p0004 p0013
  have p0015 :=
    @g_simpl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
  have p0016 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))
  have p0017 := @g_pw1argclcl (syn_chnord A) (.cv s)
  have p0018 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
      (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))
      (syn_wa (.classMem (syn_cuni (.cv s)) (syn_chnord A))
        (.classEq (.cv s) (syn_csn (syn_cuni (.cv s)))))
      p0016 p0017
  have p0019 :=
    @g_simpl (.classMem (syn_cuni (.cv s)) (syn_chnord A))
      (.classEq (.cv s) (syn_csn (syn_cuni (.cv s))))
  have p0020 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
      (syn_wa (.classMem (syn_cuni (.cv s)) (syn_chnord A))
        (.classEq (.cv s) (syn_csn (syn_cuni (.cv s)))))
      (.classMem (syn_cuni (.cv s)) (syn_chnord A)) p0018 p0019
  have p0026 := @g_elex (syn_cuni (.cv s)) (syn_chnord A)
  have p0027 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
      (.classMem (syn_cuni (.cv s)) (syn_chnord A))
      (.classMem (syn_cuni (.cv s)) (syn_cvv)) p0020 p0026
  have p0028 := @g_elhnordclndv v A (syn_cuni (.cv s)) dv_cache_0003 dv_cache_0004
  have p0029 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
      (.classMem (syn_cuni (.cv s)) (syn_cvv))
      (syn_wb (.classMem (syn_cuni (.cv s)) (syn_chnord A)) (syn_wrex v (syn_chwcn A)
          (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
      p0027 p0028
  have p0030 :=
    @g_mpbid
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
      (.classMem (syn_cuni (.cv s)) (syn_chnord A))
      (syn_wrex v (syn_chwcn A) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))
      p0020 p0029
  have p0031 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
      (syn_wrex v (syn_chwcn A) (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))
      p0015 p0030
  have p0032 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
          (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
      (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))
  have p0033 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))
  have p0034 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
          (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
      (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      p0032 p0033
  have p0036 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
      p0034 p0015
  have p0038 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
      (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) p0036 p0000
  have p0042 :=
    @g_simpr
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
  have p0043 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
      p0034 p0042
  have p0044 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A))
      (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))
  have p0045 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
      (.classMem (.cv u) (syn_chwcn A)) p0043 p0044
  have p0051 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A))
      (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))
  have p0052 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
      (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))) p0043 p0051
  have p0053 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (.classMem (.cv u) (syn_chwcn A))
      (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))) p0045 p0052
  have p0054 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
      p0038 p0053
  have p0055 := @g_hnordpw1repndv u A q dv_cache_0005 dv_cache_0001 dv_cache_0006
  have p0056 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (.classEq (.cv q) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))) p0054 p0055
  have p0080 :=
    @g_hnsiquomaprepvalndv u A q dv_cache_0005 dv_cache_0001 dv_cache_0006
      hyp_hnsiquomapfvineqndv_1
  have p0081 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q))
        (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A))))
      p0054 p0080
  have p0082 :=
    @g_eqcomd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (syn_cfv (syn_chnsiquomap A) (.cv q))
      (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A)))
      p0081
  have p0083 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
          (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
      (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))
  have p0084 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A)))
      (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)) p0082
      p0083
  have p0091 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
      (.classMem (.cv s) (syn_cpw1 (syn_chnord A))) p0036 p0016
  have p0093 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))
  have p0094 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
          (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))
      p0032 p0093
  have p0095 :=
    @g_simpl (.classMem (.cv v) (syn_chwcn A))
      (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))
  have p0096 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))
      (.classMem (.cv v) (syn_chwcn A)) p0094 p0095
  have p0100 :=
    @g_simpr (.classMem (.cv v) (syn_chwcn A))
      (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))
  have p0101 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))
      (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))) p0094 p0100
  have p0102 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (.classMem (.cv v) (syn_chwcn A))
      (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))) p0096 p0101
  have p0103 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A))))
      p0091 p0102
  have p0104 :=
    @g_hnsiquomaprepvalndv v A s dv_cache_0007 dv_cache_0003 dv_cache_0008
      hyp_hnsiquomapfvineqndv_1
  have p0105 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
      (.classEq (syn_cfv (syn_chnsiquomap A) (.cv s))
        (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) (syn_chwniso (syn_cpw1 A))))
      p0103 p0104
  have p0106 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A)))
      (syn_cfv (syn_chnsiquomap A) (.cv s))
      (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) (syn_chwniso (syn_cpw1 A)))
      p0084 p0105
  have p0114 := @g_snelpw1 (.cv u) (syn_chwcn A)
  have p0115 :=
    @g_sylibr
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (.classMem (.cv u) (syn_chwcn A))
      (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A))) p0045 p0114
  have p0116 := @g_hnsicodemapfndv A
  have p0117 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)) (syn_csn (.cv u))
      (syn_chnsicodemap A) p0116
  have p0118 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A)))
      (.classMem (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwcn (syn_cpw1 A)))
      p0115 p0117
  have p0124 := @g_snelpw1 (.cv v) (syn_chwcn A)
  have p0125 :=
    @g_sylibr
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (.classMem (.cv v) (syn_chwcn A))
      (.classMem (syn_csn (.cv v)) (syn_cpw1 (syn_chwcn A))) p0096 p0124
  have p0127 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)) (syn_csn (.cv v))
      (syn_chnsicodemap A) p0116
  have p0128 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (.classMem (syn_csn (.cv v)) (syn_cpw1 (syn_chwcn A)))
      (.classMem (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) (syn_chwcn (syn_cpw1 A)))
      p0125 p0127
  have p0129 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (.classMem (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwcn (syn_cpw1 A)))
      (.classMem (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) (syn_chwcn (syn_cpw1 A)))
      p0118 p0128
  have p0130 := @g_pw1exg A (syn_cvv)
  have p0131 := Nominal.mp hyp_hnsiquomapfvineqndv_1 p0130
  have p0132 :=
    @g_hwnisoclasseqbcl (syn_cpw1 A) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u)))
      (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) p0131
  have p0133 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (syn_wa (.classMem (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u)))
          (syn_chwcn (syn_cpw1 A))) (.classMem (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))
          (syn_chwcn (syn_cpw1 A))))
      (syn_wb (.classEq (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u)))
            (syn_chwniso (syn_cpw1 A)))
          (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) (syn_chwniso (syn_cpw1 A))))
        (syn_wbr (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u)))
          (syn_chwniso (syn_cpw1 A)) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
      p0129 p0132
  have p0134 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (.classEq (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u)))
          (syn_chwniso (syn_cpw1 A))) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))
          (syn_chwniso (syn_cpw1 A))))
      (syn_wbr (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A))
        (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))
      p0106 p0133
  have p0151 := @g_hnsicodemapkernelcl2ndv A (syn_csn (.cv v)) (syn_csn (.cv u))
  have p0152 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A)))
      (.imp (.classMem (syn_csn (.cv v)) (syn_cpw1 (syn_chwcn A)))
        (syn_wb (syn_wbr (syn_csn (.cv u)) (syn_csi (syn_chwniso A)) (syn_csn (.cv v)))
          (syn_wbr (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u)))
            (syn_chwniso (syn_cpw1 A)) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
      p0115 p0151
  have p0153 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (.classMem (syn_csn (.cv v)) (syn_cpw1 (syn_chwcn A)))
      (syn_wb (syn_wbr (syn_csn (.cv u)) (syn_csi (syn_chwniso A)) (syn_csn (.cv v)))
        (syn_wbr (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u)))
          (syn_chwniso (syn_cpw1 A)) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
      p0125 p0152
  have p0154 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (syn_wbr (syn_csn (.cv u)) (syn_csi (syn_chwniso A)) (syn_csn (.cv v)))
      (syn_wbr (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A))
        (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))
      p0134 p0153
  have p0162 := @g_elex (.cv u) (syn_chwcn A)
  have p0163 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_cvv)) p0045 p0162
  have p0169 := @g_elex (.cv v) (syn_chwcn A)
  have p0170 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv v) (syn_cvv)) p0096 p0169
  have p0171 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (.classMem (.cv u) (syn_cvv)) (.classMem (.cv v) (syn_cvv)) p0163 p0170
  have p0172 := @g_brsnsiandv (.cv u) (.cv v) (syn_chwniso A) dv_cache_0009
  have p0173 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (syn_wa (.classMem (.cv u) (syn_cvv)) (.classMem (.cv v) (syn_cvv)))
      (syn_wb (syn_wbr (syn_csn (.cv u)) (syn_csi (syn_chwniso A)) (syn_csn (.cv v)))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      p0171 p0172
  have p0174 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (syn_wbr (syn_csn (.cv u)) (syn_csi (syn_chwniso A)) (syn_csn (.cv v)))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0154 p0173
  have p0187 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0045 p0096
  have p0188 := @g_hwnisoclasseqbcl A (.cv u) (.cv v) hyp_hnsiquomapfvineqndv_1
  have p0189 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wb (.classEq (syn_cec (.cv u) (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A)))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      p0187 p0188
  have p0190 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (.classEq (syn_cec (.cv u) (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A)))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0174 p0189
  have p0191 :=
    @g_sneq (syn_cec (.cv u) (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A))
  have p0192 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (.classEq (syn_cec (.cv u) (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A)))
      (.classEq (syn_csn (syn_cec (.cv u) (syn_chwniso A)))
        (syn_csn (syn_cec (.cv v) (syn_chwniso A))))
      p0190 p0191
  have p0193 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (.cv q) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))
      (syn_csn (syn_cec (.cv v) (syn_chwniso A))) p0056 p0192
  have p0213 := @g_hnordpw1repndv v A s dv_cache_0007 dv_cache_0003 dv_cache_0008
  have p0214 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
      (.classEq (.cv s) (syn_csn (syn_cec (.cv v) (syn_chwniso A)))) p0103 p0213
  have p0215 :=
    @g_eqcomd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (.cv s) (syn_csn (syn_cec (.cv v) (syn_chwniso A))) p0214
  have p0216 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s))))
      (.cv q) (syn_csn (syn_cec (.cv v) (syn_chwniso A))) (.cv s) p0193 p0215
  have p0217 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
          (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))))
      (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))
      (.classEq (.cv q) (.cv s)) p0216
  have p0218 :=
    @g_rexlimddv
      (syn_wa (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (.classEq (syn_cuni (.cv s)) (syn_cec (.cv v) (syn_chwniso A)))
      (.imp (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q))
          (syn_cfv (syn_chnsiquomap A) (.cv s))) (.classEq (.cv q) (.cv s)))
      v (syn_chwcn A) dv_cache_0010 dv_cache_0011 p0031 p0217
  have p0219 :=
    @g_rexlimddv
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (.classMem (.cv s) (syn_cpw1 (syn_chnord A))))
      (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))
      (.imp (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q))
          (syn_cfv (syn_chnsiquomap A) (.cv s))) (.classEq (.cv q) (.cv s)))
      u (syn_chwcn A) dv_cache_0012 dv_cache_0013 p0014 p0218
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

@[expose]
noncomputable def g_hnsiquomapf1ndv (A : Class)
    (hyp_hnsiquomapf1ndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (syn_wf1 (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A))) :=
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
  have dv_cache_0004 : s ∉ ((Wff.classMem (.cv q) (syn_cpw1 (syn_chnord A)))).fv :=
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
  have dv_cache_0005 : q ∉ ((syn_cpw1 (syn_chnord A))).fv :=
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
  have dv_cache_0006 : s ∉ ((syn_cpw1 (syn_chnord A))).fv :=
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
  have dv_cache_0007 : q ∉ ((syn_chnsiquomap A)).fv :=
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
  have dv_cache_0008 : s ∉ ((syn_chnsiquomap A)).fv :=
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
  have p0000 := @g_hnsiquomapfndv A hyp_hnsiquomapf1ndv_1
  have p0001 :=
    @g_hnsiquomapfvineqndv A s q dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_hnsiquomapf1ndv_1
  have p0002 :=
    @g_ex (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (.classMem (.cv s) (syn_cpw1 (syn_chnord A)))
      (.imp (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q))
          (syn_cfv (syn_chnsiquomap A) (.cv s))) (.classEq (.cv q) (.cv s)))
      p0001
  have p0003 :=
    @g_ralrimiv (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (.imp (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q))
          (syn_cfv (syn_chnsiquomap A) (.cv s))) (.classEq (.cv q) (.cv s)))
      s (syn_cpw1 (syn_chnord A)) dv_cache_0004 p0002
  have p0004 :=
    @g_rgen
      (syn_wral s (syn_cpw1 (syn_chnord A)) (.imp
          (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) (.cv s)))
          (.classEq (.cv q) (.cv s))))
      q (syn_cpw1 (syn_chnord A)) p0003
  have p0005 :=
    @g_pm3_2i
      (syn_wf (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A)))
      (syn_wral q (syn_cpw1 (syn_chnord A)) (syn_wral s (syn_cpw1 (syn_chnord A)) (.imp
            (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q))
              (syn_cfv (syn_chnsiquomap A) (.cv s))) (.classEq (.cv q) (.cv s)))))
      p0000 p0004
  have p0006 :=
    @g_dff13 q s (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A)) (syn_chnsiquomap A)
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0003
  have p0007_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wf1 (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A)))
        (syn_wa (syn_wf (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A)))
          (syn_wral q (syn_cpw1 (syn_chnord A)) (syn_wral s (syn_cpw1 (syn_chnord A)) (.imp
                (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q))
                  (syn_cfv (syn_chnsiquomap A) (.cv s))) (.classEq (.cv q) (.cv s))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wf1 syn_wa syn_wf syn_wfun syn_wss syn_cin syn_ccompl syn_cnin
          syn_wnan syn_ccom syn_copab syn_wex syn_ccnv syn_cid syn_chnsiquomap syn_cres
          syn_cpw1 syn_chnord syn_cqs syn_wrex syn_cec syn_cima syn_csn syn_chwcn
          syn_chwniso
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
    @g_mpbir
      (syn_wf1 (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A)))
      (syn_wa (syn_wf (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A)))
        (syn_wral q (syn_cpw1 (syn_chnord A)) (syn_wral s (syn_cpw1 (syn_chnord A)) (.imp
              (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q))
                (syn_cfv (syn_chnsiquomap A) (.cv s))) (.classEq (.cv q) (.cv s))))))
      p0005 p0007_e01_recanon
  exact p0007

@[expose]
noncomputable def g_hnsiquomapf1ondv (A : Class)
    (hyp_hnsiquomapf1ondv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (syn_wf1o (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A))) :=
  by
  have p0000 := @g_hnsiquomapf1ndv A hyp_hnsiquomapf1ondv_1
  have p0001 := @g_hnsiquomapfondv A hyp_hnsiquomapf1ondv_1
  have p0002 :=
    @g_pm3_2i
      (syn_wf1 (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A)))
      (syn_wfo (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A)))
      p0000 p0001
  have p0003 :=
    (Nominal.biimpRefl
      (syn_wf1o (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A))))
  have p0004 :=
    @g_mpbir
      (syn_wf1o (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A)))
      (syn_wa (syn_wf1 (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A)))
        (syn_wfo (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A))))
      p0002 p0003
  exact p0004

@[expose]
noncomputable def g_hnordpw1shiftenndv (A : Class)
    (hyp_hnordpw1shiftenndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (syn_wbr (syn_cpw1 (syn_chnord A)) (syn_cen) (syn_chnord (syn_cpw1 A))) :=
  by
  have p0000 := @g_hnsiquomapf1ondv A hyp_hnordpw1shiftenndv_1
  have p0001 := @g_hnsiquomapexgndv A
  have p0002 := Nominal.mp hyp_hnordpw1shiftenndv_1 p0001
  have p0003 :=
    @g_f1oen (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A)) (syn_chnsiquomap A) p0002
  have p0004 := Nominal.mp p0000 p0003
  exact p0004

@[expose]
noncomputable def g_hncardtcshiftndv (A : Class)
    (hyp_hncardtcshiftndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_ctc (syn_chncard A)) (syn_chncard (syn_cpw1 A))) :=
  by
  have p0000 := @g_hnordpw1shiftenndv A hyp_hncardtcshiftndv_1
  have p0001 := @g_hncardtcshiftcondndv A hyp_hncardtcshiftndv_1 p0000
  exact p0001

@[expose]
noncomputable def g_wppconcrete6fntc7hncard1valndv :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
        (syn_chncard (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))) :=
  by
  have p0000 := @g_n_1cex
  have p0001 := @g_hncardtcshiftndv (syn_c1c) p0000
  have p0002 := (Nominal.classEqRefl (syn_chncard (syn_cpw1 (syn_c1c))))
  have p0003 :=
    @g_eqtri (syn_ctc (syn_chncard (syn_c1c))) (syn_chncard (syn_cpw1 (syn_c1c)))
      (syn_cnc (syn_chnord (syn_cpw1 (syn_c1c)))) p0001 p0002
  have p0004 :=
    @g_tceq (syn_ctc (syn_chncard (syn_c1c))) (syn_cnc (syn_chnord (syn_cpw1 (syn_c1c))))
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @g_tceq (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))
      (syn_ctc (syn_cnc (syn_chnord (syn_cpw1 (syn_c1c)))))
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))
      (syn_ctc (syn_ctc (syn_cnc (syn_chnord (syn_cpw1 (syn_c1c))))))
  have p0009 := Nominal.mp p0007 p0008
  have p0010 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_chnord (syn_cpw1 (syn_c1c)))))))
  have p0011 := Nominal.mp p0009 p0010
  have p0012 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_chnord (syn_cpw1 (syn_c1c))))))))
  have p0013 := Nominal.mp p0011 p0012
  have p0014 :=
    @g_tceq
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
      (syn_ctc (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_chnord (syn_cpw1 (syn_c1c)))))))))
  have p0015 := Nominal.mp p0013 p0014
  have p0016 :=
    @g_fveq2i
      (syn_ctc (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (syn_ctc (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_chnord (syn_cpw1 (syn_c1c))))))))))
      (syn_cwppconcrete6fn) p0015
  have p0018 := @g_pw1ex (syn_c1c) p0000
  have p0019 := @g_hnordexg (syn_cpw1 (syn_c1c))
  have p0020 := Nominal.mp p0018 p0019
  have p0021 := @g_wppconcrete6fnvalndv (syn_chnord (syn_cpw1 (syn_c1c))) p0020
  have p0022 :=
    @g_eqtri
      (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
      (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_cnc (syn_chnord (syn_cpw1 (syn_c1c)))))))))))
      (syn_chncard (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))
      p0016 p0021
  exact p0022


end NFChoice.DirectNominalPrf.WPPReplay

end
