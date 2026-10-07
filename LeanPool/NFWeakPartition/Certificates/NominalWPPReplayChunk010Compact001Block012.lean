/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk010Compact001Block011

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk010Compact001Part034`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_phi011lem1`. -/
@[expose]
noncomputable def gPhi011lem1 (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (.classEq (synCun (synCphi A) (synCsn (synC0c)))
          (synCun (synCphi B) (synCsn (synC0c)))) (synWss (synCphi A) (synCphi B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : z ∉ ((synC0c)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((synCphi A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, fresh_z_not_A,
          not_false_eq_true])
  have dv_cache_0003 : z ∉ ((synCphi B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, fresh_z_not_B,
          not_false_eq_true])
  have dv_cache_0004 :
    z ∉
      ((Wff.classEq (synCun (synCphi A) (synCsn (synC0c)))
          (synCun (synCphi B) (synCsn (synC0c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          fresh_z_not_A, fresh_z_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @gSsun1 (synCphi A) (synCsn (synC0c))
  have p0001 :=
    @gSseli (synCphi A) (synCun (synCphi A) (synCsn (synC0c))) (.cv z) p0000
  have p0002 :=
    @gEleq2 (synCun (synCphi A) (synCsn (synC0c)))
      (synCun (synCphi B) (synCsn (synC0c))) (.cv z)
  have p0003 :=
    @gSyl5ib (.classMem (.cv z) (synCphi A))
      (.classMem (.cv z) (synCun (synCphi A) (synCsn (synC0c))))
      (.classEq (synCun (synCphi A) (synCsn (synC0c)))
        (synCun (synCphi B) (synCsn (synC0c))))
      (.classMem (.cv z) (synCun (synCphi B) (synCsn (synC0c)))) p0001 p0002
  have p0004 := @gN0cnelphi A
  have p0005 := @gEleq1 (.cv z) (synC0c) (synCphi A)
  have p0006 :=
    @gMtbiri (.classEq (.cv z) (synC0c)) (.classMem (.cv z) (synCphi A))
      (.classMem (synC0c) (synCphi A)) p0004 p0005
  have p0007 :=
    @gCon2i (.classEq (.cv z) (synC0c)) (.classMem (.cv z) (synCphi A)) p0006
  have p0008 :=
    @gA1i (.imp (.classMem (.cv z) (synCphi A)) (.neg (.classEq (.cv z) (synC0c))))
      (.classEq (synCun (synCphi A) (synCsn (synC0c)))
        (synCun (synCphi B) (synCsn (synC0c))))
      p0007
  have p0009 := @gElun (.cv z) (synCphi B) (synCsn (synC0c))
  have p0010 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSn z (synC0c)
      dv_cache_0001
  have p0011 := @gEqabri (.classEq (.cv z) (synC0c)) z (synCsn (synC0c)) p0010
  have p0012 :=
    @gOrbi2i (.classMem (.cv z) (synCsn (synC0c))) (.classEq (.cv z) (synC0c))
      (.classMem (.cv z) (synCphi B)) p0011
  have p0013 :=
    @gBitri (.classMem (.cv z) (synCun (synCphi B) (synCsn (synC0c))))
      (synWo (.classMem (.cv z) (synCphi B)) (.classMem (.cv z) (synCsn (synC0c))))
      (synWo (.classMem (.cv z) (synCphi B)) (.classEq (.cv z) (synC0c))) p0009 p0012
  have p0014 :=
    @gBiimpi (.classMem (.cv z) (synCun (synCphi B) (synCsn (synC0c))))
      (synWo (.classMem (.cv z) (synCphi B)) (.classEq (.cv z) (synC0c))) p0013
  have p0015 :=
    @gOrcomd (.classMem (.cv z) (synCun (synCphi B) (synCsn (synC0c))))
      (.classMem (.cv z) (synCphi B)) (.classEq (.cv z) (synC0c)) p0014
  have p0016 :=
    @gOrd (.classMem (.cv z) (synCun (synCphi B) (synCsn (synC0c))))
      (.classEq (.cv z) (synC0c)) (.classMem (.cv z) (synCphi B)) p0015
  have p0017 :=
    @gEe22
      (.classEq (synCun (synCphi A) (synCsn (synC0c)))
        (synCun (synCphi B) (synCsn (synC0c))))
      (.classMem (.cv z) (synCphi A))
      (.classMem (.cv z) (synCun (synCphi B) (synCsn (synC0c))))
      (.neg (.classEq (.cv z) (synC0c))) (.classMem (.cv z) (synCphi B)) p0003 p0008
      p0016
  have p0018 :=
    @gSsrdv
      (.classEq (synCun (synCphi A) (synCsn (synC0c)))
        (synCun (synCphi B) (synCsn (synC0c))))
      z (synCphi A) (synCphi B) dv_cache_0002 dv_cache_0003 dv_cache_0004 p0017
  exact p0018

/-- Checked nominal proof certificate identified upstream as `g_phi011`. -/
@[expose]
noncomputable def gPhi011 (A : Class) (B : Class) :
    Nominal.NPrf
      (synWb (.classEq A B) (.classEq (synCun (synCphi A) (synCsn (synC0c)))
          (synCun (synCphi B) (synCsn (synC0c))))) :=
  by
  have p0000 := @gPhi11 A B
  have p0001 := @gUneq1 (synCphi A) (synCphi B) (synCsn (synC0c))
  have p0002 := @gPhi011lem1 A B
  have p0003 := @gPhi011lem1 B A
  have p0004 :=
    @gEqcoms (synWss (synCphi B) (synCphi A))
      (synCun (synCphi B) (synCsn (synC0c)))
      (synCun (synCphi A) (synCsn (synC0c))) p0003
  have p0005 :=
    @gEqssd
      (.classEq (synCun (synCphi A) (synCsn (synC0c)))
        (synCun (synCphi B) (synCsn (synC0c))))
      (synCphi A) (synCphi B) p0002 p0004
  have p0006 :=
    @gImpbii (.classEq (synCphi A) (synCphi B))
      (.classEq (synCun (synCphi A) (synCsn (synC0c)))
        (synCun (synCphi B) (synCsn (synC0c))))
      p0001 p0005
  have p0007 :=
    @gBitri (.classEq A B) (.classEq (synCphi A) (synCphi B))
      (.classEq (synCun (synCphi A) (synCsn (synC0c)))
        (synCun (synCphi B) (synCsn (synC0c))))
      p0000 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_proj1op`. -/
@[expose]
noncomputable def gProj1op (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (synCproj1 (synCop A B)) A) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let z : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_ne_x : z ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
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
  have dv_cache_0003 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 : y ∉ ((Wff.classEq (.cv x) (synCphi (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_z, or_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_z, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((synCphi (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_z,
          not_false_eq_true])
  have dv_cache_0009 : x ∉ ((Wff.classMem (.cv z) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, fresh_x_not_A, or_false, not_false_eq_true])
  have dv_cache_0010 :
    x ∉
      ((synWrex y B (.classEq (synCphi (.cv z))
            (synCun (synCphi (.cv y)) (synCsn (synC0c)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_not_B, fresh_x_ne_z,
          fresh_x_ne_y, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((synCop A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_z, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((Wff.classMem (synCphi (.cv z)) (synCop A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, fresh_x_not_A, fresh_x_not_B, or_false,
          not_false_eq_true])
  have dv_cache_0014 : z ∉ ((synCproj1 (synCop A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_z_not_A, fresh_z_not_B, or_false, not_false_eq_true])
  have dv_cache_0015 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOp x y A B
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @gEleq2i (synCop A B)
      (synCun (.cab x (synWrex y A (.classEq (.cv x) (synCphi (.cv y))))) (.cab x
          (synWrex y B (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))))
      (synCphi (.cv z)) p0000
  have p0002 :=
    @gElun (synCphi (.cv z))
      (.cab x (synWrex y A (.classEq (.cv x) (synCphi (.cv y)))))
      (.cab x (synWrex y B
          (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))))
  have p0003 := @gVex z
  have p0004 := @gPhiex (.cv z) p0003
  have p0005 := @gEqeq1 (.cv x) (synCphi (.cv z)) (synCphi (.cv y))
  have p0006 := @gPhi11 (.cv z) (.cv y)
  have p0007 := @gEqucom z y
  have p0008_e00_recanon :
    Nominal.NPrf (synWb (.objEq z y) (.classEq (synCphi (.cv z)) (synCphi (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCphi synWrex synWex synWa synCif synWo synCnnc synCint
          synCplc synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0006
  have p0008 :=
    @gBitr3i (.classEq (synCphi (.cv z)) (synCphi (.cv y))) (.objEq z y) (.objEq y z)
      p0008_e00_recanon p0007
  have p0009 :=
    @gSyl6bb (.classEq (.cv x) (synCphi (.cv z))) (.classEq (.cv x) (synCphi (.cv y)))
      (.classEq (synCphi (.cv z)) (synCphi (.cv y))) (.objEq y z) p0005 p0008
  have p0010 :=
    @gRexbidv (.classEq (.cv x) (synCphi (.cv z))) (.classEq (.cv x) (synCphi (.cv y)))
      (.objEq y z) y A dv_cache_0006 p0009
  have p0011 := @gRisset y (.cv z) A dv_cache_0007 dv_cache_0002
  have p0012_e01_recanon :
    Nominal.NPrf (synWb (.classMem (.cv z) A) (synWrex y A (.objEq y z))) :=
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
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0011
  have p0012 :=
    @gSyl6bbr (.classEq (.cv x) (synCphi (.cv z)))
      (synWrex y A (.classEq (.cv x) (synCphi (.cv y)))) (synWrex y A (.objEq y z))
      (.classMem (.cv z) A) p0010 p0012_e01_recanon
  have p0013 :=
    @gElab (synWrex y A (.classEq (.cv x) (synCphi (.cv y)))) (.classMem (.cv z) A) x
      (synCphi (.cv z)) dv_cache_0008 dv_cache_0009 p0004 p0012
  have p0014 :=
    @gEqeq1 (.cv x) (synCphi (.cv z)) (synCun (synCphi (.cv y)) (synCsn (synC0c)))
  have p0015 :=
    @gRexbidv (.classEq (.cv x) (synCphi (.cv z)))
      (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))
      (.classEq (synCphi (.cv z)) (synCun (synCphi (.cv y)) (synCsn (synC0c)))) y B
      dv_cache_0006 p0014
  have p0016 :=
    @gElab
      (synWrex y B (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))
      (synWrex y B
        (.classEq (synCphi (.cv z)) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))
      x (synCphi (.cv z)) dv_cache_0008 dv_cache_0010 p0004 p0015
  have p0017 :=
    @gOrbi12i
      (.classMem (synCphi (.cv z))
        (.cab x (synWrex y A (.classEq (.cv x) (synCphi (.cv y))))))
      (.classMem (.cv z) A)
      (.classMem (synCphi (.cv z)) (.cab x (synWrex y B
            (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))))
      (synWrex y B
        (.classEq (synCphi (.cv z)) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))
      p0013 p0016
  have p0018 :=
    @gN3bitri (.classMem (synCphi (.cv z)) (synCop A B))
      (.classMem (synCphi (.cv z))
        (synCun (.cab x (synWrex y A (.classEq (.cv x) (synCphi (.cv y))))) (.cab x
            (synWrex y B
              (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))))))
      (synWo (.classMem (synCphi (.cv z))
          (.cab x (synWrex y A (.classEq (.cv x) (synCphi (.cv y))))))
        (.classMem (synCphi (.cv z)) (.cab x (synWrex y B
              (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))))))
      (synWo (.classMem (.cv z) A) (synWrex y B
          (.classEq (synCphi (.cv z)) (synCun (synCphi (.cv y)) (synCsn (synC0c))))))
      p0001 p0002 p0017
  have p0019 := @gPhieq (.cv x) (.cv z)
  have p0020_e00_recanon :
    Nominal.NPrf (.imp (.objEq x z) (.classEq (synCphi (.cv x)) (synCphi (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCphi synWrex synWex synWa synCif synWo synCnnc synCint synCplc
          synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0019
  have p0020 :=
    @gEleq1d (.objEq x z) (synCphi (.cv x)) (synCphi (.cv z)) (synCop A B)
      p0020_e00_recanon
  have p0021 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfProj1 x
      (synCop A B) dv_cache_0011
  have p0022_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (.cv z)) (synWb (.classMem (synCphi (.cv x)) (synCop A B))
          (.classMem (synCphi (.cv z)) (synCop A B)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCphi synWrex synWex synWa synCif synWo synCnnc synCint
          synCplc synC1c synCop synCun synCnin synWnan synCcompl
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0020
  have p0022 :=
    @gElab2 (.classMem (synCphi (.cv x)) (synCop A B))
      (.classMem (synCphi (.cv z)) (synCop A B)) x (.cv z) (synCproj1 (synCop A B))
      dv_cache_0012 dv_cache_0013 p0003 p0022_e01_recanon p0021
  have p0023 := @gN0cnelphi (.cv z)
  have p0024 := @gSsun2 (synCsn (synC0c)) (synCphi (.cv y))
  have p0025 := @gN0cex
  have p0026 := @gSnid (synC0c) p0025
  have p0027 :=
    @gSselii (synCsn (synC0c)) (synCun (synCphi (.cv y)) (synCsn (synC0c)))
      (synC0c) p0024 p0026
  have p0028 :=
    @gEleq2 (synCphi (.cv z)) (synCun (synCphi (.cv y)) (synCsn (synC0c))) (synC0c)
  have p0029 :=
    @gMpbiri
      (.classEq (synCphi (.cv z)) (synCun (synCphi (.cv y)) (synCsn (synC0c))))
      (.classMem (synC0c) (synCphi (.cv z)))
      (.classMem (synC0c) (synCun (synCphi (.cv y)) (synCsn (synC0c)))) p0027 p0028
  have p0030 :=
    @gMto (.classEq (synCphi (.cv z)) (synCun (synCphi (.cv y)) (synCsn (synC0c))))
      (.classMem (synC0c) (synCphi (.cv z))) p0023 p0029
  have p0031 :=
    @gA1i
      (.neg (.classEq (synCphi (.cv z)) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))
      (.classMem (.cv y) B) p0030
  have p0032 :=
    @gNrex (.classEq (synCphi (.cv z)) (synCun (synCphi (.cv y)) (synCsn (synC0c))))
      y B p0031
  have p0033 :=
    @gBiorfi
      (synWrex y B
        (.classEq (synCphi (.cv z)) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))
      (.classMem (.cv z) A) p0032
  have p0034 :=
    @gN3bitr4i (.classMem (synCphi (.cv z)) (synCop A B))
      (synWo (.classMem (.cv z) A) (synWrex y B
          (.classEq (synCphi (.cv z)) (synCun (synCphi (.cv y)) (synCsn (synC0c))))))
      (.classMem (.cv z) (synCproj1 (synCop A B))) (.classMem (.cv z) A) p0018 p0022
      p0033
  have p0035 := @gEqriv z (synCproj1 (synCop A B)) A dv_cache_0014 dv_cache_0015 p0034
  exact p0035

/-- Checked nominal proof certificate identified upstream as `g_proj2op`. -/
@[expose]
noncomputable def gProj2op (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (synCproj2 (synCop A B)) B) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let z : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_ne_x : z ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
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
  have dv_cache_0003 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 :
    y ∉ ((Wff.classEq (.cv x) (synCun (synCphi (.cv z)) (synCsn (synC0c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_z, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((synCun (synCphi (.cv z)) (synCsn (synC0c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0008 :
    x ∉
      ((synWrex y A (.classEq (synCun (synCphi (.cv z)) (synCsn (synC0c)))
            (synCphi (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_z,
          fresh_x_ne_y, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0009 :
    x ∉
      ((synWrex y B (.classEq (synCun (synCphi (.cv z)) (synCsn (synC0c)))
            (synCun (synCphi (.cv y)) (synCsn (synC0c)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_not_B, fresh_x_ne_z,
          fresh_x_ne_y, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_z, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((synCop A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_z, not_false_eq_true])
  have dv_cache_0013 :
    x ∉
      ((Wff.classMem (synCun (synCphi (.cv z)) (synCsn (synC0c))) (synCop A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, fresh_x_not_A, fresh_x_not_B,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0014 : z ∉ ((synCproj2 (synCop A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_z_not_A, fresh_z_not_B, or_false, not_false_eq_true])
  have dv_cache_0015 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_B, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOp x y A B
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @gEleq2i (synCop A B)
      (synCun (.cab x (synWrex y A (.classEq (.cv x) (synCphi (.cv y))))) (.cab x
          (synWrex y B (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))))
      (synCun (synCphi (.cv z)) (synCsn (synC0c))) p0000
  have p0002 :=
    @gElun (synCun (synCphi (.cv z)) (synCsn (synC0c)))
      (.cab x (synWrex y A (.classEq (.cv x) (synCphi (.cv y)))))
      (.cab x (synWrex y B
          (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))))
  have p0003 := @gVex z
  have p0004 := @gPhiex (.cv z) p0003
  have p0005 := @gSnex (synC0c)
  have p0006 := @gUnex (synCphi (.cv z)) (synCsn (synC0c)) p0004 p0005
  have p0007 :=
    @gEqeq1 (.cv x) (synCun (synCphi (.cv z)) (synCsn (synC0c))) (synCphi (.cv y))
  have p0008 :=
    @gRexbidv (.classEq (.cv x) (synCun (synCphi (.cv z)) (synCsn (synC0c))))
      (.classEq (.cv x) (synCphi (.cv y)))
      (.classEq (synCun (synCphi (.cv z)) (synCsn (synC0c))) (synCphi (.cv y))) y A
      dv_cache_0006 p0007
  have p0009 :=
    @gElab (synWrex y A (.classEq (.cv x) (synCphi (.cv y))))
      (synWrex y A
        (.classEq (synCun (synCphi (.cv z)) (synCsn (synC0c))) (synCphi (.cv y))))
      x (synCun (synCphi (.cv z)) (synCsn (synC0c))) dv_cache_0007 dv_cache_0008 p0006
      p0008
  have p0010 := @gPhi011 (.cv z) (.cv y)
  have p0011 := @gEqucom z y
  have p0012_e00_recanon :
    Nominal.NPrf
      (synWb (.objEq z y) (.classEq (synCun (synCphi (.cv z)) (synCsn (synC0c)))
          (synCun (synCphi (.cv y)) (synCsn (synC0c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCun synCnin synWnan synWa synCcompl synCphi synWrex
          synWex synCif synWo synCnnc synCint synCplc synC1c synCsn synC0c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0010
  have p0012 :=
    @gBitr3i
      (.classEq (synCun (synCphi (.cv z)) (synCsn (synC0c)))
        (synCun (synCphi (.cv y)) (synCsn (synC0c))))
      (.objEq z y) (.objEq y z) p0012_e00_recanon p0011
  have p0013 :=
    @gRexbii
      (.classEq (synCun (synCphi (.cv z)) (synCsn (synC0c)))
        (synCun (synCphi (.cv y)) (synCsn (synC0c))))
      (.objEq y z) y B p0012
  have p0014 :=
    @gEqeq1 (.cv x) (synCun (synCphi (.cv z)) (synCsn (synC0c)))
      (synCun (synCphi (.cv y)) (synCsn (synC0c)))
  have p0015 :=
    @gRexbidv (.classEq (.cv x) (synCun (synCphi (.cv z)) (synCsn (synC0c))))
      (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))
      (.classEq (synCun (synCphi (.cv z)) (synCsn (synC0c)))
        (synCun (synCphi (.cv y)) (synCsn (synC0c))))
      y B dv_cache_0006 p0014
  have p0016 :=
    @gElab
      (synWrex y B (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))
      (synWrex y B (.classEq (synCun (synCphi (.cv z)) (synCsn (synC0c)))
          (synCun (synCphi (.cv y)) (synCsn (synC0c)))))
      x (synCun (synCphi (.cv z)) (synCsn (synC0c))) dv_cache_0007 dv_cache_0009 p0006
      p0015
  have p0017 := @gRisset y (.cv z) B dv_cache_0010 dv_cache_0004
  have p0018_e02_recanon :
    Nominal.NPrf (synWb (.classMem (.cv z) B) (synWrex y B (.objEq y z))) :=
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
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0017
  have p0018 :=
    @gN3bitr4i
      (synWrex y B (.classEq (synCun (synCphi (.cv z)) (synCsn (synC0c)))
          (synCun (synCphi (.cv y)) (synCsn (synC0c)))))
      (synWrex y B (.objEq y z))
      (.classMem (synCun (synCphi (.cv z)) (synCsn (synC0c))) (.cab x (synWrex y B
            (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))))
      (.classMem (.cv z) B) p0013 p0016 p0018_e02_recanon
  have p0019 :=
    @gOrbi12i
      (.classMem (synCun (synCphi (.cv z)) (synCsn (synC0c)))
        (.cab x (synWrex y A (.classEq (.cv x) (synCphi (.cv y))))))
      (synWrex y A
        (.classEq (synCun (synCphi (.cv z)) (synCsn (synC0c))) (synCphi (.cv y))))
      (.classMem (synCun (synCphi (.cv z)) (synCsn (synC0c))) (.cab x (synWrex y B
            (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))))
      (.classMem (.cv z) B) p0009 p0018
  have p0020 :=
    @gBitri
      (.classMem (synCun (synCphi (.cv z)) (synCsn (synC0c)))
        (synCun (.cab x (synWrex y A (.classEq (.cv x) (synCphi (.cv y))))) (.cab x
            (synWrex y B
              (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))))))
      (synWo (.classMem (synCun (synCphi (.cv z)) (synCsn (synC0c)))
          (.cab x (synWrex y A (.classEq (.cv x) (synCphi (.cv y))))))
        (.classMem (synCun (synCphi (.cv z)) (synCsn (synC0c))) (.cab x (synWrex y B
              (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))))))
      (synWo (synWrex y A
          (.classEq (synCun (synCphi (.cv z)) (synCsn (synC0c))) (synCphi (.cv y))))
        (.classMem (.cv z) B))
      p0002 p0019
  have p0021 :=
    @gBitri (.classMem (synCun (synCphi (.cv z)) (synCsn (synC0c))) (synCop A B))
      (.classMem (synCun (synCphi (.cv z)) (synCsn (synC0c)))
        (synCun (.cab x (synWrex y A (.classEq (.cv x) (synCphi (.cv y))))) (.cab x
            (synWrex y B
              (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))))))
      (synWo (synWrex y A
          (.classEq (synCun (synCphi (.cv z)) (synCsn (synC0c))) (synCphi (.cv y))))
        (.classMem (.cv z) B))
      p0001 p0020
  have p0022 := @gPhieq (.cv x) (.cv z)
  have p0023_e00_recanon :
    Nominal.NPrf (.imp (.objEq x z) (.classEq (synCphi (.cv x)) (synCphi (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCphi synWrex synWex synWa synCif synWo synCnnc synCint synCplc
          synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0022
  have p0023 :=
    @gUneq1d (.objEq x z) (synCphi (.cv x)) (synCphi (.cv z)) (synCsn (synC0c))
      p0023_e00_recanon
  have p0024 :=
    @gEleq1d (.objEq x z) (synCun (synCphi (.cv x)) (synCsn (synC0c)))
      (synCun (synCphi (.cv z)) (synCsn (synC0c))) (synCop A B) p0023
  have p0025 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfProj2 x
      (synCop A B) dv_cache_0011
  have p0026_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (.cv z))
        (synWb (.classMem (synCun (synCphi (.cv x)) (synCsn (synC0c))) (synCop A B))
          (.classMem (synCun (synCphi (.cv z)) (synCsn (synC0c))) (synCop A B)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCun synCnin synWnan synWa synCcompl synCphi synWrex
          synWex synCif synWo synCnnc synCint synCplc synC1c synCsn synC0c
          synCop
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0024
  have p0026 :=
    @gElab2 (.classMem (synCun (synCphi (.cv x)) (synCsn (synC0c))) (synCop A B))
      (.classMem (synCun (synCphi (.cv z)) (synCsn (synC0c))) (synCop A B)) x (.cv z)
      (synCproj2 (synCop A B)) dv_cache_0012 dv_cache_0013 p0003 p0026_e01_recanon p0025
  have p0027 := @gN0cnelphi (.cv y)
  have p0028 := @gSsun2 (synCsn (synC0c)) (synCphi (.cv z))
  have p0029 := @gN0cex
  have p0030 := @gSnid (synC0c) p0029
  have p0031 :=
    @gSselii (synCsn (synC0c)) (synCun (synCphi (.cv z)) (synCsn (synC0c)))
      (synC0c) p0028 p0030
  have p0032 :=
    @gEleq2 (synCun (synCphi (.cv z)) (synCsn (synC0c))) (synCphi (.cv y)) (synC0c)
  have p0033 :=
    @gMpbii
      (.classEq (synCun (synCphi (.cv z)) (synCsn (synC0c))) (synCphi (.cv y)))
      (.classMem (synC0c) (synCun (synCphi (.cv z)) (synCsn (synC0c))))
      (.classMem (synC0c) (synCphi (.cv y))) p0031 p0032
  have p0034 :=
    @gMto (.classEq (synCun (synCphi (.cv z)) (synCsn (synC0c))) (synCphi (.cv y)))
      (.classMem (synC0c) (synCphi (.cv y))) p0027 p0033
  have p0035 :=
    @gA1i
      (.neg (.classEq (synCun (synCphi (.cv z)) (synCsn (synC0c))) (synCphi (.cv y))))
      (.classMem (.cv y) A) p0034
  have p0036 :=
    @gNrex (.classEq (synCun (synCphi (.cv z)) (synCsn (synC0c))) (synCphi (.cv y)))
      y A p0035
  have p0037 :=
    @gBiorfi
      (synWrex y A
        (.classEq (synCun (synCphi (.cv z)) (synCsn (synC0c))) (synCphi (.cv y))))
      (.classMem (.cv z) B) p0036
  have p0038 :=
    @gOrcom (.classMem (.cv z) B)
      (synWrex y A
        (.classEq (synCun (synCphi (.cv z)) (synCsn (synC0c))) (synCphi (.cv y))))
  have p0039 :=
    @gBitri (.classMem (.cv z) B)
      (synWo (.classMem (.cv z) B) (synWrex y A
          (.classEq (synCun (synCphi (.cv z)) (synCsn (synC0c))) (synCphi (.cv y)))))
      (synWo (synWrex y A
          (.classEq (synCun (synCphi (.cv z)) (synCsn (synC0c))) (synCphi (.cv y))))
        (.classMem (.cv z) B))
      p0037 p0038
  have p0040 :=
    @gN3bitr4i
      (.classMem (synCun (synCphi (.cv z)) (synCsn (synC0c))) (synCop A B))
      (synWo (synWrex y A
          (.classEq (synCun (synCphi (.cv z)) (synCsn (synC0c))) (synCphi (.cv y))))
        (.classMem (.cv z) B))
      (.classMem (.cv z) (synCproj2 (synCop A B))) (.classMem (.cv z) B) p0021 p0026
      p0039
  have p0041 := @gEqriv z (synCproj2 (synCop A B)) B dv_cache_0014 dv_cache_0015 p0040
  exact p0041

/-- Checked nominal proof certificate identified upstream as `g_opth`. -/
@[expose]
noncomputable def gOpth (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (synWb (.classEq (synCop A B) (synCop C D)) (synWa (.classEq A C) (.classEq B D))) :=
  by
  have p0000 := @gProj1eq (synCop A B) (synCop C D)
  have p0001 := @gProj1op A B
  have p0002 := @gProj1op C D
  have p0003 :=
    @gN3eqtr3g (.classEq (synCop A B) (synCop C D)) (synCproj1 (synCop A B))
      (synCproj1 (synCop C D)) A C p0000 p0001 p0002
  have p0004 := @gProj2eq (synCop A B) (synCop C D)
  have p0005 := @gProj2op A B
  have p0006 := @gProj2op C D
  have p0007 :=
    @gN3eqtr3g (.classEq (synCop A B) (synCop C D)) (synCproj2 (synCop A B))
      (synCproj2 (synCop C D)) B D p0004 p0005 p0006
  have p0008 :=
    @gJca (.classEq (synCop A B) (synCop C D)) (.classEq A C) (.classEq B D) p0003
      p0007
  have p0009 := @gOpeq12 A C B D
  have p0010 :=
    @gImpbii (.classEq (synCop A B) (synCop C D))
      (synWa (.classEq A C) (.classEq B D)) p0008 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_opexb`. -/
@[expose]
noncomputable def gOpexb (A : Class) (B : Class) :
    Nominal.NPrf
      (synWb (.classMem (synCop A B) (synCvv))
        (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))) :=
  by
  have p0000 := @gProj1op A B
  have p0001 := @gProj1exg (synCop A B) (synCvv)
  have p0002 :=
    @gSyl5eqelr (.classMem (synCop A B) (synCvv)) A (synCproj1 (synCop A B))
      (synCvv) p0000 p0001
  have p0003 := @gProj2op A B
  have p0004 := @gProj2exg (synCop A B) (synCvv)
  have p0005 :=
    @gSyl5eqelr (.classMem (synCop A B) (synCvv)) B (synCproj2 (synCop A B))
      (synCvv) p0003 p0004
  have p0006 :=
    @gJca (.classMem (synCop A B) (synCvv)) (.classMem A (synCvv))
      (.classMem B (synCvv)) p0002 p0005
  have p0007 := @gOpexg A B (synCvv) (synCvv)
  have p0008 :=
    @gImpbii (.classMem (synCop A B) (synCvv))
      (synWa (.classMem A (synCvv)) (.classMem B (synCvv))) p0006 p0007
  exact p0008


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part035`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_nfop`. -/
@[expose]
noncomputable def gNfop (x : Var) (A : Class) (B : Class)
    (hyp_nfop_1 : Nominal.NPrf (synWnfc x A))
    (hyp_nfop_2 : Nominal.NPrf (synWnfc x B)) :
    Nominal.NPrf (synWnfc x (synCop A B)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : z ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0002 : w ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_A, not_false_eq_true])
  have dv_cache_0003 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0004 : w ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_B, not_false_eq_true])
  have dv_cache_0005 : z ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have dv_cache_0006 : x ∉ ((Wff.classEq (.cv z) (synCphi (.cv w)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, fresh_x_ne_w, or_false, not_false_eq_true])
  have dv_cache_0007 :
    x ∉ ((Wff.classEq (.cv z) (synCun (synCphi (.cv w)) (synCsn (synC0c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, fresh_x_ne_w, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOp z w A B
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 := @gNfv (.classEq (.cv z) (synCphi (.cv w))) x dv_cache_0006
  have p0002 := @gNfrex (.classEq (.cv z) (synCphi (.cv w))) x w A hyp_nfop_1 p0001
  have p0003 := @gNfab (synWrex w A (.classEq (.cv z) (synCphi (.cv w)))) x z p0002
  have p0004 :=
    @gNfv (.classEq (.cv z) (synCun (synCphi (.cv w)) (synCsn (synC0c)))) x
      dv_cache_0007
  have p0005 :=
    @gNfrex (.classEq (.cv z) (synCun (synCphi (.cv w)) (synCsn (synC0c)))) x w B
      hyp_nfop_2 p0004
  have p0006 :=
    @gNfab
      (synWrex w B (.classEq (.cv z) (synCun (synCphi (.cv w)) (synCsn (synC0c))))) x
      z p0005
  have p0007 :=
    @gNfun x (.cab z (synWrex w A (.classEq (.cv z) (synCphi (.cv w)))))
      (.cab z (synWrex w B
          (.classEq (.cv z) (synCun (synCphi (.cv w)) (synCsn (synC0c))))))
      p0003 p0006
  have p0008 :=
    @gNfcxfr x (synCop A B)
      (synCun (.cab z (synWrex w A (.classEq (.cv z) (synCphi (.cv w))))) (.cab z
          (synWrex w B (.classEq (.cv z) (synCun (synCphi (.cv w)) (synCsn (synC0c)))))))
      p0000 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_nfopd`. -/
@[expose]
noncomputable def gNfopd (ph : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_nfopd_1 : Nominal.NPrf (.imp ph (synWnfc x A)))
    (hyp_nfopd_2 : Nominal.NPrf (.imp ph (synWnfc x B))) :
    Nominal.NPrf (.imp ph (synWnfc x (synCop A B))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
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
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : z ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0002 : x ≠ z := by
    clear dv_cache_0001
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0003 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_B, not_false_eq_true])
  have p0000 := @gNfaba1 (.classMem (.cv z) A) x z
  have p0001 := @gNfaba1 (.classMem (.cv z) B) x z
  have p0002 :=
    @gNfop x (.cab z (.all x (.classMem (.cv z) A)))
      (.cab z (.all x (.classMem (.cv z) B))) p0000 p0001
  have p0003 := @gNfnfc1 x A
  have p0004 := @gNfnfc1 x B
  have p0005 := @gNfan (synWnfc x A) (synWnfc x B) x p0003 p0004
  have p0006 := @gAbidnf x z A dv_cache_0001 dv_cache_0002
  have p0007 :=
    @gAdantr (synWnfc x A) (.classEq (.cab z (.all x (.classMem (.cv z) A))) A)
      (synWnfc x B) p0006
  have p0008 := @gAbidnf x z B dv_cache_0003 dv_cache_0002
  have p0009 :=
    @gAdantl (synWnfc x B) (.classEq (.cab z (.all x (.classMem (.cv z) B))) B)
      (synWnfc x A) p0008
  have p0010 :=
    @gOpeq12d (synWa (synWnfc x A) (synWnfc x B))
      (.cab z (.all x (.classMem (.cv z) A))) A (.cab z (.all x (.classMem (.cv z) B))) B
      p0007 p0009
  have p0011 :=
    @gNfceqdf (synWa (synWnfc x A) (synWnfc x B)) x
      (synCop (.cab z (.all x (.classMem (.cv z) A))) (.cab z (.all x (.classMem (.cv z) B))))
      (synCop A B) p0005 p0010
  have p0012 :=
    @gSyl2anc ph (synWnfc x A) (synWnfc x B)
      (synWb (synWnfc x (synCop (.cab z (.all x (.classMem (.cv z) A)))
            (.cab z (.all x (.classMem (.cv z) B))))) (synWnfc x (synCop A B)))
      hyp_nfopd_1 hyp_nfopd_2 p0011
  have p0013 :=
    @gMpbii ph
      (synWnfc x (synCop (.cab z (.all x (.classMem (.cv z) A)))
          (.cab z (.all x (.classMem (.cv z) B)))))
      (synWnfc x (synCop A B)) p0002 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_eqvinop`. -/
@[expose]
noncomputable def gEqvinop (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_x_y : x ≠ y)
    (hyp_eqvinop_1 : Nominal.NPrf (.classMem B (synCvv)))
    (hyp_eqvinop_2 : Nominal.NPrf (.classMem C (synCvv))) :
    Nominal.NPrf
      (synWb (.classEq A (synCop B C)) (synWex x (synWex y
            (synWa (.classEq A (synCop (.cv x) (.cv y)))
              (.classEq (synCop (.cv x) (.cv y)) (synCop B C)))))) :=
  by
  have dv_cache_0001 : y ∉ ((Wff.classEq (.cv x) B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_y), dv_B_y, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (C).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_y, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classEq A (synCop (.cv x) C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_A_y, (Ne.symm dv_x_y), dv_C_y, or_false,
          not_false_eq_true])
  have dv_cache_0004 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classEq A (synCop B C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, dv_A_x,
          dv_B_x, dv_C_x, or_false, not_false_eq_true])
  have p0000 := @gOpth (.cv x) (.cv y) B C
  have p0001 := @gAncom (.classEq (.cv x) B) (.classEq (.cv y) C)
  have p0002 :=
    @gBitri (.classEq (synCop (.cv x) (.cv y)) (synCop B C))
      (synWa (.classEq (.cv x) B) (.classEq (.cv y) C))
      (synWa (.classEq (.cv y) C) (.classEq (.cv x) B)) p0000 p0001
  have p0003 :=
    @gAnbi2i (.classEq (synCop (.cv x) (.cv y)) (synCop B C))
      (synWa (.classEq (.cv y) C) (.classEq (.cv x) B))
      (.classEq A (synCop (.cv x) (.cv y))) p0002
  have p0004 :=
    @gAn13 (.classEq A (synCop (.cv x) (.cv y))) (.classEq (.cv y) C)
      (.classEq (.cv x) B)
  have p0005 :=
    @gBitri
      (synWa (.classEq A (synCop (.cv x) (.cv y)))
        (.classEq (synCop (.cv x) (.cv y)) (synCop B C)))
      (synWa (.classEq A (synCop (.cv x) (.cv y)))
        (synWa (.classEq (.cv y) C) (.classEq (.cv x) B)))
      (synWa (.classEq (.cv x) B)
        (synWa (.classEq (.cv y) C) (.classEq A (synCop (.cv x) (.cv y)))))
      p0003 p0004
  have p0006 :=
    @gExbii
      (synWa (.classEq A (synCop (.cv x) (.cv y)))
        (.classEq (synCop (.cv x) (.cv y)) (synCop B C)))
      (synWa (.classEq (.cv x) B)
        (synWa (.classEq (.cv y) C) (.classEq A (synCop (.cv x) (.cv y)))))
      y p0005
  have p0007 :=
    @gN1942v (.classEq (.cv x) B)
      (synWa (.classEq (.cv y) C) (.classEq A (synCop (.cv x) (.cv y)))) y dv_cache_0001
  have p0008 := @gOpeq2 (.cv y) C (.cv x)
  have p0009 :=
    @gEqeq2d (.classEq (.cv y) C) (synCop (.cv x) (.cv y)) (synCop (.cv x) C) A p0008
  have p0010 :=
    @gCeqsexv (.classEq A (synCop (.cv x) (.cv y))) (.classEq A (synCop (.cv x) C)) y C
      dv_cache_0002 dv_cache_0003 hyp_eqvinop_2 p0009
  have p0011 :=
    @gAnbi2i
      (synWex y (synWa (.classEq (.cv y) C) (.classEq A (synCop (.cv x) (.cv y)))))
      (.classEq A (synCop (.cv x) C)) (.classEq (.cv x) B) p0010
  have p0012 :=
    @gN3bitri
      (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y)))
          (.classEq (synCop (.cv x) (.cv y)) (synCop B C))))
      (synWex y (synWa (.classEq (.cv x) B)
          (synWa (.classEq (.cv y) C) (.classEq A (synCop (.cv x) (.cv y))))))
      (synWa (.classEq (.cv x) B)
        (synWex y (synWa (.classEq (.cv y) C) (.classEq A (synCop (.cv x) (.cv y))))))
      (synWa (.classEq (.cv x) B) (.classEq A (synCop (.cv x) C))) p0006 p0007 p0011
  have p0013 :=
    @gExbii
      (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y)))
          (.classEq (synCop (.cv x) (.cv y)) (synCop B C))))
      (synWa (.classEq (.cv x) B) (.classEq A (synCop (.cv x) C))) x p0012
  have p0014 := @gOpeq1 (.cv x) B C
  have p0015 := @gEqeq2d (.classEq (.cv x) B) (synCop (.cv x) C) (synCop B C) A p0014
  have p0016 :=
    @gCeqsexv (.classEq A (synCop (.cv x) C)) (.classEq A (synCop B C)) x B
      dv_cache_0004 dv_cache_0005 hyp_eqvinop_1 p0015
  have p0017 :=
    @gBitr2i
      (synWex x (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y)))
            (.classEq (synCop (.cv x) (.cv y)) (synCop B C)))))
      (synWex x (synWa (.classEq (.cv x) B) (.classEq A (synCop (.cv x) C))))
      (.classEq A (synCop B C)) p0013 p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_copsexg`. -/
@[expose]
noncomputable def gCopsexg (ph : Wff) (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classEq A (synCop (.cv x) (.cv y))) (synWb ph
          (synWex x (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y))) ph))))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : z ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0002 : w ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_A, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0004 : w ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_x, not_false_eq_true])
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
  have dv_cache_0006 : w ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_y, not_false_eq_true])
  have dv_cache_0007 : z ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have dv_cache_0008 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0009 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0010 : y ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show y ≠ w from (by exact fresh_y_ne_w))
  have dv_cache_0011 : x ∉ ((Wff.classEq A (synCop (.cv z) (.cv w)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_A_x, fresh_x_ne_z, fresh_x_ne_w, or_false,
          not_false_eq_true])
  have dv_cache_0012 : y ∉ ((Wff.classEq A (synCop (.cv z) (.cv w)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_A_y, fresh_y_ne_z, fresh_y_ne_w, or_false,
          not_false_eq_true])
  have dv_cache_0013 :
    z ∉
      ((Wff.imp (.classEq A (synCop (.cv x) (.cv y))) (synWb ph (synWex x
              (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y))) ph)))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_x,
          fresh_z_ne_y, fresh_z_not_ph, or_false, and_false, not_false_eq_true])
  have dv_cache_0014 :
    w ∉
      ((Wff.imp (.classEq A (synCop (.cv x) (.cv y))) (synWb ph (synWex x
              (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y))) ph)))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_not_A, fresh_w_ne_x,
          fresh_w_ne_y, fresh_w_not_ph, or_false, and_false, not_false_eq_true])
  have p0000 := @gVex x
  have p0001 := @gVex y
  have p0002 :=
    @gEqvinop z w A (.cv x) (.cv y) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 p0000 p0001
  have p0003 :=
    @gN198a (synWa (.classEq (synCop (.cv z) (.cv w)) (synCop (.cv x) (.cv y))) ph)
      y
  have p0004 :=
    @gN198a
      (synWex y (synWa (.classEq (synCop (.cv z) (.cv w)) (synCop (.cv x) (.cv y))) ph))
      x
  have p0005 :=
    @gSyl (synWa (.classEq (synCop (.cv z) (.cv w)) (synCop (.cv x) (.cv y))) ph)
      (synWex y (synWa (.classEq (synCop (.cv z) (.cv w)) (synCop (.cv x) (.cv y))) ph))
      (synWex x (synWex y
          (synWa (.classEq (synCop (.cv z) (.cv w)) (synCop (.cv x) (.cv y))) ph)))
      p0003 p0004
  have p0006 :=
    @gEx (.classEq (synCop (.cv z) (.cv w)) (synCop (.cv x) (.cv y))) ph
      (synWex x (synWex y
          (synWa (.classEq (synCop (.cv z) (.cv w)) (synCop (.cv x) (.cv y))) ph)))
      p0005
  have p0007 := @gOpth (.cv z) (.cv w) (.cv x) (.cv y)
  have p0008_e00_recanon :
    Nominal.NPrf
      (synWb (.classEq (synCop (.cv z) (.cv w)) (synCop (.cv x) (.cv y)))
        (synWa (.objEq z x) (.objEq w y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0008 :=
    @gAnbi1i (.classEq (synCop (.cv z) (.cv w)) (synCop (.cv x) (.cv y)))
      (synWa (.objEq z x) (.objEq w y)) ph p0008_e00_recanon
  have p0009 :=
    @gN2exbii (synWa (.classEq (synCop (.cv z) (.cv w)) (synCop (.cv x) (.cv y))) ph)
      (synWa (synWa (.objEq z x) (.objEq w y)) ph) x y p0008
  have p0010 := @gNfe1 (synWa (.objEq z x) (synWex y (synWa (.objEq w y) ph))) x
  have p0011 := @gNfae y x y
  have p0012 := @gAnass (.objEq z x) (.objEq w y) ph
  have p0013 := @gN198a (synWa (.objEq w y) ph) y
  have p0014 :=
    @gA1i (.imp (synWa (.objEq w y) ph) (synWex y (synWa (.objEq w y) ph)))
      (.all y (.objEq y x)) p0013
  have p0015 :=
    @gAnim2d (.all y (.objEq y x)) (synWa (.objEq w y) ph)
      (synWex y (synWa (.objEq w y) ph)) (.objEq z x) p0014
  have p0016 :=
    @gSyl5bi (synWa (synWa (.objEq z x) (.objEq w y)) ph)
      (synWa (.objEq z x) (synWa (.objEq w y) ph)) (.all y (.objEq y x))
      (synWa (.objEq z x) (synWex y (synWa (.objEq w y) ph))) p0012 p0015
  have p0017 :=
    @gEximd (.all y (.objEq y x)) (synWa (synWa (.objEq z x) (.objEq w y)) ph)
      (synWa (.objEq z x) (synWex y (synWa (.objEq w y) ph))) y p0011 p0016
  have p0018 :=
    @gBiidd (.all y (.objEq y x))
      (synWa (.objEq z x) (synWex y (synWa (.objEq w y) ph)))
  have p0019 :=
    @gDrex1 (synWa (.objEq z x) (synWex y (synWa (.objEq w y) ph)))
      (synWa (.objEq z x) (synWex y (synWa (.objEq w y) ph))) y x p0018
  have p0020 :=
    @gSylibd (.all y (.objEq y x))
      (synWex y (synWa (synWa (.objEq z x) (.objEq w y)) ph))
      (synWex y (synWa (.objEq z x) (synWex y (synWa (.objEq w y) ph))))
      (synWex x (synWa (.objEq z x) (synWex y (synWa (.objEq w y) ph)))) p0017 p0019
  have p0021 :=
    @gExbii (synWa (synWa (.objEq z x) (.objEq w y)) ph)
      (synWa (.objEq z x) (synWa (.objEq w y) ph)) y p0012
  have p0022 := @gN1940 (.objEq z x) (synWa (.objEq w y) ph) y
  have p0023 := @gNfnae y x y
  have p0024 := @gDveeq2 y x z dv_cache_0008
  have p0025 := @gNfd (.neg (.all y (.objEq y x))) (.objEq z x) y p0023 p0024
  have p0026 := @gN199d (.objEq z x) (.neg (.all y (.objEq y x))) y p0025
  have p0027 :=
    @gAnim1d (.neg (.all y (.objEq y x))) (synWex y (.objEq z x)) (.objEq z x)
      (synWex y (synWa (.objEq w y) ph)) p0026
  have p0028 :=
    @gSyl5 (synWex y (synWa (.objEq z x) (synWa (.objEq w y) ph)))
      (synWa (synWex y (.objEq z x)) (synWex y (synWa (.objEq w y) ph)))
      (.neg (.all y (.objEq y x)))
      (synWa (.objEq z x) (synWex y (synWa (.objEq w y) ph))) p0022 p0027
  have p0029 :=
    @gSyl5bi (synWex y (synWa (synWa (.objEq z x) (.objEq w y)) ph))
      (synWex y (synWa (.objEq z x) (synWa (.objEq w y) ph)))
      (.neg (.all y (.objEq y x)))
      (synWa (.objEq z x) (synWex y (synWa (.objEq w y) ph))) p0021 p0028
  have p0030 := @gN198a (synWa (.objEq z x) (synWex y (synWa (.objEq w y) ph))) x
  have p0031 :=
    @gSyl6 (.neg (.all y (.objEq y x)))
      (synWex y (synWa (synWa (.objEq z x) (.objEq w y)) ph))
      (synWa (.objEq z x) (synWex y (synWa (.objEq w y) ph)))
      (synWex x (synWa (.objEq z x) (synWex y (synWa (.objEq w y) ph)))) p0029 p0030
  have p0032 :=
    @gPm261i (.all y (.objEq y x))
      (.imp (synWex y (synWa (synWa (.objEq z x) (.objEq w y)) ph))
        (synWex x (synWa (.objEq z x) (synWex y (synWa (.objEq w y) ph)))))
      p0020 p0031
  have p0033 :=
    @gExlimi (synWex y (synWa (synWa (.objEq z x) (.objEq w y)) ph))
      (synWex x (synWa (.objEq z x) (synWex y (synWa (.objEq w y) ph)))) x p0010 p0032
  have p0034 := @gEuequ1 x z dv_cache_0009
  have p0035 := @gEqucom x z
  have p0036 := @gEubii (.objEq x z) (.objEq z x) x p0035
  have p0037 := @gMpbi (synWeu x (.objEq x z)) (synWeu x (.objEq z x)) p0034 p0036
  have p0038 := @gEupick (.objEq z x) (synWex y (synWa (.objEq w y) ph)) x
  have p0039 :=
    @gMpan (synWeu x (.objEq z x))
      (synWex x (synWa (.objEq z x) (synWex y (synWa (.objEq w y) ph))))
      (.imp (.objEq z x) (synWex y (synWa (.objEq w y) ph))) p0037 p0038
  have p0040 :=
    @gCom12 (synWex x (synWa (.objEq z x) (synWex y (synWa (.objEq w y) ph))))
      (.objEq z x) (synWex y (synWa (.objEq w y) ph)) p0039
  have p0041 := @gEuequ1 y w dv_cache_0010
  have p0042 := @gEqucom y w
  have p0043 := @gEubii (.objEq y w) (.objEq w y) y p0042
  have p0044 := @gMpbi (synWeu y (.objEq y w)) (synWeu y (.objEq w y)) p0041 p0043
  have p0045 := @gEupick (.objEq w y) ph y
  have p0046 :=
    @gMpan (synWeu y (.objEq w y)) (synWex y (synWa (.objEq w y) ph))
      (.imp (.objEq w y) ph) p0044 p0045
  have p0047 := @gCom12 (synWex y (synWa (.objEq w y) ph)) (.objEq w y) ph p0046
  have p0048 :=
    @gSylan9 (.objEq z x)
      (synWex x (synWa (.objEq z x) (synWex y (synWa (.objEq w y) ph))))
      (synWex y (synWa (.objEq w y) ph)) (.objEq w y) ph p0040 p0047
  have p0049 :=
    @gSyl5 (synWex x (synWex y (synWa (synWa (.objEq z x) (.objEq w y)) ph)))
      (synWex x (synWa (.objEq z x) (synWex y (synWa (.objEq w y) ph))))
      (synWa (.objEq z x) (.objEq w y)) ph p0033 p0048
  have p0050 :=
    @gSyl5bi
      (synWex x (synWex y
          (synWa (.classEq (synCop (.cv z) (.cv w)) (synCop (.cv x) (.cv y))) ph)))
      (synWex x (synWex y (synWa (synWa (.objEq z x) (.objEq w y)) ph)))
      (synWa (.objEq z x) (.objEq w y)) ph p0009 p0049
  have p0051_e00_recanon :
    Nominal.NPrf
      (synWb (.classEq (synCop (.cv z) (.cv w)) (synCop (.cv x) (.cv y)))
        (synWa (.objEq z x) (.objEq w y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0051 :=
    @gSylbi (.classEq (synCop (.cv z) (.cv w)) (synCop (.cv x) (.cv y)))
      (synWa (.objEq z x) (.objEq w y))
      (.imp (synWex x (synWex y
            (synWa (.classEq (synCop (.cv z) (.cv w)) (synCop (.cv x) (.cv y))) ph))) ph)
      p0051_e00_recanon p0050
  have p0052 :=
    @gImpbid (.classEq (synCop (.cv z) (.cv w)) (synCop (.cv x) (.cv y))) ph
      (synWex x (synWex y
          (synWa (.classEq (synCop (.cv z) (.cv w)) (synCop (.cv x) (.cv y))) ph)))
      p0006 p0051
  have p0053 := @gEqeq1 A (synCop (.cv z) (.cv w)) (synCop (.cv x) (.cv y))
  have p0054 :=
    @gAnbi1d (.classEq A (synCop (.cv z) (.cv w)))
      (.classEq A (synCop (.cv x) (.cv y)))
      (.classEq (synCop (.cv z) (.cv w)) (synCop (.cv x) (.cv y))) ph p0053
  have p0055 :=
    @gN2exbidv (.classEq A (synCop (.cv z) (.cv w)))
      (synWa (.classEq A (synCop (.cv x) (.cv y))) ph)
      (synWa (.classEq (synCop (.cv z) (.cv w)) (synCop (.cv x) (.cv y))) ph) x y
      dv_cache_0011 dv_cache_0012 p0054
  have p0056 :=
    @gBibi2d (.classEq A (synCop (.cv z) (.cv w)))
      (synWex x (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y))) ph)))
      (synWex x (synWex y
          (synWa (.classEq (synCop (.cv z) (.cv w)) (synCop (.cv x) (.cv y))) ph)))
      ph p0055
  have p0057 :=
    @gImbi12d (.classEq A (synCop (.cv z) (.cv w)))
      (.classEq A (synCop (.cv x) (.cv y)))
      (.classEq (synCop (.cv z) (.cv w)) (synCop (.cv x) (.cv y)))
      (synWb ph (synWex x (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y))) ph))))
      (synWb ph (synWex x (synWex y
            (synWa (.classEq (synCop (.cv z) (.cv w)) (synCop (.cv x) (.cv y))) ph))))
      p0053 p0056
  have p0058 :=
    @gMpbiri (.classEq A (synCop (.cv z) (.cv w)))
      (.imp (.classEq A (synCop (.cv x) (.cv y))) (synWb ph
          (synWex x (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y))) ph)))))
      (.imp (.classEq (synCop (.cv z) (.cv w)) (synCop (.cv x) (.cv y))) (synWb ph (synWex x
            (synWex y (synWa (.classEq (synCop (.cv z) (.cv w)) (synCop (.cv x) (.cv y)))
                ph)))))
      p0052 p0057
  have p0059 :=
    @gAdantr (.classEq A (synCop (.cv z) (.cv w)))
      (.imp (.classEq A (synCop (.cv x) (.cv y))) (synWb ph
          (synWex x (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y))) ph)))))
      (.classEq (synCop (.cv z) (.cv w)) (synCop (.cv x) (.cv y))) p0058
  have p0060 :=
    @gExlimivv
      (synWa (.classEq A (synCop (.cv z) (.cv w)))
        (.classEq (synCop (.cv z) (.cv w)) (synCop (.cv x) (.cv y))))
      (.imp (.classEq A (synCop (.cv x) (.cv y))) (synWb ph
          (synWex x (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y))) ph)))))
      z w dv_cache_0013 dv_cache_0014 p0059
  have p0061 :=
    @gSylbi (.classEq A (synCop (.cv x) (.cv y)))
      (synWex z (synWex w (synWa (.classEq A (synCop (.cv z) (.cv w)))
            (.classEq (synCop (.cv z) (.cv w)) (synCop (.cv x) (.cv y))))))
      (.imp (.classEq A (synCop (.cv x) (.cv y))) (synWb ph
          (synWex x (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y))) ph)))))
      p0002 p0060
  have p0062 :=
    @gPm243i (.classEq A (synCop (.cv x) (.cv y)))
      (synWb ph (synWex x (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y))) ph))))
      p0061
  exact p0062

/-- Checked nominal proof certificate identified upstream as `g_copsex2g`. -/
@[expose]
noncomputable def gCopsex2g (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv)
    (dv_x_y : x ≠ y)
    (hyp_copsex2g_1 : Nominal.NPrf
        (.imp (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)) (synWb ph ps))) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W)) (synWb (synWex x
            (synWex y (synWa (.classEq (synCop A B) (synCop (.cv x) (.cv y))) ph))) ps)) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classEq (.cv x) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_y), dv_A_y, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq (.cv y) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_x_y, dv_B_x, or_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (ps).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ps_x, not_false_eq_true])
  have dv_cache_0006 : y ∉ (ps).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ps_y, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((synCop A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          dv_A_x, dv_B_x, or_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((synCop A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          dv_A_y, dv_B_y, or_false, not_false_eq_true])
  have p0000 := @gElisset x A V dv_cache_0001
  have p0001 := @gElisset y B W dv_cache_0002
  have p0002 :=
    @gEeanv (.classEq (.cv x) A) (.classEq (.cv y) B) x y dv_cache_0003 dv_cache_0004
  have p0003 :=
    @gNfe1 (synWex y (synWa (.classEq (synCop A B) (synCop (.cv x) (.cv y))) ph)) x
  have p0004 := @gNfv ps x dv_cache_0005
  have p0005 :=
    @gNfbi
      (synWex x (synWex y (synWa (.classEq (synCop A B) (synCop (.cv x) (.cv y))) ph)))
      ps x p0003 p0004
  have p0006 := @gNfe1 (synWa (.classEq (synCop A B) (synCop (.cv x) (.cv y))) ph) y
  have p0007 :=
    @gNfex (synWex y (synWa (.classEq (synCop A B) (synCop (.cv x) (.cv y))) ph)) y x
      p0006
  have p0008 := @gNfv ps y dv_cache_0006
  have p0009 :=
    @gNfbi
      (synWex x (synWex y (synWa (.classEq (synCop A B) (synCop (.cv x) (.cv y))) ph)))
      ps y p0007 p0008
  have p0010 := @gOpeq12 (.cv x) A (.cv y) B
  have p0011 := @gCopsexg ph x y (synCop A B) dv_cache_0007 dv_cache_0008
  have p0012 :=
    @gEqcoms
      (synWb ph (synWex x
          (synWex y (synWa (.classEq (synCop A B) (synCop (.cv x) (.cv y))) ph))))
      (synCop A B) (synCop (.cv x) (.cv y)) p0011
  have p0013 :=
    @gSyl (synWa (.classEq (.cv x) A) (.classEq (.cv y) B))
      (.classEq (synCop (.cv x) (.cv y)) (synCop A B))
      (synWb ph (synWex x
          (synWex y (synWa (.classEq (synCop A B) (synCop (.cv x) (.cv y))) ph))))
      p0010 p0012
  have p0014 :=
    @gBitr3d (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)) ph
      (synWex x (synWex y (synWa (.classEq (synCop A B) (synCop (.cv x) (.cv y))) ph)))
      ps p0013 hyp_copsex2g_1
  have p0015 :=
    @gExlimi (synWa (.classEq (.cv x) A) (.classEq (.cv y) B))
      (synWb (synWex x
          (synWex y (synWa (.classEq (synCop A B) (synCop (.cv x) (.cv y))) ph))) ps)
      y p0009 p0014
  have p0016 :=
    @gExlimi (synWex y (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)))
      (synWb (synWex x
          (synWex y (synWa (.classEq (synCop A B) (synCop (.cv x) (.cv y))) ph))) ps)
      x p0005 p0015
  have p0017 :=
    @gSylbir (synWa (synWex x (.classEq (.cv x) A)) (synWex y (.classEq (.cv y) B)))
      (synWex x (synWex y (synWa (.classEq (.cv x) A) (.classEq (.cv y) B))))
      (synWb (synWex x
          (synWex y (synWa (.classEq (synCop A B) (synCop (.cv x) (.cv y))) ph))) ps)
      p0002 p0016
  have p0018 :=
    @gSyl2an (.classMem A V) (synWex x (.classEq (.cv x) A))
      (synWex y (.classEq (.cv y) B))
      (synWb (synWex x
          (synWex y (synWa (.classEq (synCop A B) (synCop (.cv x) (.cv y))) ph))) ps)
      (.classMem B W) p0000 p0001 p0017
  exact p0018

/-- Checked nominal proof certificate identified upstream as `g_eqop`. -/
@[expose]
noncomputable def gEqop (z : Var) (t : Var) (A : Class) (B : Class) (C : Class)
    (_dv_A_t : t ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_t : t ∉ B.fv) (dv_B_z : z ∉ B.fv)
    (dv_C_t : t ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_t_z : t ≠ z) :
    Nominal.NPrf
      (synWb (.classEq A (synCop B C)) (.all z (synWb (.classMem (.cv z) A)
            (synWo (synWrex t B (.classEq (.cv z) (synCphi (.cv t)))) (synWrex t C
                (.classEq (.cv z) (synCun (synCphi (.cv t)) (synCsn (synC0c))))))))) :=
  by
  have dv_cache_0001 : z ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_z, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((synCop B C)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          dv_B_z, dv_C_z, or_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_z, not_false_eq_true])
  have dv_cache_0004 : t ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_t, not_false_eq_true])
  have dv_cache_0005 : z ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_z, not_false_eq_true])
  have dv_cache_0006 : t ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_t, not_false_eq_true])
  have dv_cache_0007 : z ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show z ≠ t from (by exact Ne.symm dv_t_z))
  have p0000 := @gDfcleq z A (synCop B C) dv_cache_0001 dv_cache_0002
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOp z t B C
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0002 :=
    @gEleq2i (synCop B C)
      (synCun (.cab z (synWrex t B (.classEq (.cv z) (synCphi (.cv t))))) (.cab z
          (synWrex t C (.classEq (.cv z) (synCun (synCphi (.cv t)) (synCsn (synC0c)))))))
      (.cv z) p0001
  have p0003 :=
    @gElun (.cv z) (.cab z (synWrex t B (.classEq (.cv z) (synCphi (.cv t)))))
      (.cab z (synWrex t C
          (.classEq (.cv z) (synCun (synCphi (.cv t)) (synCsn (synC0c))))))
  have p0004 :=
    @gBitri (.classMem (.cv z) (synCop B C))
      (.classMem (.cv z) (synCun (.cab z (synWrex t B (.classEq (.cv z) (synCphi (.cv t)))))
          (.cab z (synWrex t C
              (.classEq (.cv z) (synCun (synCphi (.cv t)) (synCsn (synC0c))))))))
      (synWo (.classMem (.cv z) (.cab z (synWrex t B (.classEq (.cv z) (synCphi (.cv t))))))
        (.classMem (.cv z) (.cab z (synWrex t C
              (.classEq (.cv z) (synCun (synCphi (.cv t)) (synCsn (synC0c))))))))
      p0002 p0003
  have p0005 := @gAbid (synWrex t B (.classEq (.cv z) (synCphi (.cv t)))) z
  have p0006 :=
    @gAbid
      (synWrex t C (.classEq (.cv z) (synCun (synCphi (.cv t)) (synCsn (synC0c))))) z
  have p0007 :=
    @gOrbi12i
      (.classMem (.cv z) (.cab z (synWrex t B (.classEq (.cv z) (synCphi (.cv t))))))
      (synWrex t B (.classEq (.cv z) (synCphi (.cv t))))
      (.classMem (.cv z) (.cab z (synWrex t C
            (.classEq (.cv z) (synCun (synCphi (.cv t)) (synCsn (synC0c)))))))
      (synWrex t C (.classEq (.cv z) (synCun (synCphi (.cv t)) (synCsn (synC0c)))))
      p0005 p0006
  have p0008 :=
    @gBitri (.classMem (.cv z) (synCop B C))
      (synWo (.classMem (.cv z) (.cab z (synWrex t B (.classEq (.cv z) (synCphi (.cv t))))))
        (.classMem (.cv z) (.cab z (synWrex t C
              (.classEq (.cv z) (synCun (synCphi (.cv t)) (synCsn (synC0c))))))))
      (synWo (synWrex t B (.classEq (.cv z) (synCphi (.cv t)))) (synWrex t C
          (.classEq (.cv z) (synCun (synCphi (.cv t)) (synCsn (synC0c))))))
      p0004 p0007
  have p0009 :=
    @gBibi2i (.classMem (.cv z) (synCop B C))
      (synWo (synWrex t B (.classEq (.cv z) (synCphi (.cv t)))) (synWrex t C
          (.classEq (.cv z) (synCun (synCphi (.cv t)) (synCsn (synC0c))))))
      (.classMem (.cv z) A) p0008
  have p0010 :=
    @gAlbii (synWb (.classMem (.cv z) A) (.classMem (.cv z) (synCop B C)))
      (synWb (.classMem (.cv z) A) (synWo (synWrex t B (.classEq (.cv z) (synCphi (.cv t))))
          (synWrex t C (.classEq (.cv z) (synCun (synCphi (.cv t)) (synCsn (synC0c)))))))
      z p0009
  have p0011 :=
    @gBitri (.classEq A (synCop B C))
      (.all z (synWb (.classMem (.cv z) A) (.classMem (.cv z) (synCop B C))))
      (.all z (synWb (.classMem (.cv z) A)
          (synWo (synWrex t B (.classEq (.cv z) (synCphi (.cv t)))) (synWrex t C
              (.classEq (.cv z) (synCun (synCphi (.cv t)) (synCsn (synC0c))))))))
      p0000 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_mosubopt`. -/
@[expose]
noncomputable def gMosubopt (ph : Wff) (x : Var) (y : Var) (z : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) (_dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.imp (.all y (.all z (synWmo x ph))) (synWmo x
          (synWex y (synWex z (synWa (.classEq A (synCop (.cv y) (.cv z))) ph))))) :=
  by
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0002 : z ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_z, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classEq A (synCop (.cv y) (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_A_x, dv_x_y, dv_x_z, or_false, not_false_eq_true])
  have dv_cache_0004 :
    x ∉ ((synWex y (synWex z (.classEq A (synCop (.cv y) (.cv z)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, dv_A_x, dv_x_y, dv_x_z, or_false, and_false,
          not_false_eq_true])
  have p0000 := @gNfa1 (.all z (synWmo x ph)) y
  have p0001 := @gNfe1 (synWex z (synWa (.classEq A (synCop (.cv y) (.cv z))) ph)) y
  have p0002 :=
    @gNfmo (synWex y (synWex z (synWa (.classEq A (synCop (.cv y) (.cv z))) ph))) y x
      p0001
  have p0003 := @gNfa1 (synWmo x ph) z
  have p0004 := @gNfe1 (synWa (.classEq A (synCop (.cv y) (.cv z))) ph) z
  have p0005 :=
    @gNfex (synWex z (synWa (.classEq A (synCop (.cv y) (.cv z))) ph)) z y p0004
  have p0006 :=
    @gNfmo (synWex y (synWex z (synWa (.classEq A (synCop (.cv y) (.cv z))) ph))) z x
      p0005
  have p0007 := @gCopsexg ph y z A dv_cache_0001 dv_cache_0002
  have p0008 :=
    @gMobidv (.classEq A (synCop (.cv y) (.cv z))) ph
      (synWex y (synWex z (synWa (.classEq A (synCop (.cv y) (.cv z))) ph))) x
      dv_cache_0003 p0007
  have p0009 :=
    @gBiimpcd (.classEq A (synCop (.cv y) (.cv z))) (synWmo x ph)
      (synWmo x (synWex y (synWex z (synWa (.classEq A (synCop (.cv y) (.cv z))) ph))))
      p0008
  have p0010 :=
    @gSps (synWmo x ph)
      (.imp (.classEq A (synCop (.cv y) (.cv z))) (synWmo x
          (synWex y (synWex z (synWa (.classEq A (synCop (.cv y) (.cv z))) ph)))))
      z p0009
  have p0011 :=
    @gExlimd (.all z (synWmo x ph)) (.classEq A (synCop (.cv y) (.cv z)))
      (synWmo x (synWex y (synWex z (synWa (.classEq A (synCop (.cv y) (.cv z))) ph))))
      z p0003 p0006 p0010
  have p0012 :=
    @gSps (.all z (synWmo x ph))
      (.imp (synWex z (.classEq A (synCop (.cv y) (.cv z)))) (synWmo x
          (synWex y (synWex z (synWa (.classEq A (synCop (.cv y) (.cv z))) ph)))))
      y p0011
  have p0013 :=
    @gExlimd (.all y (.all z (synWmo x ph)))
      (synWex z (.classEq A (synCop (.cv y) (.cv z))))
      (synWmo x (synWex y (synWex z (synWa (.classEq A (synCop (.cv y) (.cv z))) ph))))
      y p0000 p0002 p0012
  have p0014 := @gSimpl (.classEq A (synCop (.cv y) (.cv z))) ph
  have p0015 :=
    @gN2eximi (synWa (.classEq A (synCop (.cv y) (.cv z))) ph)
      (.classEq A (synCop (.cv y) (.cv z))) y z p0014
  have p0016 :=
    @gExlimiv (synWex y (synWex z (synWa (.classEq A (synCop (.cv y) (.cv z))) ph)))
      (synWex y (synWex z (.classEq A (synCop (.cv y) (.cv z))))) x dv_cache_0004 p0015
  have p0017 :=
    @gCon3i
      (synWex x (synWex y (synWex z (synWa (.classEq A (synCop (.cv y) (.cv z))) ph))))
      (synWex y (synWex z (.classEq A (synCop (.cv y) (.cv z))))) p0016
  have p0018 :=
    @gExmo (synWex y (synWex z (synWa (.classEq A (synCop (.cv y) (.cv z))) ph))) x
  have p0019 :=
    @gOri
      (synWex x (synWex y (synWex z (synWa (.classEq A (synCop (.cv y) (.cv z))) ph))))
      (synWmo x (synWex y (synWex z (synWa (.classEq A (synCop (.cv y) (.cv z))) ph))))
      p0018
  have p0020 :=
    @gSyl (.neg (synWex y (synWex z (.classEq A (synCop (.cv y) (.cv z))))))
      (.neg (synWex x
          (synWex y (synWex z (synWa (.classEq A (synCop (.cv y) (.cv z))) ph)))))
      (synWmo x (synWex y (synWex z (synWa (.classEq A (synCop (.cv y) (.cv z))) ph))))
      p0017 p0019
  have p0021 :=
    @gPm261d1 (.all y (.all z (synWmo x ph)))
      (synWex y (synWex z (.classEq A (synCop (.cv y) (.cv z)))))
      (synWmo x (synWex y (synWex z (synWa (.classEq A (synCop (.cv y) (.cv z))) ph))))
      p0013 p0020
  exact p0021


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part036`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_phiun`. -/
@[expose]
noncomputable def gPhiun (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (synCphi (synCun A B)) (synCun (synCphi A) (synCphi B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
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
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : y ∉ ((synCun A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synCun A B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0003 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0004 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0005 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0006 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0007 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have p0000 :=
    @gRexun
      (.classEq (.cv x)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      y A B
  have p0001 :=
    @gAbbii
      (synWrex y (synCun A B) (.classEq (.cv x)
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      (synWo (synWrex y A (.classEq (.cv x)
            (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
        (synWrex y B (.classEq (.cv x)
            (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))))
      x p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfPhi y x
      (synCun A B) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfPhi y x A
      dv_cache_0004 dv_cache_0005 dv_cache_0003
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfPhi y x B
      dv_cache_0006 dv_cache_0007 dv_cache_0003
  have p0005 :=
    @gUneq12i (synCphi A)
      (.cab x (synWrex y A (.classEq (.cv x)
            (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))))
      (synCphi B)
      (.cab x (synWrex y B (.classEq (.cv x)
            (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))))
      p0003 p0004
  have p0006 :=
    @gUnab
      (synWrex y A (.classEq (.cv x)
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      (synWrex y B (.classEq (.cv x)
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      x
  have p0007 :=
    @gEqtri (synCun (synCphi A) (synCphi B))
      (synCun (.cab x (synWrex y A (.classEq (.cv x)
              (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))))
        (.cab x (synWrex y B (.classEq (.cv x)
              (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))))
      (.cab x (synWo (synWrex y A (.classEq (.cv x)
              (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
          (synWrex y B (.classEq (.cv x)
              (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))))
      p0005 p0006
  have p0008 :=
    @gN3eqtr4i
      (.cab x (synWrex y (synCun A B) (.classEq (.cv x)
            (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))))
      (.cab x (synWo (synWrex y A (.classEq (.cv x)
              (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
          (synWrex y B (.classEq (.cv x)
              (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))))
      (synCphi (synCun A B)) (synCun (synCphi A) (synCphi B)) p0001 p0002 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_phidisjnn`. -/
@[expose]
noncomputable def gPhidisjnn (A : Class) :
    Nominal.NPrf
      (.imp (.classEq (synCin A (synCnnc)) (synC0)) (.classEq (synCphi A) A)) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classEq (synCin A (synCnnc)) (synC0))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          fresh_y_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classEq (synCin A (synCnnc)) (synC0))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          fresh_x_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0007 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have p0000 := @gDisj y A (synCnnc) dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gBiimpi (.classEq (synCin A (synCnnc)) (synC0))
      (synWral y A (.neg (.classMem (.cv y) (synCnnc)))) p0000
  have p0002 :=
    @gR1921bi (.classEq (synCin A (synCnnc)) (synC0))
      (.neg (.classMem (.cv y) (synCnnc))) y A p0001
  have p0003 :=
    @gIffalse (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)
  have p0004 :=
    @gSyl (synWa (.classEq (synCin A (synCnnc)) (synC0)) (.classMem (.cv y) A))
      (.neg (.classMem (.cv y) (synCnnc)))
      (.classEq (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))
        (.cv y))
      p0002 p0003
  have p0005 :=
    @gEqeq2d (synWa (.classEq (synCin A (synCnnc)) (synC0)) (.classMem (.cv y) A))
      (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))
      (.cv y) (.cv x) p0004
  have p0006 := @gEqucom y x
  have p0007_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (.classEq (synCin A (synCnnc)) (synC0)) (.classMem (.cv y) A)) (synWb
          (.classEq (.cv x)
            (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
          (.objEq x y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCin synCcompl synCnin synWnan synCnnc synCint synC0
          synCdif synCvv synWb synCif synWo synCplc synWrex synWex synC1c
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0007 :=
    @gSyl6bbr (synWa (.classEq (synCin A (synCnnc)) (synC0)) (.classMem (.cv y) A))
      (.classEq (.cv x)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (.objEq x y) (.objEq y x) p0007_e00_recanon p0006
  have p0008 :=
    @gRexbidva (.classEq (synCin A (synCnnc)) (synC0))
      (.classEq (.cv x)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (.objEq y x) y A dv_cache_0003 p0007
  have p0009 := @gRisset y (.cv x) A dv_cache_0004 dv_cache_0001
  have p0010_e01_recanon :
    Nominal.NPrf (synWb (.classMem (.cv x) A) (synWrex y A (.objEq y x))) :=
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
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0009
  have p0010 :=
    @gSyl6bbr (.classEq (synCin A (synCnnc)) (synC0))
      (synWrex y A (.classEq (.cv x)
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      (synWrex y A (.objEq y x)) (.classMem (.cv x) A) p0008 p0010_e01_recanon
  have p0011 :=
    @gAlrimiv (.classEq (synCin A (synCnnc)) (synC0))
      (synWb (synWrex y A (.classEq (.cv x)
            (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
        (.classMem (.cv x) A))
      x dv_cache_0005 p0010
  have p0012 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfPhi y x A
      dv_cache_0001 dv_cache_0006 dv_cache_0007
  have p0013 :=
    @gEqeq1i (synCphi A)
      (.cab x (synWrex y A (.classEq (.cv x)
            (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))))
      A p0012
  have p0014 :=
    @gEqabcb
      (synWrex y A (.classEq (.cv x)
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      x A dv_cache_0006
  have p0015 :=
    @gBitri (.classEq (synCphi A) A)
      (.classEq (.cab x (synWrex y A (.classEq (.cv x)
              (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))))
        A)
      (.all x (synWb (synWrex y A (.classEq (.cv x)
              (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
          (.classMem (.cv x) A)))
      p0013 p0014
  have p0016 :=
    @gSylibr (.classEq (synCin A (synCnnc)) (synC0))
      (.all x (synWb (synWrex y A (.classEq (.cv x)
              (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
          (.classMem (.cv x) A)))
      (.classEq (synCphi A) A) p0011 p0015
  exact p0016


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part037`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_phialllem1`. -/
@[expose]
noncomputable def gPhialllem1 (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (hyp_phiall_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (synWss A (synCnnc)) (.neg (.classMem (synC0c) A)))
        (synWex x (.classEq A (synCphi (.cv x))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  let z : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have dv_cache_0001 : x ∉ ((Class.cv z)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_z, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.objEq z w)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_x_ne_z, fresh_x_ne_w, or_false, not_false_eq_true])
  have dv_cache_0003 :
    z ∉ ((synWa (synWss A (synCnnc)) (.neg (.classMem (synC0c) A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          fresh_z_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_w, not_false_eq_true])
  have dv_cache_0005 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0007 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0008 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0009 : w ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_A, not_false_eq_true])
  have dv_cache_0010 :
    w ∉ ((synWa (synWss A (synCnnc)) (.neg (.classMem (synC0c) A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          fresh_w_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 :
    x ∉
      ((synCrab y (synCnnc)
          (synWrex z A (.classEq (.cv z) (synCplc (.cv y) (synC1c)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_A_x, fresh_x_ne_z, fresh_x_ne_y,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0012 :
    w ∉
      ((synCrab y (synCnnc)
          (synWrex z A (.classEq (.cv z) (synCplc (.cv y) (synC1c)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_not_A, fresh_w_ne_z,
          fresh_w_ne_y, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0013 : x ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show x ≠ w from (by exact fresh_x_ne_w))
  have dv_cache_0014 : z ∉ ((Wff.objEq y x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, or_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ ((synCnnc)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0016 :
    y ∉ ((synWrex z A (.classEq (.cv z) (synCplc (.cv x) (synC1c))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_z,
          fresh_y_ne_x, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0017 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0018 : z ∉ ((Wff.classEq (.cv w) (synCplc (.cv x) (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_w, fresh_z_ne_x, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0019 :
    z ∉
      ((synCcnvk (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0020 : z ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0021 :
    y ∉
      ((synCimak (synCcnvk (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                      (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c)))))) A)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union,
          fresh_y_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0022 :
    x ∉
      ((Wff.classEq A (synCphi (synCrab y (synCnnc)
              (synWrex z A (.classEq (.cv z) (synCplc (.cv y) (synC1c)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_A_x, fresh_x_ne_z, fresh_x_ne_y,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 := @gEleq1 (.cv z) (synC0c) A
  have p0001 :=
    @gBiimpcd (.classEq (.cv z) (synC0c)) (.classMem (.cv z) A) (.classMem (synC0c) A)
      p0000
  have p0002 :=
    @gCon3d (.classMem (.cv z) A) (.classEq (.cv z) (synC0c)) (.classMem (synC0c) A)
      p0001
  have p0003 :=
    @gImpcom (.classMem (.cv z) A) (.neg (.classMem (synC0c) A))
      (.neg (.classEq (.cv z) (synC0c))) p0002
  have p0004 :=
    @gAdantll (.neg (.classMem (synC0c) A)) (.classMem (.cv z) A)
      (.neg (.classEq (.cv z) (synC0c))) (synWss A (synCnnc)) p0003
  have p0005 := @gSsel2 A (synCnnc) (.cv z)
  have p0006 :=
    @gAdantlr (synWss A (synCnnc)) (.classMem (.cv z) A) (.classMem (.cv z) (synCnnc))
      (.neg (.classMem (synC0c) A)) p0005
  have p0007 := @gNnc0suc x (.cv z) dv_cache_0001
  have p0008 :=
    @gSylib
      (synWa (synWa (synWss A (synCnnc)) (.neg (.classMem (synC0c) A)))
        (.classMem (.cv z) A))
      (.classMem (.cv z) (synCnnc))
      (synWo (.classEq (.cv z) (synC0c))
        (synWrex x (synCnnc) (.classEq (.cv z) (synCplc (.cv x) (synC1c)))))
      p0006 p0007
  have p0009 :=
    @gOrel1 (.classEq (.cv z) (synC0c))
      (synWrex x (synCnnc) (.classEq (.cv z) (synCplc (.cv x) (synC1c))))
  have p0010 :=
    @gSylc
      (synWa (synWa (synWss A (synCnnc)) (.neg (.classMem (synC0c) A)))
        (.classMem (.cv z) A))
      (.neg (.classEq (.cv z) (synC0c)))
      (synWo (.classEq (.cv z) (synC0c))
        (synWrex x (synCnnc) (.classEq (.cv z) (synCplc (.cv x) (synC1c)))))
      (synWrex x (synCnnc) (.classEq (.cv z) (synCplc (.cv x) (synC1c)))) p0004 p0008
      p0009
  have p0011 := @gAnidm (.classEq (.cv z) (synCplc (.cv x) (synC1c)))
  have p0012 := @gEqeq1 (.cv z) (.cv w) (synCplc (.cv x) (synC1c))
  have p0013_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq z w) (synWb (.classEq (.cv z) (synCplc (.cv x) (synC1c)))
          (.classEq (.cv w) (synCplc (.cv x) (synC1c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCplc synWrex synWex synWa synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0012
  have p0013 :=
    @gAnbi2d (.objEq z w) (.classEq (.cv z) (synCplc (.cv x) (synC1c)))
      (.classEq (.cv w) (synCplc (.cv x) (synC1c)))
      (.classEq (.cv z) (synCplc (.cv x) (synC1c))) p0013_e00_recanon
  have p0014 :=
    @gSyl5bbr (.classEq (.cv z) (synCplc (.cv x) (synC1c)))
      (synWa (.classEq (.cv z) (synCplc (.cv x) (synC1c)))
        (.classEq (.cv z) (synCplc (.cv x) (synC1c))))
      (.objEq z w)
      (synWa (.classEq (.cv z) (synCplc (.cv x) (synC1c)))
        (.classEq (.cv w) (synCplc (.cv x) (synC1c))))
      p0011 p0013
  have p0015 :=
    @gRexbidv (.objEq z w) (.classEq (.cv z) (synCplc (.cv x) (synC1c)))
      (synWa (.classEq (.cv z) (synCplc (.cv x) (synC1c)))
        (.classEq (.cv w) (synCplc (.cv x) (synC1c))))
      x (synCnnc) dv_cache_0002 p0014
  have p0016 :=
    @gSyl5ibcom
      (synWa (synWa (synWss A (synCnnc)) (.neg (.classMem (synC0c) A)))
        (.classMem (.cv z) A))
      (synWrex x (synCnnc) (.classEq (.cv z) (synCplc (.cv x) (synC1c)))) (.objEq z w)
      (synWrex x (synCnnc) (synWa (.classEq (.cv z) (synCplc (.cv x) (synC1c)))
          (.classEq (.cv w) (synCplc (.cv x) (synC1c)))))
      p0010 p0015
  have p0017 := @gEqtr3 (.cv z) (.cv w) (synCplc (.cv x) (synC1c))
  have p0018_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (.classEq (.cv z) (synCplc (.cv x) (synC1c)))
          (.classEq (.cv w) (synCplc (.cv x) (synC1c)))) (.objEq z w)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCplc synWrex synWex synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0017
  have p0018 :=
    @gRexlimivw
      (synWa (.classEq (.cv z) (synCplc (.cv x) (synC1c)))
        (.classEq (.cv w) (synCplc (.cv x) (synC1c))))
      (.objEq z w) x (synCnnc) dv_cache_0002 p0018_e00_recanon
  have p0019 :=
    @gImpbid1
      (synWa (synWa (synWss A (synCnnc)) (.neg (.classMem (synC0c) A)))
        (.classMem (.cv z) A))
      (.objEq z w)
      (synWrex x (synCnnc) (synWa (.classEq (.cv z) (synCplc (.cv x) (synC1c)))
          (.classEq (.cv w) (synCplc (.cv x) (synC1c)))))
      p0016 p0018
  have p0020 :=
    @gRexbidva (synWa (synWss A (synCnnc)) (.neg (.classMem (synC0c) A)))
      (.objEq z w)
      (synWrex x (synCnnc) (synWa (.classEq (.cv z) (synCplc (.cv x) (synC1c)))
          (.classEq (.cv w) (synCplc (.cv x) (synC1c)))))
      z A dv_cache_0003 p0019
  have p0021 := @gRisset z (.cv w) A dv_cache_0004 dv_cache_0005
  have p0022 :=
    @gRexcom
      (synWa (.classEq (.cv z) (synCplc (.cv x) (synC1c)))
        (.classEq (.cv w) (synCplc (.cv x) (synC1c))))
      x z (synCnnc) A dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0023_e01_recanon :
    Nominal.NPrf (synWb (.classMem (.cv w) A) (synWrex z A (.objEq z w))) :=
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
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0021
  have p0023 :=
    @gN3bitr4g (synWa (synWss A (synCnnc)) (.neg (.classMem (synC0c) A)))
      (synWrex z A (.objEq z w))
      (synWrex z A (synWrex x (synCnnc)
          (synWa (.classEq (.cv z) (synCplc (.cv x) (synC1c)))
            (.classEq (.cv w) (synCplc (.cv x) (synC1c))))))
      (.classMem (.cv w) A)
      (synWrex x (synCnnc) (synWrex z A
          (synWa (.classEq (.cv z) (synCplc (.cv x) (synC1c)))
            (.classEq (.cv w) (synCplc (.cv x) (synC1c))))))
      p0020 p0023_e01_recanon p0022
  have p0024 :=
    @gEqabdv (synWa (synWss A (synCnnc)) (.neg (.classMem (synC0c) A)))
      (synWrex x (synCnnc) (synWrex z A
          (synWa (.classEq (.cv z) (synCplc (.cv x) (synC1c)))
            (.classEq (.cv w) (synCplc (.cv x) (synC1c))))))
      w A dv_cache_0009 dv_cache_0010 p0023
  have p0025 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfPhi x w
      (synCrab y (synCnnc) (synWrex z A (.classEq (.cv z) (synCplc (.cv y) (synC1c)))))
      dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0026 := @gAddceq1 (.cv y) (.cv x) (synC1c)
  have p0027_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y x)
        (.classEq (synCplc (.cv y) (synC1c)) (synCplc (.cv x) (synC1c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCplc synWrex synWex synWa synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0026
  have p0027 :=
    @gEqeq2d (.objEq y x) (synCplc (.cv y) (synC1c)) (synCplc (.cv x) (synC1c))
      (.cv z) p0027_e00_recanon
  have p0028 :=
    @gRexbidv (.objEq y x) (.classEq (.cv z) (synCplc (.cv y) (synC1c)))
      (.classEq (.cv z) (synCplc (.cv x) (synC1c))) z A dv_cache_0014 p0027
  have p0029 :=
    @gRexrab (synWrex z A (.classEq (.cv z) (synCplc (.cv y) (synC1c))))
      (synWrex z A (.classEq (.cv z) (synCplc (.cv x) (synC1c))))
      (.classEq (.cv w)
        (synCif (.classMem (.cv x) (synCnnc)) (synCplc (.cv x) (synC1c)) (.cv x)))
      x y (synCnnc) dv_cache_0015 dv_cache_0016 dv_cache_0017 p0028
  have p0030 :=
    @gIftrue (.classMem (.cv x) (synCnnc)) (synCplc (.cv x) (synC1c)) (.cv x)
  have p0031 :=
    @gEqeq2d (.classMem (.cv x) (synCnnc))
      (synCif (.classMem (.cv x) (synCnnc)) (synCplc (.cv x) (synC1c)) (.cv x))
      (synCplc (.cv x) (synC1c)) (.cv w) p0030
  have p0032 :=
    @gAnbi2d (.classMem (.cv x) (synCnnc))
      (.classEq (.cv w)
        (synCif (.classMem (.cv x) (synCnnc)) (synCplc (.cv x) (synC1c)) (.cv x)))
      (.classEq (.cv w) (synCplc (.cv x) (synC1c)))
      (synWrex z A (.classEq (.cv z) (synCplc (.cv x) (synC1c)))) p0031
  have p0033 :=
    @gR1941v (.classEq (.cv z) (synCplc (.cv x) (synC1c)))
      (.classEq (.cv w) (synCplc (.cv x) (synC1c))) z A dv_cache_0018
  have p0034 :=
    @gSyl6bbr (.classMem (.cv x) (synCnnc))
      (synWa (synWrex z A (.classEq (.cv z) (synCplc (.cv x) (synC1c)))) (.classEq (.cv w)
          (synCif (.classMem (.cv x) (synCnnc)) (synCplc (.cv x) (synC1c)) (.cv x))))
      (synWa (synWrex z A (.classEq (.cv z) (synCplc (.cv x) (synC1c))))
        (.classEq (.cv w) (synCplc (.cv x) (synC1c))))
      (synWrex z A (synWa (.classEq (.cv z) (synCplc (.cv x) (synC1c)))
          (.classEq (.cv w) (synCplc (.cv x) (synC1c)))))
      p0032 p0033
  have p0035 :=
    @gRexbiia
      (synWa (synWrex z A (.classEq (.cv z) (synCplc (.cv x) (synC1c)))) (.classEq (.cv w)
          (synCif (.classMem (.cv x) (synCnnc)) (synCplc (.cv x) (synC1c)) (.cv x))))
      (synWrex z A (synWa (.classEq (.cv z) (synCplc (.cv x) (synC1c)))
          (.classEq (.cv w) (synCplc (.cv x) (synC1c)))))
      x (synCnnc) p0034
  have p0036 :=
    @gBitri
      (synWrex x (synCrab y (synCnnc)
          (synWrex z A (.classEq (.cv z) (synCplc (.cv y) (synC1c))))) (.classEq (.cv w)
          (synCif (.classMem (.cv x) (synCnnc)) (synCplc (.cv x) (synC1c)) (.cv x))))
      (synWrex x (synCnnc)
        (synWa (synWrex z A (.classEq (.cv z) (synCplc (.cv x) (synC1c)))) (.classEq (.cv w)
            (synCif (.classMem (.cv x) (synCnnc)) (synCplc (.cv x) (synC1c)) (.cv x)))))
      (synWrex x (synCnnc) (synWrex z A
          (synWa (.classEq (.cv z) (synCplc (.cv x) (synC1c)))
            (.classEq (.cv w) (synCplc (.cv x) (synC1c))))))
      p0029 p0035
  have p0037 :=
    @gAbbii
      (synWrex x (synCrab y (synCnnc)
          (synWrex z A (.classEq (.cv z) (synCplc (.cv y) (synC1c))))) (.classEq (.cv w)
          (synCif (.classMem (.cv x) (synCnnc)) (synCplc (.cv x) (synC1c)) (.cv x))))
      (synWrex x (synCnnc) (synWrex z A
          (synWa (.classEq (.cv z) (synCplc (.cv x) (synC1c)))
            (.classEq (.cv w) (synCplc (.cv x) (synC1c))))))
      w p0036
  have p0038 :=
    @gEqtri
      (synCphi (synCrab y (synCnnc)
          (synWrex z A (.classEq (.cv z) (synCplc (.cv y) (synC1c))))))
      (.cab w (synWrex x (synCrab y (synCnnc)
            (synWrex z A (.classEq (.cv z) (synCplc (.cv y) (synC1c))))) (.classEq (.cv w)
            (synCif (.classMem (.cv x) (synCnnc)) (synCplc (.cv x) (synC1c)) (.cv x)))))
      (.cab w (synWrex x (synCnnc) (synWrex z A
            (synWa (.classEq (.cv z) (synCplc (.cv x) (synC1c)))
              (.classEq (.cv w) (synCplc (.cv x) (synC1c)))))))
      p0025 p0037
  have p0039 :=
    @gSyl6eqr (synWa (synWss A (synCnnc)) (.neg (.classMem (synC0c) A))) A
      (.cab w (synWrex x (synCnnc) (synWrex z A
            (synWa (.classEq (.cv z) (synCplc (.cv x) (synC1c)))
              (.classEq (.cv w) (synCplc (.cv x) (synC1c)))))))
      (synCphi (synCrab y (synCnnc)
          (synWrex z A (.classEq (.cv z) (synCplc (.cv y) (synC1c))))))
      p0024 p0038
  have p0040 :=
    @gDfrab2 (synWrex z A (.classEq (.cv z) (synCplc (.cv y) (synC1c)))) y (synCnnc)
      dv_cache_0015
  have p0041 := @gVex y
  have p0042 :=
    @gElimak z
      (synCcnvk (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (synC1c))))))
      A (.cv y) dv_cache_0019 dv_cache_0005 dv_cache_0020 p0041
  have p0043 := @gVex z
  have p0044 :=
    @gOpkelimagek (.cv y) (.cv z)
      (synCimak (synCdif (synCins3k (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCpw1 (synCpw1 (synC1c))))
      p0041 p0043
  have p0045 :=
    @gOpkelcnvk (.cv z) (.cv y)
      (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synCpw1 (synC1c)))))
      p0043 p0041
  have p0046 := @gDfaddc2 (.cv y) (synC1c)
  have p0047 :=
    @gEqeq2i (synCplc (.cv y) (synC1c))
      (synCimak (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synCpw1 (synC1c)))) (.cv y))
      (.cv z) p0046
  have p0048 :=
    @gN3bitr4i
      (.classMem (synCopk (.cv y) (.cv z)) (synCimagek (synCimak (synCdif (synCins3k
                (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (synC1c))))))
      (.classEq (.cv z) (synCimak (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (synC1c)))) (.cv y)))
      (.classMem (synCopk (.cv z) (.cv y)) (synCcnvk (synCimagek (synCimak (synCdif
                (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c)))))))
      (.classEq (.cv z) (synCplc (.cv y) (synC1c))) p0044 p0045 p0047
  have p0049 :=
    @gRexbii
      (.classMem (synCopk (.cv z) (.cv y)) (synCcnvk (synCimagek (synCimak (synCdif
                (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c)))))))
      (.classEq (.cv z) (synCplc (.cv y) (synC1c))) z A p0048
  have p0050 :=
    @gBitri
      (.classMem (.cv y) (synCimak (synCcnvk (synCimagek (synCimak (synCdif (synCins3k
                    (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c)))))) A))
      (synWrex z A (.classMem (synCopk (.cv z) (.cv y)) (synCcnvk (synCimagek (synCimak
                (synCdif (synCins3k (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c))))))))
      (synWrex z A (.classEq (.cv z) (synCplc (.cv y) (synC1c)))) p0042 p0049
  have p0051 :=
    @gEqabi (synWrex z A (.classEq (.cv z) (synCplc (.cv y) (synC1c)))) y
      (synCimak (synCcnvk (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c)))))) A)
      dv_cache_0021 p0050
  have p0052 := @gAddcexlem
  have p0053 := @gN1cex
  have p0054 := @gPw1ex (synC1c) p0053
  have p0055 := @gPw1ex (synCpw1 (synC1c)) p0054
  have p0056 :=
    @gImakex
      (synCdif (synCins3k (synCcompl
            (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
          (synCsymdif (synCins2k (synCins2k (synCssetk)))
            (synCun (synCins2k (synCins3k (synCssetk)))
              (synCins3k (synCsik (synCsik (synCssetk))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synCpw1 (synCpw1 (synC1c))) p0052 p0055
  have p0057 :=
    @gImagekex
      (synCimak (synCdif (synCins3k (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCpw1 (synCpw1 (synC1c))))
      p0056
  have p0058 :=
    @gCnvkex
      (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synCpw1 (synC1c)))))
      p0057
  have p0059 :=
    @gImakex
      (synCcnvk (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (synC1c))))))
      A p0058 hyp_phiall_1
  have p0060 :=
    @gEqeltrri
      (synCimak (synCcnvk (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c)))))) A)
      (.cab y (synWrex z A (.classEq (.cv z) (synCplc (.cv y) (synC1c))))) (synCvv)
      p0051 p0059
  have p0061 := @gNncex
  have p0062 :=
    @gInex (.cab y (synWrex z A (.classEq (.cv z) (synCplc (.cv y) (synC1c)))))
      (synCnnc) p0060 p0061
  have p0063 :=
    @gEqeltri
      (synCrab y (synCnnc) (synWrex z A (.classEq (.cv z) (synCplc (.cv y) (synC1c)))))
      (synCin (.cab y (synWrex z A (.classEq (.cv z) (synCplc (.cv y) (synC1c)))))
        (synCnnc))
      (synCvv) p0040 p0062
  have p0064 :=
    @gPhieq (.cv x)
      (synCrab y (synCnnc) (synWrex z A (.classEq (.cv z) (synCplc (.cv y) (synC1c)))))
  have p0065 :=
    @gEqeq2d
      (.classEq (.cv x) (synCrab y (synCnnc)
          (synWrex z A (.classEq (.cv z) (synCplc (.cv y) (synC1c))))))
      (synCphi (.cv x))
      (synCphi (synCrab y (synCnnc)
          (synWrex z A (.classEq (.cv z) (synCplc (.cv y) (synC1c))))))
      A p0064
  have p0066 :=
    @gSpcev (.classEq A (synCphi (.cv x)))
      (.classEq A (synCphi (synCrab y (synCnnc)
            (synWrex z A (.classEq (.cv z) (synCplc (.cv y) (synC1c)))))))
      x
      (synCrab y (synCnnc) (synWrex z A (.classEq (.cv z) (synCplc (.cv y) (synC1c)))))
      dv_cache_0011 dv_cache_0022 p0063 p0065
  have p0067 :=
    @gSyl (synWa (synWss A (synCnnc)) (.neg (.classMem (synC0c) A)))
      (.classEq A (synCphi (synCrab y (synCnnc)
            (synWrex z A (.classEq (.cv z) (synCplc (.cv y) (synC1c)))))))
      (synWex x (.classEq A (synCphi (.cv x)))) p0039 p0066
  exact p0067

/-- Checked nominal proof certificate identified upstream as `g_phialllem2`. -/
@[expose]
noncomputable def gPhialllem2 (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (hyp_phiall_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (.neg (.classMem (synC0c) A)) (synWex x (.classEq A (synCphi (.cv x))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ ((synCin A (synCnnc))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          fresh_y_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synCun (synCdif A (synCnnc)) (.cv y))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_A_x, fresh_x_ne_y, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0003 :
    x ∉ ((Wff.classEq A (synCphi (synCun (synCdif A (synCnnc)) (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_A_x, fresh_x_ne_y, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0004 : y ∉ ((synWex x (.classEq A (synCphi (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_x, or_false, and_false,
          not_false_eq_true])
  have p0000 := @gInss2 A (synCnnc)
  have p0001 := @gInss1 A (synCnnc)
  have p0002 := @gSseli (synCin A (synCnnc)) A (synC0c) p0001
  have p0003 :=
    @gCon3i (.classMem (synC0c) (synCin A (synCnnc))) (.classMem (synC0c) A) p0002
  have p0004 := @gNncex
  have p0005 := @gInex A (synCnnc) hyp_phiall_1 p0004
  have p0006 := @gPhialllem1 y (synCin A (synCnnc)) dv_cache_0001 p0005
  have p0007 :=
    @gSylancr (.neg (.classMem (synC0c) A)) (synWss (synCin A (synCnnc)) (synCnnc))
      (.neg (.classMem (synC0c) (synCin A (synCnnc))))
      (synWex y (.classEq (synCin A (synCnnc)) (synCphi (.cv y)))) p0000 p0003 p0006
  have p0008 := @gUncom (synCdif A (synCnnc)) (synCin A (synCnnc))
  have p0009 := @gInundif A (synCnnc)
  have p0010 :=
    @gEqtri (synCun (synCdif A (synCnnc)) (synCin A (synCnnc)))
      (synCun (synCin A (synCnnc)) (synCdif A (synCnnc))) A p0008 p0009
  have p0011 := @gUneq2 (synCin A (synCnnc)) (synCphi (.cv y)) (synCdif A (synCnnc))
  have p0012 :=
    @gSyl5eqr (.classEq (synCin A (synCnnc)) (synCphi (.cv y))) A
      (synCun (synCdif A (synCnnc)) (synCin A (synCnnc)))
      (synCun (synCdif A (synCnnc)) (synCphi (.cv y))) p0010 p0011
  have p0013 := @gPhiun (synCdif A (synCnnc)) (.cv y)
  have p0014 := @gIncom (synCdif A (synCnnc)) (synCnnc)
  have p0015 := @gDisjdif (synCnnc) A
  have p0016 :=
    @gEqtri (synCin (synCdif A (synCnnc)) (synCnnc))
      (synCin (synCnnc) (synCdif A (synCnnc))) (synC0) p0014 p0015
  have p0017 := @gPhidisjnn (synCdif A (synCnnc))
  have p0018 := Nominal.mp p0016 p0017
  have p0019 :=
    @gUneq1i (synCphi (synCdif A (synCnnc))) (synCdif A (synCnnc))
      (synCphi (.cv y)) p0018
  have p0020 :=
    @gEqtri (synCphi (synCun (synCdif A (synCnnc)) (.cv y)))
      (synCun (synCphi (synCdif A (synCnnc))) (synCphi (.cv y)))
      (synCun (synCdif A (synCnnc)) (synCphi (.cv y))) p0013 p0019
  have p0021 :=
    @gSyl6eqr (.classEq (synCin A (synCnnc)) (synCphi (.cv y))) A
      (synCun (synCdif A (synCnnc)) (synCphi (.cv y)))
      (synCphi (synCun (synCdif A (synCnnc)) (.cv y))) p0012 p0020
  have p0023 := @gDifex A (synCnnc) hyp_phiall_1 p0004
  have p0024 := @gVex y
  have p0025 := @gUnex (synCdif A (synCnnc)) (.cv y) p0023 p0024
  have p0026 := @gPhieq (.cv x) (synCun (synCdif A (synCnnc)) (.cv y))
  have p0027 :=
    @gEqeq2d (.classEq (.cv x) (synCun (synCdif A (synCnnc)) (.cv y)))
      (synCphi (.cv x)) (synCphi (synCun (synCdif A (synCnnc)) (.cv y))) A p0026
  have p0028 :=
    @gSpcev (.classEq A (synCphi (.cv x)))
      (.classEq A (synCphi (synCun (synCdif A (synCnnc)) (.cv y)))) x
      (synCun (synCdif A (synCnnc)) (.cv y)) dv_cache_0002 dv_cache_0003 p0025 p0027
  have p0029 :=
    @gSyl (.classEq (synCin A (synCnnc)) (synCphi (.cv y)))
      (.classEq A (synCphi (synCun (synCdif A (synCnnc)) (.cv y))))
      (synWex x (.classEq A (synCphi (.cv x)))) p0021 p0028
  have p0030 :=
    @gExlimiv (.classEq (synCin A (synCnnc)) (synCphi (.cv y)))
      (synWex x (.classEq A (synCphi (.cv x)))) y dv_cache_0004 p0029
  have p0031 :=
    @gSyl (.neg (.classMem (synC0c) A))
      (synWex y (.classEq (synCin A (synCnnc)) (synCphi (.cv y))))
      (synWex x (.classEq A (synCphi (.cv x)))) p0007 p0030
  exact p0031

/-- Checked nominal proof certificate identified upstream as `g_phiall`. -/
@[expose]
noncomputable def gPhiall (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (hyp_phiall_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (synWex x (synWo (.classEq A (synCphi (.cv x)))
          (.classEq A (synCun (synCphi (.cv x)) (synCsn (synC0c)))))) :=
  by
  have dv_cache_0001 : x ∉ ((synCdif A (synCsn (synC0c)))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, dv_A_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classMem (synC0c) A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, dv_A_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have p0000 := @gNeldifsn (synC0c) A
  have p0001 := @gSnex (synC0c)
  have p0002 := @gDifex A (synCsn (synC0c)) hyp_phiall_1 p0001
  have p0003 := @gPhialllem2 x (synCdif A (synCsn (synC0c))) dv_cache_0001 p0002
  have p0004 := Nominal.mp p0000 p0003
  have p0005 := @gDisjsn (synCdif A (synCsn (synC0c))) (synC0c)
  have p0006 :=
    @gMpbir
      (.classEq (synCin (synCdif A (synCsn (synC0c))) (synCsn (synC0c))) (synC0))
      (.neg (.classMem (synC0c) (synCdif A (synCsn (synC0c))))) p0000 p0005
  have p0007 := @gN0cnelphi (.cv x)
  have p0008 := @gDisjsn (synCphi (.cv x)) (synC0c)
  have p0009 :=
    @gMpbir (.classEq (synCin (synCphi (.cv x)) (synCsn (synC0c))) (synC0))
      (.neg (.classMem (synC0c) (synCphi (.cv x)))) p0007 p0008
  have p0010 :=
    @gEqtr4i (synCin (synCdif A (synCsn (synC0c))) (synCsn (synC0c))) (synC0)
      (synCin (synCphi (.cv x)) (synCsn (synC0c))) p0006 p0009
  have p0011 :=
    @gBiantru
      (.classEq (synCin (synCdif A (synCsn (synC0c))) (synCsn (synC0c)))
        (synCin (synCphi (.cv x)) (synCsn (synC0c))))
      (.classEq (synCun (synCdif A (synCsn (synC0c))) (synCsn (synC0c)))
        (synCun (synCphi (.cv x)) (synCsn (synC0c))))
      p0010
  have p0012 :=
    @gUnineq (synCdif A (synCsn (synC0c))) (synCphi (.cv x)) (synCsn (synC0c))
  have p0013 :=
    @gBitri
      (.classEq (synCun (synCdif A (synCsn (synC0c))) (synCsn (synC0c)))
        (synCun (synCphi (.cv x)) (synCsn (synC0c))))
      (synWa (.classEq (synCun (synCdif A (synCsn (synC0c))) (synCsn (synC0c)))
          (synCun (synCphi (.cv x)) (synCsn (synC0c))))
        (.classEq (synCin (synCdif A (synCsn (synC0c))) (synCsn (synC0c)))
          (synCin (synCphi (.cv x)) (synCsn (synC0c)))))
      (.classEq (synCdif A (synCsn (synC0c))) (synCphi (.cv x))) p0011 p0012
  have p0014 := @gDifsnid A (synC0c)
  have p0015 :=
    @gEqeq1d (.classMem (synC0c) A)
      (synCun (synCdif A (synCsn (synC0c))) (synCsn (synC0c))) A
      (synCun (synCphi (.cv x)) (synCsn (synC0c))) p0014
  have p0016 :=
    @gSyl5bbr (.classEq (synCdif A (synCsn (synC0c))) (synCphi (.cv x)))
      (.classEq (synCun (synCdif A (synCsn (synC0c))) (synCsn (synC0c)))
        (synCun (synCphi (.cv x)) (synCsn (synC0c))))
      (.classMem (synC0c) A)
      (.classEq A (synCun (synCphi (.cv x)) (synCsn (synC0c)))) p0013 p0015
  have p0017 :=
    @gExbidv (.classMem (synC0c) A)
      (.classEq (synCdif A (synCsn (synC0c))) (synCphi (.cv x)))
      (.classEq A (synCun (synCphi (.cv x)) (synCsn (synC0c)))) x dv_cache_0002 p0016
  have p0018 :=
    @gMpbii (.classMem (synC0c) A)
      (synWex x (.classEq (synCdif A (synCsn (synC0c))) (synCphi (.cv x))))
      (synWex x (.classEq A (synCun (synCphi (.cv x)) (synCsn (synC0c))))) p0004
      p0017
  have p0019 :=
    @gOlc (.classEq A (synCun (synCphi (.cv x)) (synCsn (synC0c))))
      (.classEq A (synCphi (.cv x)))
  have p0020 :=
    @gEximi (.classEq A (synCun (synCphi (.cv x)) (synCsn (synC0c))))
      (synWo (.classEq A (synCphi (.cv x)))
        (.classEq A (synCun (synCphi (.cv x)) (synCsn (synC0c)))))
      x p0019
  have p0021 :=
    @gSyl (.classMem (synC0c) A)
      (synWex x (.classEq A (synCun (synCphi (.cv x)) (synCsn (synC0c)))))
      (synWex x (synWo (.classEq A (synCphi (.cv x)))
          (.classEq A (synCun (synCphi (.cv x)) (synCsn (synC0c))))))
      p0018 p0020
  have p0022 := @gPhialllem2 x A dv_cache_0003 hyp_phiall_1
  have p0023 :=
    @gOrc (.classEq A (synCphi (.cv x)))
      (.classEq A (synCun (synCphi (.cv x)) (synCsn (synC0c))))
  have p0024 :=
    @gEximi (.classEq A (synCphi (.cv x)))
      (synWo (.classEq A (synCphi (.cv x)))
        (.classEq A (synCun (synCphi (.cv x)) (synCsn (synC0c)))))
      x p0023
  have p0025 :=
    @gSyl (.neg (.classMem (synC0c) A)) (synWex x (.classEq A (synCphi (.cv x))))
      (synWex x (synWo (.classEq A (synCphi (.cv x)))
          (.classEq A (synCun (synCphi (.cv x)) (synCsn (synC0c))))))
      p0022 p0024
  have p0026 :=
    @gPm261i (.classMem (synC0c) A)
      (synWex x (synWo (.classEq A (synCphi (.cv x)))
          (.classEq A (synCun (synCphi (.cv x)) (synCsn (synC0c))))))
      p0021 p0025
  exact p0026


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part038`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_opeq`. -/
@[expose]
noncomputable def gOpeq (A : Class) :
    Nominal.NPrf (.classEq A (synCop (synCproj1 A) (synCproj2 A))) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have dv_cache_0001 : x ∉ ((synCproj1 A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCproj1 A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1, fresh_y_not_A,
          not_false_eq_true])
  have dv_cache_0003 : x ∉ ((synCproj2 A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj2, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0004 : y ∉ ((synCproj2 A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj2, fresh_y_not_A,
          not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Class.cab z (.classMem (synCphi (.cv z)) A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_y_ne_z, fresh_y_not_A, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0008 : z ∉ ((Wff.classMem (synCphi (.cv y)) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_not_A, or_false, not_false_eq_true])
  have dv_cache_0009 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0010 : y ∉ ((Wff.classMem (.cv x) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_A, or_false, not_false_eq_true])
  have dv_cache_0011 :
    y ∉
      ((Class.cab z (.classMem (synCun (synCphi (.cv z)) (synCsn (synC0c))) A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_ne_z, fresh_y_not_A,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0012 :
    z ∉ ((Wff.classMem (synCun (synCphi (.cv y)) (synCsn (synC0c))) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_not_A, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((Class.cv x)).fv :=
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
          fresh_y_ne_x, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOp x y
      (synCproj1 A) (synCproj2 A) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfProj1 z A
      dv_cache_0006
  have p0002 :=
    @gRexeqi (.classEq (.cv x) (synCphi (.cv y))) y (synCproj1 A)
      (.cab z (.classMem (synCphi (.cv z)) A)) dv_cache_0002 dv_cache_0007 p0001
  have p0003 := @gPhieq (.cv z) (.cv y)
  have p0004_e00_recanon :
    Nominal.NPrf (.imp (.objEq z y) (.classEq (synCphi (.cv z)) (synCphi (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCphi synWrex synWex synWa synCif synWo synCnnc synCint synCplc
          synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0003
  have p0004 :=
    @gEleq1d (.objEq z y) (synCphi (.cv z)) (synCphi (.cv y)) A p0004_e00_recanon
  have p0005 :=
    @gRexab (.classMem (synCphi (.cv z)) A) (.classMem (synCphi (.cv y)) A)
      (.classEq (.cv x) (synCphi (.cv y))) y z dv_cache_0008 dv_cache_0009 p0004
  have p0006 :=
    @gAncom (.classMem (synCphi (.cv y)) A) (.classEq (.cv x) (synCphi (.cv y)))
  have p0007 := @gEleq1 (.cv x) (synCphi (.cv y)) A
  have p0008 :=
    @gPm532i (.classEq (.cv x) (synCphi (.cv y))) (.classMem (.cv x) A)
      (.classMem (synCphi (.cv y)) A) p0007
  have p0009 :=
    @gBitr4i
      (synWa (.classMem (synCphi (.cv y)) A) (.classEq (.cv x) (synCphi (.cv y))))
      (synWa (.classEq (.cv x) (synCphi (.cv y))) (.classMem (synCphi (.cv y)) A))
      (synWa (.classEq (.cv x) (synCphi (.cv y))) (.classMem (.cv x) A)) p0006 p0008
  have p0010 :=
    @gExbii
      (synWa (.classMem (synCphi (.cv y)) A) (.classEq (.cv x) (synCphi (.cv y))))
      (synWa (.classEq (.cv x) (synCphi (.cv y))) (.classMem (.cv x) A)) y p0009
  have p0011 :=
    @gN1941v (.classEq (.cv x) (synCphi (.cv y))) (.classMem (.cv x) A) y
      dv_cache_0010
  have p0012 :=
    @gAncom (synWex y (.classEq (.cv x) (synCphi (.cv y)))) (.classMem (.cv x) A)
  have p0013 :=
    @gN3bitri
      (synWex y
        (synWa (.classMem (synCphi (.cv y)) A) (.classEq (.cv x) (synCphi (.cv y)))))
      (synWex y (synWa (.classEq (.cv x) (synCphi (.cv y))) (.classMem (.cv x) A)))
      (synWa (synWex y (.classEq (.cv x) (synCphi (.cv y)))) (.classMem (.cv x) A))
      (synWa (.classMem (.cv x) A) (synWex y (.classEq (.cv x) (synCphi (.cv y)))))
      p0010 p0011 p0012
  have p0014 :=
    @gN3bitri (synWrex y (synCproj1 A) (.classEq (.cv x) (synCphi (.cv y))))
      (synWrex y (.cab z (.classMem (synCphi (.cv z)) A))
        (.classEq (.cv x) (synCphi (.cv y))))
      (synWex y
        (synWa (.classMem (synCphi (.cv y)) A) (.classEq (.cv x) (synCphi (.cv y)))))
      (synWa (.classMem (.cv x) A) (synWex y (.classEq (.cv x) (synCphi (.cv y)))))
      p0002 p0005 p0013
  have p0015 :=
    @gAbbii (synWrex y (synCproj1 A) (.classEq (.cv x) (synCphi (.cv y))))
      (synWa (.classMem (.cv x) A) (synWex y (.classEq (.cv x) (synCphi (.cv y))))) x
      p0014
  have p0016 :=
    (Nominal.classEqRefl (synCrab x A (synWex y (.classEq (.cv x) (synCphi (.cv y))))))
  have p0017 :=
    @gEqtr4i (.cab x (synWrex y (synCproj1 A) (.classEq (.cv x) (synCphi (.cv y)))))
      (.cab x (synWa (.classMem (.cv x) A) (synWex y (.classEq (.cv x) (synCphi (.cv y))))))
      (synCrab x A (synWex y (.classEq (.cv x) (synCphi (.cv y))))) p0015 p0016
  have p0018 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfProj2 z A
      dv_cache_0006
  have p0019 :=
    @gRexeqi (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))) y
      (synCproj2 A)
      (.cab z (.classMem (synCun (synCphi (.cv z)) (synCsn (synC0c))) A))
      dv_cache_0004 dv_cache_0011 p0018
  have p0020_e00_recanon :
    Nominal.NPrf (.imp (.objEq z y) (.classEq (synCphi (.cv z)) (synCphi (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCphi synWrex synWex synWa synCif synWo synCnnc synCint synCplc
          synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0003
  have p0020 :=
    @gUneq1d (.objEq z y) (synCphi (.cv z)) (synCphi (.cv y)) (synCsn (synC0c))
      p0020_e00_recanon
  have p0021 :=
    @gEleq1d (.objEq z y) (synCun (synCphi (.cv z)) (synCsn (synC0c)))
      (synCun (synCphi (.cv y)) (synCsn (synC0c))) A p0020
  have p0022 :=
    @gRexab (.classMem (synCun (synCphi (.cv z)) (synCsn (synC0c))) A)
      (.classMem (synCun (synCphi (.cv y)) (synCsn (synC0c))) A)
      (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))) y z
      dv_cache_0012 dv_cache_0009 p0021
  have p0023 :=
    @gAncom (.classMem (synCun (synCphi (.cv y)) (synCsn (synC0c))) A)
      (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))
  have p0024 := @gEleq1 (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))) A
  have p0025 :=
    @gPm532i (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))
      (.classMem (.cv x) A) (.classMem (synCun (synCphi (.cv y)) (synCsn (synC0c))) A)
      p0024
  have p0026 :=
    @gBitr4i
      (synWa (.classMem (synCun (synCphi (.cv y)) (synCsn (synC0c))) A)
        (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))
      (synWa (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))
        (.classMem (synCun (synCphi (.cv y)) (synCsn (synC0c))) A))
      (synWa (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))
        (.classMem (.cv x) A))
      p0023 p0025
  have p0027 :=
    @gExbii
      (synWa (.classMem (synCun (synCphi (.cv y)) (synCsn (synC0c))) A)
        (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))
      (synWa (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))
        (.classMem (.cv x) A))
      y p0026
  have p0028 :=
    @gN1941v (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))
      (.classMem (.cv x) A) y dv_cache_0010
  have p0029 :=
    @gAncom
      (synWex y (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))
      (.classMem (.cv x) A)
  have p0030 :=
    @gN3bitri
      (synWex y (synWa (.classMem (synCun (synCphi (.cv y)) (synCsn (synC0c))) A)
          (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))))
      (synWex y (synWa (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))
          (.classMem (.cv x) A)))
      (synWa (synWex y (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))
        (.classMem (.cv x) A))
      (synWa (.classMem (.cv x) A)
        (synWex y (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))))
      p0027 p0028 p0029
  have p0031 :=
    @gN3bitri
      (synWrex y (synCproj2 A)
        (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))
      (synWrex y (.cab z (.classMem (synCun (synCphi (.cv z)) (synCsn (synC0c))) A))
        (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))
      (synWex y (synWa (.classMem (synCun (synCphi (.cv y)) (synCsn (synC0c))) A)
          (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))))
      (synWa (.classMem (.cv x) A)
        (synWex y (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))))
      p0019 p0022 p0030
  have p0032 :=
    @gAbbii
      (synWrex y (synCproj2 A)
        (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))
      (synWa (.classMem (.cv x) A)
        (synWex y (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))))
      x p0031
  have p0033 :=
    (Nominal.classEqRefl (synCrab x A
        (synWex y (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))))
  have p0034 :=
    @gEqtr4i
      (.cab x (synWrex y (synCproj2 A)
          (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))))
      (.cab x (synWa (.classMem (.cv x) A) (synWex y
            (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))))
      (synCrab x A
        (synWex y (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))))
      p0032 p0033
  have p0035 :=
    @gUneq12i (.cab x (synWrex y (synCproj1 A) (.classEq (.cv x) (synCphi (.cv y)))))
      (synCrab x A (synWex y (.classEq (.cv x) (synCphi (.cv y)))))
      (.cab x (synWrex y (synCproj2 A)
          (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))))
      (synCrab x A
        (synWex y (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))))
      p0017 p0034
  have p0036 :=
    @gUnrab (synWex y (.classEq (.cv x) (synCphi (.cv y))))
      (synWex y (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))) x A
  have p0037 :=
    @gRabid2
      (synWo (synWex y (.classEq (.cv x) (synCphi (.cv y))))
        (synWex y (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))))
      x A dv_cache_0013
  have p0038 := @gVex x
  have p0039 := @gPhiall y (.cv x) dv_cache_0014 p0038
  have p0040 :=
    @gN1943 (.classEq (.cv x) (synCphi (.cv y)))
      (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))) y
  have p0041 :=
    @gMpbi
      (synWex y (synWo (.classEq (.cv x) (synCphi (.cv y)))
          (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))))
      (synWo (synWex y (.classEq (.cv x) (synCphi (.cv y))))
        (synWex y (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))))
      p0039 p0040
  have p0042 :=
    @gA1i
      (synWo (synWex y (.classEq (.cv x) (synCphi (.cv y))))
        (synWex y (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))))
      (.classMem (.cv x) A) p0041
  have p0043 :=
    @gMprgbir
      (.classEq A (synCrab x A (synWo (synWex y (.classEq (.cv x) (synCphi (.cv y))))
            (synWex y (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))))))
      (synWo (synWex y (.classEq (.cv x) (synCphi (.cv y))))
        (synWex y (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))))
      x A p0037 p0042
  have p0044 :=
    @gEqtr4i
      (synCun (synCrab x A (synWex y (.classEq (.cv x) (synCphi (.cv y))))) (synCrab x A
          (synWex y (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))))
      (synCrab x A (synWo (synWex y (.classEq (.cv x) (synCphi (.cv y)))) (synWex y
            (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))))
      A p0036 p0043
  have p0045 :=
    @gN3eqtrri (synCop (synCproj1 A) (synCproj2 A))
      (synCun (.cab x (synWrex y (synCproj1 A) (.classEq (.cv x) (synCphi (.cv y)))))
        (.cab x (synWrex y (synCproj2 A)
            (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))))
      (synCun (synCrab x A (synWex y (.classEq (.cv x) (synCphi (.cv y))))) (synCrab x A
          (synWex y (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))))
      A p0000 p0035 p0044
  exact p0045

/-- Checked nominal proof certificate identified upstream as `g_opeqexb`. -/
@[expose]
noncomputable def gOpeqexb (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (.classMem A (synCvv))
        (synWex x (synWex y (.classEq A (synCop (.cv x) (.cv y)))))) :=
  by
  have dv_cache_0001 : y ∉ ((Wff.classEq (.cv x) (synCproj1 A))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_y), dv_A_y, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classEq (.cv y) (synCproj2 A))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj2, Finset.mem_union,
          Finset.mem_singleton, dv_x_y, dv_A_x, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((synCproj1 A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1, dv_A_x,
          not_false_eq_true])
  have dv_cache_0004 : y ∉ ((synCproj2 A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj2, dv_A_y,
          not_false_eq_true])
  have p0000 := @gOpexb (synCproj1 A) (synCproj2 A)
  have p0001 := @gOpeq A
  have p0002 := @gEleq1i A (synCop (synCproj1 A) (synCproj2 A)) (synCvv) p0001
  have p0003 :=
    @gEeanv (.classEq (.cv x) (synCproj1 A)) (.classEq (.cv y) (synCproj2 A)) x y
      dv_cache_0001 dv_cache_0002
  have p0004 :=
    @gEqeq1i A (synCop (synCproj1 A) (synCproj2 A)) (synCop (.cv x) (.cv y)) p0001
  have p0005 := @gEqcom (synCop (synCproj1 A) (synCproj2 A)) (synCop (.cv x) (.cv y))
  have p0006 := @gOpth (.cv x) (.cv y) (synCproj1 A) (synCproj2 A)
  have p0007 :=
    @gN3bitri (.classEq A (synCop (.cv x) (.cv y)))
      (.classEq (synCop (synCproj1 A) (synCproj2 A)) (synCop (.cv x) (.cv y)))
      (.classEq (synCop (.cv x) (.cv y)) (synCop (synCproj1 A) (synCproj2 A)))
      (synWa (.classEq (.cv x) (synCproj1 A)) (.classEq (.cv y) (synCproj2 A))) p0004
      p0005 p0006
  have p0008 :=
    @gN2exbii (.classEq A (synCop (.cv x) (.cv y)))
      (synWa (.classEq (.cv x) (synCproj1 A)) (.classEq (.cv y) (synCproj2 A))) x y
      p0007
  have p0009 := @gIsset x (synCproj1 A) dv_cache_0003
  have p0010 := @gIsset y (synCproj2 A) dv_cache_0004
  have p0011 :=
    @gAnbi12i (.classMem (synCproj1 A) (synCvv))
      (synWex x (.classEq (.cv x) (synCproj1 A))) (.classMem (synCproj2 A) (synCvv))
      (synWex y (.classEq (.cv y) (synCproj2 A))) p0009 p0010
  have p0012 :=
    @gN3bitr4i
      (synWex x (synWex y
          (synWa (.classEq (.cv x) (synCproj1 A)) (.classEq (.cv y) (synCproj2 A)))))
      (synWa (synWex x (.classEq (.cv x) (synCproj1 A)))
        (synWex y (.classEq (.cv y) (synCproj2 A))))
      (synWex x (synWex y (.classEq A (synCop (.cv x) (.cv y)))))
      (synWa (.classMem (synCproj1 A) (synCvv)) (.classMem (synCproj2 A) (synCvv)))
      p0003 p0008 p0011
  have p0013 :=
    @gN3bitr4i (.classMem (synCop (synCproj1 A) (synCproj2 A)) (synCvv))
      (synWa (.classMem (synCproj1 A) (synCvv)) (.classMem (synCproj2 A) (synCvv)))
      (.classMem A (synCvv))
      (synWex x (synWex y (.classEq A (synCop (.cv x) (.cv y))))) p0000 p0002 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_opeqex`. -/
@[expose]
noncomputable def gOpeqex (x : Var) (y : Var) (A : Class) (V : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (.classMem A V) (synWex x (synWex y (.classEq A (synCop (.cv x) (.cv y)))))) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0003 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 := @gElex A V
  have p0001 := @gOpeqexb x y A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0002 :=
    @gSylib (.classMem A V) (.classMem A (synCvv))
      (synWex x (synWex y (.classEq A (synCop (.cv x) (.cv y))))) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_opabbid`. -/
@[expose]
noncomputable def gOpabbid (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (hyp_opabbid_1 : Nominal.NPrf (synWnf x ph))
    (hyp_opabbid_2 : Nominal.NPrf (synWnf y ph))
    (hyp_opabbid_3 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (.classEq (synCopab x y ps) (synCopab x y ch))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_z_not_ps : z ∉ ps.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_ch : z ∉ ch.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have dv_cache_0001 : z ∉ (ph).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_ph, not_false_eq_true])
  have dv_cache_0002 : z ∉ (ps).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_ps, not_false_eq_true])
  have dv_cache_0003 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0004 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0005 : z ∉ (ch).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_ch, not_false_eq_true])
  have p0000 :=
    @gAnbi2d ph ps ch (.classEq (.cv z) (synCop (.cv x) (.cv y))) hyp_opabbid_3
  have p0001 :=
    @gExbid ph (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ps)
      (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ch) y hyp_opabbid_2 p0000
  have p0002 :=
    @gExbid ph (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ps))
      (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ch)) x hyp_opabbid_1
      p0001
  have p0003 :=
    @gAbbidv ph
      (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ps)))
      (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ch))) z
      dv_cache_0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOpab ps x y z
      dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOpab ch x y z
      dv_cache_0005 dv_cache_0003 dv_cache_0004
  have p0006 :=
    @gN3eqtr4g ph
      (.cab z (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ps))))
      (.cab z (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ch))))
      (synCopab x y ps) (synCopab x y ch) p0003 p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_opabbidv`. -/
@[expose]
noncomputable def gOpabbidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv)
    (hyp_opabbidv_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (.classEq (synCopab x y ps) (synCopab x y ch))) :=
  by
  have dv_cache_0001 : x ∉ (ph).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (ph).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_y, not_false_eq_true])
  have p0000 := @gNfv ph x dv_cache_0001
  have p0001 := @gNfv ph y dv_cache_0002
  have p0002 := @gOpabbid ph ps ch x y p0000 p0001 hyp_opabbidv_1
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_opabbii`. -/
@[expose]
noncomputable def gOpabbii (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_opabbii_1 : Nominal.NPrf (synWb ph ps)) :
    Nominal.NPrf (.classEq (synCopab x y ph) (synCopab x y ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have dv_cache_0001 : x ∉ ((Wff.classEq (.cv z) (.cv z))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Wff.classEq (.cv z) (.cv z))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_z, or_false, not_false_eq_true])
  have p0000 := @gEqid (.cv z)
  have p0001 := @gA1i (synWb ph ps) (.classEq (.cv z) (.cv z)) hyp_opabbii_1
  have p0002 :=
    @gOpabbidv (.classEq (.cv z) (.cv z)) ph ps x y dv_cache_0001 dv_cache_0002 p0001
  have p0003 := Nominal.mp p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_nfopab`. -/
@[expose]
noncomputable def gNfopab (ph : Wff) (x : Var) (y : Var) (z : Var) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) (hyp_nfopab_1 : Nominal.NPrf (synWnf z ph)) :
    Nominal.NPrf (synWnfc z (synCopab x y ph)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  let w : Var := freshVar proofSupport 0
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z_ne_w : z ≠ w := Ne.symm fresh_w_ne_z
  have dv_cache_0001 : w ∉ (ph).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_ph, not_false_eq_true])
  have dv_cache_0002 : x ≠ w := by
    clear dv_cache_0001
    exact (show x ≠ w from (by exact fresh_x_ne_w))
  have dv_cache_0003 : y ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show y ≠ w from (by exact fresh_y_ne_w))
  have dv_cache_0004 : z ∉ ((Wff.classEq (.cv w) (synCop (.cv x) (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_w, (Ne.symm dv_x_z), (Ne.symm dv_y_z),
          or_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOpab ph x y w
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @gNfv (.classEq (.cv w) (synCop (.cv x) (.cv y))) z dv_cache_0004
  have p0002 :=
    @gNfan (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph z p0001 hyp_nfopab_1
  have p0003 := @gNfex (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph) z y p0002
  have p0004 :=
    @gNfex (synWex y (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph)) z x p0003
  have p0005 :=
    @gNfab
      (synWex x (synWex y (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph))) z w
      p0004
  have p0006 :=
    @gNfcxfr z (synCopab x y ph)
      (.cab w (synWex x (synWex y (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph))))
      p0000 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_nfopab1`. -/
@[expose]
noncomputable def gNfopab1 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (synWnfc x (synCopab x y ph)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have dv_cache_0001 : z ∉ (ph).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_ph, not_false_eq_true])
  have dv_cache_0002 : x ≠ z := by
    clear dv_cache_0001
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0003 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOpab ph x y z
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @gNfe1 (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ph)) x
  have p0002 :=
    @gNfab
      (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ph))) x z
      p0001
  have p0003 :=
    @gNfcxfr x (synCopab x y ph)
      (.cab z (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ph))))
      p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_nfopab2`. -/
@[expose]
noncomputable def gNfopab2 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (synWnfc y (synCopab x y ph)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have dv_cache_0001 : z ∉ (ph).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_ph, not_false_eq_true])
  have dv_cache_0002 : x ≠ z := by
    clear dv_cache_0001
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0003 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOpab ph x y z
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @gNfe1 (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ph) y
  have p0002 :=
    @gNfex (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ph)) y x p0001
  have p0003 :=
    @gNfab
      (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ph))) y z
      p0002
  have p0004 :=
    @gNfcxfr y (synCopab x y ph)
      (.cab z (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ph))))
      p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_cbvopab1`. -/
@[expose]
noncomputable def gCbvopab1 (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var)
    (dv_x_y : x ≠ y) (dv_y_z : y ≠ z) (hyp_cbvopab1_1 : Nominal.NPrf (synWnf z ph))
    (hyp_cbvopab1_2 : Nominal.NPrf (synWnf x ps))
    (hyp_cbvopab1_3 : Nominal.NPrf (.imp (.objEq x z) (synWb ph ps))) :
    Nominal.NPrf (.classEq (synCopab x y ph) (synCopab z y ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  let w : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_w_not_ps : w ∉ ps.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z_ne_w : z ≠ w := Ne.symm fresh_w_ne_z
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_v_not_ph : v ∉ ph.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_v_not_ps : v ∉ ps.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_v_ne_x : v ≠ x := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_v : x ≠ v := Ne.symm fresh_v_ne_x
  have fresh_v_ne_y : v ≠ y := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_v : y ≠ v := Ne.symm fresh_v_ne_y
  have fresh_v_ne_z : v ≠ z := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z_ne_v : z ≠ v := Ne.symm fresh_v_ne_z
  have fresh_w_ne_v : w ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_v_ne_w : v ≠ w := Ne.symm fresh_w_ne_v
  have dv_cache_0001 :
    v ∉ ((synWex y (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_v_ne_w, fresh_v_ne_x,
          fresh_v_ne_y, fresh_v_not_ph, or_false, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classEq (.cv w) (synCop (.cv v) (.cv y)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_w, fresh_x_ne_v, dv_x_y, or_false,
          not_false_eq_true])
  have dv_cache_0003 : x ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ v from (by exact fresh_x_ne_v))
  have dv_cache_0004 : y ∉ ((Wff.classEq (.cv x) (.cv v))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_y), fresh_y_ne_v, or_false,
          not_false_eq_true])
  have dv_cache_0005 : z ∉ ((Wff.classEq (.cv w) (synCop (.cv v) (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_w, fresh_z_ne_v, (Ne.symm dv_y_z), or_false,
          not_false_eq_true])
  have dv_cache_0006 : v ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show v ≠ z from (by exact fresh_v_ne_z))
  have dv_cache_0007 :
    v ∉ ((synWex y (synWa (.classEq (.cv w) (synCop (.cv z) (.cv y))) ps))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_v_ne_w, fresh_v_ne_z,
          fresh_v_ne_y, fresh_v_not_ps, or_false, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((Wff.classEq (.cv v) (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_v, dv_y_z, or_false, not_false_eq_true])
  have dv_cache_0009 : w ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_ph, not_false_eq_true])
  have dv_cache_0010 : x ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ w from (by exact fresh_x_ne_w))
  have dv_cache_0011 : y ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show y ≠ w from (by exact fresh_y_ne_w))
  have dv_cache_0012 : w ∉ (ps).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_ps, not_false_eq_true])
  have dv_cache_0013 : z ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have p0000 :=
    @gNfv (synWex y (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph)) v
      dv_cache_0001
  have p0001 := @gNfv (.classEq (.cv w) (synCop (.cv v) (.cv y))) x dv_cache_0002
  have p0002 := @gNfs1v ph x v dv_cache_0003
  have p0003 :=
    @gNfan (.classEq (.cv w) (synCop (.cv v) (.cv y))) (synWsb v x ph) x p0001 p0002
  have p0004 :=
    @gNfex (synWa (.classEq (.cv w) (synCop (.cv v) (.cv y))) (synWsb v x ph)) x y
      p0003
  have p0005 := @gOpeq1 (.cv x) (.cv v) (.cv y)
  have p0006 :=
    @gEqeq2d (.classEq (.cv x) (.cv v)) (synCop (.cv x) (.cv y))
      (synCop (.cv v) (.cv y)) (.cv w) p0005
  have p0007 := @gSbequ12 ph x v
  have p0008_e01_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) (.cv v)) (synWb ph (synWsb v x ph))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWsb synWa synWex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0008 :=
    @gAnbi12d (.classEq (.cv x) (.cv v)) (.classEq (.cv w) (synCop (.cv x) (.cv y)))
      (.classEq (.cv w) (synCop (.cv v) (.cv y))) ph (synWsb v x ph) p0006
      p0008_e01_recanon
  have p0009 :=
    @gExbidv (.classEq (.cv x) (.cv v))
      (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph)
      (synWa (.classEq (.cv w) (synCop (.cv v) (.cv y))) (synWsb v x ph)) y
      dv_cache_0004 p0008
  have p0010_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq x v)
        (synWb (synWex y (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph)) (synWex y
            (synWa (.classEq (.cv w) (synCop (.cv v) (.cv y))) (synWsb v x ph))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWex synWa synCop synCun synCnin synWnan synCcompl synWrex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0009
  have p0010 :=
    @gCbvex (synWex y (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph))
      (synWex y (synWa (.classEq (.cv w) (synCop (.cv v) (.cv y))) (synWsb v x ph))) x
      v p0000 p0004 p0010_e02_recanon
  have p0011 := @gNfv (.classEq (.cv w) (synCop (.cv v) (.cv y))) z dv_cache_0005
  have p0012 := @gNfsb ph x v z dv_cache_0006 hyp_cbvopab1_1
  have p0013 :=
    @gNfan (.classEq (.cv w) (synCop (.cv v) (.cv y))) (synWsb v x ph) z p0011 p0012
  have p0014 :=
    @gNfex (synWa (.classEq (.cv w) (synCop (.cv v) (.cv y))) (synWsb v x ph)) z y
      p0013
  have p0015 :=
    @gNfv (synWex y (synWa (.classEq (.cv w) (synCop (.cv z) (.cv y))) ps)) v
      dv_cache_0007
  have p0016 := @gOpeq1 (.cv v) (.cv z) (.cv y)
  have p0017 :=
    @gEqeq2d (.classEq (.cv v) (.cv z)) (synCop (.cv v) (.cv y))
      (synCop (.cv z) (.cv y)) (.cv w) p0016
  have p0018 := @gSbequ ph v z x
  have p0019 := @gSbie ph ps x z hyp_cbvopab1_2 hyp_cbvopab1_3
  have p0020_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv v) (.cv z)) (synWb (synWsb v x ph) (synWsb z x ph))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWsb synWa synWex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0018
  have p0020 :=
    @gSyl6bb (.classEq (.cv v) (.cv z)) (synWsb v x ph) (synWsb z x ph) ps
      p0020_e00_recanon p0019
  have p0021 :=
    @gAnbi12d (.classEq (.cv v) (.cv z)) (.classEq (.cv w) (synCop (.cv v) (.cv y)))
      (.classEq (.cv w) (synCop (.cv z) (.cv y))) (synWsb v x ph) ps p0017 p0020
  have p0022 :=
    @gExbidv (.classEq (.cv v) (.cv z))
      (synWa (.classEq (.cv w) (synCop (.cv v) (.cv y))) (synWsb v x ph))
      (synWa (.classEq (.cv w) (synCop (.cv z) (.cv y))) ps) y dv_cache_0008 p0021
  have p0023_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq v z) (synWb (synWex y
            (synWa (.classEq (.cv w) (synCop (.cv v) (.cv y))) (synWsb v x ph)))
          (synWex y (synWa (.classEq (.cv w) (synCop (.cv z) (.cv y))) ps)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWex synWa synCop synCun synCnin synWnan synCcompl synWrex
          synCphi synWsb
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0022
  have p0023 :=
    @gCbvex
      (synWex y (synWa (.classEq (.cv w) (synCop (.cv v) (.cv y))) (synWsb v x ph)))
      (synWex y (synWa (.classEq (.cv w) (synCop (.cv z) (.cv y))) ps)) v z p0014 p0015
      p0023_e02_recanon
  have p0024 :=
    @gBitri
      (synWex x (synWex y (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph)))
      (synWex v (synWex y
          (synWa (.classEq (.cv w) (synCop (.cv v) (.cv y))) (synWsb v x ph))))
      (synWex z (synWex y (synWa (.classEq (.cv w) (synCop (.cv z) (.cv y))) ps)))
      p0010 p0023
  have p0025 :=
    @gAbbii
      (synWex x (synWex y (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph)))
      (synWex z (synWex y (synWa (.classEq (.cv w) (synCop (.cv z) (.cv y))) ps))) w
      p0024
  have p0026 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOpab ph x y w
      dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0027 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOpab ps z y w
      dv_cache_0012 dv_cache_0013 dv_cache_0011
  have p0028 :=
    @gN3eqtr4i
      (.cab w (synWex x (synWex y (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph))))
      (.cab w (synWex z (synWex y (synWa (.classEq (.cv w) (synCop (.cv z) (.cv y))) ps))))
      (synCopab x y ph) (synCopab z y ps) p0025 p0026 p0027
  exact p0028


end NFChoice.DirectNominalPrf.WPPReplay

end
