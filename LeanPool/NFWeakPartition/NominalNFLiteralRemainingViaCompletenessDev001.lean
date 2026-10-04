/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalOneFreeCompletenessBridgeDev003
public import LeanPool.NFWeakPartition.NFCompactLeafFinalGate

/-! NF weak partition development: NominalNFLiteralRemainingViaCompletenessDev001. -/


public section

namespace NFChoice.DirectNominalPrf.Nominal.NFLiteralRemainingViaCompletenessDev001

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.DirectNominalPrf.Nominal
open NFChoice.DirectNominalPrf.Nominal.NFLiteralHandlers
open NFChoice.DirectNominalPrf.Nominal.OneFreeCompletenessBridgeDev003

/-- Close finite-variable freshness goals for the literal NF axiom wrappers. -/
macro "nfWeakPartitionFreshness" : tactic =>
  `(tactic|
    first
    | ( intro a ha
        simp only [fv_syn_wex, fv_syn_wb, fv_syn_wa, fv_syn_copk, fv_syn_csn, Wff.fv,
          Class.fv, Finset.mem_erase, Finset.mem_union, Finset.mem_singleton] at ha ⊢
        simp_all <;> aesop)
    | ( simp only [fv_syn_wex, fv_syn_wb, fv_syn_wa, fv_syn_copk, fv_syn_csn, Wff.fv,
          Class.fv, Finset.mem_erase, Finset.mem_union, Finset.mem_singleton]
        aesop))

theorem axCnvFv (x y z w : Var) (_hxy : x ≠ y) (_hxz : x ≠ z) (_hxw : x ≠ w)
    (_hyz : y ≠ z) (_hyw : y ≠ w) (_hzw : z ≠ w) :
    (axCnvGoal x y z w).fv ⊆ ({ x } : Finset Var) :=
  by
  simp only [axCnvGoal]
  nfWeakPartitionFreshness

/-- Proof-translation construction identified upstream as `axCnv`. -/
@[expose]
noncomputable def axCnv (x y z w : Var) (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) : NPrf (axCnvGoal x y z w) :=
  oneFreeNPrfOfValidity x (axCnvGoal x y z w) (axCnvFv x y z w hxy hxz hxw hyz hyw hzw)
    (by
      intro S _ hNF
      simpa [axCnvGoal] using
        (NFChoice.Compiler.NFCompactLeafFinalGate.axCnvCompact hNF x y z w hxy hxz hxw hyz
          hyw hzw))

theorem axSsetFv (x y z w : Var) (_hxy : x ≠ y) (_hxz : x ≠ z) (_hxw : x ≠ w)
    (_hyz : y ≠ z) (_hyw : y ≠ w) (_hzw : z ≠ w) :
    (axSsetGoal x y z w).fv ⊆ ({ x } : Finset Var) :=
  by
  simp only [axSsetGoal]
  nfWeakPartitionFreshness

/-- Proof-translation construction identified upstream as `axSset`. -/
@[expose]
noncomputable def axSset (x y z w : Var) (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) : NPrf (axSsetGoal x y z w) :=
  oneFreeNPrfOfValidity x (axSsetGoal x y z w) (axSsetFv x y z w hxy hxz hxw hyz hyw hzw)
    (by
      intro S _ hNF
      simpa [axSsetGoal] using
        (NFChoice.Compiler.NFCompactLeafFinalGate.axSsetCompact hNF x y z w hxy hxz hxw
          hyz hyw hzw))

theorem axSiFv (x y z w : Var) (_hxy : x ≠ y) (_hxz : x ≠ z) (_hxw : x ≠ w) (_hyz : y ≠ z)
    (_hyw : y ≠ w) (_hzw : z ≠ w) : (axSiGoal x y z w).fv ⊆ ({ x } : Finset Var) :=
  by
  simp only [axSiGoal]
  nfWeakPartitionFreshness

/-- Proof-translation construction identified upstream as `axSi`. -/
@[expose]
noncomputable def axSi (x y z w : Var) (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) : NPrf (axSiGoal x y z w) :=
  oneFreeNPrfOfValidity x (axSiGoal x y z w) (axSiFv x y z w hxy hxz hxw hyz hyw hzw)
    (by
      intro S _ hNF
      simpa [axSiGoal] using
        (NFChoice.Compiler.NFCompactLeafFinalGate.axSiCompact hNF x y z w hxy hxz hxw hyz
          hyw hzw))

theorem axIns2Fv (x y z w t : Var) (_hxy : x ≠ y) (_hxz : x ≠ z) (_hxw : x ≠ w)
    (_hxt : x ≠ t) (_hyz : y ≠ z) (_hyw : y ≠ w) (_hyt : y ≠ t) (_hzw : z ≠ w)
    (_hzt : z ≠ t) (_hwt : w ≠ t) : (axIns2Goal x y z w t).fv ⊆ ({ x } : Finset Var) :=
  by
  simp only [axIns2Goal]
  nfWeakPartitionFreshness

/-- Proof-translation construction identified upstream as `axIns2`. -/
@[expose]
noncomputable def axIns2 (x y z w t : Var) (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hxt : x ≠ t) (hyz : y ≠ z) (hyw : y ≠ w) (hyt : y ≠ t) (hzw : z ≠ w) (hzt : z ≠ t)
    (hwt : w ≠ t) : NPrf (axIns2Goal x y z w t) :=
  oneFreeNPrfOfValidity x (axIns2Goal x y z w t)
    (axIns2Fv x y z w t hxy hxz hxw hxt hyz hyw hyt hzw hzt hwt)
    (by
      intro S _ hNF
      simpa [axIns2Goal] using
        (NFChoice.Compiler.NFCompactLeafFinalGate.axIns2Compact hNF x y z w t hxy hxz hxw
          hxt hyz hyw hyt hzw hzt hwt))

theorem axIns3Fv (x y z w t : Var) (_hxy : x ≠ y) (_hxz : x ≠ z) (_hxw : x ≠ w)
    (_hxt : x ≠ t) (_hyz : y ≠ z) (_hyw : y ≠ w) (_hyt : y ≠ t) (_hzw : z ≠ w)
    (_hzt : z ≠ t) (_hwt : w ≠ t) : (axIns3Goal x y z w t).fv ⊆ ({ x } : Finset Var) :=
  by
  simp only [axIns3Goal]
  nfWeakPartitionFreshness

/-- Proof-translation construction identified upstream as `axIns3`. -/
@[expose]
noncomputable def axIns3 (x y z w t : Var) (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hxt : x ≠ t) (hyz : y ≠ z) (hyw : y ≠ w) (hyt : y ≠ t) (hzw : z ≠ w) (hzt : z ≠ t)
    (hwt : w ≠ t) : NPrf (axIns3Goal x y z w t) :=
  oneFreeNPrfOfValidity x (axIns3Goal x y z w t)
    (axIns3Fv x y z w t hxy hxz hxw hxt hyz hyw hyt hzw hzt hwt)
    (by
      intro S _ hNF
      simpa [axIns3Goal] using
        (NFChoice.Compiler.NFCompactLeafFinalGate.axIns3Compact hNF x y z w t hxy hxz hxw
          hxt hyz hyw hyt hzw hzt hwt))

theorem axTypeLowerFv (x y z w : Var) (_hxy : x ≠ y) (_hxz : x ≠ z) (_hxw : x ≠ w)
    (_hyz : y ≠ z) (_hyw : y ≠ w) (_hzw : z ≠ w) :
    (axTypeLowerGoal x y z w).fv ⊆ ({ x } : Finset Var) :=
  by
  simp only [axTypeLowerGoal]
  nfWeakPartitionFreshness

/-- Proof-translation construction identified upstream as `axTypeLower`. -/
@[expose]
noncomputable def axTypeLower (x y z w : Var) (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) : NPrf (axTypeLowerGoal x y z w) :=
  oneFreeNPrfOfValidity x (axTypeLowerGoal x y z w)
    (axTypeLowerFv x y z w hxy hxz hxw hyz hyw hzw)
    (by
      intro S _ hNF
      simpa [axTypeLowerGoal] using
        (NFChoice.Compiler.NFCompactLeafFinalGate.axTypeLowerCompact hNF x y z w hxy hxz
          hxw hyz hyw hzw))


end NFChoice.DirectNominalPrf.Nominal.NFLiteralRemainingViaCompletenessDev001
