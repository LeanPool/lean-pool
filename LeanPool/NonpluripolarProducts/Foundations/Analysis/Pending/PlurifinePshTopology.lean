/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.BTTruncations
public import Mathlib.Topology.Order.Basic

/-! # Actual initial plurifine topology of all finite real PSH functions -/

@[expose] public section

open Set TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.PlurifinePshTopology

open FirstPass FirstPass.MongeAmpere

noncomputable section

variable {n : ℕ}

/-- All actual finite real PSH functions on the actual domain; off-domain values impose no
    topological condition. -/
def realPshFunctions (Ω : Opens (ComplexModel n)) : Set (ComplexModel n → ℝ) :=
  {f | PlurisubharmonicOn (fun z => (f z : EReal)) Ω}

/-- The genuine weakest topology on the actual domain making all actual real PSH functions
    continuous. -/
@[instance_reducible]
def topology (Ω : Opens (ComplexModel n)) : TopologicalSpace Ω :=
  ⨅ f : realPshFunctions Ω,
    TopologicalSpace.induced (fun z : Ω => f.val z.val) inferInstance

/-- Actual real PSH evaluation is continuous in the independently defined actual initial topology.
-/
theorem continuous_realPsh {Ω : Opens (ComplexModel n)} {f : ComplexModel n → ℝ}
    (hf : PlurisubharmonicOn (fun z => (f z : EReal)) Ω) :
    @Continuous Ω ℝ (topology Ω) inferInstance (fun z => f z.val) := by
  apply continuous_iff_le_induced.mpr
  exact iInf_le _ (⟨f, hf⟩ : realPshFunctions Ω)

/-- The true initial-topology universal property quantifies over independent topologies and every
    actual real PSH function. -/
theorem topology_universal (Ω : Opens (ComplexModel n)) (t : TopologicalSpace Ω) :
    t ≤ topology Ω ↔ ∀ f : realPshFunctions Ω,
      @Continuous Ω ℝ t inferInstance (fun z => f.val z.val) := by
  constructor
  · intro h f
    exact continuous_iff_le_induced.mpr (h.trans (iInf_le _ f))
  · intro h
    exact le_iInf fun f => continuous_iff_le_induced.mp (h f)

/-- Actual strict superlevels of genuine real PSH functions are plurifine open. -/
theorem isOpen_realPsh_superlevel {Ω : Opens (ComplexModel n)} {f : ComplexModel n → ℝ}
    (hf : PlurisubharmonicOn (fun z => (f z : EReal)) Ω) (c : ℝ) :
    IsOpen[topology Ω] {z : Ω | c < f z.val} := by
  let : TopologicalSpace Ω := topology Ω
  exact isOpen_Ioi.preimage (continuous_realPsh hf)

/-- Actual strict sublevels of genuine real PSH functions are plurifine open. -/
theorem isOpen_realPsh_sublevel {Ω : Opens (ComplexModel n)} {f : ComplexModel n → ℝ}
    (hf : PlurisubharmonicOn (fun z => (f z : EReal)) Ω) (c : ℝ) :
    IsOpen[topology Ω] {z : Ω | f z.val < c} := by
  let : TopologicalSpace Ω := topology Ω
  exact isOpen_Iio.preimage (continuous_realPsh hf)

/-- Actual finite truncation produces plurifine openness of singular PSH strict superlevels. -/
theorem isOpen_psh_superlevel {Ω : Opens (ComplexModel n)} {u : ComplexModel n → EReal}
    (hu : PlurisubharmonicOn u Ω) (c : ℝ) :
    IsOpen[topology Ω] {z : Ω | (c : EReal) < u z.val} := by
  obtain ⟨k, hk⟩ := exists_nat_gt (-c)
  have hfloor : -(k : ℝ) < c := by linarith
  convert isOpen_realPsh_superlevel (truncationReal_plurisubharmonicOn hu k) c using 1
  ext z
  change (c : EReal) < u z.val ↔ c < truncationReal u k z.val
  rw [← EReal.coe_lt_coe_iff, coe_truncationReal hu k z.property]
  simp only [truncation, lt_max_iff, not_lt.mpr (EReal.coe_le_coe_iff.mpr hfloor.le),
    or_false]

/-- Actual finite truncation produces plurifine openness of singular PSH strict sublevels. -/
theorem isOpen_psh_sublevel {Ω : Opens (ComplexModel n)} {u : ComplexModel n → EReal}
    (hu : PlurisubharmonicOn u Ω) (c : ℝ) :
    IsOpen[topology Ω] {z : Ω | u z.val < (c : EReal)} := by
  obtain ⟨k, hk⟩ := exists_nat_gt (-c)
  have hfloor : -(k : ℝ) < c := by linarith
  convert isOpen_realPsh_sublevel (truncationReal_plurisubharmonicOn hu k) c using 1
  ext z
  change u z.val < (c : EReal) ↔ truncationReal u k z.val < c
  rw [← EReal.coe_lt_coe_iff, coe_truncationReal hu k z.property]
  simp only [truncation, max_lt_iff, EReal.coe_lt_coe_iff, hfloor, and_true]

/-- The actual strict truncation locus is genuinely plurifine open, without an ordinary-open
    assertion. -/
theorem isOpen_strictTruncationLocus {Ω : Opens (ComplexModel n)} {u : ComplexModel n → EReal}
    (hu : PlurisubharmonicOn u Ω) (k : ℕ) :
    IsOpen[topology Ω] (Subtype.val ⁻¹' strictTruncationLocus Ω u k) := by
  rw [strictLocus_eq_truncationReal_superlevel hu (Nat.le_succ k)]
  convert isOpen_realPsh_superlevel (truncationReal_plurisubharmonicOn hu (k + 1)) (-(k : ℝ))
    using 1
  ext z
  simp only [mem_preimage, mem_ofPred_eq, z.property, true_and]

/-- Every actual extended-real PSH function is continuous for the actual finite-real-PSH initial
    topology, including poles. -/
theorem continuous_psh {Ω : Opens (ComplexModel n)} {u : ComplexModel n → EReal}
    (hu : PlurisubharmonicOn u Ω) :
    @Continuous Ω EReal (topology Ω) inferInstance (fun z => u z.val) := by
  let : TopologicalSpace Ω := topology Ω
  apply OrderTopology.continuous_iff.mpr
  intro a
  cases a with
  | bot =>
    refine ⟨?_, ?_⟩
    · have heq : (fun z : Ω => u z.val) ⁻¹' Ioi (⊥ : EReal) =
          ⋃ k : ℕ, {z : Ω | ((-(k : ℝ) : ℝ) : EReal) < u z.val} := by
        ext z
        constructor
        · intro hz
          obtain ⟨c, hc, hcu⟩ := EReal.exists_rat_btwn_of_lt hz
          obtain ⟨k, hk⟩ := exists_nat_gt (-(c : ℝ))
          apply mem_iUnion.mpr
          refine ⟨k, ?_⟩
          exact (EReal.coe_lt_coe_iff.mpr (by linarith : -(k : ℝ) < (c : ℝ))).trans hcu
        · intro hz
          obtain ⟨k, hk⟩ := mem_iUnion.mp hz
          exact (EReal.bot_lt_coe _).trans hk
      rw [heq]
      exact isOpen_iUnion fun k => isOpen_psh_superlevel hu (-(k : ℝ))
    · have heq : (fun z : Ω => u z.val) ⁻¹' Iio (⊥ : EReal) = ∅ := by ext z; simp
      rw [heq]
      exact isOpen_empty
  | coe c => exact ⟨isOpen_psh_superlevel hu c, isOpen_psh_sublevel hu c⟩
  | top =>
    refine ⟨?_, ?_⟩
    · have heq : (fun z : Ω => u z.val) ⁻¹' Ioi (⊤ : EReal) = ∅ := by ext z; simp
      rw [heq]
      exact isOpen_empty
    · have heq : (fun z : Ω => u z.val) ⁻¹' Iio (⊤ : EReal) = univ := by
        ext z
        simp only [mem_preimage, mem_Iio, mem_univ, iff_true]
        exact lt_top_iff_ne_top.mpr (hu z.val z.property).ne_top
      rw [heq]
      exact isOpen_univ

end

end SGPT.Foundations.Analysis.Pending.PlurifinePshTopology
