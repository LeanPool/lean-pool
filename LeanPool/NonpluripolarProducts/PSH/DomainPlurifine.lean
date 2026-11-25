/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.PSH.Basic
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PshDiscLocalGlobal
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PlurifineEuclideanComparison

/-! Reuse the genuine real-PSH initial topology, retaining source non-bottom witnesses. -/

@[expose] public section

namespace SGPT.PSH

open Set TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology

variable {n : ℕ}

/-- Every actual real function on the actual domain has an ambient representative. -/
theorem exists_ambient_real_representative (Ω : Opens (ComplexModel n)) (f : Ω → ℝ) :
    ∃ g : ComplexModel n → ℝ, ∀ z : Ω, g z.val = f z := by
  classical
  refine ⟨fun x ↦ if hx : x ∈ (Ω : Set (ComplexModel n)) then f ⟨x, hx⟩ else 0, ?_⟩
  intro z
  dsimp only
  split_ifs with hz
  · rfl
  · exact False.elim (hz z.property)

/-- On a genuine nonempty source domain, finite real PSH functions satisfy
the source non-bottom clause automatically. Values outside the domain are ignored. -/
theorem real_pshOn_iff_plurisubharmonicOn {Ω : Opens (ComplexModel n)}
    (hne : (Ω : Set (ComplexModel n)).Nonempty) (f : ComplexModel n → ℝ) :
    PSHOn (fun z ↦ (f z : EReal)) Ω ↔
      SGPT.Foundations.Analysis.PlurisubharmonicOn (fun z ↦ (f z : EReal)) Ω := by
  constructor
  · intro hf
    exact hf.disc.plurisubharmonicOn Ω.isOpen
  · intro hf
    obtain ⟨z, hz⟩ := hne
    exact ⟨hf.discPshOn,
      z, hz, EReal.coe_ne_bot (f z)⟩

/-- SGPT def:pftopologydomain, using the already proved initial topology of
all actual finite real PSH functions. Every function on Ω has an ambient
representative; only its actual restriction is evaluated. -/
@[instance_reducible]
noncomputable def domainPlurifineTopology (Ω : Opens (ComplexModel n)) : TopologicalSpace Ω :=
  SGPT.Foundations.Analysis.Pending.PlurifinePshTopology.topology Ω

/-- Exact weakest-topology property, with source PSH rather than a weakened
bottom-permitting predicate in the quantified generating function class. -/
theorem domainPlurifine_universal (Ω : Opens (ComplexModel n))
    (hne : (Ω : Set (ComplexModel n)).Nonempty) (t : TopologicalSpace Ω) :
    t ≤ domainPlurifineTopology Ω ↔ ∀ f : ComplexModel n → ℝ,
      PSHOn (fun z ↦ (f z : EReal)) Ω →
        @Continuous Ω ℝ t inferInstance (fun z ↦ f z.val) := by
  rw [domainPlurifineTopology,
    SGPT.Foundations.Analysis.Pending.PlurifinePshTopology.topology_universal]
  constructor
  · intro h f hf
    exact h ⟨f, (real_pshOn_iff_plurisubharmonicOn hne f).mp hf⟩
  · intro h f
    exact h f.val ((real_pshOn_iff_plurisubharmonicOn hne f.val).mpr f.property)

/-- SGPT prop:pf_finer for the actual Euclidean domain topology. -/
theorem domainPlurifine_le_euclidean (Ω : Opens (ComplexModel n)) :
    domainPlurifineTopology Ω ≤ (inferInstance : TopologicalSpace Ω) :=
  SGPT.Foundations.Analysis.Pending.PlurifineEuclideanComparison.topology_le_euclidean Ω

/-- Genuine source PSH evaluations are continuous, including actual poles. -/
theorem PSHOn.continuous_domainPlurifine {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → EReal} (hu : PSHOn u Ω) :
    @Continuous Ω EReal (domainPlurifineTopology Ω) inferInstance (fun z ↦ u z.val) :=
  SGPT.Foundations.Analysis.Pending.PlurifinePshTopology.continuous_psh
    (hu.disc.plurisubharmonicOn Ω.isOpen)

/-- SGPT ex:pfopenpsh: both actual strict level sets are plurifine open. -/
theorem PSHOn.isOpen_domainPlurifine_superlevel {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → EReal} (hu : PSHOn u Ω) (c : ℝ) :
    IsOpen[domainPlurifineTopology Ω] {z : Ω | (c : EReal) < u z.val} :=
  SGPT.Foundations.Analysis.Pending.PlurifinePshTopology.isOpen_psh_superlevel
    (hu.disc.plurisubharmonicOn Ω.isOpen) c

theorem PSHOn.isOpen_domainPlurifine_sublevel {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → EReal} (hu : PSHOn u Ω) (c : ℝ) :
    IsOpen[domainPlurifineTopology Ω] {z : Ω | u z.val < (c : EReal)} :=
  SGPT.Foundations.Analysis.Pending.PlurifinePshTopology.isOpen_psh_sublevel
    (hu.disc.plurisubharmonicOn Ω.isOpen) c

end SGPT.PSH
