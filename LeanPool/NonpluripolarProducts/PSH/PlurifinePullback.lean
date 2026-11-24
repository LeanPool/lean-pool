/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.PSH.DomainPlurifine
public import LeanPool.NonpluripolarProducts.PSH.HolomorphicPullback

/-! Exact source holomorphic continuity between genuine plurifine domains. -/

@[expose] public section

namespace SGPT.PSH

open Set TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology

variable {k n : ℕ}

/-- The actual map of actual domains, from the original map and image condition. -/
def holomorphicDomainMap {Ω' : Opens (ComplexModel k)} {Ω : Opens (ComplexModel n)}
    {F : ComplexModel k → ComplexModel n} (hFΩ : MapsTo F Ω' Ω) : Ω' → Ω :=
  fun z ↦ ⟨F z.val, hFΩ z.property⟩

/-- Finite real source generators pull back with a genuine non-bottom point.
No identically-bottom alternative can occur for their actual real values. -/
theorem real_pshOn_comp_holomorphic
    {Ω' : Opens (ComplexModel k)} {Ω : Opens (ComplexModel n)}
    (hne : (Ω' : Set (ComplexModel k)).Nonempty)
    {F : ComplexModel k → ComplexModel n} (hF : DifferentiableOn ℂ F Ω')
    (hFΩ : MapsTo F Ω' Ω) {g : ComplexModel n → ℝ}
    (hg : PSHOn (fun z ↦ (g z : EReal)) Ω) :
    PSHOn (fun z ↦ (g (F z) : EReal)) Ω' := by
  obtain ⟨z, hz⟩ := hne
  exact ⟨discPshOn_comp_holomorphic Ω'.isOpen Ω.isOpen hF hFΩ hg,
    z, hz, EReal.coe_ne_bot (g (F z))⟩

/-- SGPT cor:holomappfcont for the actual independently defined domain
topologies. Actual holomorphic pullback makes every finite-real generator
continuous; the initial-topology universal property supplies continuity. -/
theorem continuous_domainPlurifine_holomorphic
    {Ω' : Opens (ComplexModel k)} {Ω : Opens (ComplexModel n)}
    {F : ComplexModel k → ComplexModel n} (hF : DifferentiableOn ℂ F Ω')
    (hFΩ : MapsTo F Ω' Ω) :
    @Continuous Ω' Ω (domainPlurifineTopology Ω') (domainPlurifineTopology Ω)
      (holomorphicDomainMap hFΩ) := by
  change @Continuous Ω' Ω (domainPlurifineTopology Ω')
    (⨅ g : SGPT.Foundations.Analysis.Pending.PlurifinePshTopology.realPshFunctions Ω,
      induced (fun z : Ω ↦ g.val z.val) inferInstance) (holomorphicDomainMap hFΩ)
  apply continuous_iInf_rng.mpr
  intro g
  apply continuous_induced_rng.mpr
  exact SGPT.Foundations.Analysis.Pending.PlurifinePshTopology.continuous_realPsh
    (SGPT.Foundations.Analysis.Pending.HolomorphicPullback.plurisubharmonicOn_comp_holomorphic
      Ω'.isOpen hF hFΩ g.property)

/-- Actual source plurifine open sets have actual plurifine open inverse images. -/
theorem isOpen_domainPlurifine_preimage_holomorphic
    {Ω' : Opens (ComplexModel k)} {Ω : Opens (ComplexModel n)}
    {F : ComplexModel k → ComplexModel n} (hF : DifferentiableOn ℂ F Ω')
    (hFΩ : MapsTo F Ω' Ω) {V : Set Ω} (hV : IsOpen[domainPlurifineTopology Ω] V) :
    IsOpen[domainPlurifineTopology Ω'] ((holomorphicDomainMap hFΩ) ⁻¹' V) := by
  let : TopologicalSpace Ω' := domainPlurifineTopology Ω'
  let : TopologicalSpace Ω := domainPlurifineTopology Ω
  exact hV.preimage (continuous_domainPlurifine_holomorphic hF hFΩ)

end SGPT.PSH
