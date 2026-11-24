/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.PSH.PlurifineCompatibility
public import LeanPool.NonpluripolarProducts.PSH.Components
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PlurifineSingleSuperlevelNeighborhoods

/-! The actual source family of local PSH strict superlevels. -/

@[expose] public section

namespace SGPT.PSH

open Set TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.PlurifineSingleSuperlevelNeighborhoods
open scoped Topology

variable {n : ℕ}

/-- Finite real PSH has a genuine finite point in every local neighborhood. -/
theorem real_isPSHOn_identityAtlas {U : Set (ComplexModel n)} (hU : IsOpen U)
    {f : ComplexModel n → ℝ}
    (hf : PlurisubharmonicOn (fun z ↦ (f z : EReal)) U) :
    (VariableComplexAtlas.identityAtlas n).IsPSHOn (fun z ↦ (f z : EReal)) U := by
  apply (VariableComplexAtlas.isPSHOn_iff_chart_and_nondegenerate hU).mpr
  constructor
  · intro i
    change PlurisubharmonicOn (fun z ↦ (f z : EReal)) (univ ∩ U)
    simpa only [univ_inter] using hf
  · intro x hx O hO hxO
    exact ⟨x, ⟨hx, hxO⟩, EReal.coe_ne_bot (f x)⟩

/-- The exact local source predicate supplies actual raw PSH germs on U. -/
theorem raw_pshOn_of_identityAtlas {U : Set (ComplexModel n)}
    {u : ComplexModel n → EReal}
    (hu : (VariableComplexAtlas.identityAtlas n).IsPSHOn u U) :
    PlurisubharmonicOn u U := by
  have h := hu.chartPlurisubharmonic ()
  change PlurisubharmonicOn u (univ ∩ U) at h
  simpa only [univ_inter] using h

/-- Every source local PSH strict superlevel is fine-open in the actual
containing domain, including original singular values. -/
theorem isOpen_domainPlurifine_local_psh_superlevel (Ω : Opens (ComplexModel n))
    {U : Set (ComplexModel n)} (hU : IsOpen U) {u : ComplexModel n → EReal}
    (hu : (VariableComplexAtlas.identityAtlas n).IsPSHOn u U) :
    IsOpen[domainPlurifineTopology Ω] {z : Ω | z.val ∈ U ∧ 0 < u z.val} := by
  have hraw := raw_pshOn_of_identityAtlas hu
  convert isOpen_domainPlurifine_local_real_superlevel Ω hU
    (SGPT.Foundations.Analysis.FirstPass.MongeAmpere.truncationReal_plurisubharmonicOn (Ω := ⟨U,
      hU⟩) hraw 1)
    0 using 1
  ext z
  by_cases hz : z.val ∈ U
  · simp only [mem_ofPred_eq, hz, true_and]
    rw [← EReal.coe_lt_coe_iff,
      SGPT.Foundations.Analysis.FirstPass.MongeAmpere.coe_truncationReal (Ω := ⟨U, hU⟩) hraw 1 hz]
    norm_num [SGPT.Foundations.Analysis.FirstPass.MongeAmpere.truncation, lt_max_iff]
  · simp only [mem_ofPred_eq, hz, false_and]

/-- Actual ordinary open subsets of Ω have actual ambient open representatives. -/
theorem exists_ambient_open_of_subtype_open (Ω : Opens (ComplexModel n))
    (O : Set Ω) (hO : IsOpen O) :
    ∃ U : Set (ComplexModel n), IsOpen U ∧ U ⊆ Ω ∧ Subtype.val ⁻¹' U = O := by
  refine ⟨Subtype.val '' O, Ω.isOpen.isOpenMap_subtype_val O hO, ?_, ?_⟩
  · rintro z ⟨y, hy, rfl⟩
    exact y.property
  · ext z
    constructor
    · rintro ⟨y, hy, heq⟩
      exact (Subtype.ext heq : y = z) ▸ hy
    · intro hz
      exact ⟨z, hz, rfl⟩

/-- SGPT thm:pf_basis: precisely the sets {z∈U : u(z)>0}, with an actual
ordinary open U inside Ω and the exact local source PSH class on U. -/
def sourcePlurifineBasis (Ω : Opens (ComplexModel n)) : Set (Set Ω) :=
  {S | ∃ (U : Set (ComplexModel n)) (u : ComplexModel n → EReal),
    IsOpen U ∧ U ⊆ Ω ∧ (VariableComplexAtlas.identityAtlas n).IsPSHOn u U ∧
    S = {z : Ω | z.val ∈ U ∧ 0 < u z.val}}

/-- Every member of the exact source family is actually plurifine open. -/
theorem sourcePlurifineBasis_isOpen (Ω : Opens (ComplexModel n))
    {S : Set Ω} (hS : S ∈ sourcePlurifineBasis Ω) :
    IsOpen[domainPlurifineTopology Ω] S := by
  obtain ⟨U, u, hU, hUΩ, hu, rfl⟩ := hS
  exact isOpen_domainPlurifine_local_psh_superlevel Ω hU hu

/-- Every actual plurifine open neighborhood contains a member of the exact
source family at its original point. Reuse the genuine existing one-superlevel
producer; no local-basis premise or covering certificate is assumed. -/
theorem exists_sourcePlurifineBasis_subset (Ω : Opens (ComplexModel n))
    {S : Set Ω} (hS : IsOpen[domainPlurifineTopology Ω] S) {x : Ω} (hx : x ∈ S) :
    ∃ T ∈ sourcePlurifineBasis Ω, x ∈ T ∧ T ⊆ S := by
  obtain ⟨O, g, hO, hxO, hg, hgx, hglo, hghi, hTf, hTS⟩ :=
    exists_bounded_single_superlevel hS hx
  obtain ⟨U, hU, hUΩ, hUO⟩ := exists_ambient_open_of_subtype_open Ω O hO
  let u : ComplexModel n → EReal := fun z ↦ (g z : EReal)
  let T : Set Ω := {z : Ω | z.val ∈ U ∧ 0 < u z.val}
  have hu : (VariableComplexAtlas.identityAtlas n).IsPSHOn u U :=
    real_isPSHOn_identityAtlas hU (hg.mono hUΩ)
  have hm (z : Ω) : z.val ∈ U ↔ z ∈ O := by
    change z ∈ Subtype.val ⁻¹' U ↔ z ∈ O
    rw [hUO]
  refine ⟨T, ⟨U, u, hU, hUΩ, hu, rfl⟩, ?_, ?_⟩
  · refine ⟨(hm x).mpr hxO, ?_⟩
    change (0 : EReal) < (g x.val : EReal)
    rw [hgx]
    norm_num
  · intro z hz
    apply hTS
    exact ⟨(hm z).mp hz.1, EReal.coe_lt_coe_iff.mp hz.2⟩

/-- SGPT thm:pf_basis in both directions for the independently defined
actual domain plurifine topology. The original local source PSH class, not
merely finite real or globally defined functions, gives the whole basis. -/
theorem sourcePlurifineBasis_isTopologicalBasis (Ω : Opens (ComplexModel n)) :
    @IsTopologicalBasis Ω (domainPlurifineTopology Ω) (sourcePlurifineBasis Ω) := by
  let : TopologicalSpace Ω := domainPlurifineTopology Ω
  apply isTopologicalBasis_of_isOpen_of_nhds
  · intro T hT
    exact sourcePlurifineBasis_isOpen Ω hT
  · intro x S hx hS
    exact exists_sourcePlurifineBasis_subset Ω hS hx

end SGPT.PSH
