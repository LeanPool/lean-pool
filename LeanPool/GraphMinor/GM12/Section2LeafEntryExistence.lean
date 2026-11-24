/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2PatchEntersLike
public import LeanPool.GraphMinor.GM12.Section2LeafEntryPatchProof
public import LeanPool.GraphMinor.GM11.RadialChord
import LeanPool.GraphMinor.GM12.Section2SpokePaths
import LeanPool.GraphMinor.GM11.RadialRegions

/-!
# Entry-edge existence at leaves

The omitted entry-edge assertion on XII page 243 holds at a leaf as
well as in a sector. The approaching curve puts the vertex in the
closure of its region. Radial maximality supplies a spoke to that
region's hub. Both the incoming curve and this spoke enter the proved
leaf patch. The patch comparison yields the exact entry witness.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The entry edge exists at a vertex with exactly one half-edge.
This closes the leaf case of the omitted assertion on XII page 243. -/
theorem exists_entersLike_of_one_halfEdge
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} (hrad : PreRad (.drawing Γ) K)
    (hmax : RadMax (.drawing Γ) K) (hE : Γ.E.Nonempty)
    {γ : Set S → unitInterval → S} (hγ : EdgePar Γ γ)
    {v : S} (hv : v ∈ Γ.V) (hcard : Nat.card (halfEdges Γ γ v) = 1)
    {r : Set S} (hr : r ∈ Γ.R) {w : S} (hw : w ∈ r) (hwV : w ∈ K.V)
    {f : ℝ → S} (hf : Continuous f) {a c : ℝ} (hac : a < c) (hfc : f c = v)
    (hinside : ∀ t ∈ Ioo a c, f t ∈ r) :
    ∃ e ∈ K.E, EntersLike f a c e r v w := by
  have hccl : c ∈ closure (Ioo a c) := by
    rw [closure_Ioo hac.ne]
    exact ⟨hac.le, le_rfl⟩
  have hvr : v ∈ closure r := by
    rw [← hfc]
    exact closure_mono (image_subset_iff.mpr hinside)
      (image_closure_subset_closure_image hf ⟨c, hccl, rfl⟩)
  obtain ⟨N, X, hN, hvN, hvX, hX, hpuncture, hXZ, hcover⟩ :=
    leafEntryPatch S hS inferInstance Γ γ hγ v hv hcard r hr hvr
  obtain ⟨e, he, hcap⟩ := exists_spoke_at hrad hmax hS hE hr hw hwV hv hvr
  obtain ⟨η, hη⟩ := exists_edgePar K
  have hvK : v ∈ K.V := radial_V hrad hv
  have hvcl : v ∈ closure e := (hcap.symm ▸ (show v ∈ ({v, w} : Set S) from Or.inl rfl)).1
  have hwcl : w ∈ closure e := (hcap.symm ▸ (show w ∈ ({v, w} : Set S) from Or.inr rfl)).1
  obtain ⟨b, hb⟩ := exists_end_eq hη he hvK hvcl
  let i : halfEdges K η v := ⟨(e, b), he, hb⟩
  have hvw : v ≠ w := fun heq => region_subset hr (heq.symm ▸ hw) (Γ.V_subset_U hv)
  obtain ⟨β, hβi, _, hβe, _⟩ := exists_spoke_path_from_halfEdge hη i hvw hwV hcap
  have hβr := path_positive_in_region β hw hβe (spoke_subset_region hS hrad hr he hw hwV hwcl)
  exact ⟨e, he, entersLike_of_normal_patch hr hv hw hN hvN hvX hX hpuncture hXZ hcover
    β hβi hβe hβr hf hac hfc hinside⟩

end GraphMinor.GM12
