/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section10f

import LeanPool.GraphMinor.GM19.FragmentOrient

/-!
# Fragments under `S₃`

The proofs of (10.4) and (10.5) use a fragment whose paintings are similarly oriented.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}


/-- The sequence `(Γ_i', φ_i')` of a fragment is similarly oriented: "because $\mathscr{S}$ is
similarly oriented and if $\Sigma_{\chi'}$ is orientable then so is
$\Sigma_\chi$". -/
theorem frag_similarly {S₁ : Type} [TopologicalSpace S₁] [T2Space S₁] [Nonempty S₁] {𝒮 : Set
  (ColouredPainting χ)}
    (hcl : IsPaintingClass χ 𝒮) (hS : IsSurface S) {K : Drawing S}
    (hF : IsFeature χ.Φ K) {ψ : S₁ → S} (a₀ : β) {Γ₀ : Painting S} (D₀ : FrameData χ.Φ Γ₀ K ψ)
      (seq : ℕ → ColouredPainting χ)
    (hm : ∀ i, seq i ∈ 𝒮) (D : ∀ i, FrameData χ.Φ (seq i).Γ K ψ) (hA : ∀ i, IsAnchored (seq i).Γ K)
      (flip : Set S₁ → Bool)
    (hO : IsOrientableSurface S₁ → IsOrientableSurface S) :
    IsSimilarlyOriented (fragScheme χ a₀ D₀ hF flip) (fun m ↦ fragPainting (a₀ := a₀) D₀ hF flip
      (seq m) (D m) (hA m)) := by
  have : ConnectedSpace S := χ.connected
  rcases hcl.similarly_oriented with h | ⟨ω, hω⟩
  · exact Or.inl fun hO' ↦ h (hO hO')
  · have hfrag := D₀.pull.frag
    obtain ⟨ω₁, hω₁⟩ := GraphMinor.GM19.fragmentOrientation S _ K ψ hS inferInstance hfrag ω
    refine Or.inr ⟨ω₁, fun m e₁' he₁' h3 a' b' c' hl' ↦ ?_⟩
    have hEp : e₁' ∈ ((D m).paint flip).E := he₁'
    have hint : Painting.IsInternal e₁' := by
      refine disjoint_left.mpr fun x hx hxb ↦ ?_
      have := (((D m).paint flip).border_edge e₁' hEp ⟨x, hx, hxb⟩).1
      omega
    obtain ⟨e, he, hb', hne', rfl⟩ := (D m).exists_lift_of_internal flip hEp hint
    have hsub := (D m).pull.subset_R he hb' hne'
    have hmap := (D m).map_march_lift (flip := flip) he hb' hne'
    have hlist : ((D m).paint flip).γ (ψ ⁻¹' e) = [a', b', c'] := hl'
    rw [hlist] at hmap
    obtain ⟨hdisc, htil⟩ := ((D m).paint flip).tilde_subset_discBd hEp h3
    have hn := ((D m).paint flip).γ_nodup _ hEp
    have hset := ((D m).paint flip).γ_set _ hEp
    rw [hlist] at hn hset
    have hmem : ∀ x ∈ [a', b', c'], x ∈ discBd (closure (ψ ⁻¹' e)) := fun x hx ↦ htil (hset ▸ hx)
    have hsur : ψ '' (ψ ⁻¹' e) = e := image_preimage_eq_of_subset (hsub.trans
      (image_subset_range _ _))
    have hcl' : ψ '' closure (ψ ⁻¹' e) = closure e := by
      rw [← hfrag.isClosedMap.closure_image_eq_of_continuous hfrag.continuous_ψ, hsur]
    refine (hω₁ _ hdisc ((D m).pull.injOn_closure he hsub) a' b' c' (hmem _ (by simp)) (hmem _
      (by simp))
      (hmem _ (by simp)) (by simp at hn; tauto) (by simp at hn; tauto)
        (by simp at hn; tauto)).mpr ?_
    rw [hcl']
    have h3e : (tilde e).ncard = 3 := by
      rw [← (D m).pull.ncard_tilde he hsub]
      exact h3
    exact hω _ (hm m) e he h3e _ _ _ hmap.symm

omit [T2Space Shat] in
/-- The places of one fragment are well-behaved by `S₃`, if its capping is `Σ̂` and it has fewer
cuffs. -/
theorem wellBehaved_S3 (hS : IsSurface S) {K : Drawing S} (hF : IsFeature χ.Φ K) {𝒮 : Set
  (ColouredPainting χ)}
    (hcl : IsPaintingClass χ 𝒮)
    (hlines : ∀ e ∈ arcComponentsIn (K.U \ K.V), ∃ u v, u ≠ v ∧ closure e ∩ K.V = {u, v}
      ∧ IsLineWithEnds (closure e) u v)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] {ψ : Y → S} (hY : IsSurface Y)
      (hψ : IsCutMap ψ K.U) (hsheet : HasSheets ψ K)
    (y : Y) (l : List S) (m : ℕ) (a₀ : β) (hS3 : ConditionS3 χ cap)
    (hhat : ∀ (Shat₁ : Type) [TopologicalSpace Shat₁], IsCappedSurface (connectedComponent y) Shat₁
      → Nonempty (Shat₁ ≃ₜ Shat))
    (hc : numCuffs (connectedComponent y) < numCuffs S) (hO : IsOrientableSurface
      (connectedComponent y) → IsOrientableSurface S) :
    IsWellBehavedPlaces {X | IsCutPlace χ K (fun x : connectedComponent y ↦ ψ x.1) l m X ∧ X.P ∈ 𝒮}
      := by
  have : Nonempty (connectedComponent y) := ⟨⟨y, mem_connectedComponent⟩⟩
  apply wellBehaved_of_fragment (fun x : connectedComponent y ↦ ψ x.1) hF l m a₀
    (fun a b hab hoff ↦ Subtype.ext (hψ.2.2.1 hoff (fun h ↦ hoff (hab ▸ h)) hab))
    (fun X hX ↦ frameData_of_cut hS X.P.fits hX.inter hlines hY hψ hsheet y)
  intro seq hq h flip hflip
  set D := fun i ↦ frameData_of_cut hS (seq i).P.fits (h i).inter hlines hY hψ hsheet y with hDdef
  have hfrag := (D 0).pull.frag
  obtain ⟨Shat₁, t₁, ⟨cap₁⟩⟩ := exists_cappedSurface _ _ hfrag.isSurface hfrag.connected rfl
  have hnb := hS3 _ Shat₁ (fragScheme χ a₀ (D 0) hF flip) ⟨cap₁⟩ (hhat Shat₁ cap₁) rfl rfl hc
  have hsim := frag_similarly hcl hS hF a₀ (D 0) (fun i ↦ (seq i).P) hq D (fun i ↦
    (h i).anchored) flip hO
  by_contra hno
  push Not at hno
  exact hnb ⟨_, fun i j hij ⟨σv, σe, hσ⟩ ↦ hno i j hij σv σe hσ, hsim⟩

end GraphMinor.GM19
