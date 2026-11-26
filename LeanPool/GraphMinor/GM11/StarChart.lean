/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.CutEdges
public import LeanPool.GraphMinor.GM11.LocalCone
public import LeanPool.GraphMinor.GM11.RadialFacts

/-!
# Small star-shaped neighbourhoods of a vertex of the union of a drawing and a radial drawing

`exists_star_nbhd`: a polar chart gives arbitrarily small open sets around its centre that are
star-shaped, and so
simply-connected. `sector_join`: in such a set around a vertex `s` of `Γ`, each point `y` off `U(Γ ∪
Γ')` in a region `r`
of `Γ` is joined to an edge of `Γ'` at `s`, inside `r` and inside the set. This uses that edges of
`Γ` and `Γ'`
alternate around `s`. The proof of (6.4) of Graph Minors XI (pages 90–91) needs this to pass a curve
across `s`.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
/-- A set of a surface that is preconnected and lies in an open set: two of its points are joined in
that open set. -/
theorem joinedIn_of_isPreconnected (hS : IsClosedSurface S) {B G : Set S} (hG : IsOpen G)
  (hB : IsPreconnected B)
    (hsub : B ⊆ G) {a b : S} (ha : a ∈ B) (hb : b ∈ B) : JoinedIn G a b := by
  have := IsClosedSurface.locallyConnectedSpace hS
  have hco := hG.connectedComponentIn (x := a)
  have hpc := isPathConnected_of_isOpen hS hco isPreconnected_connectedComponentIn ⟨a,
    mem_connectedComponentIn (hsub ha)⟩
  have hsubc : B ⊆ connectedComponentIn G a := hB.subset_connectedComponentIn ha hsub
  exact (hpc.joinedIn a (hsubc ha) b (hsubc hb)).mono (connectedComponentIn_subset G a)

/-- Small star-shaped open sets around the centre of a polar chart. -/
theorem exists_star_nbhd {Γ : Drawing S} {z : S} {Φ : C(ClosedUnitDisc, S)}
  (hp : IsPolar Γ z Φ) {O : Set S}
    (hO : IsOpen O) (hz : z ∈ O) : ∃ D : Set S, IsOpen D ∧ z ∈ D ∧ D ⊆ O ∧ IsSimplyConnectedSet D ∧
      ∀ y ∈ D, ∃ x, Φ x = y ∧ ∀ c : I, Φ (discScale c x) ∈ D := by
  let O' : Set S := O ∩ interior (range Φ)
  have hO' : IsOpen O' := hO.inter isOpen_interior
  let T : Set ClosedUnitDisc := {x | ∀ c : I, Φ (discScale c x) ∈ O'}
  have hcont : Continuous fun p : I × ClosedUnitDisc => Φ (discScale p.1 p.2) :=
    Φ.continuous.comp continuous_discScale
  have hTo : IsOpen T := by
    have hcl : IsClosed ((fun p : I × ClosedUnitDisc => Φ (discScale p.1 p.2)) ⁻¹' O'ᶜ) :=
      hO'.isClosed_compl.preimage hcont
    have := isClosedMap_snd_of_compactSpace (X := I) (Y := ClosedUnitDisc) _ hcl
    convert this.isOpen_compl using 1
    ext x
    simp only [T, mem_ofPred_eq, mem_compl_iff, mem_image, mem_preimage, Prod.exists,
      exists_eq_right, not_exists,
      not_not]
  have hT : ∀ x ∈ T, ∀ c : I, discScale c x ∈ T := fun x hx c c' => by
    have : discScale c' (discScale c x) = discScale (c' * c) x := Subtype.ext (by
      simp [discScale, mul_smul])
    rw [this]
    exact hx _
  have hc : polarCentre ∈ T := fun c => by
    have : discScale c polarCentre = polarCentre := Subtype.ext (by simp [discScale, polarCentre])
    rw [this, hp.centre]
    exact ⟨hz, hp.nhd⟩
  have hemb := (Φ.continuous.isClosedEmbedding hp.inj).isEmbedding
  obtain ⟨G, hG, hGT⟩ := hemb.isInducing.isOpen_iff.mp hTo
  have hTO : ∀ x ∈ T, Φ x ∈ O' := fun x hx => by
    simpa [discScale_one] using hx 1
  have hD : Φ '' T = G ∩ O' := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(hGT ▸ hx : x ∈ Φ ⁻¹' G), hTO x hx⟩
    · rintro ⟨hyG, hyO⟩
      obtain ⟨x, rfl⟩ := interior_subset hyO.2
      exact ⟨x, (hGT ▸ (hyG : x ∈ Φ ⁻¹' G) : x ∈ T), rfl⟩
  refine ⟨Φ '' T, hD ▸ hG.inter hO', ⟨_, hc, hp.centre⟩, ?_, isSimplyConnected_star hp.inj hT ⟨_,
    hc⟩, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (hTO x hx).1
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, rfl, fun c => ⟨_, hT x hx c, rfl⟩⟩

variable [ConnectedSpace S] {Γ Γ' : Drawing S} (hrad : PreRad (PaintingOrDrawing.drawing Γ) Γ')
  (hS : IsClosedSurface S)

include hrad hS

/-- **The sectors at a vertex.** The point `y` of a star-shaped set `D` around the vertex `s` of `Γ`
lies in a region
`r` of `Γ`, and off `U(Γ ∪ Γ')`. Then `y` is joined in `r ∩ D` to a point of an edge of `Γ'` at `s`.
-/
theorem sector_join (hmax : RadMax (PaintingOrDrawing.drawing Γ) Γ') (hE : Γ.E.Nonempty) {γ : Set S
  → I → S}
    (hγ : EdgePar (radialUnion hrad) γ) {s : S} (hs : s ∈ Γ.V)
    {next : halfEdges (radialUnion hrad) γ s → halfEdges (radialUnion hrad) γ s}
    {ρ P Q : halfEdges (radialUnion hrad) γ s → Set S} {W : Set S} {τ : halfEdges
      (radialUnion hrad) γ s → I}
    (hsec : IsSectors (radialUnion hrad) γ s next ρ P W Q τ) {Φ : C(ClosedUnitDisc, S)}
    (hΦ : IsPolar (radialUnion hrad) s Φ) {D : Set S} (hDo : IsOpen D) (hsD : s ∈ D) (hDW : D ⊆ W)
    (hstar : ∀ y ∈ D, ∃ x, Φ x = y ∧ ∀ c : I, Φ (discScale c x) ∈ D) {r : Set S}
      (hr : r ∈ Γ.R) {y : S}
    (hy : y ∈ r) (hyD : y ∈ D) (hyU : y ∉ (radialUnion hrad).U) :
    ∃ k : halfEdges (radialUnion hrad) γ s, k.1.1 ∈ Γ'.E ∧ ∃ t : I, 0 < t ∧ (∀ u, u ≤ t
      → spoke γ k.1 u ∈ D) ∧
      spoke γ k.1 t ∈ r ∧ JoinedIn (r ∩ D) y (spoke γ k.1 t) := by
  classical
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hcor := IsSectors.corners hsec
  have hsU : s ∈ (radialUnion hrad).U := (radialUnion hrad).V_subset_U (by
    rw [radialUnion_V]
    exact radial_V hrad hs)
  obtain ⟨x₀, rfl, hray⟩ := hstar y hyD
  have hx₀ : x₀ ≠ polarCentre := fun h => hyU (by rw [h, hΦ.centre]; exact hsU)
  obtain ⟨k, hyk⟩ := mem_iUnion.mp (IsSectors.cover hsec ⟨hDW hyD, hyU⟩)
  have hR := IsCorners.region hcor k
  have hyρ : Φ x₀ ∈ ρ k := IsSectors.sub hsec k hyk
  -- `ρ k` lies in `r`.
  obtain ⟨r', hr', hρr'⟩ := exists_region_of_sub hrad hR
  have hrr : r' = r := region_eq_of_mem hr' hr (hρr' hyρ) hy
  subst hrr
  -- The points of the ray.
  let g : I → S := fun c => Φ (discScale c x₀)
  have hg : Continuous g := (Φ.continuous.comp continuous_discScale).comp
    (Continuous.prodMk continuous_id continuous_const)
  have hg0 : g 0 = s := by simp only [g, discScale_zero, hΦ.centre]
  have hg1 : g 1 = Φ x₀ := by simp only [g, discScale_one]
  have hgρ : ∀ c, 0 < c → g c ∈ ρ k := fun c hc => by
    obtain ⟨a, ha, h₁, h₂⟩ := hΦ.ray x₀ hx₀ c hc
    rcases ha with (⟨v, hv, rfl⟩ | ha) | ha
    · exact absurd (mem_singleton_iff.mp h₁ ▸ (radialUnion hrad).V_subset_U hv) hyU
    · exact absurd ((ha.2.1 h₁).1) hyU
    · rwa [region_eq_of_mem ha hR h₁ hyρ] at h₂
  let Ray : Set S := g '' Ioi 0
  have hRayc : IsPreconnected Ray := (isPreconnected_Ioi.image g hg.continuousOn)
  have hRayU : ∀ z ∈ Ray, z ∉ (radialUnion hrad).U ∧ z ∈ D := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨region_subset hR (hgρ c hc), hray c⟩
  let In : halfEdges (radialUnion hrad) γ s → Set S := fun j => W ∩ (interior (Q j))
  have hIn : ∀ j, IsOpen (In j) := fun j => (IsSectors.isOpen hsec).inter isOpen_interior
  have hint : ∀ j, Q j \ discBd (Q j) = interior (Q j) := fun j => by
    have hd := IsSectors.disc hsec j
    have := IsClosedDisc.frontier_eq_discBd hS hd
    rw [← this, frontier, (IsClosedDisc.isCompact hd).isClosed.closure_eq]
    ext x
    constructor
    · rintro ⟨h₁, h₂⟩
      by_contra h
      exact h₂ ⟨h₁, h⟩
    · exact fun h => ⟨interior_subset h, fun h' => h'.2 h⟩
  have hcov : ∀ z ∈ Ray, ∃ j, z ∈ In j := fun z hz => by
    obtain ⟨hzU, hzD⟩ := hRayU z hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp (IsSectors.cover hsec ⟨hDW hzD, hzU⟩)
    refine ⟨j, hDW hzD, ?_⟩
    rw [← hint j]
    exact ⟨IsSectors.subQ hsec j hj, fun h => hzU (IsSectors.bdU hsec j ⟨hDW hzD, h⟩)⟩
  have hdisj : ∀ z ∈ Ray, ∀ j j', z ∈ In j → z ∈ In j' → j = j' := fun z hz j j' h h' => by
    by_contra hne
    exact (hRayU z hz).1 (IsSectors.inter hsec j j' hne ⟨interior_subset h.2, interior_subset h'.2⟩)
  have hy1 : Φ x₀ ∈ In k := by
    obtain ⟨j, hj⟩ := hcov (Φ x₀) ⟨1, zero_lt_one, hg1⟩
    refine ⟨hDW hyD, ?_⟩
    rw [← hint k]
    exact ⟨IsSectors.subQ hsec k hyk, fun h => hyU (IsSectors.bdU hsec k ⟨hDW hyD, h⟩)⟩
  have hRayk : Ray ⊆ In k := by
    intro z hz
    by_contra hzk
    obtain ⟨j, hj⟩ := hcov z hz
    obtain ⟨w, hw, hw₁, hw₂⟩ := hRayc (In k) (⋃ j, ⋃ _ : j ≠ k, In j) (hIn k)
      (isOpen_iUnion fun j => isOpen_iUnion fun _ => hIn j) (fun w hw => by
        obtain ⟨j, hj⟩ := hcov w hw
        by_cases hjk : j = k
        · exact Or.inl (hjk ▸ hj)
        · exact Or.inr (mem_iUnion₂.mpr ⟨j, hjk, hj⟩)) ⟨_, ⟨1, zero_lt_one, hg1⟩, hy1⟩
      ⟨z, hz, mem_iUnion₂.mpr ⟨j, fun h => hzk (h ▸ hj), hj⟩⟩
    obtain ⟨j', hj', hw₂'⟩ := mem_iUnion₂.mp hw₂
    exact hj' (hdisj w hw j' k hw₂' hw₁)
  -- The side of the sector near `s`.
  obtain ⟨A, W', hW', hsW', hAc, hAQ, hAb, hAD, hin, hcl⟩ := exists_half_nbhd
    (IsSectors.disc hsec k)
    hDo.isClosed_compl (IsSectors.bd hsec k) (fun h => h hsD)
  have hAD' : A ⊆ D := fun a ha => by
    by_contra h
    exact disjoint_left.mp hAD ha h
  have hAρ : A ⊆ r' := fun a ha =>
    hρr' (IsSectors.sub hsec k (IsSectors.inside hsec k ⟨⟨hDW (hAD' ha), hAQ ha⟩, disjoint_left.mp
      hAb ha⟩))
  -- A point of the ray in `A`.
  obtain ⟨u, hu, -, hule⟩ := exists_pos_le hg hW' (by rw [hg0]; exact hsW') (zero_lt_one' I)
  have hzRay : g u ∈ Ray := ⟨u, hu, rfl⟩
  have hzA : g u ∈ A := by
    refine hin ⟨⟨hule u le_rfl, interior_subset (hRayk hzRay).2⟩, ?_⟩
    exact fun h => (hRayU _ hzRay).1 (IsSectors.bdU hsec k ⟨(hRayk hzRay).1, h⟩)
  -- The corner has an edge of `Γ'`.
  have hedge : ∃ j : halfEdges (radialUnion hrad) γ s, j.1.1 ∈ Γ'.E ∧ ∀ t, t ≤ τ j
    → spoke γ j.1 t ∈ discBd (Q k) := by
    rcases corner_has_spoke hrad hS hmax hE hγ hs hsec k with h | h
    · exact ⟨k, h, IsSectors.left hsec k⟩
    · exact ⟨next k, h, IsSectors.right hsec k⟩
  obtain ⟨j, hjE, hjb⟩ := hedge
  have hjs : spoke γ j.1 0 = s := by rw [spoke_zero]; exact j.2.2
  obtain ⟨t, ht, htτ, htle⟩ := exists_pos_le (continuous_spoke hγ j.2.1) (hW'.inter hDo)
    (by rw [hjs]; exact ⟨hsW', hsD⟩) (IsSectors.pos hsec j)
  have hptcl : spoke γ j.1 t ∈ closure A := hcl ⟨(htle t le_rfl).1, hjb t htτ⟩
  have hpte := spoke_mem_edge hγ j.2.1 ht
  obtain ⟨-, -, r₁, hr₁, -, -, -, -, hsub⟩ := spoke_ends hrad hS hjE
  obtain ⟨a, ha₁, ha⟩ := mem_closure_iff.mp hptcl r₁ (region_isOpen hr₁) (hsub hpte)
  obtain rfl : r₁ = r' := region_eq_of_mem hr₁ hr' ha₁ (hAρ ha)
  have hptr : spoke γ j.1 t ∈ r₁ := hsub hpte
  refine ⟨j, hjE, t, ht, fun v hv => (htle v hv).2, hptr, ?_⟩
  -- Joining.
  have hB₁ : IsPreconnected (insert (spoke γ j.1 t) A) :=
    hAc.subset_closure (subset_insert _ _) (insert_subset hptcl subset_closure)
  have hB : IsPreconnected (Ray ∪ insert (spoke γ j.1 t) A) :=
    hRayc.union (g u) hzRay (Or.inr hzA) hB₁
  refine joinedIn_of_isPreconnected hS ((region_isOpen hr₁).inter hDo) hB ?_ (Or.inl ⟨1,
    zero_lt_one, hg1⟩)
    (Or.inr (mem_insert _ _))
  rintro z (hz | rfl | hz)
  · obtain ⟨c, hc, rfl⟩ := hz
    exact ⟨hρr' (hgρ c hc), hray c⟩
  · exact ⟨hptr, (htle t le_rfl).2⟩
  · exact ⟨hAρ hz, hAD' hz⟩

end GraphMinor.GM11
