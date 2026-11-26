/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section5n
public import LeanPool.GraphMinor.GM19.CapModel
public import LeanPool.GraphMinor.GM19.Conditional2

/-!
# Graph Minors XIX, (5.4)

The proof of (5.4). We take the lines `K_i` of `exists_crossLine`, use (5.2) and (5.1) to make them
all equal to one
line `K`, cut along `K`, and apply `S₃` to the fragment. The inflation that this gives glues to an
inflation of the
sequence by `glue_coloured`.
The deductions that use later proofs are in `Section5oProved`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

universe w

variable {S : Type} [TopologicalSpace S] [T2Space S]


omit [T2Space S] in
/-- Frame-preserving maps compose. -/
theorem IsFramePreservingHomeo.trans {Φ : Frame S} {α β : S ≃ₜ S} (hα : IsFramePreservingHomeo Φ α)
    (hβ : IsFramePreservingHomeo Φ β) : IsFramePreservingHomeo Φ (α.trans β) := by
  refine ⟨fun v hv ↦ ?_, fun s hs ↦ ?_, fun ω Δ hΔ a b c ha hb hc hab hbc hac ↦ ?_⟩
  · change β (α v) = v
    rw [hα.fix_V v hv, hβ.fix_V v hv]
  · have : (α.trans β) '' s = β '' (α '' s) := by
      rw [image_image]
      rfl
    rw [this, hα.preserve_sides s hs, hβ.preserve_sides s hs]
  · have h₁ := hα.preserves_orientation ω Δ hΔ a b c ha hb hc hab hbc hac
    have ha' : α a ∈ discBd (α '' Δ) := GM20.image_discBd α Δ ▸ mem_image_of_mem _ ha
    have hb' : α b ∈ discBd (α '' Δ) := GM20.image_discBd α Δ ▸ mem_image_of_mem _ hb
    have hc' : α c ∈ discBd (α '' Δ) := GM20.image_discBd α Δ ▸ mem_image_of_mem _ hc
    have h₂ := hβ.preserves_orientation ω (α '' Δ) (GM20.image_isClosedDisc α hΔ) _ _ _ ha' hb' hc'
      (fun h ↦ hab (α.injective h)) (fun h ↦ hbc (α.injective h)) (fun h ↦ hac (α.injective h))
    have : (α.trans β) '' Δ = β '' (α '' Δ) := by
      rw [image_image]
      rfl
    rw [this]
    exact h₂.trans h₁

/-- An infinite set has an infinite part on which a map to a finite set is constant. -/
theorem exists_infinite_fiber {ι β : Type*} {A : Set ι} (hA : A.Infinite) {B : Set β}
  (hB : B.Finite) (g : ι → β)
    (hg : ∀ i ∈ A, g i ∈ B) : ∃ b ∈ B, (A ∩ g ⁻¹' {b}).Infinite := by
  by_contra h
  push Not at h
  refine hA ((hB.biUnion fun b hb ↦ h b hb).subset fun i hi ↦ ?_)
  exact mem_biUnion (hg i hi) ⟨hi, rfl⟩

omit [T2Space S] in
/-- All three points of a size three edge are on the boundary of its disc. -/
theorem Painting.tilde_subset_discBd (Γ : Painting S) {e : Set S} (he : e ∈ Γ.E) (h3 :
  (tilde e).ncard = 3) :
    IsClosedDisc (closure e) ∧ tilde e ⊆ discBd (closure e) := by
  rcases Γ.edge_shape e he with h | h
  · omega
  · exact ⟨h.2.2.1, h.2.2.2⟩

/-- `ω` is positive on the size three edges of `Γ`. -/
def IsPositive (ω : SurfaceOrientation S) (Γ : Painting S) : Prop :=
  ∀ e ∈ Γ.E, (tilde e).ncard = 3 → ∀ a b c : S, Γ.γ e = [a, b, c] → ω.pos (closure e) a b c

variable {α₀ : Type w} {χ : ColourScheme S α₀}

omit [T2Space S] in
/-- The image under a map that preserves `ω` of a painting positive for `ω` is positive for `ω`. -/
theorem isPositive_image {ω : SurfaceOrientation S} {α : S ≃ₜ S} (hα : ω.IsPreservedBy α) {P P' :
  ColouredPainting χ}
    (I : IsColouredImage α P P') (h : IsPositive ω P.Γ) : IsPositive ω P'.Γ := by
  intro e he h3 a b c hl
  obtain ⟨e₀, he₀, rfl⟩ : e ∈ image α '' P.Γ.E := by
    rw [← I.E_eq]
    exact he
  have h3' : (tilde e₀).ncard = 3 := by
    rw [← h3, ← ncard_image_of_injective _ α.injective, GM20.image_tilde]
  obtain ⟨hD, hsub⟩ := P.Γ.tilde_subset_discBd he₀ h3'
  have hγ := I.γ e₀ he₀
  rw [hl] at hγ
  obtain ⟨a', b', c', hl', rfl, rfl, rfl⟩ : ∃ a' b' c', P.Γ.γ e₀ = [a', b', c'] ∧ a = α a' ∧ b
    = α b' ∧ c = α c' := by
    obtain ⟨a', l₁, h₁, ha, hl₁⟩ := List.map_eq_cons_iff.mp hγ.symm
    obtain ⟨b', l₂, h₂, hb, hl₂⟩ := List.map_eq_cons_iff.mp hl₁
    obtain ⟨c', h₃, hc⟩ := List.map_eq_singleton_iff.mp hl₂
    exact ⟨a', b', c', by rw [h₁, h₂, h₃], ha.symm, hb.symm, hc.symm⟩
  have hn := P.Γ.γ_nodup e₀ he₀
  rw [hl'] at hn
  have hset := P.Γ.γ_set e₀ he₀
  have hmem : ∀ x ∈ [a', b', c'], x ∈ discBd (closure e₀) := fun x hx ↦ by
    have hx' : x ∈ {v | v ∈ P.Γ.γ e₀} := by
      rw [hl']
      exact hx
    rw [hset] at hx'
    exact hsub hx'
  have := hα (closure e₀) hD a' b' c' (hmem _ (by simp)) (hmem _ (by simp)) (hmem _ (by simp))
    (by simp at hn; tauto) (by simp at hn; tauto) (by simp at hn; tauto)
  rw [show closure (α '' e₀) = α '' closure e₀ from (α.image_closure e₀).symm]
  exact this.mpr (h e₀ he₀ h3' _ _ _ hl')

omit [T2Space S] in
/-- Over a line, a connected compact set of a cut surface lies in one of the two copies of the line.
-/
theorem hasSheets_of_pair {Y : Type} [TopologicalSpace Y] {ψ : Y → S} {K : Drawing S} {X X' : Set
  Y} (hd : Disjoint X X')
    (hu : X ∪ X' = ψ ⁻¹' K.U) (hX : IsClosed X) (hX' : IsClosed X') (hi : InjOn ψ X)
      (hi' : InjOn ψ X') :
    HasSheets ψ K := by
  intro e he J _ hJ hsub
  have hJs : J ⊆ X ∪ X' := fun x hx ↦ by
    rw [hu]
    exact (he.2.1 (hsub (mem_image_of_mem ψ hx))).1
  by_cases h₁ : (J ∩ X).Nonempty
  · by_cases h₂ : (J ∩ X').Nonempty
    · obtain ⟨z, -, hz₁, hz₂⟩ := isPreconnected_closed_iff.mp hJ X X' hX hX' hJs h₁ h₂
      exact absurd hz₂ (disjoint_left.mp hd hz₁)
    · exact hi.mono fun x hx ↦ (hJs hx).resolve_right fun hx' ↦ h₂ ⟨x, hx, hx'⟩
  · exact hi'.mono fun x hx ↦ (hJs hx).resolve_left fun hx' ↦ h₁ ⟨x, hx, hx'⟩

omit [T2Space S] in
/-- A line whose two ends are vertices of `Γ` is anchored: the two sides of a point each hold an
end. -/
theorem isAnchored_of_line {Γ : Painting S} {K : Drawing S} {a b : S} (hl : IsLineWithEnds K.U a b)
  (ha : a ∈ Γ.V)
    (hb : b ∈ Γ.V) : IsAnchored Γ K := by
  obtain ⟨f, rfl, rfl⟩ := hl
  intro u x hx hne
  have hc : Continuous fun t ↦ (f t).1 := continuous_subtype_val.comp f.continuous
  let p := f.symm ⟨x, hx⟩
  have hp : (f p).1 = x := by simp [p]
  by_cases hu : u ∈ K.U
  · let q := f.symm ⟨u, hu⟩
    have hq : (f q).1 = u := by simp [q]
    have hinj : ∀ t, (f t).1 = u → t = q := fun t ht ↦ f.injective (Subtype.ext (ht.trans hq.symm))
    rcases le_total p q with hpq | hpq
    · refine ⟨(fun t ↦ (f t).1) '' Iic p, ?_, ⟨p, le_rfl, hp⟩, isPreconnected_Iic.image _
      hc.continuousOn,
        ⟨(f 0).1, ⟨0, unitInterval.nonneg _, rfl⟩, ha⟩⟩
      rintro _ ⟨t, ht, rfl⟩
      refine ⟨(f t).2, fun htu ↦ hne ?_⟩
      have := hinj t htu
      subst this
      rw [← hp, le_antisymm hpq ht]
      exact hq
    · refine ⟨(fun t ↦ (f t).1) '' Ici p, ?_, ⟨p, le_rfl, hp⟩, isPreconnected_Ici.image _
      hc.continuousOn,
        ⟨(f 1).1, ⟨1, unitInterval.le_one _, rfl⟩, hb⟩⟩
      rintro _ ⟨t, ht, rfl⟩
      refine ⟨(f t).2, fun htu ↦ hne ?_⟩
      have := hinj t htu
      subst this
      rw [← hp, le_antisymm (show p ≤ _ from ht) hpq]
      exact hq
  · refine ⟨K.U, fun y hy ↦ ⟨hy, fun h ↦ hu (h ▸ hy)⟩, hx, ?_, ⟨(f 0).1, (f 0).2, ha⟩⟩
    have : K.U = (fun t ↦ (f t).1) '' univ := by
      ext y
      constructor
      · intro hy
        exact ⟨f.symm ⟨y, hy⟩, trivial, by simp⟩
      · rintro ⟨t, -, rfl⟩
        exact (f t).2
    rw [this]
    exact isPreconnected_univ.image _ hc.continuousOn

/-- The data of (5.3) on one fragment of a given cut. -/
theorem frameData_of_cut (hS : IsSurface S) {Φ : Frame S} {Γ : Painting S}
  (hfit : Γ.Fits Φ) {K : Drawing S}
    (hinter : Γ.U ∩ K.U ⊆ Γ.V ∩ K.V)
    (hlines : ∀ e ∈ arcComponentsIn (K.U \ K.V), ∃ u v, u ≠ v ∧ closure e ∩ K.V = {u, v} ∧
      IsLineWithEnds (closure e) u v)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] {ψ : Y → S} (hY : IsSurface Y) (hψ : IsCutMap ψ K.U)
    (hsheet : HasSheets ψ K) (y : Y) : FrameData Φ Γ K (fun x : connectedComponent y ↦ ψ x.1) := by
  have hKbd : K.U ∩ bd S ⊆ K.V := fun x hx ↦ (hinter ⟨Γ.bd_subset hx.2, hx.1⟩).2
  refine ⟨⟨hS, isCuttingFragment_of_cut hS hY hψ (K := K) rfl y, hinter,
    two_of_cut hS hY hψ hsheet hlines hKbd subset_union_right (fun C' ↦ ?_) y⟩, hfit,
    two_of_cut hS hY hψ hsheet hlines hKbd subset_union_right (Frame.two_on_cuff' hS Φ) y, hKbd⟩
  obtain ⟨p, hp, q, hq, hpq⟩ := Frame.two_on_cuff hS Φ C'
  exact ⟨p, ⟨Or.inl (hfit.V_subset hp.1), hp.2⟩, q, ⟨Or.inl (hfit.V_subset hq.1), hq.2⟩, hpq⟩

omit [T2Space S] in
/-- Cutting along a line between two cuffs. -/
theorem exists_cross_cut (hS : IsSurface S) [ConnectedSpace S] {K : Drawing S} {s t : S}
  (hst : s ≠ t)
    (hbd : K.U ∩ bd S = {s, t}) (hl : IsLineWithEnds K.U s t)
    (hne : connectedComponentIn (bd S) s ≠ connectedComponentIn (bd S) t) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : T2Space Y) (ψ : Y → S), IsSurface Y
      ∧ ConnectedSpace Y ∧
      IsCutMap ψ K.U ∧ HasSheets ψ K ∧ ∃ a b c : ℕ, Nonempty (S ≃ₜ SurfaceModel a b (c + 1)) ∧
        Nonempty (Y ≃ₜ SurfaceModel a b c) := by
  obtain ⟨Y, tY, ψ, hY, hψ, h₁, -, X, X', hd, hu, hX, hX', hb, hb'⟩ :=
    cutIArc.{0} S K.U s t hS inferInstance hst hbd hl
  have : T2Space Y := hY.2.1
  obtain ⟨hc, a, b, c, h₂, h₃⟩ := h₁ hne
  have hcl : ∀ {L : Set Y}, IsLine L → IsClosed L := fun {L} ⟨f⟩ ↦ by
    have : CompactSpace L := f.compactSpace
    exact (isCompact_iff_compactSpace.mpr this).isClosed
  exact ⟨Y, tY, inferInstance, ψ, hY, hc, IsCutting.isCutMap hψ,
    hasSheets_of_pair hd hu (hcl hX) (hcl hX') hb.injOn hb'.injOn, a, b, c, h₂, h₃⟩

theorem numCuffs_model (a b c : ℕ) : numCuffs (SurfaceModel a b c) = c := by
  obtain ⟨ht, f, hf⟩ := presents_ew a b c
  exact ncard_cuffs hf

/-- A connected space is its own component. -/
def homeoComponent {Y : Type} [TopologicalSpace Y] [ConnectedSpace Y]
  (y : Y) : Y ≃ₜ connectedComponent y :=
  (Homeomorph.Set.univ Y).symm.trans (Homeomorph.setCongr
    (PreconnectedSpace.connectedComponent_eq_univ y).symm)

variable {Shat : Type} [TopologicalSpace Shat] [T2Space Shat]

omit [T2Space S] [T2Space Shat] in
/-- The fragment of the cut along a line between two cuffs has a capping homeomorphic to `Σ̂`, and
one cuff fewer. -/
theorem capped_fragment (cap : IsCappedSurface S Shat) {Y : Type} [TopologicalSpace Y]
    [ConnectedSpace Y] {y : Y} (hY₁ : IsSurface (connectedComponent y))
    (hc₁ : ConnectedSpace (connectedComponent y)) {a b c : ℕ} (h₁ : Nonempty (S ≃ₜ SurfaceModel a b
      (c + 1)))
    (h₂ : Nonempty (Y ≃ₜ SurfaceModel a b c)) :
    ∃ (Shat₁ : Type) (_ : TopologicalSpace Shat₁), Nonempty (IsCappedSurface
      (connectedComponent y) Shat₁) ∧
      Nonempty (Shat₁ ≃ₜ Shat) ∧ numCuffs (connectedComponent y) < numCuffs S := by
  obtain ⟨e₁⟩ := h₁
  obtain ⟨e₂⟩ := h₂
  let e₃ : connectedComponent y ≃ₜ SurfaceModel a b c := (homeoComponent y).symm.trans e₂
  obtain ⟨Shat₁, t₁, ⟨cap₁⟩⟩ := exists_cappedSurface _ _ hY₁ hc₁ rfl
  obtain ⟨g₁⟩ := capModel a b c Shat₁ (cap₁.ofHomeo e₃.symm)
  obtain ⟨g₂⟩ := capModel a b (c + 1) Shat (cap.ofHomeo e₁.symm)
  refine ⟨Shat₁, t₁, ⟨cap₁⟩, ⟨g₁.trans g₂.symm⟩, ?_⟩
  rw [numCuffs_eq e₃, numCuffs_eq e₁, numCuffs_model, numCuffs_model]
  omega

/-- An orientation moves along a homeomorphism. -/
theorem isOrientable_of_homeo {X X' : Type} [TopologicalSpace X] [TopologicalSpace X'] (h : X ≃ₜ X')
    (hO : IsOrientableSurface X') : IsOrientableSurface X := by
  obtain ⟨ω⟩ := hO
  have hmem : ∀ {Δ : Set X} {a : X}, a ∈ discBd Δ → h a ∈ discBd (h '' Δ) := fun {Δ a} ha ↦
    GM20.image_discBd h Δ ▸ mem_image_of_mem _ ha
  refine ⟨⟨fun Δ a b c ↦ ω.pos (h '' Δ) (h a) (h b) (h c), fun Δ hΔ ↦ ?_,
    fun Δ₁ Δ₂ h₁ h₂ hsub a b c ha hb hc hab hbc hac ↦ ?_⟩⟩
  · obtain ⟨φ, hc, hi, hr, hp⟩ := ω.isDirection (h '' Δ) (GM20.image_isClosedDisc h hΔ)
    refine ⟨h.symm ∘ φ, h.symm.continuous.comp hc, h.symm.injective.comp hi, ?_,
      fun a b c hab hbc hac ↦ ?_⟩
    · rw [range_comp, hr, GM20.image_discBd, image_image]
      simp
    · simp only [Function.comp_apply, h.apply_symm_apply]
      exact hp a b c hab hbc hac
  · exact ω.agree _ _ (GM20.image_isClosedDisc h h₁) (GM20.image_isClosedDisc h h₂)
      (image_mono hsub) _ _ _
      ⟨hmem ha.1, hmem ha.2⟩ ⟨hmem hb.1, hmem hb.2⟩ ⟨hmem hc.1, hmem hc.2⟩
      (fun e ↦ hab (h.injective e)) (fun e ↦ hbc (h.injective e)) (fun e ↦ hac (h.injective e))


end GraphMinor.GM19
