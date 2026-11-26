/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.DiscPrune
import LeanPool.GraphMinor.GM11.Ties

/-!
# Adding a line to a set that surrounds a cuff

An `O`-arc of `X ∪ L`, where the line `L` meets `X` in one point, lies in `X`. So adding `L` to `X`
keeps `X` planar in each capped
surface, and a set that surrounds a cuff still surrounds it. The paper uses this without comment in
the proof of (7.3), when it says
that regions lie in `𝒜_{r-1}(C)`.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u

local notation "𝕀" => unitInterval

variable {S T : Type u} [TopologicalSpace S] [TopologicalSpace T]

/-- An `O`-arc in `X ∪ L` lies in `X`, when the line `L` meets the closed set `X` in at most one
point. -/
theorem oArc_subset_of_whisker [T2Space S] {X L F : Set S} {x y : S} (hX : IsClosed X)
  (hxX : x ∈ X) (hL : IsLineWithEnds L x y)
    (hLX : L ∩ X ⊆ {x}) (hF : IsOArc F) (hs : F ⊆ X ∪ L) : F ⊆ X := by
  intro z hz
  by_contra hzX
  have hLc : IsClosed L := by
    obtain ⟨f, -, -⟩ := id hL
    have h3 := isCompact_range (continuous_subtype_val.comp f.continuous)
    rw [range_comp, f.surjective.range_eq, image_univ, Subtype.range_coe] at h3
    exact h3.isClosed
  have hzL : z ∈ L := (hs hz).resolve_left hzX
  have hnot : ¬ F ⊆ L := fun h => by
    obtain ⟨f, -, -⟩ := id hL
    exact not_isOArc_of_subset_line (L := L) ⟨f⟩ hF h
  obtain ⟨w, hwF, hwL⟩ := not_subset.mp hnot
  have hwX : w ∈ X := (hs hwF).resolve_right hwL
  have hzw : z ≠ w := fun h => hzX (h ▸ hwX)
  obtain ⟨A, B, hA, hB, hu, hi⟩ := hF.lines hz hwF hzw
  have key : ∀ {A : Set S} {e₁ e₂ : S}, IsLineWithEnds A e₁ e₂ → e₁ = z → e₂ = w → A ⊆ F → x ∈ A
    := by
    intro A e₁ e₂ hA h1 h2 hAF
    obtain ⟨f, h0, h1'⟩ := id hA
    have hp : IsPreconnected A := by
      have h3 := isPreconnected_range (continuous_subtype_val.comp f.continuous)
      rwa [range_comp, f.surjective.range_eq, image_univ, Subtype.range_coe] at h3
    have hz' : z ∈ A := by
      rw [← h1, ← h0]
      exact (f 0).2
    have hw' : w ∈ A := by
      rw [← h2, ← h1']
      exact (f 1).2
    obtain ⟨p, hpA, hpX, hpL⟩ := isPreconnected_closed_iff.mp hp X L hX hLc
      (hAF.trans hs) ⟨w, hw', hwX⟩ ⟨z, hz', hzL⟩
    have : p = x := hLX ⟨hpL, hpX⟩
    exact this ▸ hpA
  have h1 := key hA rfl rfl (hu ▸ subset_union_left)
  have h2 := key hB rfl rfl (hu ▸ subset_union_right)
  have h3 : x ∈ A ∩ B := ⟨h1, h2⟩
  rw [hi] at h3
  have hxL : x ∈ L := by
    obtain ⟨f, h0, -⟩ := id hL
    rw [← h0]
    exact (f 0).2
  rcases h3 with rfl | rfl
  · exact hzX hxX
  · exact hwL hxL

/-- Adding a line to a solid set that is planar in a capped surface keeps it planar there. -/
theorem isPlanar_whisker (hS : IsSurface S) [ConnectedSpace S] {C X L : Set S} {x y : S} {j : S
  → T} {D : Set T}
    (hc : IsCappedCuff C T j D) (hX : IsSolid X) (hxX : x ∈ X) (hL : IsLineWithEnds L x y)
      (hLX : L ∩ X ⊆ {x})
    (hp : IsPlanar (j '' X)) : IsPlanar (j '' (X ∪ L)) := by
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  have : T2Space T := hc.isSurface.2.1
  have : ConnectedSpace T := hc.connectedSpace hS
  have hsol : IsSolid (X ∪ L) := theorem_11_6_proof hS hX (isSolid_of_isLineWithEnds hS hL)
  have hsolj : IsSolid (j '' (X ∪ L)) := isSolid_image_of_injOn hc.isEmbedding.continuous hsol
    hc.isEmbedding.injective.injOn
  refine (theorem_5_1_of_not_isSphere hc.isSurface (.inr (hc.image_ne_univ _)) hsolj).mpr fun F hF
    hFs => ?_
  have hsubr : F ⊆ range j := hFs.trans (image_subset_range _ _)
  have hF' : IsOArc (j ⁻¹' F) := IsOArc.pull_of_embedding hc.isEmbedding hF hsubr
  have hs' : j ⁻¹' F ⊆ X ∪ L := fun z hz => by
    obtain ⟨w, hw, he⟩ := hFs hz
    rwa [← hc.isEmbedding.injective he]
  have h1 := oArc_subset_of_whisker hX.2 hxX hL hLX hF' hs'
  refine IsPlanar.mono hp fun z hz => ?_
  obtain ⟨w, rfl⟩ := hsubr hz
  exact mem_image_of_mem j (h1 hz)

/-- Adding a line to a set that surrounds a cuff keeps this. -/
theorem surroundsCuff_whisker (hS : IsSurface S) [ConnectedSpace S] {C X L : Set S} {x y : S}
  (hX : IsSolid X) (hxX : x ∈ X)
    (hL : IsLineWithEnds L x y) (hLX : L ∩ X ⊆ {x}) (hs : SurroundsCuff X C) : SurroundsCuff
      (X ∪ L) C := by
  obtain ⟨hC, ⟨hc', ⟨T, tT, j, D, hc, hp⟩, -⟩, hn⟩ := hs
  exact ⟨hC, isPlanarInCappedCuff_of_cap hS hc (isPlanar_whisker hS hc hX hxX hL hLX hp),
    fun h => hn (IsPlanar.mono h subset_union_left)⟩

/-- Adding a line to a member of `𝒜_r(C)`. -/
theorem IsScriptASet.whisker (hS : IsSurface S) [ConnectedSpace S] {G : Drawing S} {r r' : ℕ} {C X
  L : Set S} {x y : S}
    (hX : IsScriptASet G r C X) (hxX : x ∈ X) (hL : IsLineWithEnds L x y) (hLX : L ∩ X ⊆ {x})
      (hn : G.IsNormal L)
    (hc : (G.V ∩ (X ∪ L)).ncard ≤ r') : IsScriptASet G r' C (X ∪ L) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hX
  have hLc : IsPreconnected L := by
    obtain ⟨f, -, -⟩ := id hL
    have h3 := isPreconnected_range (continuous_subtype_val.comp f.continuous)
    rwa [range_comp, f.surjective.range_eq, image_univ, Subtype.range_coe] at h3
  have hxL : x ∈ L := by
    obtain ⟨f, h0, -⟩ := id hL
    rw [← h0]
    exact (f 0).2
  refine ⟨theorem_11_6_proof hS h1 (isSolid_of_isLineWithEnds hS hL),
    ⟨h2.1.mono subset_union_left, h2.2.union x hxX hxL hLc⟩, ?_,
    surroundsCuff_whisker hS h1 hxX hL hLX h4, hc⟩
  rintro z ⟨hz | hz, hU⟩
  · exact h3 ⟨hz, hU⟩
  · exact hn ⟨hz, hU⟩

/-- A path from a closed set to a point off it gives a line from the closed set that meets it once.
-/
theorem exists_whisker_line [T2Space S] {X Z : Set S} {x₀ y : S} (hX : IsClosed X) (hx₀ : x₀ ∈ X)
  (hy : y ∉ X)
    (hj : JoinedIn Z x₀ y) :
    ∃ x ∈ X, ∃ L, L ⊆ Z ∧ IsLineWithEnds L x y ∧ L ∩ X ⊆ {x} := by
  obtain ⟨γ, hγ⟩ := hj
  have hT : IsCompact (γ ⁻¹' X) := (hX.preimage γ.continuous).isCompact
  have hne : (γ ⁻¹' X).Nonempty := ⟨0, by simpa using hx₀⟩
  obtain ⟨t, ht, hmax⟩ := hT.exists_isMaxOn hne continuous_id.continuousOn
  have hmax' : ∀ s, γ s ∈ X → s ≤ t := fun s hs => hmax hs
  have ht1 : t ≠ 1 := fun h => hy (by
    have := ht
    rw [h] at this
    simpa using this)
  let σ : ℝ → S := fun u => γ (Set.projIcc 0 1 zero_le_one ((1 - u) * t + u))
  have hσ0 : σ 0 = γ t := by simp [σ]
  have hσ1 : σ 1 = y := by simp [σ]
  have hmem : ∀ u ∈ Icc (0 : ℝ) 1, (1 - u) * t + u ∈ Icc (0 : ℝ) 1 := fun u hu => by
    have h1 := t.2
    constructor <;> nlinarith [hu.1, hu.2, h1.1, h1.2]
  have hjoin : JoinedIn (Z ∩ (Xᶜ ∪ {γ t})) (γ t) y := by
    refine JoinedIn.ofLine (f := σ) (by
      exact (γ.continuous.comp (by fun_prop)).continuousOn) hσ0 hσ1 ?_
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨hγ _, ?_⟩
    by_cases hx : σ u ∈ X
    · refine .inr ?_
      have h1 := hmax' _ hx
      have h2 : ((1 - u) * t + u) ≤ t := by
        have : ((Set.projIcc 0 1 zero_le_one ((1 - u) * t + u) : 𝕀) : ℝ) ≤ t := h1
        rwa [Set.projIcc_of_mem zero_le_one (hmem u hu)] at this
      have h3 : (t : ℝ) ≤ (1 - u) * t + u := by nlinarith [hu.1, t.2.2]
      have h4 : Set.projIcc 0 1 zero_le_one ((1 - u) * t + u) = t := by
        apply Subtype.ext
        rw [Set.projIcc_of_mem zero_le_one (hmem u hu)]
        exact le_antisymm h2 h3
      change γ _ = γ t
      rw [h4]
    · exact .inl hx
  have hne' : γ t ≠ y := fun h => hy (h ▸ ht)
  have hA : γ t ∈ Z ∩ (Xᶜ ∪ {γ t}) := ⟨hγ _, .inr rfl⟩
  have hB : y ∈ Z ∩ (Xᶜ ∪ {γ t}) := ⟨by simpa using hγ 1, .inl hy⟩
  rcases (joinedIn_iff_eq_or_exists_isLineWithEnds hA hB).mp hjoin with h | ⟨L, hLs, hl⟩
  · exact absurd h hne'
  · refine ⟨γ t, ht, L, fun z hz => (hLs hz).1, hl, ?_⟩
    rintro z ⟨hzL, hzX⟩
    exact (hLs hzL).2.resolve_left fun h => h hzX

/-- A region that meets `𝒜_r(C)` lies in it. -/
theorem region_subset_scriptA (hS : IsSurface S) [ConnectedSpace S] {G : Drawing S} {r : ℕ} {C ρ :
  Set S} (hρ : ρ ∈ G.R)
    (hm : (ρ ∩ scriptA G r C).Nonempty) : ρ ⊆ scriptA G r C := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := hS.locallyConnected
  obtain ⟨x, hxρ, X, hX, hxX⟩ := hm
  intro y hy
  by_cases hyX : y ∈ X
  · exact ⟨X, hX, hyX⟩
  have harc : IsArcConnected ρ :=
    isArcConnected_of_isOpen_of_isConnected hS (region_isOpen hρ) ⟨region_nonempty hρ,
      region_isPreconnected hρ⟩
  obtain ⟨x₁, hx₁, L, hL, hl, hLX⟩ := exists_whisker_line hX.1.2 hxX hyX
    (isArcConnected_iff_joinedIn.mp harc x hxρ y hy)
  have hoff : ∀ z ∈ L, z ∉ G.U := fun z hz hU => by
    obtain ⟨w, -, hw⟩ := hρ
    have h1 := connectedComponentIn_subset _ _ (hw ▸ hL hz)
    exact h1.2 hU
  have hcard : G.V ∩ (X ∪ L) = G.V ∩ X := by
    ext z
    refine ⟨?_, fun h => ⟨h.1, .inl h.2⟩⟩
    rintro ⟨hzV, hz | hz⟩
    · exact ⟨hzV, hz⟩
    · exact absurd (G.V_subset_U hzV) (hoff z hz)
  have hs : IsScriptASet G r C (X ∪ L) :=
    IsScriptASet.whisker hS hX hx₁ hl hLX (fun z hz => absurd hz.2 (hoff z hz.1))
      (by
        rw [hcard]
        exact hX.2.2.2.2)
  have hyL : y ∈ L := by
    obtain ⟨f, -, h1⟩ := id hl
    rw [← h1]
    exact (f 1).2
  exact ⟨X ∪ L, hs, .inr hyL⟩

end GraphMinor.GM07
