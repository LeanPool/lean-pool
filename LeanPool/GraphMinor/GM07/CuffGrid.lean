/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CuffArcWalk
public import LeanPool.GraphMinor.GM07.CylinderCap
public import LeanPool.GraphMinor.GM07.CuffForest
public import LeanPool.GraphMinor.GM09.ArcSides

/-!
# The grid between two nested discs

Graph Minors VII, (5.9), page 234: "we may apply (5.8) to the portion of $\Sigma$ between $C_1$ and
$C_\beta$". The portion lies in a disc of `Σ + CHat`, and need not be a surface that we have
by name. So we carry it to a sphere by a chart of a neighbourhood of the disc, and use
`exists_cylinder_grid` there. The two discs have `G`-normal boundaries, so a set that is normal for
the part of `G` between them is `G`-normal. The result is `exists_disc_grid`. With `s = 0` it is
also the "planar form of Menger's theorem" of page 235.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function GraphMinor.Surface GraphMinor.GM11

universe u

variable {S T : Type u} [TopologicalSpace S] [TopologicalSpace T]

/-- A path carried by a map that is one to one on it is a path. -/
theorem transport_isPathBetween {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space Y] {P : Drawing X} {Q : Drawing Y} {θ : X → Y} (hK : IsCompact P.U)
    (hc : ContinuousOn θ P.U) (hi : InjOn θ P.U)
    (hV : Q.V = θ '' P.V) (hE : Q.E = image θ '' P.E) {a b : X} (h : P.IsPathBetween a b) :
      Q.IsPathBetween (θ a) (θ b) := by
  refine GM14.Whitney.isPathBetween_map (P := P) (Q := Q) θ (image θ) ?_ hV hE
    (hi.mono P.V_subset_U) h
  rintro f y z ⟨hf, hy, hz, hc'⟩
  have hclU := P.closure_subset_U hf
  have hcl : closure (θ '' f) = θ '' closure f := by
    apply subset_antisymm
    · exact closure_minimal (image_mono subset_closure) ((hK.of_isClosed_subset isClosed_closure
        hclU).image_of_continuousOn (hc.mono hclU)).isClosed
    · exact (hc.mono hclU).image_closure
  refine ⟨hE ▸ mem_image_of_mem _ hf, hV ▸ mem_image_of_mem θ hy, hV ▸ mem_image_of_mem θ hz, ?_⟩
  rw [hcl, hV, ← image_inter_on (s := closure f) (t := P.V) (fun a ha b hb e => hi
    (P.V_subset_U ha) (hclU hb) e), hc', image_pair]

private theorem inner_disc_boundary_count
    {S : Type u}
    {T : Type u}
    [TopologicalSpace S]
    [TopologicalSpace T]
    [T2Space T]
    {j : S → T}
    {G : Drawing S}
    {D₁ : Set T}
    {Δ₂ : Set T}
    {r : ℕ}
    (hi : ∀ (B : Set T), IsClosedDisc B → D₁ ⊆ B → B ⊆ Δ₂ → G.IsNormal (j ⁻¹' discBd B) → r ≤ (G.V
      ∩ j ⁻¹' discBd B).ncard)
    (E : Set T)
    (R : Type)
    [TopologicalSpace R]
    (hRc : IsClosedSurface R)
    (τ : T → R)
    (hD₁E : D₁ ⊆ E) :
    let A : Set T := Δ₂ \ discInt D₁
    ∀ (Γ : Drawing R),
    ∀ (ρ : R → T),
    (LeftInvOn ρ τ E) →
    (∀ y ∈ τ '' E, τ (ρ y) = y) →
    (∀ (x : R), IsManifoldPoint x) →
    (IsClosedDisc (τ '' D₁)) →
    let Δ' : Set R := τ '' Δ₂
    ∀ (D₂' : Set R),
    (∀ {z : T}, z ∈ discInt D₁ → τ z ∈ discInt (τ '' D₁)) →
    (Δ' ⊆ τ '' E) →
    (∀ {X : Set T}, X ⊆ A → τ '' X ∩ Γ.U ⊆ Γ.V → G.IsNormal (j ⁻¹' X)) →
    (∀ {X : Set T}, X ⊆ A → τ '' X ∩ Γ.U ⊆ Γ.V → (G.V ∩ j ⁻¹' X).ncard ≤ (τ '' X ∩
      Γ.U).ncard) →
    (∀ {B : Set R}, Disjoint (discInt D₂') B → B ⊆ Δ') →
    (∀ {B : Set R}, B ⊆ Δ' → τ '' ρ '' B = B) →
    (∀ {B : Set R}, B ⊆ Δ' → ρ '' B ⊆ Δ₂) →
    (∀ {B : Set R}, B ⊆ Δ' → ContinuousOn ρ B) →
    (∀ {B : Set R}, B ⊆ Δ' → InjOn ρ B) →
    ∀ (B : Set R),
    (IsClosedDisc B) →
    (τ '' D₁ ⊆ B) →
    (Disjoint (discInt D₂') B) →
    (discBd B ∩ Γ.U ⊆ Γ.V) →
    r ≤ (discBd B ∩ Γ.U).ncard := by
  intro A Γ ρ hρl hτρ hRman hD₁' Δ' D₂' hτint₁ hΔ'E hnormal hcount hA₁ hρimg hρin hρcon hρinj B hB
    h3 h4 h5
  have hBΔ := hA₁ h4
  obtain ⟨hB₀, hB₀b⟩ := isClosedDisc_image hB (hρcon hBΔ) (hρinj hBΔ)
  have hD₁B : D₁ ⊆ ρ '' B := fun z hz => ⟨τ z, h3 (mem_image_of_mem τ hz), hρl (hD₁E hz)⟩
  have hbA : discBd (ρ '' B) ⊆ A := fun x hx => by
    refine ⟨hρin hBΔ (Surface.discBd_subset _ hx), fun h6 => ?_⟩
    have h7 : τ x ∈ discInt (τ '' D₁) := hτint₁ h6
    have hintSub : discInt (τ '' D₁) ⊆ B := fun _ hz => h3 hz.1
    have h8 : τ x ∈ interior B := interior_maximal hintSub (hD₁'.isOpen_discInt hRman) h7
    have h9 : τ x ∈ discBd B := by
      rw [hB₀b] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [hτρ y (hΔ'E (hBΔ (Surface.discBd_subset _ hy)))]
      exact hy
    rw [← IsClosedDisc.frontier_eq_discBd hRc hB] at h9
    exact h9.2 h8
  have hτb : τ '' discBd (ρ '' B) = discBd B := by
    rw [hB₀b]
    exact hρimg ((Surface.discBd_subset B).trans hBΔ)
  have h6 : τ '' discBd (ρ '' B) ∩ Γ.U ⊆ Γ.V := by rwa [hτb]
  have h7 := hi _ hB₀ hD₁B (hρin hBΔ) (hnormal hbA h6)
  have h8 := hcount hbA h6
  rw [hτb] at h8
  exact h7.trans h8

private theorem boundary_path_vertex_count
    {S : Type u}
    {T : Type u}
    [TopologicalSpace S]
    [TopologicalSpace T]
    [T2Space T]
    {j : S → T}
    {G : Drawing S}
    {D₁ : Set T}
    {Δ₂ : Set T}
    {s : ℕ}
    (hii : ∀ (L : Set T) (u v : T), IsLineWithEnds L u v → u ∈ discBd D₁ → v ∈ discBd Δ₂ → L ⊆ Δ₂
      → Disjoint L (discInt D₁) → G.IsNormal (j ⁻¹' L) → s ≤ (G.V ∩ j ⁻¹' L).ncard)
    (E : Set T)
    (R : Type)
    [TopologicalSpace R]
    (τ : T → R)
    (hΔ₂E : Δ₂ ⊆ E)
    (hD₁E : D₁ ⊆ E) :
    let A : Set T := Δ₂ \ discInt D₁
    ∀ (Γ : Drawing R),
    ∀ (ρ : R → T),
    (LeftInvOn ρ τ E) →
    (discBd (τ '' D₁) = τ '' discBd D₁) →
    let Δ' : Set R := τ '' Δ₂
    (discBd Δ' = τ '' discBd Δ₂) →
    ∀ (D₂' : Set R),
    (discBd D₂' = discBd Δ') →
    (∀ {z : T}, z ∈ discInt D₁ → τ z ∈ discInt (τ '' D₁)) →
    (∀ {X : Set T}, X ⊆ A → τ '' X ∩ Γ.U ⊆ Γ.V → G.IsNormal (j ⁻¹' X)) →
    (∀ {X : Set T}, X ⊆ A → τ '' X ∩ Γ.U ⊆ Γ.V → (G.V ∩ j ⁻¹' X).ncard ≤ (τ '' X ∩
      Γ.U).ncard) →
    (∀ {B : Set R}, Disjoint (discInt D₂') B → B ⊆ Δ') →
    (∀ {B : Set R}, B ⊆ Δ' → τ '' ρ '' B = B) →
    (∀ {B : Set R}, B ⊆ Δ' → ρ '' B ⊆ Δ₂) →
    (∀ {B : Set R}, B ⊆ Δ' → ContinuousOn ρ B) →
    (∀ {B : Set R}, B ⊆ Δ' → InjOn ρ B) →
    ∀ (L : Set R),
    ∀ (u : R),
    ∀ (v : R),
    (IsLineWithEnds L u v) →
    (u ∈ discBd (τ '' D₁)) →
    (v ∈ discBd D₂') →
    (L ∩ Γ.U ⊆ Γ.V) →
    (Disjoint L (discInt (τ '' D₁))) →
    (Disjoint L (discInt D₂')) →
    s ≤ (L ∩ Γ.V).ncard := by
  intro A Γ ρ hρl hD₁b Δ' hΔb D₂' hD₂b hτint₁ hnormal hcount hA₁ hρimg hρin hρcon hρinj L u v h3
    h4 h5 h6 h7 h8
  have hLΔ := hA₁ h8.symm
  have hL₀ := GM09.IsLineWithEnds.image_of_injOn h3 (hρcon hLΔ) (hρinj hLΔ)
  rw [hD₁b] at h4
  rw [hD₂b, hΔb] at h5
  obtain ⟨u₀, hu₀, rfl⟩ := h4
  obtain ⟨v₀, hv₀, rfl⟩ := h5
  have hτL := hρimg hLΔ
  have hdj : Disjoint (ρ '' L) (discInt D₁) := by
    rw [disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ hi
    obtain ⟨z, hz, rfl⟩ := hLΔ hy
    rw [hρl (hΔ₂E hz)] at hi
    exact disjoint_left.mp h7 hy (hτint₁ hi)
  have hLA : ρ '' L ⊆ A := fun x hx => ⟨hρin hLΔ hx, fun h9 => disjoint_left.mp hdj hx h9⟩
  have h9 : τ '' (ρ '' L) ∩ Γ.U ⊆ Γ.V := by
    rw [hτL]
    exact h6
  rw [hρl (hD₁E (Surface.discBd_subset _ hu₀)), hρl (hΔ₂E (Surface.discBd_subset _ hv₀))] at hL₀
  have h10 := hii _ _ _ hL₀ hu₀ hv₀ (hρin hLΔ) hdj (hnormal hLA h9)
  have h11 := hcount hLA h9
  rw [hτL] at h11
  have h12 : L ∩ Γ.U ⊆ L ∩ Γ.V := fun x hx => ⟨hx.1, h6 hx⟩
  exact h10.trans (h11.trans (ncard_le_ncard h12 (Γ.finite_V.subset inter_subset_right)))

private theorem pull_subdrawing_from_grid
    {S : Type u}
    {T : Type u}
    [TopologicalSpace S]
    [T2Space S]
    {j : S → T}
    {G : Drawing S}
    (E : Set T)
    (R : Type)
    [TopologicalSpace R]
    [T2Space R]
    (τ : T → R) :
    ∀ (A : Set T),
    let Gi : Drawing S := G.span (j ⁻¹' A) {e | j '' e ⊆ A}
    (Gi.E = {e | j '' e ⊆ A} ∩ G.E) →
    (Gi.V ⊆ G.V ∩ j ⁻¹' A) →
    ∀ (Γ : Drawing R),
    (Γ.U = τ ∘ j '' Gi.U) →
    (Γ.V = τ ∘ j '' Gi.V) →
    (Γ.E = image (τ ∘ j) '' Gi.E) →
    let κ : S → R := τ ∘ j
    ∀ (θ : R → S),
    (ContinuousOn θ (τ ∘ j '' j ⁻¹' E)) →
    ∀ [CompactSpace R],
    (∀ {x : S}, x ∈ Gi.U → θ (κ x) = x) →
    (Γ.U ⊆ κ '' j ⁻¹' E) →
    (∀ {y : R}, y ∈ Γ.U → κ (θ y) = y) →
    ∀ (D' : Drawing R),
    (D'.IsSubdrawing Γ) →
    (D'.U.Nonempty) →
    ∃ D : Drawing S, D.IsSubdrawing G ∧ κ '' D.U = D'.U ∧ κ '' D.V = D'.V ∧ D.U ⊆ Gi.U ∧ D.U = θ
      '' D'.U ∧ D.V = θ '' D'.V ∧ D.E = image θ '' D'.E := by
  intro A Gi hGiE hGiV Γ hΓU hΓV hΓE κ θ hθc _ hθκ hΓK hκθ D' hD' hne
  have hDU := hD'.U_subset
  have hc : ContinuousOn θ D'.U := hθc.mono (hDU.trans hΓK)
  have hin' : InjOn θ D'.U := fun x hx y hy e => by rw [← hκθ (hDU hx), ← hκθ (hDU hy), e]
  obtain ⟨D, h3, h4, h5⟩ := exists_transport D'.isClosed_U.isCompact hne hc hin' D' subset_rfl
  have hDΓ : D.U ⊆ Gi.U := by
    rw [h3]
    rintro _ ⟨y, hy, rfl⟩
    have h6 := hDU hy
    rw [hΓU] at h6
    obtain ⟨x, hx, rfl⟩ := h6
    rwa [hθκ hx]
  have hsubV : D.V ⊆ G.V := by
    rw [h4]
    rintro _ ⟨y, hy, rfl⟩
    have h6 := hD'.1 hy
    rw [hΓV] at h6
    obtain ⟨x, hx, rfl⟩ := h6
    rw [hθκ (Gi.V_subset_U hx)]
    exact (hGiV hx).1
  have hsubE : D.E ⊆ G.E := by
    rw [h5]
    rintro _ ⟨f, hf, rfl⟩
    have h6 := hD'.2 hf
    rw [hΓE] at h6
    obtain ⟨e, he, rfl⟩ := h6
    have hee : e ⊆ Gi.U := fun z hz => Gi.closure_subset_U he (subset_closure hz)
    have h7 : image θ (image κ e) = e := by
      rw [image_image]
      exact (image_congr fun z hz => hθκ (hee hz)).trans (image_id' e)
    rw [h7]
    rw [hGiE] at he
    exact he.2
  have himg : ∀ {W : Set R}, W ⊆ D'.U → κ '' (θ '' W) = W := fun {W} hW => by
    rw [image_image]
    exact (image_congr fun y hy => hκθ (hDU (hW hy))).trans (image_id' W)
  refine ⟨D, ⟨hsubV, hsubE⟩, ?_, ?_, hDΓ, h3, h4, h5⟩
  · rw [h3]
    exact himg subset_rfl
  · rw [h4]
    exact himg D'.V_subset_U

private theorem transport_disc_grid
    {S : Type u}
    {T : Type u}
    [TopologicalSpace S]
    [TopologicalSpace T]
    [T2Space S]
    [T2Space T]
    [ConnectedSpace S]
    {j : S → T}
    (hcj : IsClosedEmbedding j)
    {G : Drawing S}
    {D₁ : Set T}
    {Δ₂ : Set T}
    {r : ℕ}
    {s : ℕ}
    (hii' : Injective j)
    (E : Set T)
    (R : Type)
    [TopologicalSpace R]
    [T2Space R]
    (hRc : IsClosedSurface R)
    (τ : T → R)
    (hD₁E : D₁ ⊆ E) :
    let A : Set T := Δ₂ \ discInt D₁
    ∀ (Gi : Drawing S),
    (Gi.U ⊆ j ⁻¹' A) →
    (InjOn (τ ∘ j) (j ⁻¹' E)) →
    (Gi.U ⊆ j ⁻¹' E) →
    ∀ (Γ : Drawing R),
    (Γ.V = τ ∘ j '' Gi.V) →
    let κ : S → R := τ ∘ j
    ∀ (θ : R → S),
    ∀ (ρ : R → T),
    (LeftInvOn ρ τ E) →
    (IsClosedDisc (τ '' D₁)) →
    let Δ' : Set R := τ '' Δ₂
    ∀ (D₂' : Set R),
    (IsClosedDisc D₂') →
    (∀ {y : S}, y ∈ Gi.U → κ y ∈ τ '' D₁ → j y ∈ discBd D₁) →
    (∀ {y : S}, y ∈ Gi.U → κ y ∈ D₂' → j y ∈ discBd Δ₂) →
    (Disjoint Γ.U (discInt (τ '' D₁))) →
    (Disjoint Γ.U (discInt D₂')) →
    (∀ {B : Set R}, Disjoint (discInt D₂') B → B ⊆ Δ') →
    (∀ {B : Set R}, B ⊆ Δ' → ρ '' B ⊆ Δ₂) →
    (∀ {B : Set R}, B ⊆ Δ' → ContinuousOn ρ B) →
    (∀ {B : Set R}, B ⊆ Δ' → InjOn ρ B) →
    ∀ (p₁ : R),
    (p₁ ∈ discInt (τ '' D₁)) →
    ∀ (p₂ : R),
    (p₂ ∈ discInt D₂') →
    ∀ [CompactSpace R],
    ∀ (P' : Fin r → Drawing R),
    ∀ (u' : Fin r → R),
    ∀ (v' : Fin r → R),
    ∀ (B' : Fin s → Drawing R),
    ∀ (E' : Fin s → Set R),
    (∀ (i : Fin r), (P' i).IsSubdrawing Γ ∧ u' i ∈ τ '' D₁ ∧ v' i ∈ D₂' ∧ (P'
      i).IsPathBetween (u' i) (v' i)) →
    (∀ (i i' : Fin r), i ≠ i' → Disjoint (P' i).V (P' i').V) →
    (∀ (j : Fin s), (B' j).IsSubdrawing Γ ∧ (B' j).IsCircuit ∧ IsClosedDisc (E' j) ∧ discBd
      (E' j) = (B' j).U ∧ p₁ ∈ E' j ∧ p₂ ∉ E' j) →
    (∀ (j j' : Fin s), j ≤ j' → E' j ⊆ E' j') →
    (∀ (j j' : Fin s), j ≠ j' → Disjoint (B' j).V (B' j').V) →
    (∀ (i : Fin r) (j : Fin s), ∃ (Q : Drawing R) (x y : R), Q.IsSubdrawing Γ ∧ Q.U = (P' i).U ∩
      (B' j).U ∧ Q.V
      = (P' i).V ∩ (B' j).V ∧ Q.IsPathBetween x y) →
    (∀ {x : S}, x ∈ Gi.U → θ (κ x) = x) →
    (∀ {y : R}, y ∈ Γ.U → κ (θ y) = y) →
    (∀ (D' : Drawing R), D'.IsSubdrawing Γ → D'.U.Nonempty → ∃ D : Drawing S, D.IsSubdrawing G
      ∧ κ
      '' D.U = D'.U ∧ κ '' D.V = D'.V ∧ D.U ⊆ Gi.U ∧ D.U = θ '' D'.U ∧ D.V = θ '' D'.V ∧ D.E =
      image θ '' D'.E) →
    (∀ {X : Drawing R} {a b : R}, X.IsPathBetween a b → X.U.Nonempty) →
    (∀ {D' : Drawing R}, D'.IsSubdrawing Γ → InjOn θ D'.U) →
    (∀ {D' : Drawing R}, D'.IsSubdrawing Γ → ContinuousOn θ D'.U) →
    ∀ (P : Fin r → Drawing S),
    (∀ (i : Fin r), (P i).IsSubdrawing G) →
    (∀ (i : Fin r), κ '' (P i).U = (P' i).U) →
    (∀ (i : Fin r), κ '' (P i).V = (P' i).V) →
    (∀ (i : Fin r), (P i).U ⊆ Gi.U) →
    (∀ (i : Fin r), (P i).IsPathBetween (θ (u' i)) (θ (v' i))) →
    ∀ (B : Fin s → Drawing S),
    (∀ (l : Fin s), (B l).IsSubdrawing G) →
    (∀ (l : Fin s), κ '' (B l).U = (B' l).U) →
    (∀ (l : Fin s), κ '' (B l).V = (B' l).V) →
    (∀ (l : Fin s), (B l).U ⊆ Gi.U) →
    ∃ (P : Fin r → Drawing S) (u v : Fin r → S) (B : Fin s → Drawing S) (E : Fin s → Set T), (∀ i,
      (P i).IsSubdrawing G ∧ j (u i) ∈ discBd D₁ ∧ j (v i) ∈ discBd Δ₂ ∧ (P i).IsPathBetween (u i)
      (v i) ∧ j '' (P i).U ⊆ Δ₂ \ discInt D₁) ∧ (∀ i i', i ≠ i' → Disjoint (P i).V (P i').V) ∧ (∀
      l, (B l).IsSubdrawing G ∧ (B l).IsCircuit ∧ IsClosedDisc (E l) ∧ discBd (E l) = j '' (B l).U
      ∧ D₁ ⊆ E l ∧ E l ⊆ Δ₂) ∧ (∀ l l', l ≤ l' → E l ⊆ E l') ∧ (∀ l l', l ≠ l' → Disjoint (B l).V
      (B l').V) ∧ ∀ i l, ∃ (Q : Drawing S) (x y : S), Q.IsSubdrawing G ∧ Q.U = (P i).U ∩ (B l).U ∧
      Q.V = (P i).V ∩ (B l).V ∧ Q.IsPathBetween x y := by
  intro A Gi hGiU hκi hGiK Γ hΓV κ θ ρ hρl hD₁' Δ' D₂' hD₂' hκD₁ hκD₂ hi₁ hi₂ hA₁ hρin hρcon hρinj
    p₁ hp₁ p₂ hp₂ this P' u' v' B' E' hP hPd hB hEm hBd hQ hθκ hκθ hpull hnonU hthe hcthe P hPs
    hPU hPV hPG hPp B hBs hBU hBV hBG
  classical
  have hmemκ : ∀ {X : Set S} {x : S}, X ⊆ Gi.U → x ∈ Gi.U → κ x ∈ κ '' X → x ∈ X
    := fun {X x} hX hx h => by
    obtain ⟨y, hy, he⟩ := h
    exact hκi (hGiK (hX hy)) (hGiK hx) he ▸ hy
  have hsplit : ∀ {X Y Z : Set S} {X' Y' Z' : Set R}, X ⊆ Gi.U → Y ⊆ Gi.U → Z ⊆ Gi.U → κ '' X = X'
    → κ '' Y = Y' → κ '' Z = Z' → Z' = X' ∩ Y' → Z = X ∩ Y := fun {X Y Z X' Y' Z'} hX hY hZ h3 h4
      h5 h6 => by
    ext x
    constructor
    · intro hx
      have h7 : κ x ∈ X' ∩ Y' := h6 ▸ h5 ▸ mem_image_of_mem κ hx
      exact ⟨hmemκ hX (hZ hx) (h3 ▸ h7.1), hmemκ hY (hZ hx) (h4 ▸ h7.2)⟩
    · rintro ⟨hx, hy⟩
      have h7 : κ x ∈ Z' := h6 ▸ ⟨h3 ▸ mem_image_of_mem κ hx, h4 ▸ mem_image_of_mem κ hy⟩
      exact hmemκ hZ (hX hx) (h5 ▸ h7)
  have hE'data : ∀ l, E' l ⊆ Δ' ∧ τ '' D₁ ⊆ E' l := fun l => by
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hB l
    have hf₁ : Disjoint (discInt (τ '' D₁)) (discBd (E' l)) := by
      rw [c4]
      exact hi₁.symm.mono_right c1.U_subset
    have hf₂ : Disjoint (discInt D₂') (discBd (E' l)) := by
      rw [c4]
      exact hi₂.symm.mono_right c1.U_subset
    constructor
    · refine hA₁ (disjoint_left.mpr fun y hy h => c6 ?_)
      exact side_of_disc hRc hD₂' c3 hf₂ hy hp₂ h
    · have h3 : discInt (τ '' D₁) ⊆ E' l := fun y hy => side_of_disc hRc hD₁' c3 hf₁ hp₁ hy c5
      exact hD₁'.subset_closure_discInt.trans (closure_minimal h3 c3.isClosed)
  have hEl : ∀ l, IsClosedDisc (ρ '' E' l) ∧ discBd (ρ '' E' l) = j '' (B l).U := fun l => by
    obtain ⟨c1, c2, c3, c4, -⟩ := hB l
    obtain ⟨h3, h4⟩ := isClosedDisc_image c3 (hρcon (hE'data l).1) (hρinj (hE'data l).1)
    refine ⟨h3, h4.trans ?_⟩
    rw [c4, ← hBU l, image_image]
    exact image_congr fun z hz => hρl (hGiK (hBG l hz))
  have hBcirc : ∀ l, (B l).IsCircuit := fun l => by
    have hO : IsOArc (B l).U := by
      have h3 := (hEl l).1.isOArc_discBd
      rw [(hEl l).2] at h3
      have h4 := pull_oArc hcj.isEmbedding h3 (image_subset_range _ _)
      rwa [preimage_image_eq _ hii'] at h4
    obtain ⟨X, h3, h4, h5⟩ := exists_circuit_of_oArc hO (hBs l).U_subset
    have hV : X.V = (B l).V := subset_antisymm (fun x hx => mem_V_of_subdrawing (hBs l)
      (h5 ▸ X.V_subset_U hx) (h4.1 hx)) fun x hx => mem_V_of_subdrawing h4 (h5.symm ▸
        (B l).V_subset_U hx) ((hBs l).1 hx)
    have hE : X.E = (B l).E := by
      unfold Drawing.E
      rw [h5, hV]
    have : X = B l := Drawing.ext_of_V_E hV hE
    exact this ▸ h3
  have hstart : ∀ i, u' i ∈ (P' i).V ∧ v' i ∈ (P' i).V := fun i => by
    obtain ⟨-, -, -, W, -, hV, -⟩ := hP i
    exact ⟨by rw [hV]; exact W.start_mem_support, by rw [hV]; exact W.end_mem_support⟩
  have hΓmem : ∀ {y}, y ∈ Γ.V → θ y ∈ Gi.V := fun {y} hy => by
    rw [hΓV] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rwa [hθκ (Gi.V_subset_U hx)]
  refine ⟨P, fun i => θ (u' i), fun i => θ (v' i), B, fun l => ρ '' E' l, fun i
    => ⟨hPs i, ?_, ?_, hPp i, ?_⟩, fun i i' hne => ?_, fun l => ⟨hBs l, hBcirc l, (hEl l).1,
      (hEl l).2, ?_, hρin (hE'data l).1⟩, fun l l' hl => image_mono (hEm l l' hl), fun l l' hne
        => ?_, fun i l => ?_⟩
  · have h3 := hΓmem ((hP i).1.1 (hstart i).1)
    refine hκD₁ (Gi.V_subset_U h3) ?_
    rw [hκθ ((hP i).1.U_subset ((P' i).V_subset_U (hstart i).1))]
    exact (hP i).2.1
  · have h3 := hΓmem ((hP i).1.1 (hstart i).2)
    refine hκD₂ (Gi.V_subset_U h3) ?_
    rw [hκθ ((hP i).1.U_subset ((P' i).V_subset_U (hstart i).2))]
    exact (hP i).2.2.1
  · rintro _ ⟨y, hy, rfl⟩
    exact hGiU (hPG i hy)
  · rw [disjoint_left]
    intro x h3 h4
    exact disjoint_left.mp (hPd i i' hne) (hPV i ▸ mem_image_of_mem κ h3)
      (hPV i' ▸ mem_image_of_mem κ h4)
  · intro z hz
    exact ⟨τ z, (hE'data l).2 (mem_image_of_mem τ hz), hρl (hD₁E hz)⟩
  · rw [disjoint_left]
    intro x h3 h4
    exact disjoint_left.mp (hBd l l' hne) (hBV l ▸ mem_image_of_mem κ h3)
      (hBV l' ▸ mem_image_of_mem κ h4)
  · obtain ⟨Q', x, y, c1, c2, c3, c4⟩ := hQ i l
    obtain ⟨D, h3, h4, h5, h6, h7, h8, h9⟩ := hpull _ c1 (hnonU c4)
    refine ⟨D, θ x, θ y, h3, hsplit (hPG i) (hBG l) h6 (hPU i) (hBU l) h4 c2, hsplit
      ((P i).V_subset_U.trans (hPG i)) ((B l).V_subset_U.trans (hBG l)) (D.V_subset_U.trans h6)
        (hPV i) (hBV l) h5 c3, ?_⟩
    exact transport_isPathBetween Q'.isClosed_U.isCompact (hcthe c1) (hthe c1) h8 h9 c4

private theorem spanned_drawing_in_grid_region
    {S : Type u}
    {T : Type u}
    [TopologicalSpace S]
    [T1Space S]
    {j : S → T}
    {G : Drawing S}
    (A : Set T) :
    let Gi : Drawing S := G.span (j ⁻¹' A) {e | j '' e ⊆ A}
    (∀ {e : Set S}, j '' e ⊆ A → closure e ⊆ j ⁻¹' A) →
    (Gi.V ⊆ G.V ∩ j ⁻¹' A) →
    Gi.U ⊆ j ⁻¹' A := by
  intro Gi hclA hGiV
  rintro x (hx | hx)
  · exact (hGiV hx).2
  · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
    exact hclA he.1 hxe

private theorem grid_region_points_in_spanned_drawing
    {S : Type u}
    {T : Type u}
    [TopologicalSpace S]
    [T1Space S]
    [TopologicalSpace T]
    [T2Space T]
    (hT : ∀ (x : T), IsManifoldPoint x)
    {j : S → T}
    (hcj : IsClosedEmbedding j)
    {G : Drawing S}
    {D₁ : Set T}
    {Δ₂ : Set T}
    (h₁ : IsClosedDisc D₁)
    (h₂ : IsClosedDisc Δ₂)
    (hn₁ : G.IsNormal (j ⁻¹' discBd D₁))
    (hn₂ : G.IsNormal (j ⁻¹' discBd Δ₂)) :
    let A : Set T := Δ₂ \ discInt D₁
    let Gi : Drawing S := G.span (j ⁻¹' A) {e | j '' e ⊆ A}
    (Gi.E = {e | j '' e ⊆ A} ∩ G.E) →
    (∀ y ∈ G.V, j y ∈ A → y ∈ Gi.V) →
    ∀ (x : S),
    (x ∈ G.U) →
    (j x ∈ A) →
    x ∈ Gi.U := by
  intro A Gi hGiE hinV x hx hA
  by_cases hxV : x ∈ G.V
  · exact Gi.V_subset_U (hinV x hxV hA)
  obtain ⟨e, he, hxe⟩ := G.exists_edge_of_mem hx hxV
  have hpc : IsPreconnected (j '' e) := he.2.2.1.isConnected.isPreconnected.image _
    hcj.continuous.continuousOn
  have hoff : ∀ {Y : Set T}, G.IsNormal (j ⁻¹' Y) → Disjoint (j '' e) Y := fun {Y} hY => by
    rw [disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ hzb
    have hzU := he.2.1 hz
    exact hzU.2 (hY ⟨hzb, hzU.1⟩)
  have hsub : j '' e ⊆ A := by
    have h3 := inside_or_off hpc h₁.isClosed ((hoff hn₁).mono_right (frontier_disc_subset hT h₁))
    have h4 := inside_or_off hpc h₂.isClosed ((hoff hn₂).mono_right (frontier_disc_subset hT h₂))
    have h5 : j '' e ⊆ (D₁)ᶜ := h3.resolve_left fun h => hA.2 ⟨interior_subset (h
      (mem_image_of_mem j hxe)), disjoint_left.mp (hoff hn₁) (mem_image_of_mem j hxe)⟩
    have h6 : j '' e ⊆ interior Δ₂ := h4.resolve_right fun h => h (mem_image_of_mem j hxe) hA.1
    exact fun z hz => ⟨interior_subset (h6 hz), fun h7 => h5 hz h7.1⟩
  have hmem : e ∈ Gi.E := by
    rw [hGiE]
    exact ⟨hsub, he⟩
  exact Gi.closure_subset_U hmem (subset_closure hxe)

private theorem pull_grid_paths
    {S : Type u}
    {T : Type u}
    [TopologicalSpace S]
    [T2Space S]
    {G : Drawing S}
    {D₁ : Set T}
    {r : ℕ}
    (R : Type)
    [TopologicalSpace R]
    (τ : T → R)
    (Gi : Drawing S)
    (Γ : Drawing R)
    (κ : S → R)
    (θ : R → S)
    (D₂' : Set R)
    [CompactSpace R]
    (P' : Fin r → Drawing R)
    (u' : Fin r → R)
    (v' : Fin r → R)
    (hP : ∀ (i : Fin r), (P' i).IsSubdrawing Γ ∧ u' i ∈ τ '' D₁ ∧ v' i ∈ D₂' ∧ (P'
      i).IsPathBetween (u' i) (v' i))
    (hpull : ∀ (D' : Drawing R), D'.IsSubdrawing Γ → D'.U.Nonempty → ∃ D : Drawing S,
      D.IsSubdrawing G ∧ κ ''
      D.U = D'.U ∧ κ '' D.V = D'.V ∧ D.U ⊆ Gi.U ∧ D.U = θ '' D'.U ∧ D.V = θ '' D'.V ∧ D.E = image
      θ '' D'.E)
    (hnonU : ∀ {X : Drawing R} {a b : R}, X.IsPathBetween a b → X.U.Nonempty)
    (hthe : ∀ {D' : Drawing R}, D'.IsSubdrawing Γ → InjOn θ D'.U)
    (hcthe : ∀ {D' : Drawing R}, D'.IsSubdrawing Γ → ContinuousOn θ D'.U)
    (i : Fin r) :
    ∃ D : Drawing S, D.IsSubdrawing G ∧ κ '' D.U = (P' i).U ∧ κ '' D.V = (P' i).V ∧ D.U ⊆ Gi.U ∧
      D.IsPathBetween (θ (u' i)) (θ (v' i)) := by
  obtain ⟨c1, -, -, c4⟩ := hP i
  obtain ⟨D, h3, h4, h5, h6, h7, h8, h9⟩ := hpull _ c1 (hnonU c4)
  exact ⟨D, h3, h4, h5, h6, transport_isPathBetween (P' i).isClosed_U.isCompact (hcthe c1)
    (hthe c1) h8 h9 c4⟩

private theorem pull_grid_circuits
    {S : Type u}
    [TopologicalSpace S]
    {G : Drawing S}
    {s : ℕ}
    (R : Type)
    [TopologicalSpace R]
    [T2Space R]
    (Gi : Drawing S)
    (Γ : Drawing R)
    (κ : S → R)
    (θ : R → S)
    (p₁ : R)
    (p₂ : R)
    (B' : Fin s → Drawing R)
    (E' : Fin s → Set R)
    (hB : ∀ (j : Fin s), (B' j).IsSubdrawing Γ ∧ (B' j).IsCircuit ∧ IsClosedDisc (E' j) ∧ discBd
      (E' j) = (B' j).U ∧ p₁ ∈ E' j ∧ p₂ ∉ E' j)
    (hpull : ∀ (D' : Drawing R), D'.IsSubdrawing Γ → D'.U.Nonempty → ∃ D : Drawing S,
      D.IsSubdrawing G ∧ κ ''
      D.U = D'.U ∧ κ '' D.V = D'.V ∧ D.U ⊆ Gi.U ∧ D.U = θ '' D'.U ∧ D.V = θ '' D'.V ∧ D.E = image
      θ '' D'.E)
    (l : Fin s) :
    ∃ D : Drawing S, D.IsSubdrawing G ∧ κ '' D.U = (B' l).U ∧ κ '' D.V = (B' l).V ∧ D.U ⊆ Gi.U := by
  obtain ⟨c1, c2, -⟩ := hB l
  have hne : (B' l).U.Nonempty := (GM14.isOArc_of_isCircuit c2 |> isConnected_of_isOArc).nonempty
  obtain ⟨D, h3, h4, h5, h6, -⟩ := hpull _ c1 hne
  exact ⟨D, h3, h4, h5, h6⟩

private theorem grid_on_outer_disc_is_at_vertices
    {S : Type u}
    {T : Type u}
    [TopologicalSpace S]
    [TopologicalSpace T]
    {j : S → T}
    {D₁ : Set T}
    {Δ₂ : Set T}
    (R : Type)
    [TopologicalSpace R]
    (τ : T → R)
    (Gi : Drawing S)
    (Γ : Drawing R)
    (hΓU : Γ.U = τ ∘ j '' Gi.U)
    (hΓV : Γ.V = τ ∘ j '' Gi.V) :
    let κ : S → R := τ ∘ j
    ∀ (D₂' : Set R),
    (∀ {y : S}, y ∈ Gi.U → j y ∈ discBd D₁ ∪ discBd Δ₂ → y ∈ Gi.V) →
    (∀ {y : S}, y ∈ Gi.U → κ y ∈ D₂' → j y ∈ discBd Δ₂) →
    Γ.U ∩ D₂' ⊆ Γ.V := by
  intro κ D₂' hbdV hκD₂
  rintro _ ⟨hx, hb⟩
  rw [hΓU] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [hΓV]
  exact ⟨y, hbdV hy (.inr (hκD₂ hy hb)), rfl⟩

private theorem grid_avoids_outer_disc_interior
    {S : Type u}
    {T : Type u}
    [TopologicalSpace S]
    [TopologicalSpace T]
    {j : S → T}
    {D₁ : Set T}
    {Δ₂ : Set T}
    (R : Type)
    [TopologicalSpace R]
    (τ : T → R) :
    let A : Set T := Δ₂ \ discInt D₁
    ∀ (Gi : Drawing S),
    (Gi.U ⊆ j ⁻¹' A) →
    ∀ (Γ : Drawing R),
    (Γ.U = τ ∘ j '' Gi.U) →
    let Δ' : Set R := τ '' Δ₂
    ∀ (D₂' : Set R),
    (∀ {x : R}, x ∈ discInt D₂' → x ∉ Δ') →
    Disjoint Γ.U (discInt D₂') := by
  intro A Gi hGiU Γ hΓU Δ' D₂' hint₂
  rw [disjoint_left]
  intro x hx hi
  rw [hΓU] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact hint₂ hi (mem_image_of_mem τ (hGiU hy).1)

private theorem inner_disc_hit_pulls_back_to_boundary
    {S : Type u}
    {T : Type u}
    [TopologicalSpace S]
    [TopologicalSpace T]
    {j : S → T}
    {D₁ : Set T}
    {Δ₂ : Set T}
    (E : Set T)
    (R : Type)
    (τ : T → R)
    (hτi : InjOn τ E)
    (hD₁E : D₁ ⊆ E) :
    let A : Set T := Δ₂ \ discInt D₁
    ∀ (Gi : Drawing S),
    (Gi.U ⊆ j ⁻¹' A) →
    (Gi.U ⊆ j ⁻¹' E) →
    let κ : S → R := τ ∘ j
    ∀ {y : S},
    (y ∈ Gi.U) →
    (κ y ∈ τ '' D₁) →
    j y ∈ discBd D₁ := by
  intro A Gi hGiU hGiK κ y hy h
  obtain ⟨z, hz, he⟩ := h
  have h3 : z = j y := hτi (hD₁E hz) (hGiK hy) he
  by_contra hb
  exact (hGiU hy).2 ⟨h3 ▸ hz, hb⟩

private theorem outer_disc_hit_pulls_back_to_boundary
    {S : Type u}
    {T : Type u}
    [TopologicalSpace S]
    [TopologicalSpace T]
    {j : S → T}
    {D₁ : Set T}
    {Δ₂ : Set T}
    (R : Type)
    [TopologicalSpace R]
    (τ : T → R) :
    let A : Set T := Δ₂ \ discInt D₁
    ∀ (Gi : Drawing S),
    (Gi.U ⊆ j ⁻¹' A) →
    let κ : S → R := τ ∘ j
    ∀ (Δ' : Set R),
    ∀ (D₂' : Set R),
    (∀ {x : R}, x ∈ discInt Δ' → x ∉ D₂') →
    (∀ {z : T}, z ∈ Δ₂ → z ∉ discBd Δ₂ → τ z ∈ discInt Δ') →
    ∀ {y : S},
    (y ∈ Gi.U) →
    (κ y ∈ D₂') →
    j y ∈ discBd Δ₂ := by
  intro A Gi hGiU κ Δ' D₂' hnotΔ hτint y hy h
  by_contra hb
  exact hnotΔ (hτint (hGiU hy).1 hb) h

/-- **The portion between two discs.** Let `D₁` lie strictly inside `Δ₂`, with `G`-normal
boundaries. If all discs between them have at least `r` vertices on their boundaries, and all lines
across have at least `s` vertices, then there are `r` paths and `s` circuits between them, with
nested discs, and the intersection of each path and circuit is a path. -/
theorem exists_disc_grid [T2Space S] [T2Space T] [ConnectedSpace S] (hT : ∀ x : T, IsManifoldPoint
  x) {j : S → T} (hcj : IsClosedEmbedding j) {G : Drawing S} {D₁ Δ₂ : Set T} (h₁ : IsClosedDisc D₁)
    (h₂ : IsClosedDisc Δ₂)
    (hin : D₁ ⊆ Δ₂ \ discBd Δ₂) (hr : Δ₂ \ discInt D₁ ⊆ range j) (hn₁ : G.IsNormal
      (j ⁻¹' discBd D₁)) (hn₂ : G.IsNormal (j ⁻¹' discBd Δ₂)) (hint : ∀ x ∈ discBd Δ₂,
        IsInteriorPoint x) {r s : ℕ}
    (hi : ∀ B, IsClosedDisc B → D₁ ⊆ B → B ⊆ Δ₂ → G.IsNormal (j ⁻¹' discBd B) → r ≤
      (G.V ∩ j ⁻¹' discBd B).ncard)
    (hii : ∀ L u v, IsLineWithEnds L u v → u ∈ discBd D₁ → v ∈ discBd Δ₂ → L ⊆ Δ₂ → Disjoint L
      (discInt D₁) → G.IsNormal (j ⁻¹' L) → s ≤ (G.V ∩ j ⁻¹' L).ncard) :
    ∃ (P : Fin r → Drawing S) (u v : Fin r → S) (B : Fin s → Drawing S) (E : Fin s → Set T),
      (∀ i, (P i).IsSubdrawing G ∧ j (u i) ∈ discBd D₁ ∧ j (v i) ∈ discBd Δ₂ ∧ (P i).IsPathBetween
        (u i) (v i) ∧ j '' (P i).U ⊆ Δ₂ \ discInt D₁) ∧
      (∀ i i', i ≠ i' → Disjoint (P i).V (P i').V) ∧
      (∀ l, (B l).IsSubdrawing G ∧ (B l).IsCircuit ∧ IsClosedDisc (E l) ∧ discBd (E l) = j ''
        (B l).U ∧ D₁ ⊆ E l ∧ E l ⊆ Δ₂) ∧
      (∀ l l', l ≤ l' → E l ⊆ E l') ∧
      (∀ l l', l ≠ l' → Disjoint (B l).V (B l').V) ∧
      ∀ i l, ∃ (Q : Drawing S) (x y : S), Q.IsSubdrawing G ∧ Q.U = (P i).U ∩ (B l).U ∧ Q.V =
        (P i).V ∩ (B l).V ∧ Q.IsPathBetween x y := by
  classical
  have hii' := hcj.injective
  obtain ⟨E, hE, hΔE, -⟩ := Surface.exists_disc_around hT h₂ hint isOpen_univ (subset_univ _)
  obtain ⟨p⟩ := h₂.isOArc_discBd
  obtain ⟨c, c', hcc, hcc', hm, hm', hl, hr', hcE, hcb, -⟩ := exists_disc_collar h₂ hE hΔE p
  obtain ⟨R, tR, ι, hR2, hRc, hRs, hιc, hιi⟩ := exists_sphere_chart
  let τ : T → R := ι ∘ c'
  have hτc : ContinuousOn τ E := hιc.comp_continuousOn hcc'
  have hτi : InjOn τ E := fun x hx y hy h => by
    have h1 : c' x = c' y := hιi h
    rw [← hr' hx, ← hr' hy, h1]
  have hΔ₂E : Δ₂ ⊆ E := fun x hx => (hΔE hx).1
  have hD₁E : D₁ ⊆ E := fun x hx => hΔ₂E (hin hx).1
  -- the part of `G` between the discs
  let A : Set T := Δ₂ \ discInt D₁
  have hAc : IsClosed A := h₂.isClosed.inter (h₁.isOpen_discInt hT).isClosed_compl
  let Gi : Drawing S := G.span (j ⁻¹' A) {e | j '' e ⊆ A}
  have hGiE : Gi.E = {e | j '' e ⊆ A} ∩ G.E := G.span_E _ _
  have hclA : ∀ {e : Set S}, j '' e ⊆ A → closure e ⊆ j ⁻¹' A := fun {e} he => closure_minimal
    (fun z hz => he (mem_image_of_mem j hz)) (hAc.preimage hcj.continuous)
  have hGiV : Gi.V ⊆ G.V ∩ j ⁻¹' A := by
    rintro x (hx | hx)
    · exact ⟨hx.2, hx.1⟩
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      exact ⟨hxe.2, hclA he.1 hxe.1⟩
  have hGiU : Gi.U ⊆ j ⁻¹' A := by
    exact spanned_drawing_in_grid_region (S := S) (T := T) (j := j) (G := G) A hclA hGiV
  have hGiUU : Gi.U ⊆ G.U := (Drawing.span_isSubdrawing G _ _).U_subset
  have hinV : ∀ y ∈ G.V, j y ∈ A → y ∈ Gi.V := fun y hy h => .inl ⟨h, hy⟩
  -- points of `G` in `A` are in the part
  have hmemU : ∀ x ∈ G.U, j x ∈ A → x ∈ Gi.U := fun x hx hA => by
    exact grid_region_points_in_spanned_drawing (S := S) (T := T) hT (j := j) hcj (G := G) (D₁ :=
      D₁) (Δ₂ := Δ₂) h₁ h₂ hn₁ hn₂   hGiE hinV x hx hA
  -- the chart to a sphere
  have hKc : IsCompact (j ⁻¹' E) := hcj.isCompact_preimage hE.isCompact
  have hκc : ContinuousOn (τ ∘ j) (j ⁻¹' E) := hτc.comp hcj.continuous.continuousOn fun x hx => hx
  have hκi : InjOn (τ ∘ j) (j ⁻¹' E) := fun x hx y hy h => hii' (hτi hx hy h)
  have hAE : j ⁻¹' A ⊆ j ⁻¹' E := preimage_mono fun x hx => hΔ₂E hx.1
  have hGiK : Gi.U ⊆ j ⁻¹' E := hGiU.trans hAE
  have hAne : (j ⁻¹' E).Nonempty := by
    obtain ⟨z, hz⟩ := (isConnected_of_isOArc h₂.isOArc_discBd).nonempty
    obtain ⟨y, hy⟩ := hr ⟨Surface.discBd_subset _ hz, fun h3 => (hin h3.1).2 hz⟩
    exact ⟨y, by rw [mem_preimage, hy]; exact hΔ₂E (Surface.discBd_subset _ hz)⟩
  have : Nonempty S := ⟨hAne.some⟩
  obtain ⟨Γ, hΓU, hΓV, hΓE⟩ := exists_transport hKc hAne hκc hκi Gi hGiK
  let κ : S → R := τ ∘ j
  obtain ⟨θ, hθc, hθl⟩ := Surface.exists_inv_of_compactOn hKc hκc hκi
  have : Nonempty T := ⟨j hAne.some⟩
  obtain ⟨ρ, hρc, hρl⟩ := Surface.exists_inv_of_compactOn hE.isCompact hτc hτi
  have hτρ : ∀ y ∈ τ '' E, τ (ρ y) = y := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hρl hx]
  have hRman : ∀ x : R, IsManifoldPoint x := fun x => (hRc.2.2 x).isManifoldPoint
  obtain ⟨hD₁', hD₁b⟩ := isClosedDisc_image h₁ (hτc.mono hD₁E) (hτi.mono hD₁E)
  obtain ⟨hΔ', hΔb⟩ := isClosedDisc_image h₂ (hτc.mono hΔ₂E) (hτi.mono hΔ₂E)
  obtain ⟨hD₂', hD₂b⟩ := GM12.isClosedDisc_closure_compl_of_sphere hRc hRs hΔ'
  set Δ' := τ '' Δ₂ with hΔ'def
  set D₂' := closure (univ \ Δ') with hD₂'def
  have hoffD : ∀ {x}, x ∉ Δ' → x ∈ discInt D₂' := fun {x} hx => ⟨subset_closure ⟨mem_univ x, hx⟩,
    fun hb => hx (Surface.discBd_subset Δ' (hD₂b ▸ hb))⟩
  have hnotΔ : ∀ {x}, x ∈ discInt Δ' → x ∉ D₂' := fun {x} hx h => by
    obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.mp h _ (hΔ'.isOpen_discInt hRman) hx
    exact hw2.2 hw1.1
  have hint₂ : ∀ {x}, x ∈ discInt D₂' → x ∉ Δ' := fun {x} hx h => by
    refine hnotΔ ⟨h, fun hb => hx.2 ?_⟩ hx.1
    rw [hD₂b]
    exact hb
  have hτint : ∀ {z}, z ∈ Δ₂ → z ∉ discBd Δ₂ → τ z ∈ discInt Δ' := fun {z} hz hb
    => ⟨mem_image_of_mem τ hz, fun h => by
    rw [hΔb] at h
    obtain ⟨w, hw, he⟩ := h
    exact hb ((hτi (hΔ₂E (Surface.discBd_subset _ hw)) (hΔ₂E hz) he) ▸ hw)⟩
  have hd : Disjoint (τ '' D₁) D₂' := by
    rw [disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ h
    exact hnotΔ (hτint (hin hz).1 (hin hz).2) h
  -- vertices and the two boundaries
  have hbdV : ∀ {y : S}, y ∈ Gi.U → j y ∈ discBd D₁ ∪ discBd Δ₂ → y ∈ Gi.V := fun {y} hy h => by
    refine hinV y ?_ (hGiU hy)
    rcases h with h | h
    · exact hn₁ ⟨h, hGiUU hy⟩
    · exact hn₂ ⟨h, hGiUU hy⟩
  have hκD₁ : ∀ {y : S}, y ∈ Gi.U → κ y ∈ τ '' D₁ → j y ∈ discBd D₁ := fun {y} hy h => by
    exact inner_disc_hit_pulls_back_to_boundary (S := S) (T := T) (j := j) (D₁ := D₁) (Δ₂ := Δ₂) E
      R τ hτi hD₁E  Gi hGiU hGiK  (y := y) hy h
  have hκD₂ : ∀ {y : S}, y ∈ Gi.U → κ y ∈ D₂' → j y ∈ discBd Δ₂ := fun {y} hy h => by
    exact outer_disc_hit_pulls_back_to_boundary (S := S) (T := T) (j := j) (D₁ := D₁) (Δ₂ := Δ₂) R
      τ  Gi hGiU  Δ' D₂' hnotΔ hτint (y := y) hy h
  have hU₁ : Γ.U ∩ τ '' D₁ ⊆ Γ.V := by
    rintro _ ⟨hx, hb⟩
    rw [hΓU] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hΓV]
    exact ⟨y, hbdV hy (.inl (hκD₁ hy hb)), rfl⟩
  have hi₁ : Disjoint Γ.U (discInt (τ '' D₁)) := by
    rw [disjoint_left]
    intro x hx hi
    rw [hΓU] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h3 := hκD₁ hy hi.1
    exact hi.2 (hD₁b ▸ ⟨j y, h3, rfl⟩)
  have hU₂ : Γ.U ∩ D₂' ⊆ Γ.V := by
    exact grid_on_outer_disc_is_at_vertices (S := S) (T := T) (j := j) (D₁ := D₁) (Δ₂ := Δ₂) R τ
      Gi Γ hΓU hΓV  D₂' hbdV hκD₂
  have hi₂ : Disjoint Γ.U (discInt D₂') := by
    exact grid_avoids_outer_disc_interior (S := S) (T := T) (j := j) (D₁ := D₁) (Δ₂ := Δ₂) R τ
      Gi hGiU Γ hΓU D₂' hint₂
  have hτint₁ : ∀ {z}, z ∈ discInt D₁ → τ z ∈ discInt (τ '' D₁) := fun {z} hz
    => ⟨mem_image_of_mem τ hz.1, fun hb => hz.2 (by
    rw [hD₁b] at hb
    obtain ⟨w, hw, he⟩ := hb
    exact hτi (hD₁E (Surface.discBd_subset _ hw)) (hD₁E hz.1) he ▸ hw)⟩
  -- a set of the sphere in the chart
  have hΔ'E : Δ' ⊆ τ '' E := image_mono hΔ₂E
  have hnormal : ∀ {X : Set T}, X ⊆ A → τ '' X ∩ Γ.U ⊆ Γ.V → G.IsNormal (j ⁻¹' X) := fun {X} hXA h
    => by
    rintro x ⟨hx, hxU⟩
    have hy := hmemU x hxU (hXA hx)
    have h3 : κ x ∈ τ '' X ∩ Γ.U := ⟨mem_image_of_mem τ hx, hΓU ▸ mem_image_of_mem κ hy⟩
    have h4 := h h3
    rw [hΓV] at h4
    obtain ⟨y, hy', he⟩ := h4
    rw [← hκi (hGiK (Gi.V_subset_U hy')) (hGiK hy) he]
    exact (hGiV hy').1
  have hcount : ∀ {X : Set T}, X ⊆ A → τ '' X ∩ Γ.U ⊆ Γ.V → (G.V ∩ j ⁻¹' X).ncard ≤
    (τ '' X ∩ Γ.U).ncard := fun {X} hXA h => by
    have hsub : κ '' (G.V ∩ j ⁻¹' X) ⊆ τ '' X ∩ Γ.U := by
      rintro _ ⟨y, ⟨hy, hyX⟩, rfl⟩
      exact ⟨mem_image_of_mem τ hyX, hΓU ▸ mem_image_of_mem κ (Gi.V_subset_U (hinV y hy (hXA hyX)))⟩
    have hi' : InjOn κ (G.V ∩ j ⁻¹' X) := hκi.mono fun y hy => hΔ₂E (hXA hy.2).1
    rw [← hi'.ncard_image]
    exact ncard_le_ncard hsub (Γ.finite_V.subset h)
  have hA₁ : ∀ {B : Set R}, Disjoint (discInt D₂') B → B ⊆ Δ' := fun {B} h x hx => by
    by_contra hn
    exact disjoint_left.mp h (hoffD hn) hx
  have hρimg : ∀ {B : Set R}, B ⊆ Δ' → τ '' (ρ '' B) = B := fun {B} h => by
    rw [image_image]
    exact (image_congr fun y hy => hτρ y (hΔ'E (h hy))).trans (image_id' B)
  have hρin : ∀ {B : Set R}, B ⊆ Δ' → ρ '' B ⊆ Δ₂ := fun {B} h => by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := h hy
    rw [hρl (hΔ₂E hz)]
    exact hz
  have hρcon : ∀ {B : Set R}, B ⊆ Δ' → ContinuousOn ρ B := fun {B} h => hρc.mono (h.trans hΔ'E)
  have hρinj : ∀ {B : Set R}, B ⊆ Δ' → InjOn ρ B := fun {B} h x hx y hy e => by
    rw [← hτρ x (hΔ'E (h hx)), ← hτρ y (hΔ'E (h hy)), e]
  have hhi : ∀ B, IsClosedDisc B → τ '' D₁ ⊆ B → Disjoint (discInt D₂') B → discBd B ∩ Γ.U ⊆ Γ.V
    → r ≤ (discBd B ∩ Γ.U).ncard := fun B hB h3 h4 h5 => by
    exact inner_disc_boundary_count (S := S) (T := T) (j := j) (G := G) (D₁ := D₁) (Δ₂ := Δ₂) (r
      := r) hi E R hRc τ hD₁E  Γ ρ hρl hτρ hRman hD₁'  D₂' hτint₁ hΔ'E hnormal hcount hA₁ hρimg
      hρin hρcon hρinj B hB h3 h4 h5
  have hhii : ∀ (L : Set R) (u v : R), IsLineWithEnds L u v → u ∈ discBd (τ '' D₁) → v ∈ discBd D₂'
    → L ∩ Γ.U ⊆ Γ.V → Disjoint L (discInt (τ '' D₁)) → Disjoint L (discInt D₂') → s ≤
      (L ∩ Γ.V).ncard := fun L u v h3 h4 h5 h6 h7 h8 => by
    exact boundary_path_vertex_count (S := S) (T := T) (j := j) (G := G) (D₁ := D₁) (Δ₂ := Δ₂) (s
      := s) hii E R τ hΔ₂E hD₁E  Γ ρ hρl hD₁b  hΔb D₂' hD₂b hτint₁ hnormal hcount hA₁ hρimg
      hρin hρcon hρinj L u v h3 h4 h5 h6 h7 h8
  -- the grid in the sphere
  obtain ⟨p₁, hp₁⟩ := hD₁'.nonempty_discInt
  obtain ⟨p₂, hp₂⟩ := hD₂'.nonempty_discInt
  have : CompactSpace R := hRc.1
  have : ConnectedSpace R := by
    obtain ⟨e⟩ := hRs
    exact e.symm.surjective.connectedSpace e.symm.continuous
  obtain ⟨P', u', v', B', E', hP, hPd, hB, hEm, hBd, hQ⟩ := exists_cylinder_grid hRc hRs Γ hD₁'
    hD₂' hd hU₁ hi₁ hU₂ hi₂ hp₁ hp₂ hhi hhii
  have hθκ : ∀ {x}, x ∈ Gi.U → θ (κ x) = x := fun {x} hx => hθl (hGiK hx)
  have hΓK : Γ.U ⊆ κ '' (j ⁻¹' E) := by
    rw [hΓU]
    exact image_mono hGiK
  have hκθ : ∀ {y}, y ∈ Γ.U → κ (θ y) = y := fun {y} hy => by
    rw [hΓU] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hθκ hx]
  have hpull : ∀ D' : Drawing R, D'.IsSubdrawing Γ → D'.U.Nonempty → ∃ D : Drawing S,
    D.IsSubdrawing G ∧ κ '' D.U = D'.U ∧ κ '' D.V = D'.V ∧ D.U ⊆ Gi.U ∧ D.U = θ '' D'.U ∧ D.V
      = θ '' D'.V ∧ D.E = image θ '' D'.E := fun D' hD' hne => by
    exact pull_subdrawing_from_grid (S := S) (T := T) (j := j) (G := G) E R τ A hGiE hGiV Γ hΓU
      hΓV hΓE  θ hθc hθκ hΓK hκθ D' hD' hne
  have hnonU : ∀ {X : Drawing R} {a b : R}, X.IsPathBetween a b → X.U.Nonempty := fun {X a b} h
    => by
    obtain ⟨W, -, hV, -⟩ := h
    exact ⟨a, X.V_subset_U (by rw [hV]; exact W.start_mem_support)⟩
  have hthe : ∀ {D' : Drawing R}, D'.IsSubdrawing Γ → InjOn θ D'.U := fun {D'} hD' x hx y hy e => by
    rw [← hκθ (hD'.U_subset hx), ← hκθ (hD'.U_subset hy), e]
  have hcthe : ∀ {D' : Drawing R}, D'.IsSubdrawing Γ → ContinuousOn θ D'.U := fun {D'} hD'
    => hθc.mono (hD'.U_subset.trans hΓK)
  have hPex : ∀ i, ∃ (D : Drawing S), D.IsSubdrawing G ∧ κ '' D.U = (P' i).U ∧ κ '' D.V = (P' i).V
    ∧ D.U ⊆ Gi.U ∧ D.IsPathBetween (θ (u' i)) (θ (v' i)) := fun i => by
    exact pull_grid_paths (S := S) (T := T) (G := G) (D₁ := D₁) (r := r) R τ Gi Γ κ θ D₂' P' u' v'
      hP hpull hnonU hthe hcthe i
  choose P hPs hPU hPV hPG hPp using hPex
  have hBex : ∀ l, ∃ (D : Drawing S), D.IsSubdrawing G ∧ κ '' D.U = (B' l).U ∧ κ '' D.V = (B' l).V
    ∧ D.U ⊆ Gi.U := fun l => by
    exact pull_grid_circuits (S := S) (G := G) (s := s) R Gi Γ κ θ p₁ p₂ B' E' hB hpull l
  choose B hBs hBU hBV hBG using hBex
  exact transport_disc_grid (S := S) (T := T) (j := j) hcj (G := G) (D₁ := D₁) (Δ₂ := Δ₂) (r :=
    r) (s := s) hii' E R hRc τ hD₁E  Gi hGiU hκi hGiK Γ hΓV  θ ρ hρl hD₁'  D₂' hD₂' hκD₁
    hκD₂ hi₁ hi₂ hA₁ hρin hρcon hρinj p₁ hp₁ p₂ hp₂ P' u' v' B' E' hP hPd hB hEm hBd hQ hθκ hκθ
    hpull hnonU hthe hcthe P hPs hPU hPV hPG hPp B hBs hBU hBV hBG


end GraphMinor.GM07
