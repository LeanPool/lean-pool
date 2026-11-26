/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CuffReach
public import LeanPool.GraphMinor.GM07.CuffStep

/-!
# The circuits around `A(C)`

Graph Minors VII, (5.9), page 234. We fix a cuff `C` and a cuff disc `E` with boundary `A(C)`. We
erase `G` strictly inside `E`, and take the layers of regions around the region of `E`, in a closed
surface `W` that holds `Σ + CHat`.
`IsLayerSetup` holds this data. A chain of regions gives a set `X` as on page 234, so the layers
stay in the disc that holds `𝒜_{2kv-1}(C)`, and we get the circuits `C_j`.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function GraphMinor.Surface GraphMinor.GM11

universe u

variable {S T : Type u} [TopologicalSpace S] [TopologicalSpace T] {W : Type} [TopologicalSpace W]

/-- The data for the layers around a cuff disc `E`: the part `G₁` of `G` off the inside of `E`,
carried to a closed surface `W` by `i ∘ j`, and the region `r₀` of the result that holds a point `p`
of the inside of `E`. -/
structure IsLayerSetup (G : Drawing S) {C : Set S} (j : S → T) (D : Set T) (ra : ℕ) (E : Set T)
  (i : T → W) (K : Set W) (G₁ : Drawing S) (Γ : Drawing W) (r₀ : Set W) (p : T) (n : ℕ) : Prop where
  disc : IsCuffDisc G j D ra E
  cap : IsCappedCuff C T j D
  sub : G₁.IsSubdrawing G
  U : G₁.U = G.U ∩ (j ⁻¹' discInt E)ᶜ
  V : G₁.V = G.V ∩ (j ⁻¹' discInt E)ᶜ
  embed : IsClosedEmbedding i
  closedW : IsClosedSurface W
  closedK : IsClosed K
  union : range i ∪ K = univ
  inter : range i ∩ K = i '' bd T
  matched : IsMatched G₁ Γ (i ∘ j) ∅
  region : r₀ ∈ Γ.R
  inside : p ∈ discInt E
  mem : i p ∈ r₀
  bdT : bd T = j '' (bd S \ C)
  proper : G.IsProper
  α₁ : ra + n < alpha G
  α₂ : ra + (ra + n) < alpha G
  α₃ : ∀ C₁ ∈ cuffs S, C₁ ≠ C → ra + n + (G.V ∩ C₁).ncard < alpha G

variable {G G₁ : Drawing S} {C : Set S} {j : S → T} {D : Set T} {ra : ℕ} {E : Set T} {i : T
  → W} {K : Set W} {Γ : Drawing W} {r₀ : Set W} {p : T} {n : ℕ}

/-- The inside of the surface in `W` is open. -/
theorem IsLayerSetup.isOpen_inside (h : IsLayerSetup (C := C) G j D ra E i K G₁ Γ r₀ p
  n) : IsOpen (i '' (bd T)ᶜ) := by
  have : i '' (bd T)ᶜ = Kᶜ := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩ hK
      have h1 : i t ∈ range i ∩ K := ⟨mem_range_self t, hK⟩
      rw [h.inter] at h1
      obtain ⟨t', ht', he⟩ := h1
      exact ht (h.embed.injective he ▸ ht')
    · intro hx
      rcases (h.union.ge (mem_univ x)) with ⟨t, rfl⟩ | h1
      · refine ⟨t, fun hb => hx ?_, rfl⟩
        have : i t ∈ i '' bd T := mem_image_of_mem i hb
        rw [← h.inter] at this
        exact this.2
      · exact absurd h1 hx
  rw [this]
  exact h.closedK.isOpen_compl

/-- The vertices of `G` that a set of few vertices of the carried graph comes from. -/
theorem IsLayerSetup.exists_lift
  (h : IsLayerSetup (C := C) G j D ra E i K G₁ Γ r₀ p n) {A : Set W} {Y : Finset W} (hYV :
    (Y : Set W) ⊆ Γ.V) (hA : A ⊆ (Y : Set W) ∪ Γ.Uᶜ) :
    ∃ X' : Set S, X' ⊆ G.V ∧ X'.ncard ≤ Y.card ∧ ∀ z ∈ G.U, j z ∉ discInt E → i (j z) ∈ A → z ∈ X'
      := by
  classical
  have hm := h.matched
  have hii : Injective (i ∘ j) := h.embed.injective.comp h.cap.isEmbedding.injective
  have hΓV : Γ.V = (i ∘ j) '' G₁.V := by simpa using hm.image_V.symm
  have hΓU : Γ.U = (i ∘ j) '' G₁.U := by simpa using hm.image_U.symm
  refine ⟨G₁.V ∩ (i ∘ j) ⁻¹' Y, fun x hx => h.sub.1 hx.1, ?_, fun z hz h1 h2 => ?_⟩
  · have h3 : ((i ∘ j) '' (G₁.V ∩ (i ∘ j) ⁻¹' Y)) ⊆ Y := by
      rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    have h4 := ncard_le_ncard h3 Y.finite_toSet
    rwa [ncard_image_of_injective _ hii, ncard_coe_finset] at h4
  · have hzU : z ∈ G₁.U := by
      rw [h.U]
      exact ⟨hz, h1⟩
    have hmem : (i ∘ j) z ∈ Γ.U := hΓU ▸ mem_image_of_mem _ hzU
    rcases hA h2 with h3 | h3
    · have h4 := hYV h3
      rw [hΓV] at h4
      obtain ⟨w, hw, he⟩ := h4
      rw [← hii he]
      exact ⟨hw, by rw [mem_preimage, he]; exact h3⟩
    · exact absurd hmem h3

section Reach

variable [T2Space S] [CompactSpace S] [T2Space T] [T2Space W]

omit [T2Space S] [CompactSpace S] [T2Space T] [T2Space W] in
/-- A set that a chain of regions gives lies in `E` or in a set `X` of page 234. -/
theorem IsLayerSetup.reach (h : IsLayerSetup (C := C) G j D ra E i K G₁ Γ r₀ p n)
  (hS : IsSurface S) [ConnectedSpace S] {a b c : ℕ} (habc : 3 ≤ 3 * a + 3 * b + c) (hm : Nonempty
    (S ≃ₜ SurfaceModel a b c)) (hcyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2)) (hC : C ∈ cuffs S)
    {A : Set W} (hA : IsPathConnected A) (h₀ : r₀ ⊆ A) {Y : Finset W} (hcard : Y.card ≤ n) (hYV :
      (Y : Set W) ⊆ Γ.V) (hAY : A ⊆ (Y : Set W) ∪ Γ.Uᶜ) {y : W} (hy : y ∈ A) :
    ∃ t, y = i t ∧ t ∉ bd T ∧ (t ∈ E ∨ ∃ z X, t = j z ∧ IsScriptASet G (ra + n) C X ∧ z ∈ X
      ∧ j ⁻¹' discBd E ⊆ X) := by
  obtain ⟨X', h1, h2, h3⟩ := h.exists_lift hYV hAY
  exact exists_reach_in_closed hS habc hm hcyl hC h.cap h.bdT h.proper h.disc h.embed
    h.isOpen_inside hA (Surface.discInt_subset _ h.inside) (h₀ h.mem) h1
      (h2.trans hcard) h3 h.α₁ h.α₂ h.α₃ hy

omit [T2Space W] in
/-- A point in the closure of a region and off the drawing lies in the region. -/
theorem mem_region_of_mem_closure (hW : IsClosedSurface W) {Γ : Drawing W} {r : Set W}
  (hr : r ∈ Γ.R) {y : W} (hy : y ∈ closure r) (hU : y ∉ Γ.U) : y ∈ r := by
  have hlc : LocallyConnectedSpace W := IsClosedSurface.locallyConnectedSpace hW
  obtain ⟨x, hx, rfl⟩ := (mem_R_iff Γ).mp hr
  have hO : IsOpen (univ \ Γ.U) := isOpen_univ.sdiff Γ.isClosed_U
  have hyO : y ∈ univ \ Γ.U := ⟨mem_univ y, hU⟩
  have h1 : IsOpen (connectedComponentIn (univ \ Γ.U) y) := hO.connectedComponentIn
  obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.mp hy _ h1 (mem_connectedComponentIn hyO)
  rw [connectedComponentIn_eq hw2, ← connectedComponentIn_eq hw1]
  exact mem_connectedComponentIn hyO

omit [T2Space S] [CompactSpace S] [T2Space T] [T2Space W] in
/-- The vertices on the closure of a region of layer `t` are reached with one more vertex. -/
theorem IsLayerSetup.vertex_reach (h : IsLayerSetup (C := C) G j D ra E i K G₁ Γ r₀ p n)
  (hS : IsSurface S) [ConnectedSpace S] {a b c : ℕ} (habc : 3 ≤ 3 * a + 3 * b + c) (hm : Nonempty
    (S ≃ₜ SurfaceModel a b c)) (hcyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2)) (hC : C ∈ cuffs S)
    {t : ℕ} (htn : t + 1 ≤ n) {r : Set W} (hr : r ∈ regLayer Γ r₀ t) {y : W} (hy : y ∈ Γ.V)
      (hyr : y ∈ closure r) :
    ∃ t, y = i t ∧ t ∉ bd T ∧ (t ∈ E ∨ ∃ z X, t = j z ∧ IsScriptASet G (ra + n) C X ∧ z ∈ X
      ∧ j ⁻¹' discBd E ⊆ X) := by
  classical
  obtain ⟨A, hA, h1, h2, Y, hc, hYV, hAY⟩ := exists_chain_set h.closedW h.region t r hr
  have hrR : r ∈ Γ.R := regLayer_subset h.region t hr
  have hrne : r.Nonempty := by
    obtain ⟨x, hx, rfl⟩ := (mem_R_iff Γ).mp hrR
    exact ⟨x, mem_connectedComponentIn ⟨mem_univ x, hx⟩⟩
  obtain ⟨w, hw⟩ := hrne
  have hA' : IsPathConnected (A ∪ insert y r) := hA.union (isPathConnected_insert_region_surface
    h.closedW hrR hy hyr) ⟨w, h2 hw, mem_insert_of_mem _ hw⟩
  refine h.reach hS habc hm hcyl hC hA' (h1.trans subset_union_left) (Y := insert y Y)
    ((Finset.card_insert_le _ _).trans (by omega)) ?_ ?_ (.inr (mem_insert _ _))
  · rw [Finset.coe_insert]
    exact insert_subset hy hYV
  · rw [Finset.coe_insert]
    rintro x (hx | rfl | hx)
    · rcases hAY hx with h3 | h3
      · exact .inl (.inr h3)
      · exact .inr h3
    · exact .inl (.inl rfl)
    · rcases hAY (h2 hx) with h3 | h3
      · exact .inl (.inr h3)
      · exact .inr h3

omit [T2Space S] [CompactSpace S] [T2Space T] [T2Space W] in
/-- **The closures of the layers lie in the disc of `𝒜`.** This is "`Y_j(A(C)) ⊆ Δ(C)`" on page 234.
They also miss the boundary of `Σ + CHat`. -/
theorem IsLayerSetup.closure_layer_subset (h : IsLayerSetup (C := C) G j D ra E i K G₁ Γ r₀ p n)
  (hS : IsSurface S) [ConnectedSpace S] {a b c : ℕ} (habc : 3 ≤ 3 * a + 3 * b + c) (hm : Nonempty
    (S ≃ₜ SurfaceModel a b c)) (hcyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2)) (hC : C ∈ cuffs S)
    {Y : Set T} (hYc : IsClosed Y) (hEY : E ⊆ Y) (hA : ∀ z ∈ scriptA G (ra + n) C, j z ∈ Y) {t : ℕ}
      (htn : t + 1 ≤ n) {r : Set W} (hr : r ∈ regLayer Γ r₀ t) : closure r ⊆ i '' Y ∧ Disjoint
        (closure r) (i '' bd T) := by
  classical
  obtain ⟨A, hA', h1, h2, Z, hc, hYV, hAY⟩ := exists_chain_set h.closedW h.region t r hr
  have hrR : r ∈ Γ.R := regLayer_subset h.region t hr
  have hreach := fun {y} hy => h.reach hS habc hm hcyl hC hA' h1 (Y := Z) (hc.trans
    (by omega)) hYV hAY (y := y) hy
  have hmemA : ∀ z X, IsScriptASet G (ra + n) C X → z ∈ X → z ∈ scriptA G (ra + n) C
    := fun z X h3 h4 => ⟨X, ⟨h3.1, h3.2.1, h3.2.2.1, h3.2.2.2.1, h3.2.2.2.2⟩, h4⟩
  have hinY : r ⊆ i '' Y := fun y hy => by
    obtain ⟨t', rfl, -, h3⟩ := hreach (h2 hy)
    refine mem_image_of_mem i ?_
    rcases h3 with h3 | ⟨z, X, rfl, h3, h4, -⟩
    · exact hEY h3
    · exact hA z (hmemA z X h3 h4)
  refine ⟨closure_minimal hinY (h.embed.isClosedMap _ hYc), disjoint_left.mpr ?_⟩
  rintro y hy ⟨b', hb', rfl⟩
  by_cases hU : i b' ∈ Γ.U
  · have hb2 := hb'
    rw [h.bdT] at hb2
    obtain ⟨g, ⟨hg, -⟩, rfl⟩ := hb2
    have hΓU : Γ.U = (i ∘ j) '' G₁.U := by simpa using h.matched.image_U.symm
    have hΓV : Γ.V = (i ∘ j) '' G₁.V := by simpa using h.matched.image_V.symm
    rw [hΓU] at hU
    obtain ⟨g', hg', he⟩ := hU
    have hgg : g' = g := h.cap.isEmbedding.injective (h.embed.injective he)
    subst hgg
    have hgV : g' ∈ G.V := h.proper ⟨hg, by
      have : g' ∈ G.U ∩ (j ⁻¹' discInt E)ᶜ := h.U ▸ hg'
      exact this.1⟩
    have hgV₁ : g' ∈ G₁.V := by
      rw [h.V]
      have : g' ∈ G.U ∩ (j ⁻¹' discInt E)ᶜ := h.U ▸ hg'
      exact ⟨hgV, this.2⟩
    obtain ⟨t', h3, h4, -⟩ := h.vertex_reach hS habc hm hcyl hC htn hr (hΓV ▸ mem_image_of_mem
      (i ∘ j) hgV₁) hy
    exact h4 (h.embed.injective h3 ▸ hb')
  · obtain ⟨t', h3, h4, -⟩ := hreach (h2 (mem_region_of_mem_closure h.closedW hrR hy hU))
    exact h4 (h.embed.injective h3 ▸ hb')

/-- **The circuits `C_j`.** This is page 234: the layers around `E` give disjoint nested circuits of
`G` in the disc `Δ(C)`, off the boundary of `Σ + CHat`. Each vertex on them is reached as on page
234, by a set `X` that holds `A(C)`. -/
theorem IsLayerSetup.exists_nest [ConnectedSpace W] (h : IsLayerSetup (C
  := C) G j D ra E i K G₁ Γ r₀ p n) (hS : IsSurface S) [ConnectedSpace S] {a b c : ℕ} (habc : 3
    ≤ 3 * a + 3 * b + c) (hm : Nonempty (S ≃ₜ SurfaceModel a b c)) (hcyl : ¬ Nonempty
      (S ≃ₜ SurfaceModel 0 0 2)) (hC : C ∈ cuffs S)
    {Δ : Set T} (hΔ : IsClosedDisc Δ) (hEΔ : E ⊆ Δ) (hA : ∀ z ∈ scriptA G
      (ra + n) C, j z ∈ Δ) {s : ℕ} (hs : s ≤ n) :
    ∃ (B : Fin s → Drawing S) (Ds : Fin s → Set T), (∀ t, (B t).IsCircuit ∧ (B t).IsSubdrawing G₁
      ∧ IsClosedDisc (Ds t) ∧ discBd (Ds t) = j '' (B t).U ∧ E ⊆ Ds t ∧ Ds t ⊆ Δ ∧ Disjoint (Ds t)
        (bd T) ∧
        ∀ y ∈ (B t).V, ∃ X, IsScriptASet G (ra + n) C X ∧ y ∈ X ∧ j ⁻¹' discBd E ⊆ X) ∧
      ∀ t t', t < t' → Disjoint (B t).U (B t').U ∧ Ds t ⊆ Ds t' := by
  classical
  have hW := h.closedW
  have hT := h.cap.isSurface
  have hmW : ∀ x : W, IsManifoldPoint x := fun x => (hW.2.2 x).isManifoldPoint
  have hci := h.embed.continuous
  have hii := h.embed.injective
  have hji := h.cap.isEmbedding.injective
  have hΔW : IsClosedDisc (i '' Δ) := isClosedDisc_image_of_injective hci hii hΔ
  obtain ⟨Ω, hΩ, hin, -⟩ := Surface.exists_disc_around hmW hΔW (fun x _ => hW.2.2 x) isOpen_univ
    (subset_univ _)
  have hlay : ∀ t, t < s → ∀ r ∈ regLayer Γ r₀ t, closure r ⊆ i '' Δ ∧ Disjoint (closure r)
    (i '' bd T) := fun t ht r hr => h.closure_layer_subset hS habc hm hcyl hC hΔ.isClosed hEΔ hA
      (by omega) hr
  have hsub : ∀ t < s, ⋃ r ∈ regLayer Γ r₀ t, closure r ⊆ discInt Ω := fun t ht
    => iUnion₂_subset fun r hr => (hlay t ht r hr).1.trans hin
  obtain ⟨C', D', h1, h2⟩ := exists_region_nest_in_disc hW h.region h.mem hΩ hsub
  have hUin : ∀ t : Fin s, ∀ {x}, x ∈ (C' t).U → ∃ r ∈ regLayer Γ r₀ t, x ∈ closure r
    := fun t {x} hx => by
    obtain ⟨-, h3, -⟩ := h1 t
    have := boundary_subset_layer hW (h3.U_subset hx)
    simpa using this
  have hbdΩ : ∀ t, discBd (D' t) ⊆ i '' Δ := fun t x hx => by
    obtain ⟨-, -, -, h4, -⟩ := h1 t
    obtain ⟨r, hr, h5⟩ := hUin t (h4 ▸ hx)
    exact (hlay t t.2 r hr).1 h5
  have hD'Δ : ∀ t, D' t ⊆ i '' Δ := fun t => disc_subset_of_bd_in_disc hW hΩ hΔW (h1 t).2.2.1 hin
    (h1 t).2.2.2.2.2 (hbdΩ t)
  have hne : Nonempty T := ⟨p⟩
  have hTc : CompactSpace T := hT.1
  have hpre : ∀ t, IsClosedDisc (i ⁻¹' D' t) ∧ discBd (i ⁻¹' D' t) = i ⁻¹' discBd (D' t) := fun t
    => by
    have hsr : D' t ⊆ range i := (hD'Δ t).trans (image_subset_range _ _)
    have h3 : IsClosedDisc (i ⁻¹' D' t) := isClosedDisc_preimage_of_subset_range hci hii
      (h1 t).2.2.1 hsr
    have h4 := (isClosedDisc_image_of_injOn h3 hci hii.injOn).2
    rw [image_preimage_eq_of_subset hsr] at h4
    rw [h4, preimage_image_eq _ hii]
    exact ⟨h3, rfl⟩
  have hsubs : ∀ t, (C' t).IsSubdrawing Γ := fun t => by
    have h3 : (boundaryDrawing Γ (regLayer Γ r₀ t)).IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _
      _
    exact ⟨(h1 t).2.1.1.trans h3.1, (h1 t).2.1.2.trans h3.2⟩
  have hpull := fun t => exists_pull h.matched (hsubs t)
  choose B hB₁ hB₂ hB₃ hB₄ using hpull
  have hBU : ∀ t, j '' (B t).U = i ⁻¹' (C' t).U := fun t => by
    rw [← hB₂ t, image_comp, preimage_image_eq _ hii]
  have hBs : ∀ t, (B t).IsSubdrawing G₁ := hB₁
  refine ⟨B, fun t => i ⁻¹' D' t, fun t => ⟨?_, hB₁ t, (hpre t).1, ?_, ?_, ?_, ?_, ?_⟩,
    fun t t' htt => ⟨?_, ?_⟩⟩
  · have h3 := (hpre t).1.isOArc_discBd
    rw [(hpre t).2, (h1 t).2.2.2.1, ← hBU t] at h3
    have h4 := pull_oArc h.cap.isEmbedding h3 (image_subset_range _ _)
    rw [preimage_image_eq _ hji] at h4
    obtain ⟨X, h5, h6, h7⟩ := exists_circuit_of_oArc h4 (Subset.refl _)
    have hV : X.V = (B t).V := subset_antisymm h6.1 fun x hx => mem_V_of_subdrawing h6 (h7.symm ▸
      (B t).V_subset_U hx) hx
    have hE : X.E = (B t).E := by
      unfold Drawing.E
      rw [h7, hV]
    have : X = B t := Drawing.ext_of_V_E hV hE
    exact this ▸ h5
  · rw [(hpre t).2, (h1 t).2.2.2.1, hBU t]
  · have hEd := h.disc.1
    have h3 : Disjoint (discInt E) (frontier (i ⁻¹' D' t)) := by
      refine disjoint_left.mpr fun x hx hf => ?_
      have h4 := frontier_disc_subset hT.2.2 (hpre t).1 hf
      rw [(hpre t).2, (h1 t).2.2.2.1, ← hBU t] at h4
      obtain ⟨g, hg, rfl⟩ := h4
      have hg₁ : g ∈ G₁.U := (hB₁ t).U_subset hg
      rw [h.U] at hg₁
      exact hg₁.2 hx
    rcases inside_or_off hEd.isPreconnected_discInt (hpre t).1.isClosed h3 with h4 | h4
    · exact hEd.subset_closure_discInt.trans (closure_minimal (h4.trans interior_subset)
        (hpre t).1.isClosed)
    · exact absurd (h1 t).2.2.2.2.1 (h4 h.inside)
  · intro x hx
    obtain ⟨y, hy, he⟩ := hD'Δ t hx
    exact hii he ▸ hy
  · rw [disjoint_left]
    intro x hx hb
    by_cases h3 : x ∈ discBd (i ⁻¹' D' t)
    · rw [(hpre t).2] at h3
      obtain ⟨r, hr, h5⟩ := hUin t ((h1 t).2.2.2.1 ▸ h3)
      exact disjoint_left.mp (hlay t t.2 r hr).2 h5 (mem_image_of_mem i hb)
    · exact hb (Surface.isInteriorPoint_of_mem_discInt hT.2.2 (hpre t).1 ⟨hx, h3⟩)
  · intro y hy
    have h3 : i (j y) ∈ (C' t).V := by
      rw [← hB₃ t]
      exact ⟨y, hy, rfl⟩
    obtain ⟨⟨r, hr, h4⟩, -⟩ := (mem_boundaryDrawing_V hW).mp ((h1 t).2.1.1 h3)
    obtain ⟨t', ht', -, h5⟩ := h.vertex_reach hS habc hm hcyl hC
      (show t.1 + 1 ≤ n by omega) hr ((hsubs t).1 h3) h4.2.2
    have hjt : j y = t' := hii ht'
    subst hjt
    rcases h5 with h5 | ⟨z, X, h5, h6, h7, h8⟩
    · have hyU : y ∈ G₁.U := (hB₁ t).U_subset ((B t).V_subset_U hy)
      rw [h.U] at hyU
      have hsc := h.disc.isScriptASet hS hC h.cap (not_isSphere_cap hS habc hm h.cap)
      refine ⟨j ⁻¹' discBd E, ⟨hsc.1, hsc.2.1, hsc.2.2.1, hsc.2.2.2.1,
        hsc.2.2.2.2.trans (by omega)⟩, ?_, Subset.refl _⟩
      by_contra h6
      exact hyU.2 ⟨h5, h6⟩
    · have hzy : y = z := hji h5
      subst hzy
      exact ⟨X, h6, h7, h8⟩
  · rw [disjoint_left]
    intro x h3 h4
    have h5 : i (j x) ∈ (C' t).U := by
      rw [← hB₂ t]
      exact ⟨x, h3, rfl⟩
    have h6 : i (j x) ∈ (C' t').U := by
      rw [← hB₂ t']
      exact ⟨x, h4, rfl⟩
    exact boundary_off_layer hW h.region (Fin.lt_def.mp htt) ((h1 t').2.1.U_subset h6)
      (boundary_subset_layer hW ((h1 t).2.1.U_subset h5))
  · exact preimage_mono (h2 t t' htt).2

end Reach

/-- **The layer data exists.** Each cuff disc `E` gives layer data, in the closed surface got by
capping the cuffs of the surface model of `Σ + CHat`. -/
theorem exists_layer_setup (hS : IsSurface S) [ConnectedSpace S] {a b c : ℕ} (hm : Nonempty
  (S ≃ₜ SurfaceModel a b c)) (hC : C ∈ cuffs S) (hc : IsCappedCuff C T j D) (hbT : bd T = j ''
    (bd S \ C)) (hG : G.IsProper) (hd : IsCuffDisc G j D ra E) (h₁ : ra + n < alpha G) (h₂ : ra +
      (ra + n) < alpha G)
    (h₃ : ∀ C₁ ∈ cuffs S, C₁ ≠ C → ra + n + (G.V ∩ C₁).ncard < alpha G) :
    ∃ (W : Type) (_ : TopologicalSpace W) (_ : ConnectedSpace W) (i : T → W) (K : Set W)
      (G₁ : Drawing S) (Γ : Drawing W) (r₀ : Set W) (p : T), IsLayerSetup (C
        := C) G j D ra E i K G₁ Γ r₀ p n := by
  classical
  have hT := hc.isSurface
  have : T2Space T := hT.2.1
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  have hman := hT.2.2
  obtain ⟨hΔ, hDE, hn, -⟩ := id hd
  obtain ⟨-, ⟨e⟩⟩ := cappedCuff_homeo_model hS hm hC hc
  have hM : IsSurface (SurfaceModel a b (c - 1)) := isSurface_of_homeo e hT
  have hMc : ConnectedSpace (SurfaceModel a b (c - 1)) := connectedSpace_of_model ⟨Homeomorph.refl
    _⟩
  obtain ⟨W, tW, i', K, hW, hi', hK, hun, hin, hconn⟩ := exists_capAll _ hM
  have hWc := hconn hMc
  have : T2Space W := hW.2.1
  let i : T → W := i' ∘ e
  have hi : IsClosedEmbedding i := hi'.comp e.isClosedEmbedding
  have hri : range i = range i' := by
    rw [range_comp, e.surjective.range_eq, image_univ]
  have hibd : i '' bd T = i' '' bd (SurfaceModel a b (c - 1)) := by
    rw [image_comp, image_bd_homeomorph e]
  have hcj : IsClosedEmbedding j := hc.isEmbedding.continuous.isClosedEmbedding
    hc.isEmbedding.injective
  let Z : Set S := j ⁻¹' discInt E
  have hZo : IsOpen Z := (hΔ.isOpen_discInt hman).preimage hcj.continuous
  have hedge : ∀ e ∈ G.E, (∃ y ∈ e, y ∉ Z) → Disjoint e Z := by
    rintro e he ⟨y, hye, hyZ⟩
    have hpc : IsPreconnected (j '' e) := he.2.2.1.isConnected.isPreconnected.image _
      hcj.continuous.continuousOn
    have hdb : Disjoint (j '' e) (discBd E) := by
      rw [disjoint_left]
      rintro _ ⟨z, hz, rfl⟩ hzb
      have hzU := he.2.1 hz
      exact hzU.2 (hn ⟨hzb, hzU.1⟩)
    rcases inside_or_off hpc hΔ.isClosed (hdb.mono_right (frontier_disc_subset hman hΔ)) with h1 |
      h1
    · exact absurd (⟨interior_subset (h1 (mem_image_of_mem j hye)),
        disjoint_left.mp hdb (mem_image_of_mem j hye)⟩ : j y ∈ discInt E) hyZ
    · rw [disjoint_left]
      exact fun z hz hzZ => h1 (mem_image_of_mem j hz) hzZ.1
  obtain ⟨G₁, hG₁, hG₁U, hG₁V⟩ := exists_outside_drawing hZo hedge
  have hcij : IsClosedEmbedding (i ∘ j) := hi.comp hcj
  obtain ⟨Γ, hΓ⟩ := exists_image_matched hcij G₁
  obtain ⟨p, hp⟩ := hΔ.nonempty_discInt
  have hΓU : Γ.U = (i ∘ j) '' G₁.U := by simpa using hΓ.image_U.symm
  have hpoff : i p ∉ Γ.U := fun h1 => by
    rw [hΓU] at h1
    obtain ⟨g, hg, he⟩ := h1
    rw [hG₁U] at hg
    have h2 : j g = p := hi.injective he
    exact hg.2 (show j g ∈ discInt E from h2 ▸ hp)
  have hreg : connectedComponentIn (univ \ Γ.U) (i p) ∈ Γ.R := (mem_R_iff Γ).mpr ⟨i p, hpoff, rfl⟩
  refine ⟨W, tW, hWc, i, K, G₁, Γ, _, p, ⟨hd, hc, hG₁, hG₁U, hG₁V, hi, hW, hK, ?_, ?_, hΓ, hreg,
    hp, mem_connectedComponentIn ⟨mem_univ _, hpoff⟩, hbT, hG, h₁, h₂, h₃⟩⟩
  · rw [hri, hun]
  · rw [hri, hin, hibd]

/-- **The disc `Δ(C)`.** This is the start of the proof of (5.9) on page 234: `𝒜_R(C)` is planar in
`Σ + CHat` by (5.7), and a cuff disc whose boundary lies in `𝒜_R(C)` lies in the disc. -/
theorem exists_scriptA_disc (hS : IsSurface S) [ConnectedSpace S] {a b c : ℕ} (hm : Nonempty
  (S ≃ₜ SurfaceModel a b c)) (habc : 3 ≤ 3 * a + 3 * b + c) (hG : G.IsProper) (hC : C ∈ cuffs S)
    (hc : IsCappedCuff C T j D) {R : ℕ} (hR : 9 * (R + 1) ≤ 2 * alpha G) :
    ∃ Δ, IsClosedDisc Δ ∧ ∀ z ∈ scriptA G R C, j z ∈ Δ := by
  obtain ⟨Δ, h1, h2⟩ := (theorem_5_7_proof hS hm habc hG hC hR).2.2 T j D hc
  exact ⟨Δ, h1, fun z hz => h2 (mem_image_of_mem j hz)⟩

end GraphMinor.GM07
