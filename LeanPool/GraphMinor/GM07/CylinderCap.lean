/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CylinderGrid
public import LeanPool.GraphMinor.GM07.Matched
public import LeanPool.GraphMinor.GM14.RigidMap
public import LeanPool.GraphMinor.GM11.DrawingOps
public import LeanPool.GraphMinor.GM12.Section3ModelComplexity

/-!
# From the capped cylinder back to the cylinder

Capping the two cuffs of a cylinder gives a sphere. `exists_image_matched` puts a drawing in the
sphere, and `exists_pull` and `pull_path` bring subdrawings and paths back.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function Graph GraphMinor.Surface GraphMinor.GM11

universe u

section Pull

variable {S : Type u} [TopologicalSpace S] [CompactSpace S] [T2Space S] {T : Type*}
  [TopologicalSpace T] [T2Space T] {G : Drawing S} {Γ : Drawing T} {j : S → T}

omit [CompactSpace S] [T2Space S] [T2Space T] in
/-- The homeomorphism from the preimage of a subset of the range of an embedding. -/
theorem exists_pull_homeo (hj : IsEmbedding j) {L : Set T} (hL : L ⊆ range j) : ∃ e : j ⁻¹' L ≃ₜ L,
  ∀ x, (e x).1 = j x.1 := by
  have heq : j '' (j ⁻¹' L) = L := image_preimage_eq_of_subset hL
  exact ⟨(hj.homeomorphImage (j ⁻¹' L)).trans (Homeomorph.setCongr heq), fun x => rfl⟩

omit [CompactSpace S] [T2Space S] [T2Space T] in
theorem pull_line (hj : IsEmbedding j) {L : Set T} {u v : S} (hl : IsLineWithEnds L (j u) (j v))
  (hL : L ⊆ range j) : IsLineWithEnds (j ⁻¹' L) u v := by
  obtain ⟨e, he⟩ := exists_pull_homeo hj hL
  obtain ⟨f, h0, h1⟩ := hl
  refine ⟨f.trans e.symm, hj.injective ?_, hj.injective ?_⟩
  · rw [← he]
    simpa using h0
  · rw [← he]
    simpa using h1

omit [CompactSpace S] [T2Space S] [T2Space T] in
theorem pull_oArc (hj : IsEmbedding j) {L : Set T} (hl : IsOArc L) (hL : L ⊆ range j) : IsOArc
  (j ⁻¹' L) := by
  obtain ⟨e, -⟩ := exists_pull_homeo hj hL
  obtain ⟨f⟩ := hl
  exact ⟨f.trans e.symm⟩

omit [CompactSpace S] in
omit [T2Space S] [T2Space T] in
theorem image_line (hj : IsEmbedding j) {L : Set S} {u v : S} (hl : IsLineWithEnds L u v) :
  IsLineWithEnds (j '' L) (j u) (j v) := by
  obtain ⟨f, h0, h1⟩ := hl
  refine ⟨f.trans (hj.homeomorphImage L), ?_, ?_⟩
  · change j (f 0).1 = j u
    rw [h0]
  · change j (f 1).1 = j v
    rw [h1]

omit [CompactSpace S] in
omit [T2Space S] [T2Space T] in
/-- The image of a drawing under a closed embedding. -/
theorem exists_image_matched [Nonempty S] (hj : IsClosedEmbedding j) (G : Drawing S) : ∃ Γ :
  Drawing T, IsMatched G Γ j ∅ := by
  classical
  have hset : j '' G.U \ j '' G.V = j '' (G.U \ G.V) := (image_sdiff hj.injective _ _).symm
  have harc : ∀ {F : Set S}, arcComponentsIn (j '' F) = image j '' arcComponentsIn F := fun {F}
    => by
    refine arcComponentsIn_image (g := invFun j) hj.continuous.continuousOn ?_ fun x _
      => leftInverse_invFun hj.injective x
    rw [hj.isInducing.continuousOn_iff]
    refine continuousOn_id.congr ?_
    rintro _ ⟨x, -, rfl⟩
    simp [leftInverse_invFun hj.injective x]
  have hcl : ∀ e : Set S, closure (j '' e) = j '' closure e := fun e =>
    (image_closure_subset_closure_image hj.continuous).antisymm' (closure_minimal
      (image_mono subset_closure) (hj.isClosedMap _ isClosed_closure))
  have hcap : ∀ e : Set S, closure (j '' e) ∩ j '' G.V = j '' (closure e ∩ G.V) := fun e => by
    rw [hcl, image_inter hj.injective]
  let Γ : Drawing T :=
    { U := j '' G.U
      V := j '' G.V
      V_subset_U := image_mono G.V_subset_U
      isClosed_U := hj.isClosedMap _ G.isClosed_U
      finite_V := G.finite_V.image _
      finite_edges := by
        rw [hset, harc]
        exact G.finite_edges.image _
      edge_cond := by
        rw [hset, harc]
        rintro _ ⟨e, he, rfl⟩
        rcases G.edge_cond e he with ⟨u, v, h1, h2, h3⟩ | ⟨u, h2, h3⟩
        · refine .inl ⟨j u, j v, hj.injective.ne h1, by rw [hcap, h2, image_pair], ?_⟩
          rw [hcl]
          exact image_line hj.isEmbedding h3
        · refine .inr ⟨j u, by rw [hcap, h2, image_singleton], ?_⟩
          rw [hcl]
          exact h3.elim fun φ => ⟨φ.trans (hj.isEmbedding.homeomorphImage _)⟩ }
  have hE : Γ.E = image j '' G.E := by
    change arcComponentsIn (j '' G.U \ j '' G.V) = _
    rw [hset, harc]
    rfl
  exact ⟨Γ, ⟨hj.continuous, hj.injective.injOn, empty_subset _, fun _ _ => disjoint_empty _,
    by simp [Γ], by simp [Γ], hE⟩⟩

/-- A subdrawing of the image comes from a subdrawing. -/
theorem exists_pull (h : IsMatched G Γ j ∅) {D' : Drawing T} (hD : D'.IsSubdrawing Γ) : ∃ D :
  Drawing S, D.IsSubdrawing G ∧ j '' D.U = D'.U ∧ j '' D.V = D'.V ∧ image j '' D.E = D'.E := by
  classical
  have hVΓ : Γ.V = j '' G.V := by simpa using h.image_V.symm
  let D := G.span (j ⁻¹' D'.V) {e | j '' e ∈ D'.E}
  have hDE : D.E = {e ∈ G.E | j '' e ∈ D'.E} := by
    rw [G.span_E]
    exact inter_comm _ _
  have hDV : D.V = j ⁻¹' D'.V ∩ G.V := by
    refine subset_antisymm ?_ (fun x hx => .inl hx)
    rintro x (hx | hx)
    · exact hx
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      have h3 : j x ∈ closure (j '' e) ∩ Γ.V :=
        ⟨by rw [h.closure_image]; exact ⟨x, hxe.1, rfl⟩, by rw [hVΓ]; exact ⟨x, hxe.2, rfl⟩⟩
      rw [← hD.closure_inter_V he.1] at h3
      exact ⟨h3.2, hxe.2⟩
  have hIV : j '' D.V = D'.V := by
    rw [hDV]
    refine subset_antisymm ?_ fun y hy => ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.1
    · have h3 := hD.1 hy
      rw [hVΓ] at h3
      obtain ⟨x, hx, rfl⟩ := h3
      exact ⟨x, ⟨hy, hx⟩, rfl⟩
  have hIE : image j '' D.E = D'.E := by
    rw [hDE]
    refine subset_antisymm ?_ fun f hf => ?_
    · rintro _ ⟨e, he, rfl⟩
      exact he.2
    · have h3 := hD.2 hf
      rw [h.image_E] at h3
      obtain ⟨e, he, rfl⟩ := h3
      exact ⟨e, ⟨he, hf⟩, rfl⟩
  refine ⟨D, Drawing.span_isSubdrawing G _ _, ?_, hIV, hIE⟩
  rw [D.U_eq, D'.U_eq, image_union, hIV, ← hIE]
  congr 1
  ext y
  simp only [mem_image, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨x, ⟨e, he, hx⟩, rfl⟩
    exact ⟨_, ⟨e, he, rfl⟩, by rw [h.closure_image]; exact ⟨x, hx, rfl⟩⟩
  · rintro ⟨_, ⟨e, he, rfl⟩, hy⟩
    rw [h.closure_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, ⟨e, he, hx⟩, rfl⟩

omit [T2Space S] in
/-- A path of the image comes from a path. -/
theorem pull_path (h : IsMatched G Γ j ∅) (hj : Injective j) {D : Drawing S} {D' : Drawing T}
  (hU : j '' D.V = D'.V) (hE : image j '' D.E = D'.E) {a b : S} (hp : D'.IsPathBetween (j a)
    (j b)) :
    D.IsPathBetween a b := by
  have : Nonempty S := ⟨a⟩
  have hg : ∀ x, invFun j (j x) = x := leftInverse_invFun hj
  have hmap := GM14.Whitney.isPathBetween_map (P := D') (Q := D) (invFun j)
    (preimage j) ?_ ?_ ?_ ?_ hp
  · rwa [hg, hg] at hmap
  · rintro f y z ⟨hf, hy, hz, hc⟩
    rw [← hE] at hf
    rw [← hU] at hy hz
    obtain ⟨e, he, rfl⟩ := hf
    obtain ⟨y, hy, rfl⟩ := hy
    obtain ⟨z, hz, rfl⟩ := hz
    rw [preimage_image_eq _ hj, hg, hg]
    refine ⟨he, hy, hz, ?_⟩
    apply image_injective.mpr hj
    rw [image_inter hj, ← h.closure_image, hU, hc, image_pair]
  · rw [← hU, image_image]
    simp [hg]
  · rw [← hE, image_image]
    simp [preimage_image_eq _ hj]
  · rw [← hU]
    rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩ he
    rw [hg, hg] at he
    rw [he]

end Pull

section Cap

variable {S : Type u} [TopologicalSpace S]

/-- Capping both cuffs of a cylinder gives a sphere. -/
theorem exists_sphere_cap (hS : IsSurface S) (he : Nonempty (S ≃ₜ SurfaceModel 0 0 2)) {C₁ C₂ : Set
  S} (hcuffs : cuffs S = {C₁, C₂}) (hne : C₁ ≠ C₂) :
    ∃ (T : Type) (_ : TopologicalSpace T) (j : S → T) (D₁ D₂ : Set T), IsClosedSurface T
      ∧ IsSphere T ∧ ConnectedSpace T ∧ IsClosedEmbedding j ∧ IsClosedDisc D₁ ∧ IsClosedDisc D₂
        ∧ Disjoint D₁ D₂ ∧
      discBd D₁ = j '' C₁ ∧ discBd D₂ = j '' C₂ ∧ range j ∪ D₁ ∪ D₂ = univ ∧ range j ∩ D₁ = j '' C₁
        ∧ range j ∩ D₂ = j '' C₂ := by
  have hT2 : T2Space S := hS.2.1
  have hcompact : CompactSpace S := hS.1
  obtain ⟨e₀⟩ := id he
  have : ConnectedSpace S := by
    have := (isSurface_model 0 0 2).2
    exact e₀.symm.surjective.connectedSpace e₀.symm.continuous
  have hC₁ : C₁ ∈ cuffs S := by rw [hcuffs]; simp
  have hC₂ : C₂ ∈ cuffs S := by rw [hcuffs]; simp
  have hdis : Disjoint C₁ C₂ := cuffs_disjoint hC₁ hC₂ hne
  have hbdS : bd S = C₁ ∪ C₂ := by rw [← sUnion_cuffs, hcuffs, sUnion_pair]
  obtain ⟨Y, tY, j₁, D₁', hcap₁, hbdY⟩ := exists_cappedCuff hS hC₁
  obtain ⟨-, ⟨e₁⟩⟩ := cappedCuff_homeo_model hS he hC₁ hcap₁
  have hY : IsSurface Y := hcap₁.isSurface
  have : T2Space Y := hY.2.1
  have : ConnectedSpace Y := by
    have := (isSurface_model 0 0 1).2
    exact e₁.symm.surjective.connectedSpace e₁.symm.continuous
  have hbdY' : bd Y = j₁ '' C₂ := by
    rw [hbdY, hbdS, union_sdiff_left, sdiff_eq_left.mpr hdis.symm]
  have hC₂Y : j₁ '' C₂ ∈ cuffs Y := by
    obtain ⟨x, hx, hxe⟩ := id hC₂
    have hp : IsPreconnected C₂ := hxe ▸ isPreconnected_connectedComponentIn
    have hxC : x ∈ C₂ := by
      rw [← hxe]
      exact mem_connectedComponentIn hx
    have hbp : IsPreconnected (bd Y) := hbdY' ▸ hp.image _ hcap₁.isEmbedding.continuous.continuousOn
    have hy : j₁ x ∈ bd Y := hbdY' ▸ mem_image_of_mem _ hxC
    refine ⟨j₁ x, hy, ?_⟩
    rw [hbp.connectedComponentIn hy, hbdY']
  obtain ⟨Z, tZ, j₂, D₂', hcap₂, hbdZ⟩ := exists_cappedCuff hY hC₂Y
  obtain ⟨-, ⟨e₂⟩⟩ := cappedCuff_homeo_model hY ⟨e₁⟩ hC₂Y hcap₂
  have hZ : IsSurface Z := hcap₂.isSurface
  have : T2Space Z := hZ.2.1
  have : CompactSpace Z := hZ.1
  obtain ⟨s₀⟩ := GM12.isSphere_model_zero
  let s : Z ≃ₜ OnePoint EuclideanPlane := e₂.trans s₀
  have hbdZ' : bd Z = ∅ := by rw [hbdZ, hbdY', sdiff_self, image_empty]
  have hTcs : CompactSpace (OnePoint EuclideanPlane) := s.compactSpace
  have hTt2 : T2Space (OnePoint EuclideanPlane) := s.t2Space
  have hTs : IsClosedSurface (OnePoint EuclideanPlane) := by
    refine ⟨hTcs, hTt2, fun x => ?_⟩
    have h3 : IsInteriorPoint (s.symm x) := by
      by_contra hn
      have h4 : s.symm x ∈ bd Z := hn
      rw [hbdZ'] at h4
      exact h4
    have := (isInteriorPoint_homeomorph_iff s (s.symm x)).mpr h3
    rwa [s.apply_symm_apply] at this
  have hj₁ := hcap₁.isEmbedding
  have hj₂ := hcap₂.isEmbedding
  let f₂ : Y → OnePoint EuclideanPlane := s ∘ j₂
  have hf₂c : Continuous f₂ := s.continuous.comp hj₂.continuous
  have hf₂i : Injective f₂ := s.injective.comp hj₂.injective
  let j : S → OnePoint EuclideanPlane := f₂ ∘ j₁
  have hjc : Continuous j := hf₂c.comp hj₁.continuous
  have hji : Injective j := hf₂i.comp hj₁.injective
  obtain ⟨hd1, hb1⟩ := isClosedDisc_image hcap₁.isClosedDisc hf₂c.continuousOn hf₂i.injOn
  obtain ⟨hd2, hb2⟩ := isClosedDisc_image hcap₂.isClosedDisc s.continuous.continuousOn
    s.injective.injOn
  have hm₁ : ∀ {y}, y ∈ D₁' → ∀ c, j₁ c = y → c ∈ C₁ := fun {y} hy c hc => by
    have h3 : y ∈ range j₁ ∩ D₁' := ⟨⟨c, hc⟩, hy⟩
    rw [hcap₁.inter_eq] at h3
    obtain ⟨c', hc', he⟩ := h3
    exact hj₁.injective (he.trans hc.symm) ▸ hc'
  have hm₂ : ∀ {y}, j₂ y ∈ D₂' → ∃ c ∈ C₂, j₁ c = y := fun {y} hy => by
    have h3 : j₂ y ∈ range j₂ ∩ D₂' := ⟨⟨y, rfl⟩, hy⟩
    rw [hcap₂.inter_eq] at h3
    obtain ⟨y', ⟨c, hc, rfl⟩, he⟩ := h3
    exact ⟨c, hc, hj₂.injective he⟩
  refine ⟨OnePoint EuclideanPlane, inferInstance, j, f₂ '' D₁', s '' D₂', hTs, ⟨Homeomorph.refl _⟩,
    (haveI := (isSurface_model 0 0 0).2; s₀.surjective.connectedSpace s₀.continuous),
    hjc.isClosedEmbedding hji, hd1, hd2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine disjoint_left.mpr ?_
    rintro _ ⟨y, hy, rfl⟩ ⟨z, hz, he⟩
    have hzy : z = j₂ y := s.injective he
    subst hzy
    obtain ⟨c, hc, rfl⟩ := hm₂ hz
    exact disjoint_left.mp hdis (hm₁ hy c rfl) hc
  · rw [hb1, hcap₁.discBd_eq, image_image]
    rfl
  · rw [hb2, hcap₂.discBd_eq, image_image, image_image]
    rfl
  · refine eq_univ_of_forall fun x => ?_
    have h3 : s.symm x ∈ range j₂ ∪ D₂' := hcap₂.union_eq ▸ mem_univ _
    rcases h3 with ⟨y, hy⟩ | h3
    · have h4 : y ∈ range j₁ ∪ D₁' := hcap₁.union_eq ▸ mem_univ _
      have hx : x = f₂ y := by
        change x = s (j₂ y)
        rw [hy, s.apply_symm_apply]
      rcases h4 with ⟨c, rfl⟩ | h4
      · exact .inl (.inl ⟨c, hx.symm⟩)
      · exact .inl (.inr ⟨y, h4, hx.symm⟩)
    · exact .inr ⟨_, h3, s.apply_symm_apply x⟩
  · ext x
    constructor
    · rintro ⟨⟨c, rfl⟩, y, hy, he⟩
      have h3 : j₁ c = y := (hf₂i he).symm
      exact ⟨c, hm₁ hy c h3, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      refine ⟨mem_range_self c, j₁ c, ?_, rfl⟩
      have h3 : j₁ c ∈ range j₁ ∩ D₁' := by
        rw [hcap₁.inter_eq]
        exact ⟨c, hc, rfl⟩
      exact h3.2
  · ext x
    constructor
    · rintro ⟨⟨c, rfl⟩, z, hz, he⟩
      have hzy : z = j₂ (j₁ c) := s.injective he
      subst hzy
      obtain ⟨c', hc', he'⟩ := hm₂ hz
      exact ⟨c, hj₁.injective he' ▸ hc', rfl⟩
    · rintro ⟨c, hc, rfl⟩
      refine ⟨mem_range_self c, j₂ (j₁ c), ?_, rfl⟩
      have h3 : j₂ (j₁ c) ∈ range j₂ ∩ D₂' := by
        rw [hcap₂.inter_eq]
        exact ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact h3.2

/-- An `O`-arc of the cylinder that separates two points off the cylinder is not null-homotopic. -/
theorem not_null_of_separating (hS : IsSurface S) {T : Type} [TopologicalSpace T]
  [T2Space T] (hsph : IsSphere T) {j : S → T} (hj : IsClosedEmbedding j) {F : Set S}
    (hF : IsOArc F) {B : Set T}
    (hB : IsClosedDisc B) (hb : discBd B = j '' F) {p a : T} (hpB : p ∈ B) (haB : a ∉ B)
      (hp : p ∉ range j) (ha : a ∉ range j) : ¬ IsNullHomotopicOArc F := by
  intro hnull
  obtain ⟨Δ, hΔ, hbΔ⟩ := nullHomotopicOArc_bounds_disc hS hF hnull
  obtain ⟨hd, hbd⟩ := isClosedDisc_image hΔ hj.continuous.continuousOn hj.injective.injOn
  have hO : IsOArc (j '' F) := hb ▸ hB.isOArc_discBd
  obtain ⟨Δ₁, Δ₂, -, h1, h2, b1, b2, hcup, -, -, huniq⟩ := sphere_disc T hsph _ hO
  have hset : discBd (j '' Δ) = j '' F := by rw [hbd, hbΔ]
  have hBeq := huniq B hB hb
  have hΔeq := huniq _ hd hset
  have hra : ∀ {x}, x ∈ j '' Δ → x ∈ range j := fun {x} hx => image_subset_range _ _ hx
  rcases hBeq with rfl | rfl <;> rcases hΔeq with h | h
  · exact hp (hra (h ▸ hpB))
  · have : a ∈ B ∪ Δ₂ := hcup ▸ mem_univ a
    exact ha (hra (h ▸ this.resolve_left haB))
  · have : a ∈ Δ₁ ∪ B := hcup ▸ mem_univ a
    exact ha (hra (h ▸ this.resolve_right haB))
  · exact hp (hra (h ▸ hpB))

end Cap

variable {S : Type u} [TopologicalSpace S]

/-- Graph Minors VII, (5.8) (page 233; essentially Theorem (4.1) of Graph Minors III):
"(5.8) *Let $\Sigma$ be a cylinder and let $C_1, C_2$ be the two cuffs. Let $G$ be a proper graph in
$\Sigma$. Let $r, s \ge 0$ be integers. Suppose that*
*(i) every $G$-normal $O$-arc $F$ with $|F \cap V(G)| < r$ is null-homotopic, and*
*(ii) every $G$-normal $I$-arc $F$ with $|F \cap V(G)| < s$ has both its ends in the same cuff.*
*Then there are mutually vertex-disjoint paths $P_1, \dots, P_r$ of $G$, each between $C_1$ and
$C_2$, and mutually vertex-disjoint circuits $B_1, \dots, B_s$ of $G$, none null-homotopic, such
that for $1 \le i \le r$ and $1 \le j \le s$ the intersection of $P_i$ and $B_j$ is a path.*" -/
theorem theorem_5_8_proof (hS : IsSurface S) (he : Nonempty
  (S ≃ₜ SurfaceModel 0 0 2)) {C₁ C₂ : Set S} (hcuffs : cuffs S = {C₁, C₂}) (hne : C₁ ≠ C₂)
    (G : Drawing S) (r s : ℕ) (hG : G.IsProper)
    (hi : ∀ F : Set S, G.IsNormal F → IsOArc F → (F ∩ G.V).ncard < r → IsNullHomotopicOArc F)
    (hii : ∀ F : Set S, G.IsNormal F → IsIArc F → (F ∩ G.V).ncard < s → lineEnds F ⊆ C₁
      ∨ lineEnds F ⊆ C₂) :
    ∃ (P : Fin r → Drawing S) (u v : Fin r → S) (B : Fin s → Drawing S),
      (∀ i : Fin r, (P i).IsSubdrawing G ∧ u i ∈ C₁ ∧ v i ∈ C₂ ∧ (P i).IsPathBetween (u i) (v i)) ∧
      (∀ i i' : Fin r, i ≠ i' → Disjoint (P i).V (P i').V) ∧
      (∀ j : Fin s, (B j).IsSubdrawing G ∧ IsOArc (B j).U ∧ ¬ IsNullHomotopicOArc (B j).U) ∧
      (∀ j j' : Fin s, j ≠ j' → Disjoint (B j).V (B j').V) ∧
      (∀ (i : Fin r) (j : Fin s), ∃ Q : Drawing S, ∃ x y : S, Q.U = (P i).U ∩ (B j).U ∧ Q.V =
        (P i).V ∩ (B j).V ∧ Q.IsPathBetween x y) := by
  classical
  have hT2 : T2Space S := hS.2.1
  have hcp : CompactSpace S := hS.1
  obtain ⟨T, tT, j, D₁, D₂, hTs, hsph, hconn, hj, h₁, h₂, hd, hb₁, hb₂, hcov, hin₁, hin₂⟩
    := exists_sphere_cap hS he hcuffs hne
  have hT2T : T2Space T := hTs.2.1
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hTs.2.2 x).isManifoldPoint
  have hC₁ : C₁ ∈ cuffs S := by rw [hcuffs]; simp
  have hC₂ : C₂ ∈ cuffs S := by rw [hcuffs]; simp
  have hdis : Disjoint C₁ C₂ := cuffs_disjoint hC₁ hC₂ hne
  have hbdS : ∀ {x}, x ∈ C₁ ∪ C₂ → x ∈ bd S := fun {x} hx => by
    rw [← sUnion_cuffs, hcuffs, sUnion_pair]
    exact hx
  have : Nonempty S := by
    obtain ⟨x, hx⟩ := isOArc_nonempty (cuff_isOArc hS hC₁)
    exact ⟨x⟩
  obtain ⟨Γ, hm⟩ := exists_image_matched hj G
  have hΓU : Γ.U = j '' G.U := by simpa using hm.image_U.symm
  have hΓV : Γ.V = j '' G.V := by simpa using hm.image_V.symm
  have hs₁ : ∀ {x}, j x ∈ D₁ → x ∈ C₁ := fun {x} hx => by
    have h3 : j x ∈ range j ∩ D₁ := ⟨⟨x, rfl⟩, hx⟩
    rw [hin₁] at h3
    obtain ⟨y, hy, he⟩ := h3
    exact hj.injective he ▸ hy
  have hs₂ : ∀ {x}, j x ∈ D₂ → x ∈ C₂ := fun {x} hx => by
    have h3 : j x ∈ range j ∩ D₂ := ⟨⟨x, rfl⟩, hx⟩
    rw [hin₂] at h3
    obtain ⟨y, hy, he⟩ := h3
    exact hj.injective he ▸ hy
  have hnormal : ∀ {x}, x ∈ C₁ ∪ C₂ → x ∈ G.U → x ∈ G.V := fun {x} h3 h4 => hG ⟨hbdS h3, h4⟩
  have hU₁ : Γ.U ∩ D₁ ⊆ Γ.V := by
    rw [hΓU, hΓV]
    rintro _ ⟨⟨x, hx, rfl⟩, h3⟩
    exact ⟨x, hnormal (.inl (hs₁ h3)) hx, rfl⟩
  have hU₂ : Γ.U ∩ D₂ ⊆ Γ.V := by
    rw [hΓU, hΓV]
    rintro _ ⟨⟨x, hx, rfl⟩, h3⟩
    exact ⟨x, hnormal (.inr (hs₂ h3)) hx, rfl⟩
  have hoffI₁ : ∀ x, j x ∉ discInt D₁ := fun x h => h.2 (hb₁ ▸ mem_image_of_mem j (hs₁ h.1))
  have hoffI₂ : ∀ x, j x ∉ discInt D₂ := fun x h => h.2 (hb₂ ▸ mem_image_of_mem j (hs₂ h.1))
  have hi₁ : Disjoint Γ.U (discInt D₁) := by
    rw [hΓU]
    refine disjoint_left.mpr ?_
    rintro _ ⟨x, -, rfl⟩
    exact hoffI₁ x
  have hi₂ : Disjoint Γ.U (discInt D₂) := by
    rw [hΓU]
    refine disjoint_left.mpr ?_
    rintro _ ⟨x, -, rfl⟩
    exact hoffI₂ x
  obtain ⟨p, hp⟩ := h₁.nonempty_discInt
  obtain ⟨a, ha⟩ := h₂.nonempty_discInt
  have hpr : p ∉ range j := by
    rintro ⟨x, rfl⟩
    exact hoffI₁ x hp
  have har : a ∉ range j := by
    rintro ⟨x, rfl⟩
    exact hoffI₂ x ha
  have hrng : ∀ {X : Set T}, Disjoint X (discInt D₁) → Disjoint X (discInt D₂) → X ⊆ range j
    := fun {X} h3 h4 z hz => by
    have hc : z ∈ range j ∪ D₁ ∪ D₂ := hcov ▸ mem_univ z
    rcases hc with (h | h) | h
    · exact h
    · have hb : z ∈ discBd D₁ := by
        by_contra hn
        exact disjoint_left.mp h3 hz ⟨h, hn⟩
      rw [hb₁] at hb
      exact image_subset_range _ _ hb
    · have hb : z ∈ discBd D₂ := by
        by_contra hn
        exact disjoint_left.mp h4 hz ⟨h, hn⟩
      rw [hb₂] at hb
      exact image_subset_range _ _ hb
  have hpull : ∀ {X : Set T}, X ⊆ range j → X ∩ Γ.U ⊆ Γ.V → G.IsNormal (j ⁻¹' X) ∧
    (j ⁻¹' X ∩ G.V).ncard = (X ∩ Γ.U).ncard := fun {X} h3 h4 => by
    have hnor : G.IsNormal (j ⁻¹' X) := fun x hx => by
      have h5 := h4 ⟨hx.1, hΓU ▸ mem_image_of_mem j hx.2⟩
      rw [hΓV] at h5
      obtain ⟨y, hy, he⟩ := h5
      exact hj.injective he ▸ hy
    refine ⟨hnor, ?_⟩
    have h6 : j '' (j ⁻¹' X ∩ G.V) = X ∩ Γ.U := by
      refine subset_antisymm ?_ fun z hz => ?_
      · rintro _ ⟨x, hx, rfl⟩
        exact ⟨hx.1, hΓU ▸ mem_image_of_mem j (G.V_subset_U hx.2)⟩
      · have h7 := h4 hz
        rw [hΓV] at h7
        obtain ⟨x, hx, rfl⟩ := h7
        exact ⟨x, ⟨hz.1, hx⟩, rfl⟩
    rw [← h6, ncard_image_of_injective _ hj.injective]
  have hi' : ∀ B, IsClosedDisc B → D₁ ⊆ B → Disjoint (discInt D₂) B → discBd B ∩ Γ.U ⊆ Γ.V → r ≤
    (discBd B ∩ Γ.U).ncard := fun B hB hsub hdisB hbn => by
    by_contra hlt
    have hX1 : Disjoint (discBd B) (discInt D₁) := disjoint_left.mpr fun z h3 h4 =>
      (discInt_mono hman h₁ hsub h4).2 h3
    have hX2 : Disjoint (discBd B) (discInt D₂) := disjoint_left.mpr fun z h3 h4
      => disjoint_left.mp hdisB h4 (Surface.discBd_subset _ h3)
    have hXr := hrng hX1 hX2
    obtain ⟨hnor, hcard⟩ := hpull hXr hbn
    have hFO := pull_oArc hj.isEmbedding hB.isOArc_discBd hXr
    have hnull := hi _ hnor hFO (by omega)
    exact not_null_of_separating hS hsph hj hFO hB (image_preimage_eq_of_subset hXr).symm
      (hsub hp.1) (fun h => disjoint_left.mp hdisB ha h) hpr har hnull
  have hii' : ∀ (L : Set T) (u v : T), IsLineWithEnds L u v → u ∈ discBd D₁ → v ∈ discBd D₂
    → L ∩ Γ.U ⊆ Γ.V → Disjoint L (discInt D₁) → Disjoint L (discInt D₂) → s ≤ (L ∩ Γ.V).ncard
      := fun L u v hl hu hv hLU h3 h4 => by
    by_contra hlt
    have hXr := hrng h3 h4
    obtain ⟨hnor, hcard⟩ := hpull hXr hLU
    have hset : L ∩ Γ.V = L ∩ Γ.U := subset_antisymm (fun z hz => ⟨hz.1, Γ.V_subset_U hz.2⟩) fun z
      hz => ⟨hz.1, hLU hz⟩
    rw [hb₁] at hu
    rw [hb₂] at hv
    obtain ⟨u₀, hu₀, rfl⟩ := hu
    obtain ⟨v₀, hv₀, rfl⟩ := hv
    have hFl := pull_line hj.isEmbedding hl hXr
    have hI : IsIArc (j ⁻¹' L) := ⟨u₀, v₀, hbdS (.inl hu₀), hbdS (.inr hv₀), hFl⟩
    rcases hii _ hnor hI (by rw [hcard, ← hset]; omega) with h | h
    · exact disjoint_left.mp hdis (h (show v₀ ∈ lineEnds _ from ⟨u₀, hFl.symm⟩)) hv₀
    · exact disjoint_left.mp hdis hu₀ (h (show u₀ ∈ lineEnds _ from ⟨v₀, hFl⟩))
  obtain ⟨P', u', v', B', E', hP, hPd, hB, -, hBd, hQ⟩ := exists_cylinder_grid hTs hsph Γ h₁ h₂ hd
    hU₁ hi₁ hU₂ hi₂ hp ha hi' hii'
  have hends : ∀ i, ∃ x y, x ∈ C₁ ∧ y ∈ C₂ ∧ j x = u' i ∧ j y = v' i := fun i => by
    obtain ⟨c1, c2, c3, W, -, hV, -⟩ := hP i
    have h3 : u' i ∈ Γ.V := c1.1 (by rw [hV]; exact W.start_mem_support)
    have h4 : v' i ∈ Γ.V := c1.1 (by rw [hV]; exact W.end_mem_support)
    rw [hΓV] at h3 h4
    obtain ⟨x, -, hx⟩ := h3
    obtain ⟨y, -, hy⟩ := h4
    exact ⟨x, y, hs₁ (hx ▸ c2), hs₂ (hy ▸ c3), hx, hy⟩
  choose u v hu hv hju hjv using hends
  choose P hPs hPU hPV hPE using fun i => exists_pull hm (hP i).1
  choose B hBs hBU hBV hBE using fun i => exists_pull hm (hB i).1
  have hdV : ∀ {X Y : Drawing S} {X' Y' : Drawing T}, j '' X.V = X'.V → j '' Y.V = Y'.V
    → Disjoint X'.V Y'.V → Disjoint X.V Y.V := fun {X Y X' Y'} h3 h4 h5 => by
    rw [← h3, ← h4] at h5
    exact (disjoint_image_iff hj.injective).mp h5
  refine ⟨P, u, v, B, fun i => ⟨hPs i, hu i, hv i, ?_⟩, fun i i' hne' => hdV (hPV i) (hPV i')
    (hPd i i' hne'), fun l => ⟨hBs l, ?_⟩, fun l l' hne' => hdV (hBV l) (hBV l')
      (hBd l l' hne'), fun i l => ?_⟩
  · refine pull_path hm hj.injective (hPV i) (hPE i) ?_
    rw [hju, hjv]
    exact (hP i).2.2.2
  · obtain ⟨-, c2, hΔ, hbΔ, hpΔ, haΔ⟩ := hB l
    have hO' := GM14.isOArc_of_isCircuit c2
    have hsub : (B' l).U ⊆ range j := hBU l ▸ image_subset_range _ _
    have hO : IsOArc (B l).U := by
      have := pull_oArc hj.isEmbedding hO' hsub
      rwa [← hBU, preimage_image_eq _ hj.injective] at this
    exact ⟨hO, not_null_of_separating hS hsph hj hO hΔ (hbΔ.trans (hBU l).symm) hpΔ haΔ hpr har⟩
  · obtain ⟨Q', x', y', hQs, hQU, hQV, hQp⟩ := hQ i l
    obtain ⟨Q, -, h3, h4, h5⟩ := exists_pull hm hQs
    obtain ⟨W, -, hV, -⟩ := id hQp
    have hx : x' ∈ j '' Q.V := by rw [h4, hV]; exact W.start_mem_support
    have hy : y' ∈ j '' Q.V := by rw [h4, hV]; exact W.end_mem_support
    obtain ⟨x, -, rfl⟩ := hx
    obtain ⟨y, -, rfl⟩ := hy
    refine ⟨Q, x, y, image_injective.mpr hj.injective ?_, image_injective.mpr hj.injective ?_,
      pull_path hm hj.injective h4 h5 hQp⟩
    · rw [h3, hQU, image_inter hj.injective, hPU, hBU]
    · rw [h4, hQV, image_inter hj.injective, hPV, hBV]

end GraphMinor.GM07
