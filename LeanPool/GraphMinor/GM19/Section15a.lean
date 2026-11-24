/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Conditional2

/-!
# Tools for the proof of (4.1)

The set `𝒮` of the proof of (4.1) consists of all images of a similarly oriented sequence. A finite
union of well-behaved sets is well-behaved, and a rooted location that isolates a tangle also
isolates
it for larger `θ`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {χ : ColourScheme S α}

omit [T2Space S] in
theorem IsFramePreservingHomeo.refl' (Φ : Frame S) : IsFramePreservingHomeo Φ
  (Homeomorph.refl S) where
  fix_V _ _ := rfl
  preserve_sides s _ := by simp
  preserves_orientation ω Δ _ a b c _ _ _ _ _ _ := by simp

omit [T2Space S] in
theorem IsFramePreservingHomeo.comp {Φ : Frame S} {f g : S ≃ₜ S}
    (hf : IsFramePreservingHomeo Φ f) (hg : IsFramePreservingHomeo Φ g) :
    IsFramePreservingHomeo Φ (f.trans g) where
  fix_V v hv := by simp [hf.fix_V v hv, hg.fix_V v hv]
  preserve_sides s hs := by
    rw [show ⇑(f.trans g) = g ∘ f from rfl, image_comp, hf.preserve_sides s hs,
      hg.preserve_sides s hs]
  preserves_orientation ω Δ hΔ a b c ha hb hc hab hbc hac := by
    have h₁ := hf.preserves_orientation ω Δ hΔ a b c ha hb hc hab hbc hac
    have hΔ' : IsClosedDisc (f '' Δ) := GM20.image_isClosedDisc f hΔ
    have hbd := GM20.image_discBd f Δ
    have h₂ := hg.preserves_orientation ω (f '' Δ) hΔ' (f a) (f b) (f c)
      (hbd ▸ mem_image_of_mem _ ha) (hbd ▸ mem_image_of_mem _ hb) (hbd ▸ mem_image_of_mem _ hc)
      (fun h ↦ hab (f.injective h)) (fun h ↦ hbc (f.injective h)) (fun h ↦ hac (f.injective h))
    change ω.pos ((g ∘ f) '' Δ) (g (f a)) (g (f b)) (g (f c)) ↔ _
    rw [image_comp]
    exact h₂.trans h₁

omit [T2Space S] in
theorem IsColouredImage.refl' (P : ColouredPainting χ) :
    IsColouredImage (Homeomorph.refl S) P P where
  U := by simp
  V := by simp
  γ e _ := by simp
  φ e _ := by simp

omit [T2Space S] in
theorem IsColouredImage.comp {f g : S ≃ₜ S} {P P' P'' : ColouredPainting χ}
    (I : IsColouredImage f P P') (J : IsColouredImage g P' P'') :
    IsColouredImage (f.trans g) P P'' where
  U := by rw [J.U, I.U]; exact (image_comp g f _).symm
  V := by rw [J.V, I.V]; exact (image_comp g f _).symm
  γ e he := by
    have hm : f '' e ∈ P'.Γ.E := I.E_eq ▸ mem_image_of_mem _ he
    change P''.Γ.γ ((g ∘ f) '' e) = List.map (g ∘ f) (P.Γ.γ e)
    rw [image_comp, J.γ _ hm, I.γ e he, List.map_map]
  φ e he := by
    have hm : f '' e ∈ P'.Γ.E := I.E_eq ▸ mem_image_of_mem _ he
    change P''.φ ((g ∘ f) '' e) = P.φ e
    rw [image_comp, J.φ _ hm, I.φ e he]

omit [T2Space S] in
/-- The image of a painting under a `Φ`-preserving homeomorphism has the same orientations. -/
theorem IsColouredImage.oriented {f : S ≃ₜ S} {P P' : ColouredPainting χ}
    (I : IsColouredImage f P P') (hf : IsFramePreservingHomeo χ.Φ f) {ω : SurfaceOrientation S}
    (hω : ∀ e ∈ P.Γ.E, (tilde e).ncard = 3 → ∀ a b c : S, P.Γ.γ e = [a, b, c] →
      ω.pos (closure e) a b c) {e' : Set S} (he' : e' ∈ P'.Γ.E) (h3 : (tilde e').ncard = 3)
    {a b c : S} (hγ : P'.Γ.γ e' = [a, b, c]) : ω.pos (closure e') a b c := by
  rw [I.E_eq] at he'
  obtain ⟨d, hd, rfl⟩ := he'
  have h3' : (tilde d).ncard = 3 := by rwa [ncard_tilde_image] at h3
  rw [I.γ d hd] at hγ
  obtain ⟨a₀, b₀, c₀, h₀, rfl, rfl, rfl⟩ : ∃ a₀ b₀ c₀, P.Γ.γ d = [a₀, b₀, c₀] ∧ f a₀ = a ∧ f b₀ = b
    ∧
      f c₀ = c := by
    generalize P.Γ.γ d = l at hγ
    match l, hγ with
    | [a₀, b₀, c₀], h =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
      exact ⟨a₀, b₀, c₀, rfl, h.1, h.2.1, h.2.2⟩
  have hdisc : IsClosedDisc (closure d) ∧ tilde d ⊆ discBd (closure d) := by
    rcases P.Γ.edge_shape d hd with h | h
    · omega
    · exact ⟨h.2.2.1, h.2.2.2⟩
  have hset := P.Γ.γ_set d hd
  have hnd := P.Γ.γ_nodup d hd
  rw [h₀] at hset hnd
  have hmem : ∀ x, x ∈ [a₀, b₀, c₀] → x ∈ discBd (closure d) := fun x hx ↦
    hdisc.2 (hset ▸ hx)
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    and_true, not_false_eq_true] at hnd
  change ω.pos (closure (f '' d)) _ _ _
  rw [← f.image_closure]
  exact (hf.preserves_orientation ω _ hdisc.1 a₀ b₀ c₀ (hmem _ (by simp)) (hmem _ (by simp))
    (hmem _ (by simp)) hnd.1.1 hnd.2 hnd.1.2).mpr (hω d hd h3' a₀ b₀ c₀ h₀)

/-- The set `𝒮` of the proof of (4.1): "Let $\mathscr{S}$ be a similarly oriented set of
$\chi$-coloured paintings containing
$(\Gamma_i, \phi_i)$ for each $i \ge 0$, and closed under $\Phi_\chi$-preserving
homeomorphisms of $\Sigma_\chi$. This exists since $\{(\Gamma_i, \phi_i) \colon i \ge 0\}$
is similarly oriented and so are all images of each $(\Gamma_i, \phi_i)$ under
$\Phi_\chi$-preserving homeomorphisms." -/
def imageClass (P : ℕ → ColouredPainting χ) : Set (ColouredPainting χ) :=
  {P' | ∃ i, ∃ f : S ≃ₜ S, IsFramePreservingHomeo χ.Φ f ∧ IsColouredImage f (P i) P'}

omit [T2Space S] in
theorem mem_imageClass (P : ℕ → ColouredPainting χ) (i : ℕ) : P i ∈ imageClass P :=
  ⟨i, _, IsFramePreservingHomeo.refl' _, IsColouredImage.refl' _⟩

omit [T2Space S] in
theorem isPaintingClass_imageClass {P : ℕ → ColouredPainting χ} (h : IsSimilarlyOriented χ P) :
    IsPaintingClass χ (imageClass P) := by
  refine ⟨?_, ?_⟩
  · rcases h with h | ⟨ω, hω⟩
    · exact Or.inl h
    · refine Or.inr ⟨ω, ?_⟩
      rintro P' ⟨i, f, hf, I⟩ e he h3 a b c hγ
      exact I.oriented hf (hω i) he h3 hγ
  · rintro P' ⟨i, f, hf, I⟩ g P'' hg J
    exact ⟨i, f.trans g, hf.comp hg, I.comp J⟩

omit [T2Space S] in
/-- A finite union of well-behaved sets is well-behaved. A sequence in the union has an infinite
part
in one of the sets. -/
theorem IsWellBehavedPlaces.iUnion {ι : Type*} [Finite ι] {C : ι → Set (Place χ)}
    (hC : ∀ i, IsWellBehavedPlaces (C i)) : IsWellBehavedPlaces (⋃ i, C i) := by
  intro β Ω hΩ seq hseq ξ hξ
  classical
  choose c hc using fun n ↦ mem_iUnion.mp (hseq n)
  obtain ⟨j, hj⟩ := Finite.exists_infinite_fiber c
  have hfreq : ∀ N, ∃ n > N, c n = j := by
    intro N
    have hinf : (c ⁻¹' {j}).Infinite := infinite_coe_iff.mp hj
    obtain ⟨n, hn, hN⟩ := hinf.exists_gt N
    exact ⟨n, hN, hn⟩
  obtain ⟨g, hg, hgj⟩ := Nat.exists_strictMono_subsequence hfreq
  obtain ⟨a, b, hab, τ, hτ, hle⟩ := hC j Ω hΩ (fun n ↦ seq (g n))
    (fun n ↦ hgj n ▸ hc (g n)) (fun n ↦ ξ (g n)) (fun n ↦ hξ (g n))
  exact ⟨g a, g b, hg hab, τ, hτ, hle⟩

omit [T2Space S] in
theorem IsWellBehavedPlaces.union {C D : Set (Place χ)} (hC : IsWellBehavedPlaces C)
    (hD : IsWellBehavedPlaces D) : IsWellBehavedPlaces (C ∪ D) := by
  rw [union_eq_iUnion]
  exact IsWellBehavedPlaces.iUnion fun b ↦ by
    cases b
    · exact hD
    · exact hC

omit [T2Space S] [T2Space Shat] in
/-- A rooted location that `θ₁`-isolates a tangle also `θ₂`-isolates it, for `θ₁ ≤ θ₂ ≤ ord(𝒯)`. -/
theorem RootedLocation.Isolates.mono {Γ : Painting S} {cap : IsCappedSurface S Shat}
    {rad : RadialDrawing cap Γ} {tb : TieBreaker rad} {L : RootedLocation Γ} {θ₁ θ₂ ord : ℕ}
    {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} (h : L.Isolates tb θ₁ ord 𝒯)
    (h₁ : θ₁ ≤ θ₂) (h₂ : θ₂ ≤ ord) : L.Isolates tb θ₂ ord 𝒯 where
  seps_subset := h.seps_subset
  ord_lt := lt_of_lt_of_le h.ord_lt h₁
  le_ord := h₂
  distinction_le A hA ord' 𝒯' h𝒯' hθ := h.distinction_le A hA ord' 𝒯' h𝒯' (h₁.trans hθ)

/-- A bound on `dist(Γ)`, or on `rep(Γ)`, used with no fractions. -/
theorem two_mul_le_of_lt {N x : ℕ} {d : ℕ∞} (h : (N : ℕ∞) < d) (hx : x ≤ 2 * N + 2) :
    (x : ℕ∞) ≤ 2 * d := by
  induction d using ENat.recTopCoe with
  | top =>
    rw [ENat.mul_top (by simp)]
    exact le_top
  | coe n =>
    have h₁ : N < n := by exact_mod_cast h
    have h₂ : x ≤ 2 * n := by omega
    exact_mod_cast h₂

theorem two_mul_lt_of_lt {N x : ℕ} {d : ℕ∞} (h : (N : ℕ∞) < d) (hx : x < 2 * N + 2) :
    (x : ℕ∞) < 2 * d := by
  induction d using ENat.recTopCoe with
  | top =>
    rw [ENat.mul_top (by simp)]
    exact ENat.natCast_lt_top _
  | coe n =>
    have h₁ : N < n := by exact_mod_cast h
    have h₂ : x < 2 * n := by omega
    exact_mod_cast h₂

end GraphMinor.GM19
