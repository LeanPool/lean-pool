/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section14z
public import LeanPool.GraphMinor.GM19.FragmentOrient

/-!
# Graph Minors XIX, Section 14: the colour scheme `χ'`

The paper takes a colour scheme in `Σ'` with the frame `Φ'`. An internal edge keeps its colour, a
short side has one colour, and the colours of a long side record
the sector at each edge of `R`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 TangleDatum

universe w

variable {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat] [T2Space S] [T2Space Shat] {α
  : Type w}
  {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

/-- The scheme `χ'`. -/
noncomputable def cutScheme {X : Type} [TopologicalSpace X] (hX : IsSurface X)
  (hc : ConnectedSpace X) (Φ : Frame X) (Ω2 Ω3 Ωc : QuasiOrder α) (h2 : Ω2.IsWQO) (h3 : Ω3.IsWQO)
    (hcw : Ωc.IsWQO) (a₀ : α) :
    ColourScheme X α := by
  classical exact
  { isSurface := hX
    connected := hc
    Φ := Φ
    Ω2 := Ω2
    Ω3 := Ω3
    ΩS := fun s ↦ if Φ.isLong s then Ωc else QuasiOrder.single a₀
    shortElem := fun _ ↦ a₀
    isWQO_2 := h2
    isWQO_3 := h3
    isWQO_S := fun s _ ↦ by
      by_cases h : Φ.isLong s
      · rw [ite_eq_left h]
        exact hcw
      · rw [ite_eq_right h]
        exact QuasiOrder.isWQO_single a₀
    short_singleton := fun s hs ↦ by
      rw [ite_eq_right hs.2]
      rfl }

namespace Slice

variable {T : Set S} {D : TangleDatum cap χ} (s : Slice T D)

open Classical in
/-- The colour of a border edge. -/
noncomputable def borderCol (col : ↥s.𝒲 → ℕ → α) (a₀ : α) (e : Set ↥Tᶜ) : α :=
  if h : ∃ W p, p < (s.fr W).R.k ∧ e = s.arc W p then col h.choose h.choose_spec.choose else a₀

open Classical in
/-- The colour of an edge of `Γ'`. -/
noncomputable def cutφ (col : ↥s.𝒲 → ℕ → α) (a₀ : α) (Z : Set ↥Tᶜ) (e : Set ↥Tᶜ) : α :=
  if Painting.IsInternal e then s.Q.φ (Subtype.val '' e) else if Disjoint e Z then s.borderCol col
    a₀ e else a₀

include s

theorem borderCol_arc (col : ↥s.𝒲 → ℕ → α) (a₀ : α) {W : ↥s.𝒲} {p : ℕ} (hp : p <
  (s.fr W).R.k) : s.borderCol col a₀ (s.arc W p) = col W p := by
  classical
  have h : ∃ W' p', p' < (s.fr W').R.k ∧ s.arc W p = s.arc W' p' := ⟨W, p, hp, rfl⟩
  rw [borderCol, dite_eq_left h]
  have key : ∀ W' p', p' < (s.fr W').R.k → s.arc W p = s.arc W' p' → col W' p' = col W p := by
    intro W' p' hp' he
    obtain rfl := s.arc_wheel he
    rw [s.arc_pos W hp hp' he]
  exact key _ _ h.choose_spec.choose_spec.1 h.choose_spec.choose_spec.2

theorem exists_pos {c : Set ↥Tᶜ} (hc : c ∈ arcComponentsIn (bd ↥Tᶜ \ s.Nb)) : ∃ W p, p <
  (s.fr W).R.k ∧ c = s.arc W p := by
  obtain ⟨x, hx⟩ := hc.1
  obtain ⟨C, hC, hxC⟩ := sUnion_cuffs (S := ↥Tᶜ) ▸ (hc.2.1 hx).1
  obtain ⟨W, hW⟩ := s.exists_wheel ⟨C, hC⟩
  obtain ⟨i, hi, e⟩ := s.arc_cover W hc hx (hW ▸ hxC)
  exact ⟨W, i, hi, e⟩

/-- An edge of `Γ` in the part that we keep is not in `Z`. -/
theorem not_above {ω₀ : α} (hz : ∀ e ∈ D.Γ.E, χ.unionLE ω₀ (D.P.φ e) → ∃ W ∈ s.𝒲, cap.emb '' e ⊆ W)
  {e : Set S} (he : e ∈ s.Q.Γ.E) {x : ↥Tᶜ} (hx : x.1 ∈ e) :
    ¬ χ.unionLE ω₀ (s.Q.φ e) := by
  have hE : e ∈ (D.P.Γ.push s.f.symm).E := he
  rw [push_E] at hE
  obtain ⟨c, hc, rfl⟩ := hE
  intro hle
  have hφ : s.Q.φ (s.f.symm '' c) = D.P.φ c := s.isImage.φ c hc
  rw [hφ] at hle
  obtain ⟨W, hW, hsub⟩ := hz c hc hle
  obtain ⟨y, hy, hxy⟩ := hx
  have hxy' : s.f x.1 = y := by rw [← hxy]; simp
  have hin : cap.emb y ∈ W := hsub (mem_image_of_mem _ hy)
  have hbd : cap.emb y ∈ discBd W := by
    by_contra hb
    have hT : x.1 ∈ cutT (cap.emb ∘ s.f) s.𝒲 := by
      refine mem_iUnion₂.mpr ⟨W, hW, ?_⟩
      change cap.emb (s.f x.1) ∈ _
      rw [hxy']
      exact ⟨hin, hb⟩
    rw [s.hT] at hT
    exact x.2 hT
  have hU : cap.emb y ∈ D.rad.G.U := (s.fr ⟨W, hW⟩).R.G_sub hbd
  have hyU : y ∈ D.P.Γ.U := (hc.2.1 hy).1
  have hV : cap.emb y ∈ D.P.Γ.hatV cap := by
    rw [← D.rad.isPreRadial.1]
    exact ⟨⟨y, hyU, rfl⟩, hU⟩
  obtain ⟨v, hv, e'⟩ := hV
  exact (hc.2.1 hy).2 ((cap.isEmbedding.injective e') ▸ hv)

variable [Nonempty ↥Tᶜ]

omit s in
/-- The hypotheses on the orders of `χ'`. -/
structure IsCutOrders (s : Slice T D) (ω₀ : α) (Ω2 Ω3 Ωc : QuasiOrder α) (col : ↥s.𝒲 → ℕ
  → α) : Prop where
  mem_2 : ∀ c ∈ χ.Ω2.E, ¬ χ.unionLE ω₀ c → c ∈ Ω2.E
  mem_3 : ∀ c ∈ χ.Ω3.E, ¬ χ.unionLE ω₀ c → c ∈ Ω3.E
  covered : ∀ e ∈ D.Γ.E, χ.unionLE ω₀ (D.P.φ e) → ∃ W ∈ s.𝒲, cap.emb '' e ⊆ W
  mem_c : ∀ W p, p < (s.fr W).R.k → p ∉ s.sing W → col W p ∈ Ωc.E

theorem lift_φ (ε : Set ↥Tᶜ → Bool) {e₁ : Set ↥Tᶜ} (he₁ : e₁ ∈ (s.paint ε).E)
  (hi : Painting.IsInternal e₁) (col : ↥s.𝒲 → ℕ → α) (a₀ : α) (Z : Set ↥Tᶜ) :
    ∃ e ∈ s.Q.Γ.E, e₁ = Subtype.val ⁻¹' e ∧ Subtype.val '' e₁ = e ∧ s.cutφ col a₀ Z e₁ = s.Q.φ e ∧
      (tilde e₁).ncard = (tilde e).ncard ∧ Painting.IsInternal e ∧ ∃ x : ↥Tᶜ, x.1 ∈ e := by
  classical
  obtain ⟨e, he, hb, hne, rfl⟩ := s.fd.exists_lift_of_internal _ he₁ hi
  have hsub := s.fd.pull.subset_R he hb hne
  have hsur : Subtype.val '' (Subtype.val ⁻¹' e : Set ↥Tᶜ) = e := image_preimage_eq_of_subset
    (hsub.trans (image_subset_range _ _))
  refine ⟨e, he, rfl, hsur, ?_, s.fd.pull.ncard_tilde he hsub, isInternal_iff_not_border.mpr hb,
    hne⟩
  rw [cutφ, ite_eq_left hi, hsur]

/-- The coloured painting `(Γ', φ')`. -/
noncomputable def colPaint (ε : Set ↥Tᶜ → Bool) {Φ' : Frame ↥Tᶜ} {Z : Set ↥Tᶜ}
  (hF : s.IsCutFrame Φ' Z ε) {ω₀ : α} {Ω2 Ω3 Ωc : QuasiOrder α} (h2 : Ω2.IsWQO) (h3 : Ω3.IsWQO)
    (hcw : Ωc.IsWQO) (a₀ : α)
    (col : ↥s.𝒲 → ℕ → α) (hO : s.IsCutOrders ω₀ Ω2 Ω3 Ωc col) : ColouredPainting
      (cutScheme s.isSurface s.connected Φ' Ω2 Ω3 Ωc h2 h3 hcw a₀) where
  Γ := s.paint ε
  φ := s.cutφ col a₀ Z
  fits := s.paint_fits hF
  internal_2_mem e₁ he₁ hi h2' := by
    obtain ⟨e, he, rfl, hsur, hφ, hn, hint, x, hx⟩ := s.lift_φ ε he₁ hi col a₀ Z
    rw [hφ]
    exact hO.mem_2 _ (s.Q.internal_2_mem e he hint (hn ▸ h2')) (s.not_above hO.covered he hx)
  internal_3_mem e₁ he₁ hi h3' := by
    obtain ⟨e, he, rfl, hsur, hφ, hn, hint, x, hx⟩ := s.lift_φ ε he₁ hi col a₀ Z
    rw [hφ]
    exact hO.mem_3 _ (s.Q.internal_3_mem e he hint (hn ▸ h3')) (s.not_above hO.covered he hx)
  border_mem e he c hc hbs := by
    classical
    have ha := s.border_arc ε he hbs.1
    have hni : ¬ Painting.IsInternal e := fun hi ↦ isInternal_iff_not_border.mp hi hbs.1
    change s.cutφ col a₀ Z e ∈ _
    rw [cutφ, ite_eq_right hni]
    change _ ∈ ((if Φ'.isLong c then Ωc else QuasiOrder.single a₀)).E
    have hc' : c ∈ arcComponentsIn (bd ↥Tᶜ \ s.markN) := by
      have : c ∈ arcComponentsIn (bd ↥Tᶜ \ Φ'.V) := hc
      rwa [hF.V_eq] at this
    by_cases hl : Φ'.isLong c
    · rw [ite_eq_left hl]
      have hdis : Disjoint e Z := ((hF.long_iff c).mp hl).mono_left hbs.2
      rw [ite_eq_left hdis]
      obtain ⟨W, p, hp, rfl⟩ := s.exists_pos ha
      rw [s.borderCol_arc col a₀ hp]
      refine hO.mem_c W p hp fun hsing ↦ ?_
      have hz : s.zx W p ∈ s.markZ := mem_iUnion.mpr ⟨W, mem_iUnion₂.mpr ⟨_, hsing, rfl⟩⟩
      exact disjoint_left.mp hdis (s.zx_arc W p) (hF.Z_eq ▸ hz)
    · rw [ite_eq_right hl]
      have hnd : ¬ Disjoint c s.markZ := fun hd ↦ hl ((hF.long_iff c).mpr (hF.Z_eq ▸ hd))
      obtain ⟨z, hzc, hz⟩ := not_disjoint_iff.mp hnd
      obtain ⟨W, hz⟩ := mem_iUnion.mp hz
      obtain ⟨i, hi, rfl⟩ := mem_iUnion₂.mp hz
      obtain rfl : c = s.arc W i := arcComp_eq_of_mem hc' (s.arc_side hi) hzc (s.zx_arc W i)
      obtain ⟨x, hx⟩ := ha.1
      obtain rfl : e = s.arc W i := arcComp_eq_of_mem ha (s.arc_mem W i) hx (hbs.2 hx)
      have hnd' : ¬ Disjoint (s.arc W i) Z := fun hd ↦ hnd (hF.Z_eq ▸ hd)
      rw [ite_eq_right hnd']
      rfl

/-- The orientation passes to `Γ'`. -/
theorem paint_pos (ε : Set ↥Tᶜ → Bool) {ω : SurfaceOrientation S} {ω₁ : SurfaceOrientation ↥Tᶜ}
    (hω₁ : ∀ Δ : Set ↥Tᶜ, IsClosedDisc Δ → InjOn Subtype.val Δ → ∀ a b c : ↥Tᶜ, a ∈ discBd Δ
      → b ∈ discBd Δ → c ∈ discBd Δ → a ≠ b → b ≠ c → a ≠ c → (ω₁.pos Δ a b c ↔ ω.pos
        (Subtype.val '' Δ) a.1 b.1 c.1))
    (hω : ∀ e ∈ s.Q.Γ.E, (tilde e).ncard = 3 → ∀ a b c : S, s.Q.Γ.γ e = [a, b, c] → ω.pos
      (closure e) a b c) :
    ∀ e ∈ (s.paint ε).E, (tilde e).ncard = 3 → ∀ a b c : ↥Tᶜ, (s.paint ε).γ e = [a, b, c] → ω₁.pos
      (closure e) a b c := by
  intro e₁' he₁' h3 a' b' c' hl'
  have hEp : e₁' ∈ (s.paint ε).E := he₁'
  have hint : Painting.IsInternal e₁' := by
    refine disjoint_left.mpr fun x hx hxb ↦ ?_
    have := ((s.paint ε).border_edge e₁' hEp ⟨x, hx, hxb⟩).1
    omega
  obtain ⟨e, he, hb', hne', rfl⟩ := s.fd.exists_lift_of_internal _ hEp hint
  have hsub := s.fd.pull.subset_R he hb' hne'
  have hmap := s.fd.map_march_lift (flip := flipOf ε) he hb' hne'
  have hlist : (s.paint ε).γ (Subtype.val ⁻¹' e) = [a', b', c'] := hl'
  have hmap' : [a', b', c'].map Subtype.val = s.Q.Γ.γ e := by
    rw [← hlist]
    exact hmap
  obtain ⟨hdisc, htil⟩ := (s.paint ε).tilde_subset_discBd hEp h3
  have hn := (s.paint ε).γ_nodup _ hEp
  have hset := (s.paint ε).γ_set _ hEp
  rw [hlist] at hn hset
  have hmem : ∀ x ∈ [a', b', c'], x ∈ discBd (closure (Subtype.val ⁻¹' e : Set ↥Tᶜ))
    := fun x hx ↦ htil (hset ▸ hx)
  have hsur : Subtype.val '' (Subtype.val ⁻¹' e : Set ↥Tᶜ) = e := image_preimage_eq_of_subset
    (hsub.trans (image_subset_range _ _))
  have hfrag := s.fd.pull.frag
  have hcl' : Subtype.val '' closure (Subtype.val ⁻¹' e : Set ↥Tᶜ) = closure e := by
    rw [← hfrag.isClosedMap.closure_image_eq_of_continuous hfrag.continuous_ψ, hsur]
  refine (hω₁ _ hdisc (s.fd.pull.injOn_closure he hsub) a' b' c' (hmem _ (by simp)) (hmem _
    (by simp))
    (hmem _ (by simp)) (by simp at hn; tauto) (by simp at hn; tauto) (by simp at hn; tauto)).mpr ?_
  rw [hcl']
  have h3e : (tilde e).ncard = 3 := by
    rw [← s.fd.pull.ncard_tilde he hsub]
    exact h3
  exact hω e he h3e _ _ _ hmap'.symm

omit [Nonempty ↥Tᶜ] in
/-- `Σ'` is orientable only if `Σ` is. -/
theorem orientable [Nonempty ↥Tᶜ] (hO : IsOrientableSurface ↥Tᶜ) : IsOrientableSurface S := by
  obtain ⟨cap'⟩ := s.nonempty_capped
  have := cap.connected
  obtain ⟨e, P, hP, hs', ht⟩ := exists_cap_chart s.isSurface cap'
  obtain ⟨ω⟩ := hO
  exact isOrientable_of_embedding cap.isEmbedding (isOrientable_of_inside cap.isClosedSurface hP e
    hs' ht.1 (ω.isPartial _))

end Slice

end GraphMinor.GM19
