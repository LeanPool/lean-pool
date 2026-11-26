/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.CollarCut
public import LeanPool.GraphMinor.GM11.Restraints
public import LeanPool.GraphMinor.GM11.PerimeterWalk
public import LeanPool.GraphMinor.Surface.Crossing

/-!
# Graph Minors XI, (8.1)

`theorem_8_1` is (8.1) of the paper: two arc-wise connected subsets of `X` whose ends alternate
along a
perimeter walk of `X` must meet. We state it for times along the collar of the perimeter walk, so it
covers
the vertices of the walk and the other points of `bd(X)`.

The proof in the paper joins the four points to a new point outside `X`, and uses that `O`-arcs in a
disc do
not cross once. We use the same fact in the form `disc_crossing`, for the disc bounded by a circle
of the
collar (`exists_disc_of_collar`), inside the sphere obtained from an open disc around `X`.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval OnePoint

universe u

/-- A connected set that misses an `O`-arc in a sphere lies in one of the two discs bounded by the
`O`-arc. -/
theorem exists_disc_of_collar {S : Type u} [TopologicalSpace S]
  (hS : IsClosedSurface S)
    (hsph : IsSphere S) {W J : Set S} (hJ : IsOArc J) (hWp : IsPreconnected W)
      (hWJ : Disjoint W J) :
    ∃ Δ, IsClosedDisc Δ ∧ discBd Δ = J ∧ W ⊆ Δ := by
  have hT2 : T2Space S := hS.2.1
  obtain ⟨Δ₁, Δ₂, -, hΔ₁, hΔ₂, hb₁, hb₂, hcup, hcap, -, -⟩ := sphere_disc S hsph J hJ
  have hint₁ : IsOpen (Δ₁ \ J) := by
    have := interior_eq_sdiff_discBd hS hΔ₁
    rw [hb₁] at this
    exact this ▸ isOpen_interior
  have hint₂ : IsOpen (Δ₂ \ J) := by
    have := interior_eq_sdiff_discBd hS hΔ₂
    rw [hb₂] at this
    exact this ▸ isOpen_interior
  have hcover : W ⊆ (Δ₁ \ J) ∪ (Δ₂ \ J) := by
    intro x hx
    have hxJ : x ∉ J := disjoint_left.mp hWJ hx
    have : x ∈ Δ₁ ∪ Δ₂ := hcup ▸ mem_univ x
    exact this.elim (fun h => Or.inl ⟨h, hxJ⟩) fun h => Or.inr ⟨h, hxJ⟩
  have hdis : Disjoint (Δ₁ \ J) (Δ₂ \ J) := disjoint_left.mpr fun x h₁ h₂ => h₁.2
    (hcap ▸ ⟨h₁.1, h₂.1⟩)
  rcases hWp.subset_or_subset hint₁ hint₂ hdis hcover with h | h
  · exact ⟨Δ₁, hΔ₁, hb₁, fun x hx => (h hx).1⟩
  · exact ⟨Δ₂, hΔ₂, hb₂, fun x hx => (h hx).1⟩

/-- A connected subset of the circle that misses two points does not meet both arcs between them. -/
theorem circle_no_cross {s₁ s₂ s₃ s₄ : ℝ} (h₁₂ : s₁ < s₂) (h₂₃ : s₂ < s₃) (h₃₄ : s₃ < s₄)
  (h₄ : s₄ < s₁ + 1)
    {C : Set Circle} (hC : IsPreconnected C) (hC₁ : circlePt s₁ ∉ C) (hC₃ : circlePt s₃ ∉ C)
    (h₂ : circlePt s₂ ∈ C) (h₄' : circlePt s₄ ∈ C) : False := by
  have hI : ∀ {t}, s₁ ≤ t → t < s₁ + 1 → t ∈ Ico s₁ (s₁ + 1) := fun h h' => ⟨h, h'⟩
  have hdis : Disjoint (circlePt '' Ioo s₁ s₃) (circlePt '' Ioo s₃ (s₁ + 1)) := by
    refine disjoint_left.mpr ?_
    rintro _ ⟨t, ht, rfl⟩ ⟨t', ht', he⟩
    have := circlePt_injOn (hI (by linarith [ht'.1]) ht'.2) (hI ht.1.le (by linarith [ht.2])) he
    linarith [ht.2, ht'.1]
  have hcov : C ⊆ (circlePt '' Ioo s₁ s₃) ∪ (circlePt '' Ioo s₃ (s₁ + 1)) := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := exists_circlePt_time s₁ z
    have hn₁ : t ≠ s₁ := fun h => hC₁ (h ▸ hz)
    have hn₃ : t ≠ s₃ := fun h => hC₃ (h ▸ hz)
    rcases lt_or_gt_of_ne hn₃ with h | h
    · exact Or.inl ⟨t, ⟨lt_of_le_of_ne ht.1 hn₁.symm, h⟩, rfl⟩
    · exact Or.inr ⟨t, ⟨h, ht.2⟩, rfl⟩
  rcases hC.subset_or_subset (isOpenMap_circlePt _ isOpen_Ioo) (isOpenMap_circlePt _ isOpen_Ioo)
    hdis hcov with
    h | h
  · exact disjoint_left.mp hdis (h h₄') ⟨s₄, ⟨h₃₄, h₄⟩, rfl⟩
  · exact disjoint_left.mp hdis ⟨s₂, ⟨h₁₂, h₂₃⟩, rfl⟩ (h h₂)

variable {S : Type u} [TopologicalSpace S] [T2Space S] {X A : Set S}

private theorem embedded_collar_pairs_cross {T : Type u} [TopologicalSpace T]
    {k : Circle → T} {B : Set T} (hkemb : IsEmbedding k) (hB : B = k '' univ)
    {s₁ s₂ s₃ s₄ : ℝ} (h₁₂' : s₁ < s₂) (h₂₃' : s₂ < s₃) (h₃₄' : s₃ < s₄)
    (h₄₁' : s₄ < s₁ + 1) :
    PairsCrossOn B (k (circlePt s₁)) (k (circlePt s₃)) (k (circlePt s₂)) (k (circlePt s₄)) := by
  have h13 : s₁ < s₃ := h₁₂'.trans h₂₃'
  have h24 : s₂ < s₄ := h₂₃'.trans h₃₄'
  have h14 : s₁ < s₄ := h13.trans h₃₄'
  have hm₁ : s₁ ∈ Ico s₁ (s₁ + 1) := ⟨le_rfl, by linarith⟩
  have hm₂ : s₂ ∈ Ico s₁ (s₁ + 1) := ⟨h₁₂'.le, by linarith⟩
  have hm₃ : s₃ ∈ Ico s₁ (s₁ + 1) := ⟨h13.le, by linarith⟩
  have hm₄ : s₄ ∈ Ico s₁ (s₁ + 1) := ⟨h14.le, h₄₁'⟩
  have hkne : ∀ {s s' : ℝ}, s ∈ Ico s₁ (s₁ + 1) → s' ∈ Ico s₁ (s₁ + 1) → s ≠ s' →
      k (circlePt s) ≠ k (circlePt s') :=
    fun hs hs' hne he => hne (circlePt_injOn hs hs' (hkemb.injective he))
  have hkmem : ∀ s, k (circlePt s) ∈ B := fun s => hB ▸ mem_image_of_mem _ (mem_univ _)
  refine ⟨hkmem _, hkmem _, hkmem _, hkmem _, hkne hm₁ hm₃ h13.ne, hkne hm₂ hm₄ h24.ne,
    hkne hm₁ hm₂ h₁₂'.ne, hkne hm₁ hm₄ h14.ne, hkne hm₃ hm₂ h₂₃'.ne', hkne hm₃ hm₄ h₃₄'.ne, ?_⟩
  intro he
  set C₀ := B \ {k (circlePt s₁), k (circlePt s₃)} with hC₀
  have hb₀ : k (circlePt s₂) ∈ C₀ := ⟨hkmem _, by
    rintro (h' | h')
    · exact hkne hm₂ hm₁ h₁₂'.ne' h'
    · exact hkne hm₂ hm₃ h₂₃'.ne h'⟩
  have hd₀ : k (circlePt s₄) ∈ C₀ := ⟨hkmem _, by
    rintro (h' | h')
    · exact hkne hm₄ hm₁ h14.ne' h'
    · exact hkne hm₄ hm₃ h₃₄'.ne' h'⟩
  have hsub₀ : connectedComponentIn C₀ (k (circlePt s₂)) ⊆ C₀ := connectedComponentIn_subset _ _
  have hpre : IsPreconnected (k ⁻¹' connectedComponentIn C₀ (k (circlePt s₂))) := by
    rw [← hkemb.isInducing.isPreconnected_image, image_preimage_eq_of_subset]
    · exact isPreconnected_connectedComponentIn
    · intro y hy
      have := (hsub₀ hy).1
      rw [hB] at this
      obtain ⟨z, -, rfl⟩ := this
      exact mem_range_self z
  refine circle_no_cross h₁₂' h₂₃' h₃₄' h₄₁' hpre (fun hm => (hsub₀ hm).2 (Or.inl rfl))
    (fun hm => (hsub₀ hm).2 (Or.inr rfl)) (mem_connectedComponentIn hb₀) ?_
  change k (circlePt s₄) ∈ connectedComponentIn C₀ (k (circlePt s₂))
  rw [he]
  exact mem_connectedComponentIn hd₀

/-- **(8.1)** of Graph Minors XI (page 96), for a collar `h` of a closed, simply-connected, nice set
`X` with
`X ≠ ∅, Σ`: "if $A, B \subseteq X$ are arc-wise connected and $v_{i_1}, v_{i_3} \in A$ and $v_{i_2},
v_{i_4} \in B$, then $A \cap B \ne \emptyset$". Here the points `v_i` are points `h(e^{2π i s_j},
0)` of the circle of the collar. -/
theorem theorem_8_1_proof (hS : IsClosedSurface S) (hA : IsOpenDisc A) (hXA : X ⊆ A)
    (hXp : IsPathConnected X) {h : C(Circle × I, S)} (hinj : InjOn h {p | 0 < p.2})
    (hoff : ∀ p : Circle × I, 0 < p.2 → h p ∉ X) (hbot : ∀ z, h (z, 0) ∈ X)
    {s₁ s₂ s₃ s₄ : ℝ} (h₁₂ : s₁ ≤ s₂) (h₂₃ : s₂ ≤ s₃) (h₃₄ : s₃ ≤ s₄)
    (h₄₁ : s₄ ≤ s₁ + 1) {P Q : Set S} (hP : IsPathConnected P) (hQ : IsPathConnected Q)
      (hPX : P ⊆ X)
    (hQX : Q ⊆ X) (hP₁ : h (circlePt s₁, 0) ∈ P) (hP₃ : h (circlePt s₃, 0) ∈ P)
    (hQ₂ : h (circlePt s₂, 0) ∈ Q) (hQ₄ : h (circlePt s₄, 0) ∈ Q) : (P ∩ Q).Nonempty := by
  classical
  rcases eq_or_lt_of_le h₁₂ with rfl | h₁₂'
  · exact ⟨_, hP₁, hQ₂⟩
  rcases eq_or_lt_of_le h₂₃ with rfl | h₂₃'
  · exact ⟨_, hP₃, hQ₂⟩
  rcases eq_or_lt_of_le h₃₄ with rfl | h₃₄'
  · exact ⟨_, hP₃, hQ₄⟩
  rcases eq_or_lt_of_le h₄₁ with he | h₄₁'
  · refine ⟨_, hP₁, ?_⟩
    have : circlePt s₄ = circlePt s₁ := by
      rw [he]
      simp only [circlePt, mul_add, mul_one, Circle.exp_add, Circle.exp_two_pi]
    rwa [this] at hQ₄
  -- The collar, low enough to lie in `A`.
  have hK : CompactSpace S := hS.1
  have hX₀ : (univ : Set Circle) ×ˢ ({0} : Set I) ⊆ h ⁻¹' A := by
    rintro ⟨z, t⟩ ⟨-, ht⟩
    obtain rfl : t = 0 := ht
    exact hXA (hbot z)
  obtain ⟨U₁, V₁, -, hV₁, hU₁, h0V₁, hUV⟩ := generalized_tube_lemma isCompact_univ
    isCompact_singleton
    (hA.1.preimage h.continuous) hX₀
  obtain ⟨ε, hε, hsm⟩ := exists_small (hV₁.mem_nhds (h0V₁ rfl))
  have hlow : ∀ z, ∀ t : I, t ≤ ε → h (z, t) ∈ A := fun z t ht => hUV (mk_mem_prod (hU₁
    (mem_univ z)) (hsm t ht))
  have hPC : PathConnectedSpace I := isPathConnected_iff_pathConnectedSpace.mp
    ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, by simp⟩)
  -- The rays of the collar.
  let ray : ℝ → Set S := fun s => (fun u : I => h (circlePt s, u * ε)) '' univ
  have hrayp : ∀ s, IsPathConnected (ray s) := fun s => isPathConnected_univ.image (by fun_prop)
  have hray₀ : ∀ s, h (circlePt s, 0) ∈ ray s := fun s => ⟨0, mem_univ _, by simp⟩
  have hrayε : ∀ s, h (circlePt s, ε) ∈ ray s := fun s => ⟨1, mem_univ _, by simp⟩
  have hrayt : ∀ s, ∀ y ∈ ray s, ∃ t : I, t ≤ ε ∧ y = h (circlePt s, t) := by
    rintro s _ ⟨u, -, rfl⟩
    exact ⟨u * ε, unitInterval.mul_le_right, rfl⟩
  have hrayX : ∀ s, ∀ y ∈ ray s, y ∈ X → y = h (circlePt s, 0) := by
    intro s y hy hyX
    obtain ⟨t, -, rfl⟩ := hrayt s y hy
    have ht : t = 0 := by
      by_contra hne
      exact hoff _ (unitInterval.pos_iff_ne_zero.mpr hne) hyX
    rw [ht]
  have hpt : ∀ {s₁' s₂' : ℝ}, s₁' ∈ Ico s₁ (s₁ + 1) → s₂' ∈ Ico s₁ (s₁ + 1) → s₁' ≠ s₂' →
      circlePt s₁' ≠ circlePt s₂' := fun h₁ h₂ hne he => hne (circlePt_injOn h₁ h₂ he)
  have h13 : s₁ < s₃ := h₁₂'.trans h₂₃'
  have h14 : s₁ < s₄ := h13.trans h₃₄'
  have hm₁ : s₁ ∈ Ico s₁ (s₁ + 1) := ⟨le_rfl, by linarith⟩
  have hm₂ : s₂ ∈ Ico s₁ (s₁ + 1) := ⟨h₁₂, by linarith⟩
  have hm₃ : s₃ ∈ Ico s₁ (s₁ + 1) := ⟨by linarith, by linarith⟩
  have hm₄ : s₄ ∈ Ico s₁ (s₁ + 1) := ⟨by linarith, h₄₁'⟩
  -- The set `X` with the part of the collar below height `ε`.
  obtain ⟨x₀, hx₀⟩ := hXp.nonempty
  let T : Circle → Set S := fun z => X ∪ (fun u : I => h (z, u)) '' Iio ε
  have hTp : ∀ z, IsPreconnected (T z) := by
    intro z
    refine hXp.isConnected.isPreconnected.union' ?_ ((isPreconnected_Iio).image _ (by fun_prop))
    exact ⟨h (z, 0), hbot z, 0, hε, rfl⟩
  have hW : IsPreconnected (⋃ z, T z) := isPreconnected_iUnion
    ⟨x₀, mem_iInter.mpr fun z => Or.inl hx₀⟩ hTp
  let J : Set S := range fun z : Circle => h (z, ε)
  have hWJ : Disjoint (⋃ z, T z) J := by
    refine disjoint_left.mpr ?_
    rintro _ hy ⟨z', rfl⟩
    obtain ⟨z, hy⟩ := mem_iUnion.mp hy
    change h (z', ε) ∈ T z at hy
    rcases hy with hy | ⟨u, hu, hue⟩
    · exact hoff _ hε hy
    · have hu' : u < ε := hu
      by_cases hu0 : u = 0
      · subst hu0
        refine hoff (z', ε) hε ?_
        have : h (z, 0) = h (z', ε) := hue
        rw [← this]
        exact hbot z
      · have := hinj (unitInterval.pos_iff_ne_zero.mpr hu0 : (0 : I) < u) hε hue
        exact hu'.ne (congrArg Prod.snd this)
  -- The sphere.
  have hsph := isSphere_onePoint hA
  obtain ⟨hS', hconn'⟩ := IsSphere.isClosedSurface hsph
  have hT2' : T2Space (OnePoint A) := hS'.2.1
  have hf : Continuous (collapse A) := continuous_collapse hA.1
  let f := collapse A
  have hinjA : InjOn f A := by
    intro x hx y hy he
    change collapse A x = collapse A y at he
    rw [collapse_of_mem hx, collapse_of_mem hy] at he
    exact congrArg Subtype.val (OnePoint.coe_injective he)
  let k : Circle → OnePoint A := fun z => f (h (z, ε))
  have hkc : Continuous k := hf.comp (by fun_prop)
  have hki : Function.Injective k := by
    intro z z' he
    have := hinj hε hε (hinjA (hlow z ε le_rfl) (hlow z' ε le_rfl) he)
    exact congrArg Prod.fst this
  have hkemb := (hkc.isClosedEmbedding hki).isEmbedding
  have hJ' : IsOArc (k '' univ) :=
    isOArc_image ⟨(Homeomorph.Set.univ Circle).symm⟩ hkc.continuousOn hki.injOn
  have hWA : (⋃ z, T z) ⊆ A := by
    refine iUnion_subset fun z => ?_
    rintro y (hy | ⟨u, hu, rfl⟩)
    · exact hXA hy
    · exact hlow z u (le_of_lt hu)
  have hJA : J ⊆ A := by
    rintro _ ⟨z, rfl⟩
    exact hlow z ε le_rfl
  have hdisf : Disjoint (f '' ⋃ z, T z) (k '' univ) := by
    refine disjoint_left.mpr ?_
    rintro _ ⟨y, hy, rfl⟩ ⟨z, -, he⟩
    have := hinjA (hJA ⟨z, rfl⟩) (hWA hy) he
    exact disjoint_left.mp hWJ hy ⟨z, this⟩
  obtain ⟨Δ, hΔ, hbΔ, hsubΔ⟩ := exists_disc_of_collar hS' hsph hJ' (hW.image f hf.continuousOn)
    hdisf
  have hJΔ : k '' univ ⊆ Δ := by
    rw [← hbΔ]
    exact discBd_subset Δ
  have hlowΔ : ∀ z, ∀ t : I, t ≤ ε → f (h (z, t)) ∈ Δ := by
    intro z t ht
    rcases eq_or_lt_of_le ht with rfl | hlt
    · exact hJΔ ⟨z, mem_univ _, rfl⟩
    · exact hsubΔ ⟨_, mem_iUnion.mpr ⟨z, Or.inr ⟨t, hlt, rfl⟩⟩, rfl⟩
  have hXΔ : ∀ y ∈ X, f y ∈ Δ := fun y hy => hsubΔ ⟨y, mem_iUnion.mpr ⟨Classical.arbitrary _,
    Or.inl hy⟩, rfl⟩
  let A₀ : Set S := P ∪ ray s₁ ∪ ray s₃
  let B₀ : Set S := Q ∪ ray s₂ ∪ ray s₄
  have hA₀ : IsPathConnected A₀ :=
    (hP.union (hrayp s₁) ⟨_, hP₁, hray₀ s₁⟩).union (hrayp s₃) ⟨_, Or.inl hP₃, hray₀ s₃⟩
  have hB₀ : IsPathConnected B₀ :=
    (hQ.union (hrayp s₂) ⟨_, hQ₂, hray₀ s₂⟩).union (hrayp s₄) ⟨_, Or.inl hQ₄, hray₀ s₄⟩
  have hrayΔ : ∀ s, ∀ y ∈ ray s, f y ∈ Δ := fun s y hy => by
    obtain ⟨t, ht, rfl⟩ := hrayt s y hy
    exact hlowΔ _ t ht
  have hrayA : ∀ s, ∀ y ∈ ray s, y ∈ A := fun s y hy => by
    obtain ⟨t, ht, rfl⟩ := hrayt s y hy
    exact hlow _ t ht
  have hA₀Δ : f '' A₀ ⊆ Δ := by
    rintro _ ⟨y, (((hy | hy) | hy)), rfl⟩
    · exact hXΔ y (hPX hy)
    · exact hrayΔ _ y hy
    · exact hrayΔ _ y hy
  have hB₀Δ : f '' B₀ ⊆ Δ := by
    rintro _ ⟨y, (((hy | hy) | hy)), rfl⟩
    · exact hXΔ y (hQX hy)
    · exact hrayΔ _ y hy
    · exact hrayΔ _ y hy
  have hA₀A : A₀ ⊆ A := by
    rintro y ((hy | hy) | hy)
    · exact hXA (hPX hy)
    · exact hrayA _ y hy
    · exact hrayA _ y hy
  have hB₀A : B₀ ⊆ A := by
    rintro y ((hy | hy) | hy)
    · exact hXA (hQX hy)
    · exact hrayA _ y hy
    · exact hrayA _ y hy
  have hcross := embedded_collar_pairs_cross hkemb hbΔ h₁₂' h₂₃' h₃₄' h₄₁'
  obtain ⟨y, ⟨p, hp, rfl⟩, ⟨q, hq, hpq⟩⟩ := disc_crossing.of_isPathConnected Δ (f '' A₀)
    (f '' B₀) _ _ _ _ hΔ
    hA₀Δ hB₀Δ (hA₀.image hf) (hB₀.image hf) ⟨_, Or.inl (Or.inr (hrayε s₁)), rfl⟩
    ⟨_, Or.inr (hrayε s₃), rfl⟩ ⟨_, Or.inl (Or.inr (hrayε s₂)), rfl⟩ ⟨_, Or.inr
      (hrayε s₄), rfl⟩ hcross
  obtain rfl : q = p := hinjA (hB₀A hq) (hA₀A hp) hpq
  have hP' : ∀ s, h (circlePt s, 0) ∈ P → q ∈ ray s → q ∈ Q → (P ∩ Q).Nonempty := fun s h₁ h₂ h₃ =>
    ⟨q, by rwa [hrayX s q h₂ (hQX h₃)], h₃⟩
  have hQ' : ∀ s, h (circlePt s, 0) ∈ Q → q ∈ ray s → q ∈ P → (P ∩ Q).Nonempty := fun s h₁ h₂ h₃ =>
    ⟨q, h₃, by rwa [hrayX s q h₂ (hPX h₃)]⟩
  have hRR : ∀ {s s' : ℝ}, h (circlePt s, 0) ∈ P → h (circlePt s', 0) ∈ Q
    → circlePt s ≠ circlePt s' →
      q ∈ ray s → q ∈ ray s' → (P ∩ Q).Nonempty := by
    intro s s' h₁ h₂ hne hs hs'
    obtain ⟨t, -, ht⟩ := hrayt s q hs
    obtain ⟨t', -, ht'⟩ := hrayt s' q hs'
    by_cases ht0 : t = 0
    · have hqX : q ∈ X := by
        rw [ht, ht0]
        exact hbot _
      exact ⟨q, by rwa [hrayX s q hs hqX], by rwa [hrayX s' q hs' hqX]⟩
    · have hpos : (0 : I) < t := unitInterval.pos_iff_ne_zero.mpr ht0
      by_cases ht'0 : t' = 0
      · refine (hoff (circlePt s, t) hpos ?_).elim
        rw [← ht, ht', ht'0]
        exact hbot _
      · have hpos' : (0 : I) < t' := unitInterval.pos_iff_ne_zero.mpr ht'0
        have := hinj hpos hpos' (ht.symm.trans ht')
        exact (hne (congrArg Prod.fst this)).elim
  rcases hp with (hp | hp) | hp <;> rcases hq with (hq | hq) | hq
  · exact ⟨q, hp, hq⟩
  · exact hQ' _ hQ₂ hq hp
  · exact hQ' _ hQ₄ hq hp
  · exact hP' _ hP₁ hp hq
  · exact hRR hP₁ hQ₂ (hpt hm₁ hm₂ h₁₂'.ne) hp hq
  · exact hRR hP₁ hQ₄ (hpt hm₁ hm₄ h14.ne) hp hq
  · exact hP' _ hP₃ hp hq
  · exact hRR hP₃ hQ₂ (hpt hm₃ hm₂ h₂₃'.ne') hp hq
  · exact hRR hP₃ hQ₄ (hpt hm₃ hm₄ h₃₄'.ne) hp hq

end GraphMinor.GM11
