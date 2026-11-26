/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CuffCore

/-!
# An `O`-arc through a vertex of a cuff

Graph Minors VII, (5.9), page 237: the second half of claim (b). An `O`-arc through a vertex of the
cuff `C` that has few other vertices stays near `C`, and it must go through every vertex of `G` on
`C`, or else it is null-homotopic.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function Metric GraphMinor.Surface GraphMinor.GM11

universe u

variable {S T : Type u} [TopologicalSpace S] [TopologicalSpace T]

/-- A connected set with a point inside a disc and a point off the disc meets the boundary of the
disc. -/
theorem exists_mem_discBd_of_preconnected [T2Space T] (hman : ∀ x : T, IsManifoldPoint x) {E Z :
  Set T} (hE : IsClosedDisc E) (hZ : IsPreconnected Z) {p q : T} (hp : p ∈ Z) (hpi : p ∈ discInt E)
    (hq : q ∈ Z) (hqo : q ∉ E) : ∃ z ∈ Z, z ∈ discBd E := by
  by_contra hn
  push Not at hn
  rcases hE.side hman hZ (disjoint_left.mpr hn) with h1 | h1
  · exact hqo (h1 hq).1
  · exact disjoint_left.mp h1 hp hpi.1

/-- An `O`-arc with a point inside a disc and a point off the disc meets the boundary of the disc at
two points at least. -/
theorem exists_two_crossings [T2Space S] [T2Space T] (hman : ∀ x : T, IsManifoldPoint x) {j : S
  → T} (hj : Continuous j) {B : Set S} (hO : IsOArc B) {E : Set T} (hE : IsClosedDisc E) {x y : S}
    (hx : x ∈ B) (hy : y ∈ B) (hxi : j x ∈ discInt E) (hyo : j y ∉ E) : ∃ p ∈ B, ∃ p' ∈ B, p ≠ p'
      ∧ j p ∈ discBd E ∧ j p' ∈ discBd E := by
  have hne : x ≠ y := fun h => hyo (h ▸ hxi.1)
  obtain ⟨A₁, A₂, h1, h2, hu, hi⟩ := hO.lines hx hy hne
  have hc : ∀ {A : Set S}, IsLineWithEnds A x y → ∃ p ∈ A, j p ∈ discBd E := fun {A} hA => by
    obtain ⟨z, ⟨p, hp, rfl⟩, hz⟩ := exists_mem_discBd_of_preconnected hman hE
      ((GM12.line_conn hA).image j hj.continuousOn) (mem_image_of_mem j hA.left_mem) hxi
        (mem_image_of_mem j hA.right_mem) hyo
    exact ⟨p, hp, hz⟩
  obtain ⟨p, hp, hpb⟩ := hc h1
  obtain ⟨p', hp', hpb'⟩ := hc h2
  refine ⟨p, hu ▸ .inl hp, p', hu ▸ .inr hp', fun he => ?_, hpb, hpb'⟩
  have h3 : p ∈ A₁ ∩ A₂ := ⟨hp, he ▸ hp'⟩
  rw [hi] at h3
  rcases h3 with rfl | h3
  · exact hxi.2 hpb
  · have h4 : p = y := h3
    subst h4
    exact hyo (Surface.discBd_subset _ hpb)

variable {G : Drawing S} {C : Set S} {j : S → T} {D : Set T} {r v ks m : ℕ} {Y E₀ Δ' Do : Set T}
  {Nk Bo : Drawing S} {R : Fin ks → Drawing S} {x t : Fin ks → S} {Q : ∀ i, GraphWalk G.toGraph
    (x i) (t i)} {L : Fin m → Drawing S} {El : Fin m → Set T}

/-- The first step: an `O`-arc through a vertex of `C` stays in the disc `Y`, since otherwise it
would cross each of the circuits `L i` twice. -/
theorem IsCuffCore.oArc_in_Y (h : IsCuffCore G C j D r v Y E₀ Δ' Do Nk Bo R x t Q L El) [T2Space S]
  [T2Space T] (hman : ∀ x : T, IsManifoldPoint x) (hj : Continuous j) (hji : Injective j)
    (hCD : ∀ z ∈ C, j z ∈ D) {ρ : S → S} {A B : Set S} (hnorm : ∀ z ∈ A, ρ z ∈ B → z ∈ G.U
      → z ∈ G.V) (hcount : ∀ Z : Set S, Z ⊆ A ∩ G.V → ρ '' Z ⊆ B → Z.ncard < v)
        (hid : ∀ z, j z ∈ Do → j z ∉ Δ' → z ∈ G.U → z ∈ A ∧ ρ z = z) (hO : IsOArc B) {x₀ : S}
          (hx₀ : x₀ ∈ B) (hx₀C : x₀ ∈ C) : ∀ y ∈ B, j y ∈ Y := by
  classical
  intro y₀ hy₀
  by_contra hyY
  have hcross := fun i => exists_two_crossings hman hj hO (h.layerDisc i) hx₀ hy₀ (h.layerIn i
    (hCD x₀ hx₀C)) (fun h1 => hyY (h.layerY i h1))
  choose p hp p' hp' hne hb hb' using hcross
  have hprop : ∀ i (z : S), z ∈ B → j z ∈ discBd (El i) → z ∈ A ∩ (L i).V ∧ ρ z = z
    := fun i z hz hzb => by
    have hzU : z ∈ (L i).U := by
      have h1 := hzb
      rw [h.layerBd i] at h1
      obtain ⟨z', hz', he⟩ := h1
      exact hji he ▸ hz'
    have hzG : z ∈ G.U := (h.layerSub i).U_subset hzU
    have hin : j z ∈ Y := h.layerY i (Surface.discBd_subset _ hzb)
    obtain ⟨h1, h2⟩ := hid z (h.YO hin) (fun h3 => disjoint_left.mp (h.layerOff i) h3 hzb) hzG
    have hV := hnorm z h1 (by rw [h2]; exact hz) hzG
    exact ⟨⟨h1, mem_V_of_subdrawing (h.layerSub i) hzU hV⟩, h2⟩
  let f : Fin m × Bool → S := fun q => if q.2 then p q.1 else p' q.1
  have hfp : ∀ q, f q ∈ B ∧ j (f q) ∈ discBd (El q.1) := fun q => by
    rcases q with ⟨i, _ | _⟩
    · exact ⟨hp' i, hb' i⟩
    · exact ⟨hp i, hb i⟩
  have hfinj : Injective f := by
    rintro ⟨i, b⟩ ⟨i', b'⟩ he
    have h1 := (hprop i _ (hfp (i, b)).1 (hfp (i, b)).2).1.2
    have h2 := (hprop i' _ (hfp (i', b')).1 (hfp (i', b')).2).1.2
    by_cases hii : i = i'
    · subst hii
      rcases b with _ | _ <;> rcases b' with _ | _
      · rfl
      · exact absurd he.symm (hne i)
      · exact absurd he (hne i)
      · rfl
    · have h3 : f (i, b) ∈ (L i').V := he ▸ h2
      exact absurd h3 (disjoint_left.mp (h.layerDis i i' hii) h1)
  have hZ := hcount (range f) (by
    rintro _ ⟨q, rfl⟩
    obtain ⟨h1, -⟩ := hprop q.1 _ (hfp q).1 (hfp q).2
    exact ⟨h1.1, (h.layerSub q.1).1 h1.2⟩) (by
    rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
    rw [(hprop q.1 _ (hfp q).1 (hfp q).2).2]
    exact (hfp q).1)
  have hcard : (range f).ncard = 2 * m := by
    rw [← image_univ, hfinj.injOn.ncard_image, ncard_univ]
    simp [Nat.card_eq_fintype_card, mul_comm]
  have := h.mv
  omega

/-- The second step, the part of the paper's proof with the paths past `N_i(C)`. If `B` bounds a
disc `Δ_B` of `T` in `Y` around `D`, then `B` goes through every vertex of `G` on `C`. Otherwise the
images of the `v` paths past the piece `N_i(C)` give `v` vertices of `B`. -/
theorem IsCuffCore.oArc_all_vertices (h : IsCuffCore G C j D r v Y E₀ Δ' Do Nk Bo R x t Q L El)
  [T2Space T] (hman : ∀ x : T, IsManifoldPoint x) (hj : Continuous j)
    (hji : Injective j) (hCD : ∀ z ∈ C, j z ∈ D) {ρ : S → S} {A B : Set S} (hρ : Continuous ρ)
      (htree : ∀ i, ∀ a ∈ (R i).U, ρ a = x i) (hnorm : ∀ z ∈ A, ρ z ∈ B → z ∈ G.U → z ∈ G.V)
        (hcount : ∀ Z : Set S, Z ⊆ A ∩ G.V → ρ '' Z ⊆ B → Z.ncard < v) (hab : ∀ z, j z ∈ Do
          → j z ∉ E₀ → z ∈ G.U → z ∈ A) (hid : ∀ z, j z ∈ Do → j z ∉ Δ' → z ∈ G.U → z ∈ A ∧ ρ z
            = z) (hx : ∀ y ∈ G.V ∩ C, ∃ i, x i = y) {Δ_B : Set T} (hΔ : IsClosedDisc Δ_B)
              (hbd : discBd Δ_B = j '' B) (hsub : Δ_B ⊆ Y) (hDB : D ⊆ Δ_B) : G.V ∩ C ⊆ B := by
  classical
  intro y hy
  by_contra hyB
  obtain ⟨i, rfl⟩ := hx y hy
  obtain ⟨Γ, w, y', hgate, hdis⟩ := h.gates i
  have hcross : ∀ a, ∃ z ∈ Γ a, z ≠ w a ∧ ρ z ∈ B := fun a => by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hgate a
    have hrw : ρ (w a) = x i := htree i _ ((R i).V_subset_U h5)
    obtain ⟨hA', hρy⟩ := hid (y' a) h7 (fun h9 => h6 (h.ΔY h9)) (h2 h4)
    have hconn : IsPreconnected ((j ∘ ρ) '' Γ a) := h1.image _ (hj.comp hρ).continuousOn
    have hint : j (x i) ∈ discInt Δ_B := by
      refine ⟨hDB (hCD _ hy.2), fun hb => ?_⟩
      rw [hbd] at hb
      obtain ⟨z, hz, he⟩ := hb
      exact hyB (hji he ▸ hz)
    obtain ⟨_, ⟨z, hz, rfl⟩, hzb⟩ := exists_mem_discBd_of_preconnected hman hΔ hconn
      (mem_image_of_mem _ h3 : (j ∘ ρ) (w a) ∈ _) (by simpa [hrw] using hint)
        (mem_image_of_mem _ h4 : (j ∘ ρ) (y' a) ∈ _) (by
      simp only [comp_apply, hρy]
      exact fun h9 => h6 (hsub h9))
    rw [hbd] at hzb
    obtain ⟨b, hb, he⟩ := hzb
    have hzB : ρ z ∈ B := hji he ▸ hb
    refine ⟨z, hz, fun he' => ?_, hzB⟩
    rw [he', hrw] at hzB
    exact hyB hzB
  choose z hz hzw hzB using hcross
  have hzA : ∀ a, z a ∈ A ∩ G.V := fun a => by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hgate a
    obtain ⟨h9, h10⟩ := h8 (z a) (hz a) (hzw a)
    have h11 := hab _ h10 h9 (h2 (hz a))
    exact ⟨h11, hnorm _ h11 (hzB a) (h2 (hz a))⟩
  have hinj : Injective z := fun a a' he => by
    by_contra hne
    have h1 : z a ∈ G.V ∩ Γ a' := by
      rw [he]
      exact ⟨(hzA a').2, hz a'⟩
    exact disjoint_left.mp (hdis a a' hne) ⟨(hzA a).2, hz a⟩ h1
  have hZ := hcount (range z) (by
    rintro _ ⟨a, rfl⟩
    exact hzA a) (by
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact hzB a)
  have hcard : (range z).ncard = v := by
    rw [← image_univ, hinj.injOn.ncard_image, ncard_univ]
    simp [Nat.card_eq_fintype_card]
  omega

/-- **The `O`-arc through a vertex of a cuff.** This is the case `L > 0` of claim (b) of the proof
of (5.9). -/
theorem IsCuffCore.touch (h : IsCuffCore G C j D r v Y E₀ Δ' Do Nk Bo R x t Q L El)
  (hS : IsSurface S) [ConnectedSpace S] (hc : IsCappedCuff C T j D) (hns : ¬ IsSphere T) {ρ : S
    → S} {A B : Set S} (hρ : Continuous ρ) (htree : ∀ i, ∀ a ∈ (R i).U, ρ a = x i)
      (hnorm : ∀ z ∈ A, ρ z ∈ B → z ∈ G.U → z ∈ G.V) (hcount : ∀ Z : Set S, Z ⊆ A ∩ G.V
        → ρ '' Z ⊆ B → Z.ncard < v) (hab : ∀ z, j z ∈ Do → j z ∉ E₀ → z ∈ G.U → z ∈ A)
          (hid : ∀ z, j z ∈ Do → j z ∉ Δ' → z ∈ G.U → z ∈ A ∧ ρ z = z)
            (hx : ∀ y ∈ G.V ∩ C, ∃ i, x i = y) (hO : IsOArc B) (hne : (B ∩
              (G.V ∩ C)).Nonempty) : IsNullHomotopicOArc B ∨ (IsNullHomotopicOArcInCappedCuff C B
                ∧ G.V ∩ C ⊆ B) := by
  classical
  have hT := hc.isSurface
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have : T2Space T := hT.2.1
  have : ConnectedSpace T := hc.connectedSpace hS
  have hman := hT.2.2
  have hcont := hc.isEmbedding.continuous
  have hji := hc.isEmbedding.injective
  have hCD : ∀ z ∈ C, j z ∈ D := fun z hz => Surface.discBd_subset D (hc.discBd_eq ▸
    mem_image_of_mem j hz)
  obtain ⟨x₀, hx₀, hx₀V⟩ := hne
  have hin := h.oArc_in_Y hman hcont hji hCD hnorm hcount hid hO hx₀ hx₀V.2
  have hO' : IsOArc (j '' B) := by
    obtain ⟨f⟩ := id hO
    exact ⟨f.trans (hc.isEmbedding.homeomorphImage B)⟩
  have hplY : IsPlanar (j '' B) := ⟨Y, h.discY, by
    rintro _ ⟨z, hz, rfl⟩
    exact hin z hz⟩
  have hnull := (isPlanar_iff_isNullHomotopicOArc_of_isOArc hT hO').mp hplY
  obtain ⟨Δ_B, hΔ, hbd⟩ := nullHomotopicOArc_bounds_disc hT hO' hnull
  have hsub : Δ_B ⊆ Y := disc_subset_of_bd_subset hT hns h.discY hΔ (by
    rw [hbd]
    rintro _ ⟨z, hz, rfl⟩
    exact hin z hz)
  by_cases hDB : D ⊆ Δ_B
  · refine .inr ⟨?_, h.oArc_all_vertices hman hcont hji hCD hρ htree hnorm hcount hab hid hx hΔ hbd
      hsub hDB⟩
    have hP : IsPlanarInCappedCuff C B := isPlanarInCappedCuff_of_cap hS hc hplY
    refine ⟨hc.cuff, hO, fun S' _ j' D' hcap => ?_⟩
    have hO'' : IsOArc (j' '' B) := by
      obtain ⟨f⟩ := id hO
      exact ⟨f.trans (hcap.isEmbedding.homeomorphImage B)⟩
    exact (isPlanar_iff_isNullHomotopicOArc_of_isOArc hcap.isSurface hO'').mp (hP.2.2 S' j' D' hcap)
  · have hoff : Disjoint (discInt D) (discBd Δ_B) := by
      rw [hbd, disjoint_left]
      rintro _ h1 ⟨y, -, rfl⟩
      exact not_mem_discInt_cap hc y h1
    have hdis : ∀ z ∈ Δ_B, z ∉ discInt D := fun z hz hi => hDB (disc_subset_of_int_off_bd hman
      hc.isClosedDisc hΔ hoff ⟨z, hi, hz⟩)
    have hr : Δ_B ⊆ range j := fun z hz => by
      by_contra hzr
      rcases hc.union_eq.ge (mem_univ z) with h1 | h1
      · exact hzr h1
      · refine hdis z hz ⟨h1, fun hb => hzr ?_⟩
        rw [hc.discBd_eq] at hb
        exact image_subset_range _ _ hb
    have hdisc := isClosedDisc_preimage_of_subset_range hcont hji hΔ hr
    have hpl : IsPlanar B := ⟨_, hdisc, fun z hz => by
      have h1 : j z ∈ discBd Δ_B := hbd ▸ mem_image_of_mem j hz
      exact Surface.discBd_subset Δ_B h1⟩
    exact .inl ((isPlanar_iff_isNullHomotopicOArc_of_isOArc hS hO).mp hpl)

end GraphMinor.GM07
