/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FreeFrame
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import LeanPool.GraphMinor.GM19.FragmentForm

/-!
# The fragment outside a closed disc

Let `Z` be a closed disc of `Σ̂` whose boundary holds `K`. We show that the fragment outside `Z`
meets the fibre of `ψ` in at most one
point (`injOn_of_outside`). The reason is local. Near a point of the boundary of `Z`, the outside of
`Z` is connected, so all points
of the fragment near that point lie near one lift of it.

If the fragment has as many cuffs as `Σ`, then it is a copy of `Σ`, by the classification of
surfaces (`nonempty_homeomorph_of_cap`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Metric GraphMinor.Surface

variable {T : Type} [TopologicalSpace T] [T2Space T]

/-- The rectangle of polar coordinates around a point `ζ` of the unit circle. -/
noncomputable def polarBox (ζ : ℂ) (r₁ r₂ δ : ℝ) : Set ℂ := (fun p : ℝ × ℝ ↦ ζ *
  Complex.polarCoord.symm p) '' (Ioo r₁ r₂ ×ˢ Ioo (-δ) δ)

theorem norm_polar_mul {ζ : ℂ} (hζ : ‖ζ‖ = 1) {p : ℝ × ℝ} (hp : 0 ≤ p.1) : ‖ζ *
  Complex.polarCoord.symm p‖ = p.1 := by
  rw [norm_mul, hζ, one_mul, Complex.polarCoord_symm_apply, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hp]
  have : ((Real.cos p.2 : ℝ) : ℂ) + (Real.sin p.2 : ℝ) * Complex.I = Complex.exp (p.2 * Complex.I)
    := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [this, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem isOpen_polarBox {ζ : ℂ} (hζ : ‖ζ‖ = 1) {r₁ r₂ δ : ℝ} (h₁ : 0 ≤ r₁) (hδ : δ
  ≤ Real.pi) : IsOpen (polarBox ζ r₁ r₂ δ) := by
  have hne : ζ ≠ 0 := by
    intro h
    simp [h] at hζ
  have hO : IsOpen (Complex.polarCoord.symm '' (Ioo r₁ r₂ ×ˢ Ioo (-δ) δ)) := by
    refine Complex.polarCoord.symm.isOpen_image_of_subset_source (isOpen_Ioo.prod isOpen_Ioo) ?_
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    rw [OpenPartialHomeomorph.symm_source, Complex.polarCoord_target]
    exact ⟨lt_of_le_of_lt h₁ hr.1, by simpa using ⟨by linarith [hθ.1], by linarith [hθ.2]⟩⟩
  have : polarBox ζ r₁ r₂ δ = (Homeomorph.mulLeft₀ ζ hne) '' (Complex.polarCoord.symm ''
    (Ioo r₁ r₂ ×ˢ Ioo (-δ) δ)) := by
    rw [polarBox, image_image]
    rfl
  rw [this]
  exact (Homeomorph.mulLeft₀ ζ hne).isOpenMap _ hO

/-- **A neighbourhood of a boundary point whose outside part is connected.** -/
theorem exists_nhd_outside (hT : IsClosedSurface T) {Z W : Set T} (hZ : IsClosedDisc Z) {p : T}
  (hp : p ∈ discBd Z) (hW : IsOpen W)
    (hpW : p ∈ W) : ∃ O, IsOpen O ∧ p ∈ O ∧ O ⊆ W ∧ IsPreconnected (O \ Z) := by
  classical
  have hman : ∀ x : T, IsManifoldPoint x := fun x ↦ (hT.2.2 x).isManifoldPoint
  obtain ⟨Δ', hΔ', hin, -⟩ := Surface.exists_disc_around hman hZ (fun x _ ↦ hT.2.2 x) isOpen_univ
    (subset_univ _)
  obtain ⟨φ⟩ := hZ.isOArc_discBd
  obtain ⟨c, c', hcc, hc'c, hcm, hc'm, hl, hr, hcZ, hcb, hcφ⟩ := exists_disc_collar hZ hΔ' hin φ
  obtain ⟨w, hw⟩ := φ.surjective ⟨p, hp⟩
  set ζ : ℂ := (w : ℂ) with hζdef
  have hζ : ‖ζ‖ = 1 := Circle.norm_coe w
  have hcζ : c ζ = p := by rw [hζdef, hcφ w, hw]
  have hζB : ζ ∈ ball (0 : ℂ) 2 := by
    rw [mem_ball_zero_iff, hζ]
    norm_num
  have hcat : ContinuousAt c ζ := hcc.continuousAt (Filter.mem_of_superset (ball_mem_nhds _
    (by norm_num : (0 : ℝ) < 2 - 1)) (fun z hz ↦ by
    rw [mem_closedBall_zero_iff]
    have h₀ : dist z ζ < 2 - 1 := hz
    have h₁ : ‖z - ζ‖ < 1 := by
      rw [dist_eq_norm] at h₀
      linarith
    have h₂ := norm_add_le (z - ζ) ζ
    rw [sub_add_cancel, hζ] at h₂
    linarith))
  have hwn : c ⁻¹' W ∈ 𝓝 ζ := hcat.preimage_mem_nhds (by rw [hcζ]; exact hW.mem_nhds hpW)
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.1 hwn
  let Q : ℝ × ℝ → ℂ := fun q ↦ ζ * Complex.polarCoord.symm q
  have hQc : Continuous Q := continuous_const.mul (by
    have : (Complex.polarCoord.symm : ℝ × ℝ → ℂ) = fun q ↦ (q.1 : ℂ) * ((Real.cos q.2 : ℝ) +
      (Real.sin q.2 : ℝ) * Complex.I) := by
      ext q
      exact Complex.polarCoord_symm_apply q
    rw [this]
    fun_prop)
  have hQ1 : Q (1, 0) = ζ := by
    change ζ * Complex.polarCoord.symm (1, 0) = ζ
    rw [Complex.polarCoord_symm_apply]
    simp
  have hbop : IsOpen (Q ⁻¹' ball ζ ε) := isOpen_ball.preimage hQc
  have hQmem : (1, 0) ∈ Q ⁻¹' ball ζ ε := by
    rw [mem_preimage, hQ1]
    exact mem_ball_self hε
  obtain ⟨δ₀, hδ₀, hδs⟩ := Metric.isOpen_iff.1 hbop (1, 0) hQmem
  obtain ⟨δ, hδ, hδ₁, hδ₂⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ δ ≤ 1 / 2 := ⟨min δ₀ (1 / 2), lt_min hδ₀
    (by norm_num), min_le_left _ _, min_le_right _ _⟩
  have hpi := Real.pi_gt_three
  have hnorm : ∀ {r θ : ℝ}, 0 ≤ r → ‖Q (r, θ)‖ = r := fun {r θ} h ↦ norm_polar_mul hζ (p :=
    (r, θ)) h
  have hbox : polarBox ζ (1 - δ) (1 + δ) δ ⊆ ball ζ ε ∩ ball 0 2 := by
    rintro _ ⟨⟨r, θ⟩, ⟨hr, hθ⟩, rfl⟩
    have h0 : 0 ≤ r := by linarith [hr.1]
    refine ⟨hδs ?_, ?_⟩
    · rw [mem_ball, Prod.dist_eq, max_lt_iff]
      refine ⟨?_, ?_⟩
      · change |r - 1| < δ₀
        rw [abs_lt]
        constructor <;> linarith [hr.1, hr.2]
      · change |θ - 0| < δ₀
        rw [sub_zero, abs_lt]
        constructor <;> linarith [hθ.1, hθ.2]
    · rw [mem_ball_zero_iff]
      refine lt_of_eq_of_lt (hnorm h0) ?_
      linarith [hr.2]
  have hboxo : IsOpen (polarBox ζ (1 - δ) (1 + δ) δ) := isOpen_polarBox hζ (by linarith)
    (by linarith)
  have hball : ball (0 : ℂ) 2 ⊆ closedBall 0 2 := ball_subset_closedBall
  have hinjc : InjOn c (closedBall 0 2) := hl.injOn
  have hIm : c '' ball 0 2 = discInt Δ' := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      refine ⟨hcm (hball hz), fun hb ↦ ?_⟩
      rw [← hcb] at hb
      obtain ⟨u, hu, he⟩ := hb
      have := hinjc (sphere_subset_closedBall hu) (hball hz) he
      rw [this, mem_sphere_zero_iff_norm] at hu
      rw [mem_ball_zero_iff, hu] at hz
      exact lt_irrefl _ hz
    · rintro x ⟨hx, hb⟩
      refine ⟨c' x, ?_, hr hx⟩
      have hm := hc'm hx
      rw [mem_closedBall_zero_iff] at hm
      rw [mem_ball_zero_iff]
      refine lt_of_le_of_ne hm fun he ↦ hb ?_
      rw [← hcb]
      exact ⟨c' x, by rw [mem_sphere_zero_iff_norm, he], hr hx⟩
  have hopen : IsOpen (c '' polarBox ζ (1 - δ) (1 + δ) δ) := by
    have hDo : IsOpen (discInt Δ') := hΔ'.isOpen_discInt hman
    have heq : c '' polarBox ζ (1 - δ) (1 + δ) δ = discInt Δ' ∩ c' ⁻¹' polarBox ζ (1 - δ) (1 + δ) δ
      := by
      apply Subset.antisymm
      · rintro _ ⟨z, hz, rfl⟩
        have hzb := (hbox hz).2
        refine ⟨hIm ▸ mem_image_of_mem c hzb, ?_⟩
        rw [mem_preimage, hl (hball hzb)]
        exact hz
      · rintro x ⟨hx, hx'⟩
        exact ⟨c' x, hx', hr (discInt_subset _ hx)⟩
    rw [heq]
    exact (hc'c.mono (discInt_subset _)).isOpen_inter_preimage hDo hboxo
  refine ⟨_, hopen, ⟨ζ, ⟨(1, 0), ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, hQ1⟩,
    hcζ⟩, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hεs (hbox hz).1
  · have heq : c '' polarBox ζ (1 - δ) (1 + δ) δ \ Z = c '' polarBox ζ 1 (1 + δ) δ := by
      apply Subset.antisymm
      · rintro _ ⟨⟨z, ⟨⟨r, θ⟩, ⟨hr, hθ⟩, rfl⟩, rfl⟩, hn⟩
        have h0 : 0 ≤ r := by linarith [hr.1]
        refine mem_image_of_mem c ⟨(r, θ), ⟨⟨?_, hr.2⟩, hθ⟩, rfl⟩
        by_contra hle
        refine hn (hcZ ▸ mem_image_of_mem c ?_)
        change Q (r, θ) ∈ _
        rw [mem_closedBall_zero_iff, hnorm h0]
        exact not_lt.1 hle
      · rintro _ ⟨z, ⟨⟨r, θ⟩, ⟨hr, hθ⟩, rfl⟩, rfl⟩
        have h0 : 0 ≤ r := by linarith [hr.1]
        have hz : Q (r, θ) ∈ polarBox ζ (1 - δ) (1 + δ) δ := ⟨(r, θ), ⟨⟨by linarith [hr.1], hr.2⟩,
          hθ⟩, rfl⟩
        refine ⟨mem_image_of_mem c hz, fun hin' ↦ ?_⟩
        rw [← hcZ] at hin'
        obtain ⟨u, hu, he⟩ := hin'
        have := hinjc (closedBall_subset_closedBall (by norm_num) hu) (hball (hbox hz).2) he
        rw [mem_closedBall_zero_iff, this] at hu
        change ‖Q (r, θ)‖ ≤ 1 at hu
        rw [hnorm h0] at hu
        linarith [hr.1]
    rw [heq]
    have hcon : IsPreconnected (polarBox ζ 1 (1 + δ) δ) :=
      ((convex_Ioo _ _).prod (convex_Ioo _ _)).isPreconnected.image _ hQc.continuousOn
    refine hcon.image _ (hcc.mono ?_)
    rintro _ ⟨⟨r, θ⟩, ⟨hr, hθ⟩, rfl⟩
    exact hball (hbox ⟨(r, θ), ⟨⟨by linarith [hr.1], hr.2⟩, hθ⟩, rfl⟩).2

/-- **One side of a chord of `E` lies inside `Δ`, and the other misses `Δ`.** Here `Δ` is a closed
disc whose boundary holds the chord `β`, and whose boundary
meets the inside of `E` only in `β`. -/
theorem exists_chord_side (hT : IsClosedSurface T) {Δ E β : Set T}
  (hΔ : IsClosedDisc Δ) (hE : IsClosedDisc E) {s t : T} (hst : s ≠ t)
    (hl : IsLineWithEnds β s t) (hβΔ : β ⊆ discBd Δ) (hβE : β ⊆ E) (hmeet : β ∩ discBd E = {s, t})
      (hoff : discInt E ∩ discBd Δ ⊆ β) :
    ∃ A A' D D' : Set T, IsClosedDisc D ∧ IsClosedDisc D' ∧ D ∪ D' = E ∧ D ∩ D' = β ∧ discBd D
      = A ∪ β ∧ discBd D' = A' ∪ β ∧ A ⊆ discBd E \ {s, t} ∧
      A' ⊆ discBd E \ {s, t} ∧ discBd E \ {s, t} ⊆ A ∪ A' ∧ IsPreconnected A'
        ∧ discInt D ⊆ discInt Δ ∧ Disjoint (discInt D') Δ ∧ discInt D ⊆ discInt E \ β ∧
      discInt D' ⊆ discInt E \ β ∧ discInt E \ β ⊆ discInt D ∪ discInt D' := by
  classical
  have hman : ∀ x : T, IsManifoldPoint x := fun x ↦ (hT.2.2 x).isManifoldPoint
  have hsβ : s ∈ β := by
    have : s ∈ β ∩ discBd E := by rw [hmeet]; exact mem_insert _ _
    exact this.1
  have htβ : t ∈ β := by
    have : t ∈ β ∩ discBd E := by rw [hmeet]; exact mem_insert_of_mem _ rfl
    exact this.1
  obtain ⟨A, A', D, D', hAne, hcomp, hD, hD', hun, hint, hbd, hbd', hcomp'⟩
    := disc_iArc E β s t hE hβE hst hl hmeet
  have hmemc : ∀ {B}, B ∈ componentsIn (discBd E \ {s, t}) → B ⊆ discBd E \ {s, t} := by
    rintro _ ⟨x, -, rfl⟩
    exact connectedComponentIn_subset _ _
  have hpc : ∀ {B}, B ∈ componentsIn (discBd E \ {s, t}) → IsPreconnected B := by
    rintro _ ⟨x, -, rfl⟩
    exact isPreconnected_connectedComponentIn
  have hA₀ : A ∈ componentsIn (discBd E \ {s, t}) := by rw [hcomp]; exact mem_insert _ _
  have hA₁ : A' ∈ componentsIn (discBd E \ {s, t}) := by rw [hcomp]; exact mem_insert_of_mem _ rfl
  have hAs := hmemc hA₀
  have hAs' := hmemc hA₁
  have hcov : discBd E \ {s, t} ⊆ A ∪ A' := by
    intro x hx
    have : connectedComponentIn (discBd E \ {s, t}) x ∈ componentsIn (discBd E \ {s, t})
      := mem_image_of_mem _ hx
    rw [hcomp] at this
    have hm := mem_connectedComponentIn hx
    rcases this with h | h
    · exact Or.inl (h ▸ hm)
    · exact Or.inr ((mem_singleton_iff.1 h) ▸ hm)
  have hoffβ : ∀ {x}, x ∈ discBd E \ {s, t} → x ∉ β := fun {x} hx hxβ ↦ hx.2 (hmeet ▸ ⟨hxβ, hx.1⟩)
  have hEopen : IsOpen (discInt E) := hE.isOpen_discInt hman
  -- The inside of each half lies in the inside of `E`, off `β`.
  have hinner : ∀ {D D' A A' : Set T}, D ∩ D' = β → discBd D = A ∪ β → discBd D' = A' ∪ β
    → A ⊆ discBd E \ {s, t} → D ⊆ E →
      discBd E \ {s, t} ⊆ A ∪ A' → IsClosedDisc D' → discInt D ⊆ discInt E \ β := by
    intro D D' A A' hint hbd hbd' hAs hDE hcov hD' y hy
    have hyβ : y ∉ β := fun h ↦ hy.2 (hbd ▸ Or.inr h)
    refine ⟨⟨hDE hy.1, fun hb ↦ ?_⟩, hyβ⟩
    have hyn : y ∉ ({s, t} : Set T) := by
      rintro (h | h)
      · exact hyβ (h ▸ hsβ)
      · exact hyβ ((mem_singleton_iff.1 h) ▸ htβ)
    rcases hcov ⟨hb, hyn⟩ with h | h
    · exact hy.2 (hbd ▸ Or.inl h)
    · have : y ∈ D' := Surface.discBd_subset _ (hbd' ▸ Or.inl h)
      exact hyβ (hint ▸ ⟨hy.1, this⟩)
  have hcover : ∀ {D D' A A' : Set T}, D ∪ D' = E → discBd D = A ∪ β → discBd D' = A' ∪ β
    → A ⊆ discBd E \ {s, t} →
      A' ⊆ discBd E \ {s, t} → discInt E \ β ⊆ discInt D ∪ discInt D' := by
    intro D D' A A' hun hbd hbd' hAs hAs' y hy
    have hy' : y ∈ D ∪ D' := hun ▸ hy.1.1
    rcases hy' with h | h
    · refine Or.inl ⟨h, fun hb ↦ ?_⟩
      rw [hbd] at hb
      rcases hb with h' | h'
      · exact hy.1.2 (hAs h').1
      · exact hy.2 h'
    · refine Or.inr ⟨h, fun hb ↦ ?_⟩
      rw [hbd'] at hb
      rcases hb with h' | h'
      · exact hy.1.2 (hAs' h').1
      · exact hy.2 h'
  have hDE : D ⊆ E := hun ▸ subset_union_left
  have hDE' : D' ⊆ E := hun ▸ subset_union_right
  have hint' : D' ∩ D = β := by rw [inter_comm, hint]
  have hi₁ := hinner hint hbd hbd' hAs hDE hcov hD'
  have hi₂ := hinner hint' hbd' hbd hAs' hDE' (by rw [union_comm]; exact hcov) hD
  have hbdj : ∀ {X}, X ⊆ discInt E \ β → Disjoint X (discBd Δ) := fun hX ↦
    disjoint_left.2 fun x hx hb ↦ (hX hx).2 (hoff ⟨(hX hx).1, hb⟩)
  obtain ⟨f, hf0, hf1⟩ := hl
  let b : T := (f (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval)).1
  have hbβ : b ∈ β := (f _).2
  have hb_ne : ∀ {r : unitInterval}, r ≠ ⟨1 / 2, by norm_num, by norm_num⟩ → (f r).1 ≠ b
    := fun hr he ↦ hr (f.injective (Subtype.ext he))
  have hbs : b ≠ s := fun he ↦ hb_ne (r := 0) (fun h ↦ by have := congrArg Subtype.val h; norm_num
    at this) (hf0.trans he.symm)
  have hbt : b ≠ t := fun he ↦ hb_ne (r := 1) (fun h ↦ by have := congrArg Subtype.val h; norm_num
    at this) (hf1.trans he.symm)
  have hbE : b ∈ discInt E := ⟨hβE hbβ, fun hb' ↦ by
    have : b ∈ ({s, t} : Set T) := hmeet ▸ ⟨hbβ, hb'⟩
    rcases this with h | h
    · exact hbs h
    · exact hbt h⟩
  rcases hΔ.side hman hD.isPreconnected_discInt (hbdj hi₁) with h₁ | h₁ <;>
    rcases hΔ.side hman hD'.isPreconnected_discInt (hbdj hi₂) with h₂ | h₂
  · exfalso
    have hsub : E ⊆ Δ := by
      rw [← hun, ← closure_discInt hD, ← closure_discInt hD']
      exact union_subset (closure_minimal (h₁.trans (discInt_subset Δ)) hΔ.isClosed)
        (closure_minimal (h₂.trans (discInt_subset Δ)) hΔ.isClosed)
    have := subset_discInt_of_isOpen (fun y _ ↦ hT.2.2 y) hEopen ((discInt_subset E).trans hsub) hbE
    exact this.2 (hβΔ hbβ)
  · exact ⟨A, A', D, D', hD, hD', hun, hint, hbd, hbd', hAs, hAs', hcov, hpc hA₁, h₁, h₂, hi₁,
      hi₂, hcover hun hbd hbd' hAs hAs'⟩
  · refine ⟨A', A, D', D, hD', hD, by rw [union_comm, hun], hint', hbd', hbd, hAs', hAs, ?_,
      hpc hA₀, h₂, h₁, hi₂, hi₁, ?_⟩
    · rw [union_comm]
      exact hcov
    · rw [union_comm]
      exact hcover hun hbd hbd' hAs hAs'
  · exfalso
    have hbcl := hΔ.subset_closure_discInt (Surface.discBd_subset _ (hβΔ hbβ))
    obtain ⟨w, hw, hwi⟩ := _root_.mem_closure_iff.1 hbcl _ hEopen hbE
    have hwβ : w ∉ β := fun h ↦ hwi.2 (hβΔ h)
    rcases hcover hun hbd hbd' hAs hAs' ⟨hw, hwβ⟩ with h | h
    · exact disjoint_left.1 h₁ h (discInt_subset Δ hwi)
    · exact disjoint_left.1 h₂ h (discInt_subset Δ hwi)


/-- **Half of a closed disc `E` added to a closed disc `Δ`.** The line `β` lies on the boundary of
`Δ` and cuts `E` in two. Every other
point of `E` on the boundary of `Δ` lies on the boundary of `E`, and is reached from inside `Δ`
through `E`. This form of (the second
half of) `exists_split` allows that `E` touches `Δ` again. -/
theorem exists_outer_half (hT : IsClosedSurface T) {Δ E β : Set T}
  (hΔ : IsClosedDisc Δ) (hE : IsClosedDisc E) {s t : T} (hst : s ≠ t)
    (hl : IsLineWithEnds β s t) (hβΔ : β ⊆ discBd Δ) (hβE : β ⊆ E) (hmeet : β ∩ discBd E = {s, t})
      (hoff : discInt E ∩ discBd Δ ⊆ β)
    (htouch : ∀ x ∈ discBd E ∩ discBd Δ, x ∉ β → ∃ C, C ⊆ discInt E \ β ∧ C ⊆ Δ ∧ C.Nonempty
      ∧ IsPreconnected C ∧ x ∈ closure C) :
    ∃ Z A' : Set T, IsClosedDisc Z ∧ A' ⊆ discBd E ∧ IsPreconnected A' ∧ discBd Z = (discBd Δ \
      (β \ {s, t})) ∪ A' ∧ Disjoint A' Δ ∧
      discBd E \ A' ⊆ Δ ∧ E ⊆ Z ∧ Δ ⊆ Z ∧ Z \ Δ ⊆ E ∧ ∀ x ∉ discInt E, x ∈ discInt Z ↔ x ∈ discInt
        Δ := by
  classical
  have hman : ∀ x : T, IsManifoldPoint x := fun x ↦ (hT.2.2 x).isManifoldPoint
  have hsβ : s ∈ β := by
    have : s ∈ β ∩ discBd E := by rw [hmeet]; exact mem_insert _ _
    exact this.1
  have htβ : t ∈ β := by
    have : t ∈ β ∩ discBd E := by rw [hmeet]; exact mem_insert_of_mem _ rfl
    exact this.1
  have hoffβ : ∀ {x}, x ∈ discBd E \ {s, t} → x ∉ β := fun {x} hx hxβ ↦ hx.2 (hmeet ▸ ⟨hxβ, hx.1⟩)
  obtain ⟨A, A', D, D', hD, hD', hun, hint, hbd, hbd', hAs, hAs', hcov, hApc, hin, hout, hi₁, -,
    hcoverE⟩ := exists_chord_side hT hΔ hE hst hl hβΔ hβE hmeet hoff
  have hsubb : ∀ {x}, x ∈ β → x ∈ Δ := fun hx ↦ Surface.discBd_subset _ (hβΔ hx)
  have hβD' : β ⊆ discBd D' := fun x hx ↦ hbd' ▸ Or.inr hx
  have hDΔ : D ⊆ Δ := by
    rw [← closure_discInt hD]
    exact closure_minimal (hin.trans (discInt_subset Δ)) hΔ.isClosed
  have hA'D' : A' ⊆ D' := fun x hx ↦ Surface.discBd_subset _ (hbd' ▸ Or.inl hx)
  have hAD : A ⊆ D := fun x hx ↦ Surface.discBd_subset _ (hbd ▸ Or.inl hx)
  have hDE : D ⊆ E := hun ▸ subset_union_left
  have hDE' : D' ⊆ E := hun ▸ subset_union_right
  have hA₂out : Disjoint A' Δ := by
    refine disjoint_left.2 fun x hx hxΔ ↦ ?_
    have hxβ : x ∉ β := hoffβ (hAs' hx)
    have hxcl : x ∈ closure (discInt D') := (closure_discInt hD').symm ▸ hA'D' hx
    have hxb : x ∈ discBd Δ := by
      by_contra hb
      obtain ⟨w, hwi, hw⟩ := _root_.mem_closure_iff.1 hxcl _ (hΔ.isOpen_discInt hman) ⟨hxΔ, hb⟩
      exact disjoint_left.1 hout hw (discInt_subset Δ hwi)
    obtain ⟨C, hC, hCΔ, hCne, hCc, hxC⟩ := htouch x ⟨(hAs' hx).1, hxb⟩ hxβ
    have hsplit := hCc.subset_or_subset (hD.isOpen_discInt hman) (hD'.isOpen_discInt hman)
      (disjoint_left.2 fun y hy hy' ↦ (by
        have hyβ : y ∈ β := hint ▸ ⟨hy.1, hy'.1⟩
        exact hy.2 (hbd ▸ Or.inr hyβ))) (hC.trans hcoverE)
    rcases hsplit with h | h
    · have : x ∈ D := closure_minimal (h.trans (discInt_subset D)) hD.isClosed hxC
      exact hxβ (hint ▸ ⟨this, hA'D' hx⟩)
    · obtain ⟨y, hy⟩ := hCne
      exact disjoint_left.1 hout (h hy) (hCΔ hy)
  have hmd2 : Δ ∩ D' = β := by
    apply Subset.antisymm
    · rintro x ⟨hx, hx'⟩
      by_contra hn
      by_cases hb : x ∈ discBd D'
      · rw [hbd'] at hb
        rcases hb with h | h
        · exact disjoint_left.1 hA₂out h hx
        · exact hn h
      · exact disjoint_left.1 hout ⟨hx', hb⟩ hx
    · exact fun x hx ↦ ⟨hsubb hx, Surface.discBd_subset _ (hβD' hx)⟩
  obtain ⟨hu, hub⟩ := disc_union Δ D' β s t hΔ hD' hl hmd2 hβΔ hβD'
  have hoffA : ∀ {B}, B ⊆ discBd E \ {s, t} → ∀ {x}, x ∈ B → x ∉ β := fun hB _ hx ↦ hoffβ (hB hx)
  have hbd₂ : discBd (Δ ∪ D') = (discBd Δ \ (β \ {s, t})) ∪ A' := by
    rw [hub]
    ext x
    constructor
    · rintro ⟨hx | hx, hn⟩
      · exact Or.inl ⟨hx, hn⟩
      · rw [hbd'] at hx
        rcases hx with h | h
        · exact Or.inr h
        · exact Or.inl ⟨hβΔ h, hn⟩
    · rintro (⟨hx, hn⟩ | hx)
      · exact ⟨Or.inl hx, hn⟩
      · exact ⟨Or.inr (hbd' ▸ Or.inl hx), fun h ↦ hoffA hAs' hx h.1⟩
  have hEsub : E ⊆ Δ ∪ D' := by
    rw [← hun]
    rintro x (h | h)
    · exact Or.inl (hDΔ h)
    · exact Or.inr h
  refine ⟨Δ ∪ D', A', hu, fun x hx ↦ (hAs' hx).1, hApc, hbd₂, hA₂out, ?_, hEsub,
    subset_union_left, ?_, ?_⟩
  · rintro x ⟨hx, hn⟩
    by_cases hxe : x ∈ ({s, t} : Set T)
    · rcases hxe with h' | h'
      · exact h' ▸ hsubb hsβ
      · exact (mem_singleton_iff.1 h') ▸ hsubb htβ
    · rcases hcov ⟨hx, hxe⟩ with h | h
      · exact hDΔ (hAD h)
      · exact absurd h hn
  · rintro x ⟨h | h, hn⟩
    · exact absurd h hn
    · exact hDE' h
  · intro x hx
    constructor
    · rintro ⟨hxu, hn⟩
      have hxΔ : x ∈ Δ := by
        rcases hxu with h | h
        · exact h
        · by_contra hxΔ
          have hxb : x ∈ discBd E := by
            by_contra hb'
            exact hx ⟨hDE' h, hb'⟩
          by_cases hxe : x ∈ ({s, t} : Set T)
          · rcases hxe with h' | h'
            · exact hxΔ (h' ▸ hsubb hsβ)
            · exact hxΔ ((mem_singleton_iff.1 h') ▸ hsubb htβ)
          · rcases hcov ⟨hxb, hxe⟩ with h' | h'
            · exact hxΔ (hDΔ (hAD h'))
            · exact hn (hbd₂ ▸ Or.inr h')
      refine ⟨hxΔ, fun hb' ↦ hn ?_⟩
      rw [hbd₂]
      refine Or.inl ⟨hb', fun h ↦ hx ⟨hβE h.1, fun hE' ↦ h.2 (hmeet ▸ ⟨h.1, hE'⟩)⟩⟩
    · rintro ⟨hxΔ, hn⟩
      refine ⟨Or.inl hxΔ, fun hb' ↦ ?_⟩
      rw [hbd₂] at hb'
      rcases hb' with h | h
      · exact hn h.1
      · exact disjoint_left.1 hA₂out h hxΔ

omit [T2Space T] in
/-- Two connected pieces of an `O`-arc that both miss the point `w` meet in a path-connected set. -/
theorem oArc_inter_isPathConnected {F P Q : Set T} (hF : IsOArc F) {w : T} (hw : w ∈ F)
  (hP : P ⊆ F \ {w}) (hQ : Q ⊆ F \ {w})
    (hPc : IsPreconnected P) (hQc : IsPreconnected Q) : P ∩ Q = ∅ ∨ IsPathConnected (P ∩ Q) := by
  classical
  obtain ⟨φ⟩ := hF
  set c : Circle := φ.symm ⟨w, hw⟩ with hc
  let E : ℝ → T := fun t ↦ (φ (c * Circle.exp (t + Real.pi))).1
  have hEc : Continuous E := continuous_subtype_val.comp (φ.continuous.comp (continuous_const.mul
    (Circle.exp.continuous.comp (continuous_id.add continuous_const))))
  let g : T → Circle := fun x ↦ if h : x ∈ F then φ.symm ⟨x, h⟩ else 1
  have hg : ∀ {x} (h : x ∈ F), g x = φ.symm ⟨x, h⟩ := fun {x} h ↦ dite_eq_left h
  let f : T → ℂ := fun x ↦ -(((g x : Circle) : ℂ) / (c : ℂ))
  let G : T → ℝ := fun x ↦ Complex.arg (f x)
  have hne1 : ∀ z : Circle, z ≠ c → -((z : ℂ) / (c : ℂ)) ∈ Complex.slitPlane := by
    intro z hz
    set u : Circle := z / c with hu
    have hval : -((z : ℂ) / (c : ℂ)) = -(u : ℂ) := by simp [hu]
    rw [hval, Complex.mem_slitPlane_iff]
    by_contra hno
    push Not at hno
    obtain ⟨h₁, h₂⟩ := hno
    have hnorm := Circle.norm_coe u
    have hre : (u : ℂ).re ^ 2 + (u : ℂ).im ^ 2 = 1 := by
      have := Complex.sq_norm (u : ℂ)
      rw [hnorm, Complex.normSq_apply] at this
      nlinarith
    have him : (u : ℂ).im = 0 := by simpa using h₂
    have hre' : 0 ≤ (u : ℂ).re := by simpa using h₁
    have h1 : (u : ℂ).re = 1 := by
      rw [him] at hre
      nlinarith
    have hu1 : u = 1 := Circle.ext (Complex.ext (by simpa using h1) (by simpa using him))
    exact hz (by rw [hu] at hu1; exact div_eq_one.1 hu1)
  have hoffw : ∀ {x} (h : x ∈ F), x ≠ w → φ.symm ⟨x, h⟩ ≠ c := fun {x} h hne he ↦
    hne (congrArg Subtype.val (φ.symm.injective he))
  have hGE : ∀ {x} (_ : x ∈ F \ {w}), E (G x) = x ∧ G x ∈ Ioo (-Real.pi) Real.pi := by
    rintro x ⟨hx, hxw⟩
    set z : Circle := φ.symm ⟨x, hx⟩ with hz
    have hzc := hoffw hx hxw
    have hG : G x = Complex.arg (-((z : ℂ) / (c : ℂ))) := by
      change Complex.arg (-(((g x : Circle) : ℂ) / (c : ℂ))) = _
      rw [hg hx]
    have hs := hne1 z hzc
    have hnm : ‖-((z : ℂ) / (c : ℂ))‖ = 1 := by simp
    have hexp : Circle.exp (G x + Real.pi) = z / c := by
      apply Circle.ext
      rw [Circle.coe_exp, hG]
      push_cast
      rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
      have h₁ := Complex.norm_mul_exp_arg_mul_I (-((z : ℂ) / (c : ℂ)))
      rw [hnm] at h₁
      simp only [Complex.ofReal_one, one_mul] at h₁
      rw [h₁]
      simp
    refine ⟨?_, ?_⟩
    · change (φ (c * Circle.exp (G x + Real.pi))).1 = x
      have hcz : c * (z / c) = z := by rw [mul_comm, div_mul_cancel]
      rw [hexp, hcz]
      simp [hz]
    · rw [hG]
      exact ⟨lt_of_le_of_ne (Complex.neg_pi_lt_arg _ |>.le) (fun h ↦ absurd h
        (Complex.neg_pi_lt_arg _).ne),
        lt_of_le_of_ne (Complex.arg_le_pi _) (Complex.mem_slitPlane_iff_arg.1 hs).1⟩
  have hgc : ContinuousOn g F := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine φ.symm.continuous.congr fun x ↦ ?_
    change φ.symm x = g x.1
    rw [hg x.2]
  have hGc : ContinuousOn G (F \ {w}) := by
    intro x hx
    have h₁ : ContinuousWithinAt f (F \ {w}) x :=
      ((continuous_subtype_val.continuousWithinAt.comp ((hgc x hx.1).mono sdiff_subset)
        (mapsTo_univ _ _)).div_const _).neg
    have h₂ : f x ∈ Complex.slitPlane := by
      change -(((g x : Circle) : ℂ) / (c : ℂ)) ∈ _
      rw [hg hx.1]
      exact hne1 _ (hoffw hx.1 hx.2)
    exact ContinuousAt.comp_continuousWithinAt (f := f) (Complex.continuousAt_arg h₂) h₁
  have hOrd : ∀ {R : Set T}, R ⊆ F \ {w} → IsPreconnected R → (G '' R).OrdConnected := fun hR hRc ↦
    (hRc.image _ (hGc.mono hR)).ordConnected
  have himage : P ∩ Q = E '' (G '' P ∩ G '' Q) := by
    ext x
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨G x, ⟨mem_image_of_mem _ h₁, mem_image_of_mem _ h₂⟩, (hGE (hP h₁)).1⟩
    · rintro ⟨_, ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩, rfl⟩
      have hab' : a = b := by
        rw [← (hGE (hP ha)).1, ← (hGE (hQ hb)).1, hab]
      refine ⟨by rw [(hGE (hP ha)).1]; exact ha, by rw [(hGE (hP ha)).1, hab']; exact hb⟩
  by_cases hne : (P ∩ Q).Nonempty
  · right
    rw [himage]
    have hne' : (G '' P ∩ G '' Q).Nonempty := by
      obtain ⟨x, h₁, h₂⟩ := hne
      exact ⟨G x, mem_image_of_mem _ h₁, mem_image_of_mem _ h₂⟩
    have hconv : Convex ℝ (G '' P ∩ G '' Q) := ((hOrd hP hPc).inter (hOrd hQ hQc)).convex
    exact (hconv.isPathConnected hne').image hEc
  · exact Or.inl (not_nonempty_iff_eq_empty.1 hne)

section Lift

variable {S Shat Y : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  [TopologicalSpace Y]
  [T2Space Y] {ψ : Y → S} {K : Drawing S}

/-- **The fragment outside a closed disc meets each fibre once.** -/
theorem injOn_of_outside (hS : IsSurface S) (cap : IsCappedSurface S Shat) (hY : IsSurface Y)
  (hψ : IsCutMap ψ K.U) (y : Y)
    {Z : Set Shat} (hZ : IsClosedDisc Z) (hsub : cap.emb '' K.U ⊆ discBd Z)
      (hrest : discBd Z ⊆ cap.discs ∪ cap.emb '' K.U)
    (hoth : ∀ Θ ∈ cuffs S, closure (cap.cuffDisc Θ) ⊆ Z ∨ Disjoint (closure (cap.cuffDisc Θ)) Z)
    (him : ψ '' connectedComponent y ⊆ (cap.emb ⁻¹' discInt Z)ᶜ) : InjOn ψ (connectedComponent y)
      := by
  classical
  have hT := cap.isClosedSurface
  have : CompactSpace Y := hY.1
  have hfrag := isCuttingFragment_of_cut hS hY hψ (K := K) rfl y
  have hfc : (cuffs S).Finite := (cuff_statement S hS).2.1
  intro x₁ h₁ x₂ h₂ he
  by_contra hne
  have hk : ψ x₁ ∈ K.U := by
    by_contra hk
    exact hne (hψ.2.2.1 hk (fun h ↦ hk (he ▸ h)) he)
  set x := ψ x₁ with hx
  have hp : cap.emb x ∈ discBd Z := hsub (mem_image_of_mem _ hk)
  have hF : (ψ ⁻¹' {x}).Finite := hψ.2.2.2.1 x
  obtain ⟨U, hU, hUd⟩ := hF.t2_separation
  have hx₁F : x₁ ∈ ψ ⁻¹' {x} := rfl
  have hx₂F : x₂ ∈ ψ ⁻¹' {x} := he.symm
  let V₂ : Set Y := ⋃ w ∈ (ψ ⁻¹' {x}) \ {x₁}, U w
  have hV₂o : IsOpen V₂ := isOpen_biUnion fun w _ ↦ (hU w).2
  have hdis : Disjoint (U x₁) V₂ := by
    refine disjoint_left.2 fun z hz hz' ↦ ?_
    obtain ⟨w, hw, hzw⟩ := mem_iUnion₂.1 hz'
    exact disjoint_left.1 (hUd hx₁F hw.1 (Ne.symm hw.2)) hz hzw
  set N : Set Y := U x₁ ∪ V₂ with hN
  have hNo : IsOpen N := (hU x₁).2.union hV₂o
  have hFN : ψ ⁻¹' {x} ⊆ N := fun w hw ↦ by
    by_cases h : w = x₁
    · exact Or.inl (h ▸ (hU x₁).1)
    · exact Or.inr (mem_iUnion₂.2 ⟨w, ⟨hw, h⟩, (hU w).1⟩)
  have hcl : IsClosed (ψ '' Nᶜ) := (isClosedMap_of_isCutMap hψ) _ hNo.isClosed_compl
  obtain ⟨O₀, hO₀, hO₀e⟩ := cap.isEmbedding.isInducing.isOpen_iff.1 hcl.isOpen_compl
  have hxO : cap.emb x ∈ O₀ := by
    change x ∈ cap.emb ⁻¹' O₀
    rw [hO₀e]
    rintro ⟨w, hw, hwx⟩
    exact hw (hFN hwx)
  have hdf : {Θ ∈ cuffs S | Disjoint (closure (cap.cuffDisc Θ)) Z}.Finite
    := hfc.subset fun _ h ↦ h.1
  let G : Set Shat := ⋂ Θ ∈ {Θ ∈ cuffs S | Disjoint (closure (cap.cuffDisc Θ)) Z}, (closure
    (cap.cuffDisc Θ))ᶜ
  have hGo : IsOpen G := hdf.isOpen_biInter fun _ _ ↦ isClosed_closure.isOpen_compl
  have hpG : cap.emb x ∈ G := mem_iInter₂.2 fun Θ hΘ h ↦ disjoint_left.1 hΘ.2 h
    (Surface.discBd_subset _ hp)
  obtain ⟨O, hOo, hpO, hOW, hOc⟩ := exists_nhd_outside hT hZ hp (hO₀.inter hGo) ⟨hxO, hpG⟩
  set C : Set S := cap.emb ⁻¹' (O \ Z) with hC
  have hrange : O \ Z ⊆ range cap.emb := by
    rintro z ⟨hzO, hzZ⟩
    by_contra hzr
    have hzc : z ∈ (range cap.emb)ᶜ := hzr
    rw [cap.compl_eq] at hzc
    obtain ⟨Θ, hΘ, hzΘ⟩ := mem_iUnion₂.1 hzc
    rcases hoth Θ hΘ with h | h
    · exact hzZ (h (subset_closure hzΘ))
    · exact (mem_iInter₂.1 (hOW hzO).2 Θ ⟨hΘ, h⟩) (subset_closure hzΘ)
  have hCc : IsPreconnected C := by
    rw [← cap.isEmbedding.isInducing.isPreconnected_image, image_preimage_eq_of_subset hrange]
    exact hOc
  have hCK : C ⊆ K.Uᶜ := fun z hz hzK ↦ hz.2 (Surface.discBd_subset _ (hsub
    (mem_image_of_mem _ hzK)))
  have hpc : IsPreconnected (ψ ⁻¹' C) := isPreconnected_preimage_of_isCutMap hψ K.isClosed_U hCK hCc
  have hsubN : ψ ⁻¹' C ⊆ U x₁ ∪ V₂ := fun z hz ↦ by
    by_contra hzN
    have hmem : cap.emb (ψ z) ∈ O₀ := (hOW hz.1).1
    have : ψ z ∈ cap.emb ⁻¹' O₀ := hmem
    rw [hO₀e] at this
    exact this ⟨z, hzN, rfl⟩
  have hmeet : ∀ {w}, w ∈ connectedComponent y → ψ w = x → ((ψ ⁻¹' C) ∩ U w).Nonempty := by
    intro w hw hwx
    have hS₁ := hfrag.isSurface
    have hcv : Continuous fun z : connectedComponent y ↦ ψ z.1 := hfrag.continuous_ψ
    let G₁ : Set (connectedComponent y) := Subtype.val ⁻¹' U w ∩ (fun z ↦ ψ z.1) ⁻¹' (cap.emb ⁻¹' O)
    have hG₁ : IsOpen G₁ := ((hU w).2.preimage continuous_subtype_val).inter (hOo.preimage
      (cap.isEmbedding.continuous.comp hcv))
    have hwG : (⟨w, hw⟩ : connectedComponent y) ∈ G₁ := ⟨(hU w).1, by
      change cap.emb (ψ w) ∈ O
      rw [hwx]
      exact hpO⟩
    obtain ⟨z, hzG, hzi⟩ := (dense_interior' hS₁).inter_open_nonempty _ hG₁ ⟨_, hwG⟩
    have hoff := disjoint_left.1 hfrag.maps_interior_disjoint (mem_image_of_mem _ hzi)
    refine ⟨z.1, ⟨hzG.2, fun hzZ ↦ ?_⟩, hzG.1⟩
    have hzim : cap.emb (ψ z.1) ∉ discInt Z := him (mem_image_of_mem _ z.2)
    have hzb : cap.emb (ψ z.1) ∈ discBd Z := by
      by_contra hb
      exact hzim ⟨hzZ, hb⟩
    rcases hrest hzb with h | ⟨a, ha, hae⟩
    · obtain ⟨Θ, hΘ, hzΘ⟩ := mem_iUnion₂.1 h
      exact hoff (Or.inl (cap.bd_of_mem hS hΘ hzΘ))
    · exact hoff (Or.inr (cap.isEmbedding.injective hae ▸ ha))
  obtain ⟨a, ha, ha'⟩ := hmeet h₁ rfl
  obtain ⟨b, hb, hb'⟩ := hmeet h₂ he.symm
  have hin := hpc.subset_left_of_subset_union (hU x₁).2 hV₂o hdis hsubN ⟨a, ha, ha'⟩
  have hbV : b ∈ V₂ := mem_iUnion₂.2 ⟨x₂, ⟨hx₂F, Ne.symm hne⟩, hb'⟩
  exact disjoint_left.1 hdis (hin hb) hbV

/-- **Surfaces with the same capping and the same number of cuffs are homeomorphic.** -/
theorem nonempty_homeomorph_of_cap {S₁ S₂ T₁ T₂ : Type} [TopologicalSpace S₁] [TopologicalSpace S₂]
  [TopologicalSpace T₁]
    [TopologicalSpace T₂] (h₁ : IsSurface S₁) (c₁ : ConnectedSpace S₁) (h₂ : IsSurface S₂)
      (c₂ : ConnectedSpace S₂)
    (cap₁ : IsCappedSurface S₁ T₁) (cap₂ : IsCappedSurface S₂ T₂) (hT : Nonempty (T₁ ≃ₜ T₂))
      (hn : numCuffs S₁ = numCuffs S₂) :
    Nonempty (S₁ ≃ₜ S₂) := by
  obtain ⟨a, b, c, ⟨e₁⟩⟩ := classification S₁ h₁ c₁
  obtain ⟨a', b', c', ⟨e₂⟩⟩ := classification S₂ h₂ c₂
  obtain ⟨g₁⟩ := capModel a b c T₁ (cap₁.ofHomeo e₁.symm)
  obtain ⟨g₂⟩ := capModel a' b' c' T₂ (cap₂.ofHomeo e₂.symm)
  obtain ⟨t⟩ := hT
  have hc : c = c' := by
    rw [numCuffs_eq e₁, numCuffs_eq e₂, numCuffs_model, numCuffs_model] at hn
    exact hn
  obtain ⟨-, h₃, h₄⟩ := (modelCriterion.2 a b 0 a' b' 0).1 ⟨g₁.symm.trans (t.trans g₂)⟩
  obtain ⟨m⟩ := (modelCriterion.2 a b c a' b' c').2 ⟨hc, h₃, h₄⟩
  exact ⟨e₁.trans (m.trans e₂.symm)⟩

end Lift

end GraphMinor.GM19
