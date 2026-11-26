/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.RadialExists
public import LeanPool.GraphMinor.Surface.Cap
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Complex.Convex

/-!
# Two open discs across an edge

A region of a radial drawing `Γ'` is made of an edge `e` of `Γ` and the two faces of `Γ ∪ Γ'` on the
two
sides of `e`. To see that it is an open disc we use `open_disc`, so we must find a closed disc
around
each `O`-arc in the region.

The tool is `exists_disc_off`. Let `A` be an open disc and let `N` be a closed disc that meets the
frontier
of `A` in a connected piece. Collapse the complement of `A` to a point `∞`. This gives a sphere, in
which
the image of `bd(N)` is an `O`-arc through `∞`. So the part of `A` outside `N` is a closed disc with
`∞`
on its boundary, and a chord near `∞` cuts off a closed disc `ρ ⊆ A` that holds any given compact
set. It
meets `N` in a line, so `N ∪ ρ` is a closed disc.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval Metric OnePoint

universe u

variable {S : Type u} [TopologicalSpace S]

/-- A loop that is injective apart from its ends has an `O`-arc as range. -/
theorem isOArc_of_loop {X : Type u} [TopologicalSpace X] [T2Space X] {m : I → X} (hm : Continuous m)
    (h01 : m 0 = m 1) (hinj : InjOn m (Ioo 0 1)) (hne : ∀ t ∈ Ioo (0 : I) 1, m t ≠ m 0) :
    IsOArc (range m) := by
  let h : I := ⟨1 / 2, by norm_num, by norm_num⟩
  let a : I → X := fun t => m ⟨t.1 / 2, by have := t.2.1; positivity, by have := t.2.2; linarith⟩
  let b : I → X := fun t => m ⟨1 - t.1 / 2, by have := t.2.2; linarith, by have := t.2.1; linarith⟩
  have hac : Continuous a := hm.comp (by fun_prop)
  have hbc : Continuous b := hm.comp (by fun_prop)
  have hmi : ∀ {s t : I}, m s = m t → s = t ∨ s ∉ Ioo (0 : I) 1 ∧ t ∉ Ioo (0 : I) 1 := by
    intro s t hst
    by_cases hs : s ∈ Ioo (0 : I) 1
    · by_cases ht : t ∈ Ioo (0 : I) 1
      · exact Or.inl (hinj hs ht hst)
      · exfalso
        have hend : m t = m 0 := by
          have : t = 0 ∨ t = 1 := by
            by_contra hc
            push Not at hc
            exact ht ⟨unitInterval.pos_iff_ne_zero.mpr hc.1, unitInterval.lt_one_iff_ne_one.mpr
              hc.2⟩
          rcases this with rfl | rfl
          · rfl
          · exact h01.symm
        exact hne s hs (hst.trans hend)
    · by_cases ht : t ∈ Ioo (0 : I) 1
      · exfalso
        have hend : m s = m 0 := by
          have : s = 0 ∨ s = 1 := by
            by_contra hc
            push Not at hc
            exact hs ⟨unitInterval.pos_iff_ne_zero.mpr hc.1, unitInterval.lt_one_iff_ne_one.mpr
              hc.2⟩
          rcases this with rfl | rfl
          · rfl
          · exact h01.symm
        exact hne t ht (hst.symm.trans hend)
      · exact Or.inr ⟨hs, ht⟩
  have hnotIoo : ∀ {u : I}, u ∉ Ioo (0 : I) 1 → u.1 = 0 ∨ u.1 = 1 := by
    intro u hu
    by_contra hc
    push Not at hc
    exact hu ⟨unitInterval.pos_iff_ne_zero.mpr fun h => hc.1 (by rw [h]; rfl),
      unitInterval.lt_one_iff_ne_one.mpr fun h => hc.2 (by rw [h]; rfl)⟩
  have hai : Function.Injective a := by
    intro s t hst
    rcases hmi hst with h' | ⟨h₁, h₂⟩
    · have := congrArg Subtype.val h'
      simp only at this
      exact Subtype.ext (by linarith)
    · rcases hnotIoo h₁ with h₃ | h₃ <;> rcases hnotIoo h₂ with h₄ | h₄ <;>
        simp only at h₃ h₄ <;> first
          | exact Subtype.ext (by linarith)
          | (exfalso; have := s.2.2; have := t.2.2; linarith)
  have hbi : Function.Injective b := by
    intro s t hst
    rcases hmi hst with h' | ⟨h₁, h₂⟩
    · have := congrArg Subtype.val h'
      simp only at this
      exact Subtype.ext (by linarith)
    · rcases hnotIoo h₁ with h₃ | h₃ <;> rcases hnotIoo h₂ with h₄ | h₄ <;>
        simp only at h₃ h₄ <;> first
          | exact Subtype.ext (by linarith)
          | (exfalso; have := s.2.2; have := t.2.2; have := s.2.1; have := t.2.1; linarith)
  have h0 : a 0 = b 0 := by
    have e₀ : a 0 = m 0 := congrArg m (Subtype.ext (by simp))
    have e₁ : b 0 = m 1 := congrArg m (Subtype.ext (by simp))
    rw [e₀, e₁, h01]
  have h1 : a 1 = b 1 := by
    refine congrArg m (Subtype.ext ?_)
    simp only [Icc.coe_one]
    norm_num
  have hmeet : ∀ s t, a s = b t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    intro s t hst
    rcases hmi hst with h' | ⟨h₁, h₂⟩
    · have := congrArg Subtype.val h'
      simp only at this
      right
      have hs := s.2.2
      have ht := t.2.1
      have ht' := t.2.2
      have hs' := s.2.1
      exact ⟨Subtype.ext (show s.1 = 1 by linarith), Subtype.ext (show t.1 = 1 by linarith)⟩
    · rcases hnotIoo h₁ with h₃ | h₃ <;> rcases hnotIoo h₂ with h₄ | h₄ <;> simp only at h₃ h₄
      · exfalso
        have := t.2.2
        linarith
      · exact Or.inl ⟨Subtype.ext (show s.1 = 0 by linarith), Subtype.ext (show t.1
        = 0 by linarith)⟩
      · exfalso
        have := s.2.2
        linarith
      · exfalso
        have := s.2.2
        linarith
  obtain ⟨f⟩ := oArc_of_two_arcs (a := a) (b := b) ⟨hac, hai⟩ ⟨hbc, hbi⟩ h0 h1 hmeet
  have hr : range a ∪ range b = range m := by
    apply subset_antisymm
    · rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩) <;> exact mem_range_self _
    · rintro _ ⟨t, rfl⟩
      by_cases ht : t.1 ≤ 1 / 2
      · refine Or.inl ⟨⟨2 * t.1, by have := t.2.1; positivity, by linarith⟩, ?_⟩
        refine congrArg m (Subtype.ext ?_)
        simp
      · push Not at ht
        refine Or.inr ⟨⟨2 * (1 - t.1), by have := t.2.2; linarith, by linarith⟩, ?_⟩
        refine congrArg m (Subtype.ext ?_)
        simp
  exact ⟨f.trans (Homeomorph.setCongr hr)⟩

/-- The map that collapses the complement of the open set `A` to the point at infinity. -/
noncomputable def collapse (A : Set S) (x : S) : OnePoint A := by
  classical
  exact if h : x ∈ A then ((⟨x, h⟩ : A) : OnePoint A) else ∞

omit [TopologicalSpace S] in
theorem collapse_of_mem {A : Set S} {x : S} (h : x ∈ A) : collapse A x =
  ((⟨x, h⟩ : A) : OnePoint A) := by
  simp [collapse, h]

omit [TopologicalSpace S] in
theorem collapse_of_notMem {A : Set S} {x : S} (h : x ∉ A) : collapse A x = ∞ := by
  simp [collapse, h]

theorem continuous_collapse [T2Space S] {A : Set S} (hA : IsOpen A) :
    Continuous (collapse A) := by
  classical
  refine continuous_def.mpr fun V hV => ?_
  rw [OnePoint.isOpen_def] at hV
  obtain ⟨h₁, h₂⟩ := hV
  have hop : IsOpen (Subtype.val '' ((↑) ⁻¹' V : Set A)) := hA.isOpenMap_subtype_val _ h₂
  by_cases hinf : ∞ ∈ V
  · have hcomp := h₁ hinf
    have : (collapse A ⁻¹' V)ᶜ = Subtype.val '' ((↑) ⁻¹' V : Set A)ᶜ := by
      ext x
      constructor
      · intro hx
        by_cases hxA : x ∈ A
        · refine ⟨⟨x, hxA⟩, ?_, rfl⟩
          intro h
          apply hx
          simpa [collapse_of_mem hxA] using h
        · exact absurd (by simpa [collapse_of_notMem hxA] using hinf) hx
      · rintro ⟨a, ha, rfl⟩ h
        apply ha
        simpa [collapse_of_mem a.2] using h
    rw [← isClosed_compl_iff, this]
    exact (hcomp.image continuous_subtype_val).isClosed
  · have : collapse A ⁻¹' V = Subtype.val '' ((↑) ⁻¹' V : Set A) := by
      ext x
      constructor
      · intro hx
        by_cases hxA : x ∈ A
        · refine ⟨⟨x, hxA⟩, ?_, rfl⟩
          simpa [mem_preimage, collapse_of_mem hxA] using hx
        · exact absurd (by simpa [mem_preimage, collapse_of_notMem hxA] using hx) hinf
      · rintro ⟨a, ha, rfl⟩
        simpa [mem_preimage, collapse_of_mem a.2] using ha
    rw [this]
    exact hop

/-- The one-point compactification of an open disc is a sphere. -/
theorem isSphere_onePoint {A : Set S} (hA : IsOpenDisc A) : IsSphere (OnePoint A) := by
  obtain ⟨-, ⟨φ⟩⟩ := hA
  have hb : OpenUnitDisc ≃ₜ EuclideanPlane := (Homeomorph.unitBall (E := EuclideanPlane)).symm
  exact ⟨(φ.symm.trans hb).onePointCongr⟩

/-- The map back from the compactification. -/
noncomputable def uncollapse {A : Set S} (z : S) (x : OnePoint A) : S := x.elim z Subtype.val

omit [TopologicalSpace S] in
theorem uncollapse_coe {A : Set S} (z : S) (a : A) : uncollapse z (a : OnePoint A) = a.1 := rfl

theorem continuousAt_uncollapse {A : Set S} (z : S) (a : A) :
    ContinuousAt (uncollapse z) (a : OnePoint A) := by
  have h : uncollapse z ∘ ((↑) : A → OnePoint A) = Subtype.val := rfl
  have : ContinuousAt (uncollapse z ∘ ((↑) : A → OnePoint A)) a := by
    rw [h]
    exact continuous_subtype_val.continuousAt
  exact (OnePoint.isOpenEmbedding_coe.continuousAt_iff).mp this

/-- A closed disc mapped by a continuous injective map into a Hausdorff space is a closed disc. -/
theorem isClosedDisc_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {K : Set X} (hK : IsClosedDisc K) {G : X → Y} (hG : ContinuousOn G K) (hi : InjOn G K) :
    IsClosedDisc (G '' K) ∧ discBd (G '' K) = G '' discBd K := by
  obtain ⟨φ⟩ := id hK
  have hc : CompactSpace K := by
    have : CompactSpace ClosedUnitDisc := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
    exact φ.compactSpace
  let j : K → G '' K := fun x => ⟨G x.1, x.1, x.2, rfl⟩
  have hjc : Continuous j := Continuous.subtype_mk hG.domRestrict _
  have hjb : Function.Bijective j := by
    constructor
    · intro x y hxy
      exact Subtype.ext (hi x.2 y.2 (congrArg Subtype.val hxy))
    · rintro ⟨_, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have : T2Space (G '' K) := inferInstance
  let J : K ≃ₜ G '' K := hjc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective j hjb)
  let ψ : ClosedUnitDisc ≃ₜ G '' K := φ.trans J
  refine ⟨⟨ψ⟩, ?_⟩
  rw [disc_boundary _ ψ, disc_boundary _ φ, image_image]
  rfl

/-- A rotation of a chart. -/
theorem isChart_rotate {X : Type*} [TopologicalSpace X] {D : Set X} {h : X → ℂ} {g : ℂ → X}
    (c : IsChart D h g) {u : ℂ} (hu : ‖u‖ = 1) :
    IsChart D (fun x => u * h x) (fun z => g (u⁻¹ * z)) := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have hnorm : ∀ z : ℂ, ‖u⁻¹ * z‖ = ‖z‖ := fun z => by simp [hu]
  have hnorm' : ∀ z : ℂ, ‖u * z‖ = ‖z‖ := fun z => by simp [hu]
  have hin : ∀ z ∈ closedBall (0 : ℂ) 1, u⁻¹ * z ∈ closedBall (0 : ℂ) 1 := fun z hz => by
    rw [mem_closedBall, dist_zero_right, hnorm]
    simpa using hz
  refine ⟨continuousOn_const.mul c.hc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact c.gc.comp (continuousOn_const.mul continuousOn_id) hin
  · intro x hx
    have := c.hm hx
    rw [mem_closedBall, dist_zero_right] at this ⊢
    rwa [hnorm']
  · intro z hz
    exact c.gm (hin z hz)
  · intro x hx
    simp only [inv_mul_cancel_left₀ hu0]
    exact c.gh hx
  · intro z hz
    simp only
    rw [c.hg (hin z hz), mul_inv_cancel_left₀ hu0]
  · rw [show (fun x => u * h x) '' discBd D = (fun z => u * z) '' (h '' discBd D) by
      rw [image_image], c.bd]
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [mem_sphere_zero_iff_norm] at hw ⊢
      rwa [hnorm']
    · intro hz
      refine ⟨u⁻¹ * z, ?_, mul_inv_cancel_left₀ hu0 z⟩
      rw [mem_sphere_zero_iff_norm] at hz ⊢
      rwa [hnorm]

/-- The part of the closed unit disc on the right of a vertical chord. -/
def rightPart (τ : ℝ) : Set ℂ := {z | z ∈ closedBall (0 : ℂ) 1 ∧ τ ≤ z.re}

theorem rightPart_disc {τ : ℝ} (hτ : τ < 1 / 4) :
    IsClosedDisc (rightPart τ) ∧ discBd (rightPart τ) = frontier (rightPart τ) := by
  have hc : Convex ℝ (rightPart τ) :=
    (convex_closedBall 0 1).inter (convex_halfSpace_re_ge τ)
  have hcl : IsClosed (rightPart τ) :=
    isClosed_closedBall.inter (isClosed_le continuous_const Complex.continuous_re)
  have hb : Bornology.IsBounded (rightPart τ) := isBounded_closedBall.subset fun z hz => hz.1
  refine isClosedDisc_of_convex hc ⟨(1 / 2 : ℂ), ?_⟩ hb hcl
  refine mem_interior.mpr ⟨ball (1 / 2 : ℂ) (1 / 4), ?_, isOpen_ball, mem_ball_self (by norm_num)⟩
  intro z hz
  have hz' : ‖z - 1 / 2‖ < 1 / 4 := by simpa [dist_eq_norm] using hz
  refine ⟨?_, ?_⟩
  · have : ‖z‖ ≤ ‖z - 1 / 2‖ + ‖(1 / 2 : ℂ)‖ := by
      simpa using norm_add_le (z - 1 / 2) (1 / 2 : ℂ)
    have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    simp only [mem_closedBall, dist_zero_right]
    linarith
  · have h1 : |(z - 1 / 2).re| ≤ ‖z - 1 / 2‖ := Complex.abs_re_le_norm _
    have h2 := (abs_le.mp h1).1
    have h3 : (z - 1 / 2).re = z.re - 1 / 2 := by simp
    rw [h3] at h2
    linarith

theorem rightPart_sphere {τ : ℝ} (_hτ : -1 < τ) (_hτ' : τ < 1) {η : ℝ} (hη : Real.cos η = -τ)
    (h0 : 0 < η) (hπ : η < Real.pi) :
    rightPart τ ∩ sphere 0 1 = cis' '' Icc (-(Real.pi - η)) (Real.pi - η) := by
  have hcos : Real.cos (Real.pi - η) = τ := by rw [Real.cos_pi_sub, hη, neg_neg]
  have hre : ∀ θ : ℝ, (cis' θ).re = Real.cos θ := fun θ => Complex.exp_ofReal_mul_I_re θ
  have hη' : Real.pi - η ∈ Icc 0 Real.pi := ⟨by linarith, by linarith⟩
  ext z
  constructor
  · rintro ⟨⟨-, hz⟩, hs⟩
    have hn : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hs
    have hz' : cis' (Complex.arg z) = z := by
      have := Complex.norm_mul_exp_arg_mul_I z
      rw [hn] at this
      simpa [cis'] using this
    refine ⟨Complex.arg z, ?_, hz'⟩
    have hle : |Complex.arg z| ≤ Real.pi - η := by
      by_contra hc
      push Not at hc
      have h₁ : |Complex.arg z| ∈ Icc 0 Real.pi := ⟨abs_nonneg _, Complex.abs_arg_le_pi z⟩
      have h₂ := Real.strictAntiOn_cos hη' h₁ hc
      rw [Real.cos_abs, ← hre, hz', hcos] at h₂
      linarith
    exact abs_le.mp hle
  · rintro ⟨θ, hθ, rfl⟩
    have hn : ‖cis' θ‖ = 1 := norm_cis' θ
    refine ⟨⟨by simp [hn], ?_⟩, by simp [hn]⟩
    rw [hre, ← Real.cos_abs θ, ← hcos]
    exact Real.strictAntiOn_cos.antitoneOn ⟨abs_nonneg _, (abs_le.mpr hθ).trans hη'.2⟩ hη'
      (abs_le.mpr hθ)

private theorem exists_disc_off_on_other_side {A N C : Set S} [T2Space S]
    {O Δ₁ Δ₂ : Set (OnePoint A)}
    (hd₁ : IsClosedDisc Δ₁) (hd₂ : IsClosedDisc Δ₂)
    (hb₁ : discBd Δ₁ = O) (hb₂ : discBd Δ₂ = O)
    (hu : Δ₁ ∪ Δ₂ = univ) (hi : Δ₁ ∩ Δ₂ = O)
    (hinfO : (∞ : OnePoint A) ∈ O)
    (hκ : Continuous (collapse A)) (hκA : InjOn (collapse A) A)
    (hbdO : ∀ {x : S}, x ∈ discBd N → collapse A x ∈ O)
    (hObd : ∀ {x : S}, x ∈ A → collapse A x ∈ O → x ∈ discBd N)
    (hTne : (discInt N ∩ A).Nonempty)
    (hC : IsCompact C) (hCA : C ⊆ A) (hCT : Disjoint C (discInt N)) (hCne : C.Nonempty) :
    let T' := collapse A '' (discInt N ∩ A)
    Disjoint T' O → IsOpen T' → closure T' ⊆ T' ∪ O → T' ⊆ Δ₁ →
      ∃ (ρ L : Set S) (s t : S), IsClosedDisc ρ ∧ ρ ⊆ A ∧ C ⊆ ρ ∧ ρ ∩ N = L ∧
        IsLineWithEnds L s t ∧ L ⊆ discBd ρ ∧ L ⊆ discBd N := by
  intro T' hT'O hT'open hclT hT'₁
  have hO₂ : O ⊆ Δ₂ := hb₂ ▸ discBd_subset Δ₂
  -- The inside of `Δ₁` is `T'`.
  have hint : Δ₁ \ O ⊆ T' := by
    have hpre : IsPreconnected (discInt Δ₁) := hd₁.isPreconnected_discInt
    have heq : discInt Δ₁ = Δ₁ \ O := by rw [discInt, hb₁]
    rw [heq] at hpre
    obtain ⟨y, hy⟩ := hTne
    have hyT : collapse A y ∈ T' := ⟨y, hy, rfl⟩
    refine hpre.subset_of_closure_inter_subset hT'open
      ⟨_, ⟨hT'₁ hyT, fun h => disjoint_left.mp hT'O hyT h⟩, hyT⟩ ?_
    rintro x ⟨hx, -, hxO⟩
    exact (hclT hx).resolve_right hxO
  have hT'₂ : Disjoint T' Δ₂ := by
    refine disjoint_left.mpr fun x hx hx₂ => ?_
    exact disjoint_left.mp hT'O hx (hi ▸ ⟨hT'₁ hx, hx₂⟩)
  have hCΔ : ∀ x ∈ C, collapse A x ∈ Δ₂ := by
    intro x hx
    have huniv : collapse A x ∈ Δ₁ ∪ Δ₂ := hu ▸ mem_univ _
    rcases huniv with h | h
    · by_cases hxO : collapse A x ∈ O
      · exact hO₂ hxO
      · obtain ⟨y, hy, hyx⟩ := hint ⟨h, hxO⟩
        have : y = x := hκA hy.2 (hCA hx) hyx
        exact absurd (this ▸ hy.1) (disjoint_left.mp hCT hx)
    · exact h
  -- The chart of `Δ₂`, with `∞` at the point `-1`.
  obtain ⟨h₀, g₀, c₀⟩ := hd₂.exists_isChart
  have hinfb : (∞ : OnePoint A) ∈ discBd Δ₂ := hb₂.symm ▸ hinfO
  have hbn : ‖h₀ ∞‖ = 1 := by
    have : h₀ ∞ ∈ sphere (0 : ℂ) 1 := c₀.bd ▸ mem_image_of_mem h₀ hinfb
    exact mem_sphere_zero_iff_norm.mp this
  have hbne : h₀ ∞ ≠ 0 := fun h => by
    rw [h] at hbn
    simp at hbn
  obtain ⟨h, g, c, hh⟩ : ∃ h g, IsChart Δ₂ h g ∧ h ∞ = -1 := by
    refine ⟨_, _, isChart_rotate c₀ (u := -(h₀ ∞)⁻¹) (by simp [hbn]), ?_⟩
    rw [neg_mul, inv_mul_cancel₀ hbne]
  have hg1 : g (-1) = ∞ := by
    rw [← hh]
    exact c.gh (hO₂ hinfO)
  have hOg : O = g '' sphere 0 1 := by
    rw [← c.bd, hb₂, c.g_h (hO₂)]
  -- A chord that keeps `C` on its right.
  have hCc : IsCompact (h '' (collapse A '' C)) :=
    ((hC.image hκ).image_of_continuousOn
      (c.hc.mono (image_subset_iff.mpr fun x hx => hCΔ x hx)))
  obtain ⟨z₀, hz₀, hmin⟩ := hCc.exists_isMinOn (hCne.image _ |>.image _)
    Complex.continuous_re.continuousOn
  obtain ⟨_, ⟨x₀, hx₀, rfl⟩, rfl⟩ := hz₀
  have hz₀b := c.hm (hCΔ x₀ hx₀)
  have hzne : h (collapse A x₀) ≠ -1 := by
    intro he
    have := c.gh (hCΔ x₀ hx₀)
    simp only [he, hg1] at this
    rw [collapse_of_mem (hCA hx₀)] at this
    exact OnePoint.infty_ne_coe _ this
  set w := h (collapse A x₀) with hw
  have hwn : ‖w‖ ≤ 1 := by simpa using hz₀b
  have hwre : -1 < w.re := by
    by_contra hc
    push Not at hc
    apply hzne
    have h₁ : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
    have h₂ := Complex.sq_norm w
    have h₃ : w.re = -1 := by
      have := (abs_le.mp (h₁.trans hwn)).1
      linarith
    have h₄ : w.im = 0 := by
      rw [Complex.normSq_apply] at h₂
      nlinarith [mul_self_nonneg w.im, norm_nonneg w]
    exact Complex.ext (by simpa using h₃) (by simpa using h₄)
  have hwre' : w.re ≤ 1 := (Complex.re_le_norm w).trans hwn
  set τ : ℝ := (w.re - 1) / 2 with hτ
  have hτ₁ : -1 < τ := by rw [hτ]; linarith
  have hτ₂ : τ ≤ 0 := by rw [hτ]; linarith
  have hτ₃ : τ < w.re := by rw [hτ]; linarith
  set η := Real.arccos (-τ) with hηd
  have hηc : Real.cos η = -τ := Real.cos_arccos (by linarith) (by linarith)
  have hη₀ : 0 < η := Real.arccos_pos.mpr (by linarith)
  have hηπ : η < Real.pi := Real.arccos_lt_pi.mpr (by linarith) |>.trans_le le_rfl
  obtain ⟨hdK, hbK⟩ := rightPart_disc (τ := τ) (by linarith)
  have hsph := rightPart_sphere hτ₁ (by linarith) hηc hη₀ hηπ
  have hKball : rightPart τ ⊆ closedBall 0 1 := fun z hz => hz.1
  have hne1 : ∀ z ∈ rightPart τ, z ≠ -1 := by
    rintro z ⟨-, hz⟩ rfl
    simp at hz
    linarith
  have hgne : ∀ z ∈ rightPart τ, g z ≠ ∞ := by
    intro z hz he
    apply hne1 z hz
    have h₁ := c.hg (hKball hz)
    simp only [he, hh] at h₁
    exact h₁.symm
  -- The disc in `S`.
  let G : ℂ → S := fun z => uncollapse x₀ (g z)
  have hGκ : ∀ z ∈ rightPart τ, G z ∈ A ∧ collapse A (G z) = g z := by
    intro z hz
    have hne := hgne z hz
    obtain ⟨a, ha⟩ := OnePoint.ne_infty_iff_exists.mp hne
    have hG : G z = a.1 := by
      change uncollapse x₀ (g z) = a.1
      rw [← ha]
      rfl
    rw [hG]
    exact ⟨a.2, by rw [collapse_of_mem a.2, ← ha]⟩
  have hGc : ContinuousOn G (rightPart τ) := by
    intro z hz
    obtain ⟨a, ha⟩ := OnePoint.ne_infty_iff_exists.mp (hgne z hz)
    have h₁ : ContinuousAt (uncollapse x₀) (g z) := by
      rw [← ha]
      exact continuousAt_uncollapse x₀ a
    exact h₁.comp_continuousWithinAt ((c.gc z (hKball hz)).mono hKball)
  have hGi : InjOn G (rightPart τ) := by
    intro y hy z hz hyz
    have h₁ : g y = g z := by rw [← (hGκ y hy).2, ← (hGκ z hz).2, hyz]
    have h₂ := c.hg (hKball hy)
    rw [← h₂, ← c.hg (hKball hz)]
    simp only [h₁]
  obtain ⟨hρ, hρb⟩ := isClosedDisc_image hdK hGc hGi
  -- The line.
  let cl : ℝ → ℝ := fun θ => max (-(Real.pi - η)) (min θ (Real.pi - η))
  have hcl : ∀ θ ∈ Icc (-(Real.pi - η)) (Real.pi - η), cl θ = θ := fun θ hθ => by
    simp only [cl]
    rw [min_eq_left hθ.2, max_eq_right hθ.1]
  have hclm : ∀ θ, cis' (cl θ) ∈ rightPart τ := by
    intro θ
    have hab : -(Real.pi - η) ≤ Real.pi - η := by linarith
    have : cl θ ∈ Icc (-(Real.pi - η)) (Real.pi - η) :=
      ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
    exact (hsph.ge (mem_image_of_mem cis' this)).1
  let p : ℝ → S := fun θ => G (cis' (cl θ))
  have hpc : Continuous p := by
    refine hGc.comp_continuous (continuous_cis'.comp ?_) hclm
    exact continuous_const.max (continuous_id.min continuous_const)
  have hpi : InjOn p (Icc (-(Real.pi - η)) (Real.pi - η)) := by
    intro a ha b hb hab
    have h₁ := hGi (hclm a) (hclm b) hab
    rw [hcl a ha, hcl b hb] at h₁
    have ha' : a ∈ Ioo (-Real.pi) Real.pi := ⟨by linarith [ha.1], by linarith [ha.2]⟩
    have hb' : b ∈ Ioo (-Real.pi) Real.pi := ⟨by linarith [hb.1], by linarith [hb.2]⟩
    exact cis'_injOn ha' hb' h₁
  have hline := isLine_of_injOn hpc (a := -(Real.pi - η)) (b := Real.pi - η) (by linarith) hpi
  have hLeq : p '' Icc (-(Real.pi - η)) (Real.pi - η) = G '' (rightPart τ ∩ sphere 0 1) := by
    rw [hsph, image_image]
    exact image_congr fun θ hθ => by simp only [p, hcl θ hθ]
  have hρN : G '' rightPart τ ∩ N = G '' (rightPart τ ∩ sphere 0 1) := by
    apply subset_antisymm
    · rintro _ ⟨⟨z, hz, rfl⟩, hzN⟩
      obtain ⟨hzA, hzκ⟩ := hGκ z hz
      have hzΔ : collapse A (G z) ∈ Δ₂ := by
        rw [hzκ]
        exact c.gm (hKball hz)
      have hzb : G z ∈ discBd N := by
        by_contra hn
        exact disjoint_left.mp hT'₂ ⟨_, ⟨⟨hzN, hn⟩, hzA⟩, rfl⟩ hzΔ
      have hzO := hbdO hzb
      rw [hzκ, hOg] at hzO
      obtain ⟨y, hy, hyz⟩ := hzO
      have : y = z := by
        have h₁ := c.hg (sphere_subset_closedBall hy)
        rw [hyz, c.hg (hKball hz)] at h₁
        exact h₁.symm
      exact ⟨z, ⟨hz, this ▸ hy⟩, rfl⟩
    · rintro _ ⟨z, ⟨hz, hzs⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      obtain ⟨hzA, hzκ⟩ := hGκ z hz
      refine discBd_subset N (hObd hzA ?_)
      rw [hzκ, hOg]
      exact mem_image_of_mem g hzs
  refine ⟨G '' rightPart τ, G '' (rightPart τ ∩ sphere 0 1), _, _, hρ, ?_, ?_, hρN,
    hLeq ▸ hline, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact (hGκ z hz).1
  · intro x hx
    have hxr : h (collapse A x) ∈ rightPart τ := by
      refine ⟨c.hm (hCΔ x hx), hτ₃.le.trans ?_⟩
      exact hmin (mem_image_of_mem h (mem_image_of_mem _ hx))
    refine ⟨_, hxr, ?_⟩
    apply hκA (hGκ _ hxr).1 (hCA hx)
    rw [(hGκ _ hxr).2]
    exact c.gh (hCΔ x hx)
  · rw [hρb, hbK]
    refine image_mono fun z hz => ?_
    refine ⟨subset_closure hz.1, fun hi' => ?_⟩
    have hb' : z ∈ interior (closedBall (0 : ℂ) 1) := interior_mono hKball hi'
    rw [interior_closedBall _ one_ne_zero] at hb'
    have h₁ : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz.2
    have h₂ : ‖z‖ < 1 := by simpa using hb'
    linarith
  · rintro _ ⟨z, ⟨hz, hzs⟩, rfl⟩
    obtain ⟨hzA, hzκ⟩ := hGκ z hz
    refine hObd hzA ?_
    rw [hzκ, hOg]
    exact mem_image_of_mem g hzs

/-- **A closed disc off a closed disc.** See the module docstring. The closed disc `N` meets the
complement of the open disc `A` so that the rest of `bd(N)` is the open part of the curve `ℓ` with
ends off `A`. Each compact subset of `A` that misses the inside of `N` lies in a closed disc in `A`
that meets `N` in a line of both boundaries. -/
theorem exists_disc_off (hS : IsClosedSurface S) {A N C : Set S} (hA : IsOpenDisc A)
    (hN : IsClosedDisc N) {ℓ : I → S} (hℓ : Continuous ℓ) (h0 : ℓ 0 ∉ A) (h1 : ℓ 1 ∉ A)
    (hinj : InjOn ℓ (Ioo 0 1)) (hbd : discBd N ∩ A = ℓ '' Ioo 0 1)
    (hT : IsPreconnected (discInt N ∩ A)) (hTne : (discInt N ∩ A).Nonempty)
    (hC : IsCompact C) (hCA : C ⊆ A) (hCT : Disjoint C (discInt N)) (hCne : C.Nonempty) :
    ∃ (ρ L : Set S) (s t : S), IsClosedDisc ρ ∧ ρ ⊆ A ∧ C ⊆ ρ ∧ ρ ∩ N = L ∧
      IsLineWithEnds L s t ∧ L ⊆ discBd ρ ∧ L ⊆ discBd N := by
  classical
  have hK : CompactSpace S := hS.1
  have hT2 : T2Space S := hS.2.1
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hAo : IsOpen A := hA.1
  have hXT : T2Space (OnePoint A) := by
    obtain ⟨e⟩ := isSphere_onePoint hA
    exact e.symm.t2Space
  have hκ : Continuous (collapse A) := continuous_collapse hAo
  have hκA : InjOn (collapse A) A := by
    intro x hx y hy hxy
    rw [collapse_of_mem hx, collapse_of_mem hy] at hxy
    exact congrArg Subtype.val (OnePoint.coe_injective hxy)
  have hκmem : ∀ {x : S}, collapse A x ≠ ∞ → x ∈ A := fun {x} h => by
    by_contra hx
    exact h (collapse_of_notMem hx)
  let m : I → OnePoint A := collapse A ∘ ℓ
  have hm : Continuous m := hκ.comp hℓ
  have hm0 : m 0 = ∞ := collapse_of_notMem h0
  have hm1 : m 1 = ∞ := collapse_of_notMem h1
  have hIoo : ∀ {t : I}, t ∈ Ioo (0 : I) 1 → ℓ t ∈ A := fun ht =>
    (hbd.ge (mem_image_of_mem ℓ ht)).2
  have hO : IsOArc (range m) := by
    refine isOArc_of_loop hm (hm0.trans hm1.symm) ?_ ?_
    · intro s hs t ht hst
      exact hinj hs ht (hκA (hIoo hs) (hIoo ht) hst)
    · intro t ht
      rw [hm0]
      change collapse A (ℓ t) ≠ ∞
      rw [collapse_of_mem (hIoo ht)]
      exact OnePoint.coe_ne_infty _
  set O := range m with hOdef
  have hinfO : (∞ : OnePoint A) ∈ O := ⟨0, hm0⟩
  have hbdO : ∀ {x : S}, x ∈ discBd N → collapse A x ∈ O := by
    intro x hx
    by_cases hxA : x ∈ A
    · obtain ⟨t, ht, rfl⟩ := hbd.subset ⟨hx, hxA⟩
      exact ⟨t, rfl⟩
    · rw [collapse_of_notMem hxA]
      exact hinfO
  have hObd : ∀ {x : S}, x ∈ A → collapse A x ∈ O → x ∈ discBd N := by
    rintro x hx ⟨t, ht⟩
    have ht' : collapse A (ℓ t) = collapse A x := ht
    have htA : ℓ t ∈ A := by
      apply hκmem
      rw [ht', collapse_of_mem hx]
      exact OnePoint.coe_ne_infty _
    have hxt : ℓ t = x := hκA htA hx ht'
    have htIoo : t ∈ Ioo (0 : I) 1 := by
      refine ⟨unitInterval.pos_iff_ne_zero.mpr ?_, unitInterval.lt_one_iff_ne_one.mpr ?_⟩
      · rintro rfl
        exact h0 htA
      · rintro rfl
        exact h1 htA
    exact (hbd.ge (mem_image_of_mem ℓ htIoo)).1 |> fun h => hxt ▸ h
  let T' : Set (OnePoint A) := collapse A '' (discInt N ∩ A)
  have hT'c : IsPreconnected T' := hT.image _ hκ.continuousOn
  have hT'O : Disjoint T' O := by
    refine disjoint_left.mpr ?_
    rintro _ ⟨x, ⟨hx, hxA⟩, rfl⟩ hO'
    exact hx.2 (hObd hxA hO')
  have hT'open : IsOpen T' := by
    have hop : IsOpen (discInt N ∩ A) := (hN.isOpen_discInt hman).inter hAo
    have : T' = ((↑) : A → OnePoint A) '' (Subtype.val ⁻¹' (discInt N ∩ A)) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx.2⟩, hx, (collapse_of_mem hx.2).symm⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a.1, ha, collapse_of_mem a.2⟩
    rw [this]
    exact OnePoint.isOpenEmbedding_coe.isOpenMap _ (hop.preimage continuous_subtype_val)
  have hNc : IsCompact N := hN.isCompact
  have hκN : collapse A '' N ⊆ T' ∪ O := by
    rintro _ ⟨x, hx, rfl⟩
    by_cases hxA : x ∈ A
    · by_cases hxb : x ∈ discBd N
      · exact Or.inr (hbdO hxb)
      · exact Or.inl ⟨x, ⟨⟨hx, hxb⟩, hxA⟩, rfl⟩
    · rw [collapse_of_notMem hxA]
      exact Or.inr hinfO
  have hclT : closure T' ⊆ T' ∪ O := by
    have hcl : IsClosed (collapse A '' N) := (hNc.image hκ).isClosed
    have hsub : T' ⊆ collapse A '' N := image_mono fun x hx => hx.1.1
    exact (closure_minimal hsub hcl).trans hκN
  obtain ⟨Δ₁, Δ₂, -, hd₁, hd₂, hb₁, hb₂, hu, hi, -, -⟩ :=
    sphere_disc (OnePoint A) (isSphere_onePoint hA) O hO
  have hcls : ∀ {Δ : Set (OnePoint A)}, IsClosedDisc Δ → IsClosed Δ := fun h => h.isCompact.isClosed
  have hsub : T' ⊆ Δ₁ ∪ Δ₂ := by
    rw [hu]
    exact subset_univ _
  have hdis : ∀ x ∈ T', x ∈ Δ₁ → x ∉ Δ₂ := by
    intro x hx hx₁ hx₂
    have : x ∈ O := hi ▸ ⟨hx₁, hx₂⟩
    exact disjoint_left.mp hT'O hx this
  rcases subset_or_subset_of_closed hT'c (hcls hd₁) (hcls hd₂) hsub hdis with h | h
  · exact exists_disc_off_on_other_side hd₁ hd₂ hb₁ hb₂ hu hi hinfO hκ hκA hbdO hObd
      hTne hC hCA hCT hCne hT'O hT'open hclT h
  · exact exists_disc_off_on_other_side hd₂ hd₁ hb₂ hb₁ (by rw [union_comm]; exact hu)
      (by rw [inter_comm]; exact hi) hinfO hκ hκA hbdO hObd hTne hC hCA hCT hCne
      hT'O hT'open hclT h

end GraphMinor.GM11
