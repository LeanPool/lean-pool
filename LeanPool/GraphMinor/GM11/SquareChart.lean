/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Collar
public import LeanPool.GraphMinor.Surface.Cap
public import LeanPool.GraphMinor.GM11.Defs
public import Mathlib.Analysis.Complex.Convex

/-!
# Coordinates on a closed disc with three sides

Let `D` be a closed disc in a surface whose boundary is three lines that form a triangle. We give
coordinates on `D` by the unit square: the bottom of the square is the first line, the left and
right sides
are the two other lines, and the top is collapsed to the point where these two meet
(`exists_square_chart`). The boundary map is prescribed, so such charts of neighbouring discs agree
on a
common side.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval Metric

universe u

/-- The triangle with vertices `0`, `1` and `1/2 + i`. -/
def tri : Set ℂ := {z | 0 ≤ z.im ∧ z.im ≤ 1 ∧ z.im / 2 ≤ z.re ∧ z.re ≤ 1 - z.im / 2}

theorem isClosed_tri : IsClosed tri := by
  have h₁ : Continuous fun z : ℂ => z.im := Complex.continuous_im
  have h₂ : Continuous fun z : ℂ => z.re := Complex.continuous_re
  exact (isClosed_le continuous_const h₁).inter ((isClosed_le h₁ continuous_const).inter
    ((isClosed_le (h₁.div_const 2) h₂).inter (isClosed_le h₂ (continuous_const.sub
      (h₁.div_const 2)))))

theorem convex_tri : Convex ℝ tri := by
  intro x hx y hy a b ha hb hab
  obtain ⟨x₁, x₂, x₃, x₄⟩ := hx
  obtain ⟨y₁, y₂, y₃, y₄⟩ := hy
  have e₁ : (a • x + b • y).im = a * x.im + b * y.im := by simp
  have e₂ : (a • x + b • y).re = a * x.re + b * y.re := by simp
  have hb' : b = 1 - a := by linarith
  subst hb'
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [e₁] <;> try rw [e₂]
  · positivity
  · nlinarith
  · nlinarith
  · nlinarith

theorem tri_subset_ball : tri ⊆ ball (0 : ℂ) 3 := by
  rintro z ⟨h₁, h₂, h₃, h₄⟩
  rw [mem_ball, dist_zero_right]
  have := Complex.norm_le_abs_re_add_abs_im z
  have h₅ : |z.re| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have h₆ : |z.im| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

theorem mem_interior_tri {z : ℂ} (h₁ : 0 < z.im) (h₃ : z.im / 2 < z.re) (h₄ : z.re < 1 - z.im / 2) :
    z ∈ interior tri := by
  have hO : IsOpen {w : ℂ | 0 < w.im ∧ w.im / 2 < w.re ∧ w.re < 1 - w.im / 2} := by
    have c₁ : Continuous fun z : ℂ => z.im := Complex.continuous_im
    have c₂ : Continuous fun z : ℂ => z.re := Complex.continuous_re
    exact (isOpen_lt continuous_const c₁).inter ((isOpen_lt (c₁.div_const 2) c₂).inter
      (isOpen_lt c₂ (continuous_const.sub (c₁.div_const 2))))
  refine mem_interior.mpr ⟨_, ?_, hO, h₁, h₃, h₄⟩
  rintro w ⟨a₁, a₂, a₃⟩
  exact ⟨a₁.le, by linarith, a₂.le, a₃.le⟩

/-- A point of `tri` on one of the three sides is not an interior point. -/
theorem notMem_interior_tri {z : ℂ} (h : z.im = 0 ∨ z.re = z.im / 2 ∨ z.re = 1 - z.im / 2) :
    z ∉ interior tri := by
  intro hz
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
  have hin : ∀ w, ‖w‖ = ε / 2 → z + w ∈ tri := fun w hw =>
    interior_subset (hb (by simp [dist_eq_norm, hw]; linarith))
  rcases h with h | h | h
  · have := (hin (⟨0, -(ε / 2)⟩ : ℂ) (by
      rw [Complex.norm_def, Complex.normSq_mk]
      simp only [mul_zero, zero_add, neg_mul_neg]
      rw [Real.sqrt_mul_self (by positivity)])).1
    simp [h] at this
    linarith
  · have := (hin (⟨-(ε / 2), 0⟩ : ℂ) (by
      rw [Complex.norm_def, Complex.normSq_mk]
      simp only [mul_zero, add_zero, neg_mul_neg]
      rw [Real.sqrt_mul_self (by positivity)])).2.2.1
    simp at this
    linarith
  · have := (hin (⟨ε / 2, 0⟩ : ℂ) (by
      rw [Complex.norm_def, Complex.normSq_mk]
      simp only [mul_zero, add_zero]
      rw [Real.sqrt_mul_self (by positivity)])).2.2.2
    simp at this
    linarith

theorem mem_frontier_tri {z : ℂ} : z ∈ frontier tri ↔
    z ∈ tri ∧ (z.im = 0 ∨ z.re = z.im / 2 ∨ z.re = 1 - z.im / 2) := by
  rw [frontier, isClosed_tri.closure_eq]
  constructor
  · rintro ⟨hz, hn⟩
    refine ⟨hz, ?_⟩
    by_contra hc
    push Not at hc
    obtain ⟨h₁, h₂, h₃⟩ := hc
    obtain ⟨a₁, -, a₃, a₄⟩ := hz
    exact hn (mem_interior_tri (lt_of_le_of_ne a₁ h₁.symm) (lt_of_le_of_ne a₃ h₂.symm)
      (lt_of_le_of_ne a₄ h₃))
  · rintro ⟨hz, h⟩
    exact ⟨hz, notMem_interior_tri h⟩

theorem tri_disc : IsClosedDisc tri ∧ discBd tri = frontier tri :=
  isClosedDisc_of_convex convex_tri ⟨⟨1 / 2, 1 / 2⟩, mem_interior_tri (by norm_num) (by norm_num)
    (by norm_num)⟩ (isBounded_ball.subset tri_subset_ball) isClosed_tri

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- The point of `tri` at height `t`, at the place `u` between its two sides. -/
noncomputable def triPoint (u t : I) : ℂ := ⟨t.1 / 2 + (1 - t.1) * u.1, t.1⟩

theorem continuous_triPoint : Continuous fun p : I × I => triPoint p.1 p.2 := by
  have h₁ : Continuous fun p : I × I => (p.1.1 : ℝ) := continuous_subtype_val.comp continuous_fst
  have h₂ : Continuous fun p : I × I => (p.2.1 : ℝ) := continuous_subtype_val.comp continuous_snd
  have : (fun p : I × I => triPoint p.1 p.2) = fun p =>
      Complex.equivRealProdCLM.symm (p.2.1 / 2 + (1 - p.2.1) * p.1.1, p.2.1) := by
    funext p
    apply Complex.ext <;> simp [triPoint]
  rw [this]
  exact Complex.equivRealProdCLM.symm.continuous.comp ((by fun_prop : Continuous fun p : I × I =>
    (p.2.1 / 2 + (1 - p.2.1) * p.1.1 : ℝ)).prodMk h₂)

theorem triPoint_mem (u t : I) : triPoint u t ∈ tri := by
  have ha := u.2.1
  have hb := u.2.2
  have hc := t.2.1
  have hd := t.2.2
  refine ⟨hc, hd, ?_, ?_⟩ <;> simp only [triPoint]
  · nlinarith
  · nlinarith

theorem exists_triPoint {z : ℂ} (hz : z ∈ tri) : ∃ u t, triPoint u t = z := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hz
  let t : I := ⟨z.im, h₁, h₂⟩
  by_cases h1 : z.im = 1
  · refine ⟨0, t, Complex.ext ?_ (by simp [triPoint, t])⟩
    simp only [triPoint, t, h1]
    rw [h1] at h₃ h₄
    norm_num
    linarith
  · have hp : 0 < 1 - z.im := by
      have : z.im < 1 := lt_of_le_of_ne h₂ h1
      linarith
    let u : I := ⟨(z.re - z.im / 2) / (1 - z.im), div_nonneg (by linarith) hp.le, by
      rw [div_le_one hp]
      linarith⟩
    refine ⟨u, t, Complex.ext ?_ (by simp [triPoint, t])⟩
    simp only [triPoint, t, u]
    field_simp
    ring

theorem triPoint_inj {u t u' t' : I} (ht : t.1 < 1) (h : triPoint u t = triPoint u' t') :
    u = u' ∧ t = t' := by
  have h₂ : t.1 = t'.1 := congrArg Complex.im h
  have h₁ : t.1 / 2 + (1 - t.1) * u.1 = t'.1 / 2 + (1 - t'.1) * u'.1 := congrArg Complex.re h
  rw [← h₂] at h₁
  have h₃ : (1 - t.1) * u.1 = (1 - t.1) * u'.1 := by linarith
  have h₄ : u.1 = u'.1 := mul_left_cancel₀ (by linarith) h₃
  exact ⟨Subtype.ext h₄, Subtype.ext h₂⟩

/-- A homeomorphism between the triangle and a closed disc with a given boundary map. -/
theorem exists_tri_map {D : Set S} (hD : IsClosedDisc D) {D' : Set S} (hD' : IsClosedDisc D')
    (hin : D ⊆ D' \ discBd D') {β : ℂ → S} (hβc : ContinuousOn β (frontier tri))
    (hβi : InjOn β (frontier tri)) (hβs : β '' frontier tri = discBd D) :
    ∃ ψ : ℂ → S, ContinuousOn ψ tri ∧ InjOn ψ tri ∧ ψ '' tri = D ∧ ∀ z ∈ frontier tri, ψ z = β z
      := by
  classical
  obtain ⟨hT, hTb⟩ := tri_disc
  obtain ⟨p₁⟩ := hT.isOArc_discBd
  have hmem : ∀ w, β (p₁ w).1 ∈ discBd D := fun w =>
    hβs ▸ mem_image_of_mem β (hTb ▸ (p₁ w).2)
  let f : Circle → discBd D := fun w => ⟨β (p₁ w).1, hmem w⟩
  have hfc : Continuous f := by
    refine Continuous.subtype_mk (hβc.comp_continuous ?_ ?_) _
    · exact continuous_subtype_val.comp p₁.continuous
    · exact fun w => hTb ▸ (p₁ w).2
  have hfi : Function.Injective f := by
    intro a b h
    have h₁ := hβi (hTb ▸ (p₁ a).2) (hTb ▸ (p₁ b).2) (congrArg Subtype.val h)
    exact p₁.injective (Subtype.ext h₁)
  have hfs : Function.Surjective f := by
    rintro ⟨x, hx⟩
    rw [← hβs] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    refine ⟨p₁.symm ⟨z, hTb.symm ▸ hz⟩, Subtype.ext ?_⟩
    simp [f]
  let p₂ : Circle ≃ₜ discBd D :=
    (Equiv.ofBijective f ⟨hfi, hfs⟩).toHomeomorphOfContinuousClosed hfc
      (hfc.isClosedMap)
  obtain ⟨c₂, c₂', h₁, -, -, -, h₅, -, h₇, -, h₉⟩ := exists_disc_collar hD hD' hin p₂
  have hbig := isClosedDisc_of_convex (convex_closedBall (0 : ℂ) 3)
    (by rw [interior_closedBall _ (by norm_num)]; exact ⟨0, by simp⟩) isBounded_closedBall
    isClosed_closedBall
  have hbd3 : discBd (closedBall (0 : ℂ) 3) = sphere 0 3 := by
    rw [hbig.2, frontier_closedBall _ (by norm_num)]
  have hTin : tri ⊆ closedBall (0 : ℂ) 3 \ discBd (closedBall (0 : ℂ) 3) := by
    intro z hz
    have := tri_subset_ball hz
    refine ⟨ball_subset_closedBall this, ?_⟩
    rw [hbd3]
    intro h
    rw [mem_ball, dist_zero_right] at this
    rw [mem_sphere, dist_zero_right] at h
    linarith
  obtain ⟨c₁, c₁', g₁, g₂, g₃, g₄, g₅, g₆, g₇, -, g₉⟩ := exists_disc_collar hT hbig.1 hTin p₁
  have hsub12 : closedBall (0 : ℂ) 1 ⊆ closedBall 0 2 := closedBall_subset_closedBall (by norm_num)
  have hin₁ : ∀ z ∈ tri, c₁' z ∈ closedBall (0 : ℂ) 1 ∧ c₁ (c₁' z) = z := by
    intro z hz
    rw [← g₇] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [g₅ (hsub12 hw)]
    exact ⟨hw, rfl⟩
  have hsub3 : tri ⊆ closedBall (0 : ℂ) 3 := fun z hz => (hTin hz).1
  refine ⟨fun z => c₂ (c₁' z), ?_, ?_, ?_, ?_⟩
  · exact (h₁.mono hsub12).comp (g₂.mono hsub3) fun z hz => (hin₁ z hz).1
  · intro z hz z' hz' h
    have h₃ := h₅.injOn (hsub12 (hin₁ z hz).1) (hsub12 (hin₁ z' hz').1) h
    rw [← (hin₁ z hz).2, ← (hin₁ z' hz').2, h₃]
  · ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact h₇ ▸ mem_image_of_mem c₂ (hin₁ z hz).1
    · intro hx
      rw [← h₇] at hx
      obtain ⟨w, hw, rfl⟩ := hx
      refine ⟨c₁ w, g₇ ▸ mem_image_of_mem c₁ hw, ?_⟩
      simp only
      rw [g₅ (hsub12 hw)]
  · intro z hz
    obtain ⟨w, hw⟩ := p₁.surjective ⟨z, hTb.symm ▸ hz⟩
    have hzw : c₁ w = z := by rw [g₉, hw]
    have hwb : (w : ℂ) ∈ closedBall (0 : ℂ) 2 := by simp
    simp only
    rw [← hzw, g₅ hwb, h₉, g₉]
    rfl

/-- Clamp a real number to the unit interval. -/
noncomputable def clamp (x : ℝ) : I := projIcc 0 1 zero_le_one x

theorem clamp_coe (u : I) : clamp u.1 = u := by
  simp [clamp]

theorem continuous_clamp : Continuous clamp := by
  change Continuous (projIcc (0 : ℝ) 1 zero_le_one)
  exact continuous_projIcc

theorem clamp_of_mem {x : ℝ} (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : (clamp x).1 = x := by
  simp [clamp, projIcc_of_mem zero_le_one (show x ∈ Icc (0 : ℝ) 1 from ⟨h₀, h₁⟩)]

/-- **Coordinates on a closed disc with three sides.** -/
theorem exists_square_chart {D : Set S} (hD : IsClosedDisc D) (hman : ∀ x : S, IsInteriorPoint x)
    {ε ℓ₀ ℓ₁ : I → S} (hε : Continuous ε) (h₀ : Continuous ℓ₀) (h₁ : Continuous ℓ₁)
    (iε : Function.Injective ε) (i₀ : Function.Injective ℓ₀) (i₁ : Function.Injective ℓ₁)
    (e00 : ε 0 = ℓ₀ 0) (e10 : ε 1 = ℓ₁ 0) (e11 : ℓ₀ 1 = ℓ₁ 1)
    (m₀ : ∀ s t, ε s = ℓ₀ t → s = 0 ∧ t = 0) (m₁ : ∀ s t, ε s = ℓ₁ t → s = 1 ∧ t = 0)
    (m₂ : ∀ s t, ℓ₀ s = ℓ₁ t → s = 1 ∧ t = 1)
    (hbd : discBd D = range ε ∪ range ℓ₀ ∪ range ℓ₁) :
    ∃ G : I × I → S, Continuous G ∧ (∀ u, G (u, 0) = ε u) ∧ (∀ t, G (0, t) = ℓ₀ t) ∧
      (∀ t, G (1, t) = ℓ₁ t) ∧ (∀ u, G (u, 1) = ℓ₀ 1) ∧ InjOn G {p | p.2 < 1} ∧ range G = D ∧
      (∀ p : I × I, 0 < p.1 → p.1 < 1 → 0 < p.2 → p.2 < 1 → G p ∉ discBd D) := by
  classical
  have hmanP : ∀ x : S, IsManifoldPoint x := fun x => (hman x).isManifoldPoint
  obtain ⟨D', hD', hin, -⟩ := exists_disc_around hmanP hD (fun x _ => hman x) isOpen_univ
    (subset_univ _)
  let β : ℂ → S := fun z =>
    if z.im = 0 then ε (clamp z.re) else if z.re = z.im / 2 then ℓ₀ (clamp z.im) else ℓ₁
      (clamp z.im)
  have hbot : ∀ z : ℂ, z.im = 0 → β z = ε (clamp z.re) := fun z h => by simp [β, h]
  have hzero : clamp 0 = 0 := by
    have := clamp_coe (0 : I)
    simpa using this
  have hone : clamp 1 = 1 := by
    have := clamp_coe (1 : I)
    simpa using this
  have hlft : ∀ z : ℂ, z.re = z.im / 2 → β z = ℓ₀ (clamp z.im) := fun z h => by
    by_cases h0 : z.im = 0
    · have hr : z.re = 0 := by rw [h, h0]; simp
      rw [hbot z h0, hr, h0, hzero, e00]
    · simp [β, h0, h]
  have hrgt : ∀ z : ℂ, z.re = 1 - z.im / 2 → β z = ℓ₁ (clamp z.im) := fun z h => by
    by_cases h0 : z.im = 0
    · have hr : z.re = 1 := by rw [h, h0]; simp
      rw [hbot z h0, hr, h0, hzero, hone, e10]
    · by_cases h2 : z.re = z.im / 2
      · have hi : z.im = 1 := by linarith
        rw [hlft z h2, hi, hone, e11]
      · simp [β, h0, h2]
  let Bot : Set ℂ := {z | z ∈ tri ∧ z.im = 0}
  let Lft : Set ℂ := {z | z ∈ tri ∧ z.re = z.im / 2}
  let Rgt : Set ℂ := {z | z ∈ tri ∧ z.re = 1 - z.im / 2}
  have cre : Continuous fun z : ℂ => z.re := Complex.continuous_re
  have cim : Continuous fun z : ℂ => z.im := Complex.continuous_im
  have cBot : IsClosed Bot := isClosed_tri.inter (isClosed_eq cim continuous_const)
  have cLft : IsClosed Lft := isClosed_tri.inter (isClosed_eq cre (cim.div_const 2))
  have cRgt : IsClosed Rgt := isClosed_tri.inter (isClosed_eq cre (continuous_const.sub
    (cim.div_const 2)))
  have hfr : frontier tri = Bot ∪ Lft ∪ Rgt := by
    ext z
    rw [mem_frontier_tri]
    constructor
    · rintro ⟨hz, h | h | h⟩
      · exact Or.inl (Or.inl ⟨hz, h⟩)
      · exact Or.inl (Or.inr ⟨hz, h⟩)
      · exact Or.inr ⟨hz, h⟩
    · rintro ((⟨hz, h⟩ | ⟨hz, h⟩) | ⟨hz, h⟩)
      · exact ⟨hz, Or.inl h⟩
      · exact ⟨hz, Or.inr (Or.inl h)⟩
      · exact ⟨hz, Or.inr (Or.inr h)⟩
  have hβc : ContinuousOn β (frontier tri) := by
    rw [hfr]
    refine ContinuousOn.union_of_isClosed (ContinuousOn.union_of_isClosed ?_ ?_ cBot cLft) ?_
      (cBot.union cLft) cRgt
    · exact (hε.comp (continuous_clamp.comp cre)).continuousOn.congr fun z hz => hbot z hz.2
    · exact (h₀.comp (continuous_clamp.comp cim)).continuousOn.congr fun z hz => hlft z hz.2
    · exact (h₁.comp (continuous_clamp.comp cim)).continuousOn.congr fun z hz => hrgt z hz.2
  -- Points of the sides, from their coordinates.
  have hreb : ∀ {z : ℂ}, z ∈ tri → 0 ≤ z.re ∧ z.re ≤ 1 := fun ⟨a, _, c, d⟩
    => ⟨by linarith, by linarith⟩
  have ceq : ∀ {x y : ℝ}, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → clamp x = clamp y → x = y := by
    intro x y a b c d h
    have := congrArg Subtype.val h
    rwa [clamp_of_mem a b, clamp_of_mem c d] at this
  have hclamp0 : ∀ {x : ℝ}, 0 ≤ x → x ≤ 1 → clamp x = 0 → x = 0 := fun a b h =>
    ceq a b le_rfl zero_le_one (h.trans hzero.symm)
  have hclamp1 : ∀ {x : ℝ}, 0 ≤ x → x ≤ 1 → clamp x = 1 → x = 1 := fun a b h =>
    ceq a b zero_le_one le_rfl (h.trans hone.symm)
  have hβi : InjOn β (frontier tri) := by
    rw [hfr]
    rintro z ((⟨hz, a⟩ | ⟨hz, a⟩) | ⟨hz, a⟩) w ((⟨hw, b⟩ | ⟨hw, b⟩) | ⟨hw, b⟩) h
    · rw [hbot z a, hbot w b] at h
      exact Complex.ext (ceq (hreb hz).1 (hreb hz).2 (hreb hw).1 (hreb hw).2 (iε h))
        (a.trans b.symm)
    · rw [hbot z a, hlft w b] at h
      obtain ⟨h₃, h₄⟩ := m₀ _ _ h
      have i₄ := hclamp0 hw.1 hw.2.1 h₄
      have r₃ := hclamp0 (hreb hz).1 (hreb hz).2 h₃
      exact Complex.ext (by rw [r₃, b, i₄]; simp) (by rw [a, i₄])
    · rw [hbot z a, hrgt w b] at h
      obtain ⟨h₃, h₄⟩ := m₁ _ _ h
      have i₄ := hclamp0 hw.1 hw.2.1 h₄
      have r₃ := hclamp1 (hreb hz).1 (hreb hz).2 h₃
      exact Complex.ext (by rw [r₃, b, i₄]; simp) (by rw [a, i₄])
    · rw [hlft z a, hbot w b] at h
      obtain ⟨h₃, h₄⟩ := m₀ _ _ h.symm
      have i₄ := hclamp0 hz.1 hz.2.1 h₄
      have r₃ := hclamp0 (hreb hw).1 (hreb hw).2 h₃
      exact Complex.ext (by rw [r₃, a, i₄]; simp) (by rw [b, i₄])
    · rw [hlft z a, hlft w b] at h
      have i₃ := ceq hz.1 hz.2.1 hw.1 hw.2.1 (i₀ h)
      exact Complex.ext (by rw [a, b, i₃]) i₃
    · rw [hlft z a, hrgt w b] at h
      obtain ⟨h₃, h₄⟩ := m₂ _ _ h
      have i₃ := hclamp1 hz.1 hz.2.1 h₃
      have i₄ := hclamp1 hw.1 hw.2.1 h₄
      exact Complex.ext (by rw [a, b, i₃, i₄]; norm_num) (i₃.trans i₄.symm)
    · rw [hrgt z a, hbot w b] at h
      obtain ⟨h₃, h₄⟩ := m₁ _ _ h.symm
      have i₄ := hclamp0 hz.1 hz.2.1 h₄
      have r₃ := hclamp1 (hreb hw).1 (hreb hw).2 h₃
      exact Complex.ext (by rw [r₃, a, i₄]; simp) (by rw [b, i₄])
    · rw [hrgt z a, hlft w b] at h
      obtain ⟨h₃, h₄⟩ := m₂ _ _ h.symm
      have i₃ := hclamp1 hz.1 hz.2.1 h₄
      have i₄ := hclamp1 hw.1 hw.2.1 h₃
      exact Complex.ext (by rw [a, b, i₃, i₄]; norm_num) (i₃.trans i₄.symm)
    · rw [hrgt z a, hrgt w b] at h
      have i₃ := ceq hz.1 hz.2.1 hw.1 hw.2.1 (i₁ h)
      exact Complex.ext (by rw [a, b, i₃]) i₃
  have hmemb : ∀ u : I, ((u.1 : ℂ)) ∈ tri := fun u => by
    refine ⟨by simp, by simp, by simpa using u.2.1, by simpa using u.2.2⟩
  have hmeml : ∀ t : I, triPoint 0 t ∈ tri := fun t => triPoint_mem _ _
  have hmemr : ∀ t : I, triPoint 1 t ∈ tri := fun t => triPoint_mem _ _
  have lre : ∀ t : I, (triPoint 0 t).re = (triPoint 0 t).im / 2 := fun t => by simp [triPoint]
  have rre : ∀ t : I, (triPoint 1 t).re = 1 - (triPoint 1 t).im / 2 := fun t => by
    simp [triPoint]
    ring
  have him : ∀ u t : I, (triPoint u t).im = t.1 := fun _ _ => rfl
  have bim : ∀ t : I, triPoint t 0 = (t.1 : ℂ) := fun t => Complex.ext (by simp [triPoint])
    (by simp [triPoint])
  have hβs : β '' frontier tri = discBd D := by
    rw [hbd, hfr]
    apply subset_antisymm
    · rintro _ ⟨z, (⟨hz, a⟩ | ⟨hz, a⟩) | ⟨hz, a⟩, rfl⟩
      · rw [hbot z a]
        exact Or.inl (Or.inl ⟨_, rfl⟩)
      · rw [hlft z a]
        exact Or.inl (Or.inr ⟨_, rfl⟩)
      · rw [hrgt z a]
        exact Or.inr ⟨_, rfl⟩
    · rintro x ((⟨t, rfl⟩ | ⟨t, rfl⟩) | ⟨t, rfl⟩)
      · refine ⟨t.1, Or.inl (Or.inl ⟨hmemb t, by simp⟩), ?_⟩
        rw [hbot _ (by simp)]
        simp [clamp_coe]
      · refine ⟨triPoint 0 t, Or.inl (Or.inr ⟨hmeml t, lre t⟩), ?_⟩
        rw [hlft _ (lre t), him, clamp_coe]
      · refine ⟨triPoint 1 t, Or.inr ⟨hmemr t, rre t⟩, ?_⟩
        rw [hrgt _ (rre t), him, clamp_coe]
  obtain ⟨ψ, hψc, hψi, hψs, hψb⟩ := exists_tri_map hD hD' hin hβc hβi hβs
  have hfrm : ∀ {z}, z ∈ Bot ∪ Lft ∪ Rgt → z ∈ frontier tri := fun h => hfr ▸ h
  refine ⟨fun p => ψ (triPoint p.1 p.2), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hψc.comp_continuous continuous_triPoint fun p => triPoint_mem _ _
  · intro u
    have hz : (u.1 : ℂ) ∈ Bot := ⟨hmemb u, by simp⟩
    simp only
    rw [bim, hψb _ (hfrm (Or.inl (Or.inl hz))), hbot _ hz.2]
    simp [clamp_coe]
  · intro t
    simp only
    rw [hψb _ (hfrm (Or.inl (Or.inr ⟨hmeml t, lre t⟩))), hlft _ (lre t), him, clamp_coe]
  · intro t
    simp only
    rw [hψb _ (hfrm (Or.inr ⟨hmemr t, rre t⟩)), hrgt _ (rre t), him, clamp_coe]
  · intro u
    have heq : triPoint u 1 = triPoint 0 1 := Complex.ext (by simp [triPoint]) rfl
    simp only
    rw [heq, hψb _ (hfrm (Or.inl (Or.inr ⟨hmeml 1, lre 1⟩))), hlft _ (lre 1), him, clamp_coe]
  · rintro ⟨u, t⟩ ht ⟨u', t'⟩ ht' h
    obtain ⟨a, b⟩ := triPoint_inj ht (hψi (triPoint_mem _ _) (triPoint_mem _ _) h)
    exact Prod.ext a b
  · ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact hψs ▸ mem_image_of_mem ψ (triPoint_mem _ _)
    · intro hx
      rw [← hψs] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      obtain ⟨u, t, rfl⟩ := exists_triPoint hz
      exact ⟨(u, t), rfl⟩
  · rintro ⟨u, t⟩ hu0 hu1 ht0 ht1 hmem
    rw [← hβs] at hmem
    obtain ⟨z, hz, hze⟩ := hmem
    have hzt : z ∈ tri := frontier_subset_closure (s := tri) hz |> fun h
      => isClosed_tri.closure_eq ▸ h
    rw [← hψb z hz] at hze
    have heq := hψi hzt (triPoint_mem _ _) hze
    have hmem' := mem_frontier_tri.mp hz
    rw [heq] at hmem'
    have u₀ : (0 : ℝ) < u.1 := hu0
    have u₁ : u.1 < 1 := hu1
    have t₀ : (0 : ℝ) < t.1 := ht0
    have t₁ : t.1 < 1 := ht1
    rcases hmem'.2 with h | h | h
    · simp only [triPoint] at h
      linarith
    · simp only [triPoint] at h
      nlinarith
    · simp only [triPoint] at h
      nlinarith

end GraphMinor.GM11
