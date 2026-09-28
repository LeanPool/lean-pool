/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Motion.Foundations.Development003
public import LeanPool.MovingSofa.Sofa.Applications.Development001

/-!
# Moving sofa: related mathematical developments

* `Motion.RotationAngle`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Motion / Rotation Angle
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- A nonnegative combination of two points of a convex set containing the origin, with
coefficient sum at most one, lies in the set. -/
private theorem smul_add_smul_mem_of_convex {U : Set Point} (hU : Convex ℝ U)
    (h0 : (0 : Point) ∈ U) {x y : Point} (hx : x ∈ U) (hy : y ∈ U)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    a • x + b • y ∈ U := by
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ (![a, b, 1 - a - b] : Fin 3 → ℝ) i := by
    intro i _
    fin_cases i
    · exact ha
    · exact hb
    · show (0 : ℝ) ≤ 1 - a - b
      linarith
  have hsum : ∑ i ∈ (Finset.univ : Finset (Fin 3)), (![a, b, 1 - a - b] : Fin 3 → ℝ) i = 1 := by
    simp [Fin.sum_univ_three]
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      (![x, y, (0 : Point)] : Fin 3 → Point) i ∈ U := by
    intro i _
    fin_cases i
    · exact hx
    · exact hy
    · exact h0
  simpa [Fin.sum_univ_three] using hU.sum_mem hw hsum hz

/-- A point of the strip parallelogram on or below the line through `o_ω - v₀` and
`o_ω - u_ω` lies in every convex set containing the origin and those two points. -/
private theorem mem_of_inner_add_le_one_sub_sin {ω : ℝ} (hω0 : 0 < ω) (hω : ω < Real.pi / 2)
    {U : Set Point} (hU : Convex ℝ U) (h0 : (0 : Point) ∈ U)
    (ha : (stripParallelogram ω).2.2 - tangentVector 0 ∈ U)
    (hb : (stripParallelogram ω).2.2 - normalVector (ω : Real.Angle) ∈ U)
    {p : Point} (hy : 0 ≤ p 1) (hx : 0 ≤ inner ℝ p (normalVector (ω : Real.Angle)))
    (hsum : inner ℝ p (normalVector (ω : Real.Angle)) + p 1 ≤ 1 - Real.sin ω) :
    p ∈ U := by
  have hpi := Real.pi_pos
  have hcos : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo ⟨by linarith, hω⟩
  have hsinlt : Real.sin ω < 1 := by nlinarith [Real.sin_sq_add_cos_sq ω]
  have hgap := parallelogram_gap ω ⟨hω0.le, hω⟩
  have hccos : Real.tan ((Real.pi / 2 - ω) / 2) * Real.cos ω = 1 - Real.sin ω := by
    rw [hgap.2.2.2.2, Real.tan_eq_sin_div_cos]
    field_simp
  have hi1 : inner ℝ (normalVector (0 : Real.Angle)) (normalVector (ω : Real.Angle)) =
      Real.cos ω := by
    rw [← Real.Angle.coe_zero, inner_normalVector_normalVector, zero_sub, Real.cos_neg]
  have hi2 : inner ℝ (normalVector (0 : Real.Angle))
      (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := by
    rw [← Real.Angle.coe_zero, inner_normalVector_normalVector, zero_sub, Real.cos_neg,
      Real.cos_pi_div_two]
  have hi3 : inner ℝ (tangentVector (ω : Real.Angle)) (normalVector (ω : Real.Angle)) = 0 := by
    rw [inner_tangentVector_normalVector_real, sub_self, Real.sin_zero]
  have hi4 : inner ℝ (tangentVector (ω : Real.Angle))
      (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = Real.cos ω := by
    rw [inner_tangentVector_normalVector_real, Real.sin_pi_div_two_sub]
  have hsne : Real.sin (ω - Real.pi / 2) = -Real.cos ω := by
    rw [Real.sin_sub, Real.sin_pi_div_two, Real.cos_pi_div_two]
    ring
  have hden : (1 : ℝ) - Real.sin ω ≠ 0 := by linarith
  have hkey : p = (inner ℝ p (normalVector (ω : Real.Angle)) / (1 - Real.sin ω)) •
        ((stripParallelogram ω).2.2 - tangentVector 0) +
      (p 1 / (1 - Real.sin ω)) •
        ((stripParallelogram ω).2.2 - normalVector (ω : Real.Angle)) := by
    refine eq_of_inner_normalVector_eq (s := ω) (t := Real.pi / 2) ?_ ?_ ?_
    · rw [hsne]
      exact neg_ne_zero.mpr hcos.ne'
    · rw [hgap.1, hgap.2.1, inner_add_left, real_inner_smul_left, real_inner_smul_left,
        real_inner_smul_left, real_inner_smul_left, hi1, hi3, hccos]
      field_simp
      ring
    · rw [inner_normalVector_pi_div_two, hgap.1, hgap.2.1, inner_add_left,
        real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
        real_inner_smul_left, hi2, hi4, hccos]
      field_simp
      ring
  rw [hkey]
  refine smul_add_smul_mem_of_convex hU h0 ha hb (div_nonneg hx (by linarith))
    (div_nonneg hy (by linarith)) ?_
  rw [← add_div, div_le_one (by linarith)]
  linarith

/-- The width of a clipped strip parallelogram is at most one in every direction between
its rotation angle and a right angle. -/
private theorem inner_sub_inner_le_one_of_clipped {ω : ℝ} (hω0 : 0 ≤ ω)
    (hcos : 0 < Real.cos ω) {p q : Point}
    (hpA : inner ℝ p (normalVector (ω : Real.Angle)) ≤ 1) (hpB : p 1 ≤ 1)
    (hqA : 0 ≤ inner ℝ q (normalVector (ω : Real.Angle))) (hqB : 0 ≤ q 1)
    (hq : 1 - Real.sin ω ≤ inner ℝ q (normalVector (ω : Real.Angle)) + q 1)
    {t : ℝ} (ht : ω ≤ t) (ht' : t ≤ Real.pi / 2) :
    inner ℝ p (normalVector (t : Real.Angle)) -
      inner ℝ q (normalVector (t : Real.Angle)) ≤ 1 := by
  have hpi := Real.pi_pos
  have hct : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc ⟨by linarith, ht'⟩
  have hst : 0 ≤ Real.sin (t - ω) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hsub : Real.sin (t - ω) = Real.sin t * Real.cos ω - Real.cos t * Real.sin ω :=
    Real.sin_sub t ω
  have hid : ∀ z : Point, Real.cos ω * inner ℝ z (normalVector (t : Real.Angle)) =
      Real.cos t * inner ℝ z (normalVector (ω : Real.Angle)) + Real.sin (t - ω) * z 1 := by
    intro z
    rw [inner_normalVector_real, inner_normalVector_real, hsub]
    ring
  have hmain : Real.cos ω * (inner ℝ p (normalVector (t : Real.Angle)) -
      inner ℝ q (normalVector (t : Real.Angle))) ≤ Real.cos ω := by
    rw [mul_sub, hid p, hid q]
    have h1 : Real.cos t * inner ℝ p (normalVector (ω : Real.Angle)) ≤ Real.cos t :=
      mul_le_of_le_one_right hct hpA
    have h2 : Real.sin (t - ω) * p 1 ≤ Real.sin (t - ω) :=
      mul_le_of_le_one_right hst hpB
    rcases le_total (Real.cos t) (Real.sin (t - ω)) with hle | hle
    · have e1 : Real.cos t * (1 - Real.sin ω) ≤
          Real.cos t * (inner ℝ q (normalVector (ω : Real.Angle)) + q 1) :=
        mul_le_mul_of_nonneg_left hq hct
      have e2 : 0 ≤ (Real.sin (t - ω) - Real.cos t) * q 1 := mul_nonneg (by linarith) hqB
      have h3 : Real.cos t * (1 - Real.sin ω) ≤
          Real.cos t * inner ℝ q (normalVector (ω : Real.Angle)) + Real.sin (t - ω) * q 1 := by
        nlinarith [e1, e2]
      have h4 : Real.sin (t - ω) + Real.cos t * Real.sin ω = Real.sin t * Real.cos ω := by
        rw [hsub]; ring
      have h5 : Real.sin t * Real.cos ω ≤ Real.cos ω := by
        nlinarith [Real.sin_le_one t]
      linarith
    · have e1 : Real.sin (t - ω) * (1 - Real.sin ω) ≤
          Real.sin (t - ω) * (inner ℝ q (normalVector (ω : Real.Angle)) + q 1) :=
        mul_le_mul_of_nonneg_left hq hst
      have e2 : 0 ≤ (Real.cos t - Real.sin (t - ω)) *
          inner ℝ q (normalVector (ω : Real.Angle)) := mul_nonneg (by linarith) hqA
      have h3 : Real.sin (t - ω) * (1 - Real.sin ω) ≤
          Real.cos t * inner ℝ q (normalVector (ω : Real.Angle)) + Real.sin (t - ω) * q 1 := by
        nlinarith [e1, e2]
      have h4 : Real.cos t + Real.sin (t - ω) * Real.sin ω =
          Real.cos ω * Real.cos (t - ω) := by
        rw [hsub, Real.cos_sub]
        linear_combination (-Real.cos t) * Real.sin_sq_add_cos_sq ω
      have h5 : Real.cos ω * Real.cos (t - ω) ≤ Real.cos ω := by
        nlinarith [Real.cos_le_one (t - ω)]
      linarith
  nlinarith [hmain]

/-- Normalizing data for the rotated copies of a sofa of width at most one: a continuous
minimal height and a uniform horizontal bound. -/
private theorem exists_normalization_of_width {s : Set Point} {ω : ℝ}
    (hcpt : IsCompact s) (hne : s.Nonempty)
    (hwidth : ∀ t : ℝ, ω ≤ t → t ≤ Real.pi / 2 → ∀ p ∈ s, ∀ q ∈ s,
      inner ℝ p (normalVector (t : Real.Angle)) -
        inner ℝ q (normalVector (t : Real.Angle)) ≤ 1) :
    ∃ (low : ℝ → ℝ) (M : ℝ), Continuous low ∧
      (∀ d : ℝ, ∀ p ∈ s, (rotationMap ((d : ℝ) : Real.Angle) p) 0 ≤ M) ∧
      (∀ d : ℝ, ∀ p ∈ s, low d ≤ (rotationMap ((d : ℝ) : Real.Angle) p) 1) ∧
      (∀ d : ℝ, 0 ≤ d → d ≤ Real.pi / 2 - ω → ∀ p ∈ s,
        (rotationMap ((d : ℝ) : Real.Angle) p) 1 - low d ≤ 1) := by
  have hcoord1 : ∀ (d : ℝ) (p : Point), (rotationMap ((d : ℝ) : Real.Angle) p) 1 =
      inner ℝ p (normalVector ((Real.pi / 2 - d : ℝ) : Real.Angle)) := by
    intro d p
    rw [rotationMap_apply_one, inner_normalVector_real, Real.Angle.cos_coe, Real.Angle.sin_coe,
      Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
    ring
  obtain ⟨R, hR⟩ := hcpt.isBounded.subset_closedBall (0 : Point)
  refine ⟨fun d ↦ -supportValue s ((Real.pi / 2 - d + Real.pi : ℝ) : Real.Angle),
    max R 0, ?_, ?_, ?_, ?_⟩
  · exact ((compactSet_support_continuity s s hne hcpt hne hcpt).2.2.1.comp
      (Real.Angle.continuous_coe.comp (by fun_prop))).neg
  · intro d p hp
    have hnp : ‖p‖ ≤ max R 0 := by
      have h := hR hp
      rw [Metric.mem_closedBall, dist_zero_right] at h
      exact h.trans (le_max_left _ _)
    have hn : ‖rotationMap ((d : ℝ) : Real.Angle) p‖ = ‖p‖ := by
      show ‖(EuclideanGeometry.o.rotation ((d : ℝ) : Real.Angle)) p‖ = ‖p‖
      exact LinearIsometryEquiv.norm_map _ p
    calc (rotationMap ((d : ℝ) : Real.Angle) p) 0
        = inner ℝ (rotationMap ((d : ℝ) : Real.Angle) p)
            (normalVector ((0 : ℝ) : Real.Angle)) := (inner_normalVector_zero _).symm
      _ ≤ ‖rotationMap ((d : ℝ) : Real.Angle) p‖ *
            ‖normalVector ((0 : ℝ) : Real.Angle)‖ := real_inner_le_norm _ _
      _ = ‖p‖ := by rw [norm_normalVector_real, hn, mul_one]
      _ ≤ max R 0 := hnp
  · intro d p hp
    rw [hcoord1]
    have h := inner_le_supportValue_of_isCompact hcpt hp
      ((Real.pi / 2 - d + Real.pi : ℝ) : Real.Angle)
    rw [normalVector_add_pi, inner_neg_right] at h
    show -supportValue s ((Real.pi / 2 - d + Real.pi : ℝ) : Real.Angle) ≤ _
    linarith
  · intro d hd0 hd1 p hp
    have ht : ω ≤ Real.pi / 2 - d := by linarith
    have ht' : Real.pi / 2 - d ≤ Real.pi / 2 := by linarith
    have hstep : supportValue s ((Real.pi / 2 - d + Real.pi : ℝ) : Real.Angle) ≤
        1 - inner ℝ p (normalVector ((Real.pi / 2 - d : ℝ) : Real.Angle)) := by
      refine csSup_le (hne.image _) ?_
      rintro _ ⟨q, hq, rfl⟩
      simp only [normalVector_add_pi, inner_neg_right]
      have h := hwidth (Real.pi / 2 - d) ht ht' p hp q hq
      linarith
    rw [hcoord1]
    show inner ℝ p (normalVector ((Real.pi / 2 - d : ℝ) : Real.Angle)) -
      -supportValue s ((Real.pi / 2 - d + Real.pi : ℝ) : Real.Angle) ≤ 1
    linarith

/-- A sofa of rotation angle `ω` that can be placed at height between zero and one in every
intermediate rotated position admits, after rotating by `π/2 - ω`, a motion of rotation
angle `π/2`. -/
private theorem hasRotationAngle_rotationMap_of_normalization {s : Set Point} {ω : ℝ}
    (hlt : ω < Real.pi / 2) (hconn : IsConnected s) (hcpt : IsCompact s)
    (hrot : HasRotationAngle s ω) (low : ℝ → ℝ) (M : ℝ) (hlowcont : Continuous low)
    (hhoriz : ∀ d : ℝ, ∀ p ∈ s, (rotationMap ((d : ℝ) : Real.Angle) p) 0 ≤ M)
    (hloleq : ∀ d : ℝ, ∀ p ∈ s, low d ≤ (rotationMap ((d : ℝ) : Real.Angle) p) 1)
    (hupleq : ∀ d : ℝ, 0 ≤ d → d ≤ Real.pi / 2 - ω → ∀ p ∈ s,
      (rotationMap ((d : ℝ) : Real.Angle) p) 1 - low d ≤ 1) :
    HasRotationAngle (rotationMap ((Real.pi / 2 - ω : ℝ) : Real.Angle) '' s)
      (Real.pi / 2) := by
  have hrot0 : ∀ p : Point, rotationMap ((0 : ℝ) : Real.Angle) p = p := by
    intro p
    rw [rotationMap, Real.Angle.coe_zero, Orientation.rotation_zero]
    rfl
  set δ₀ : ℝ := Real.pi / 2 - ω with hδ₀def
  have hδ₀pos : 0 < δ₀ := by rw [hδ₀def]; linarith
  -- the original motion witnessing rotation angle `ω`
  obtain ⟨m₀, hm₀, α₀, hα₀c, hα₀0, hα₀1, hm₀lift⟩ := hrot
  obtain ⟨v, hv⟩ := hm₀.2.2.2.1
  have hm₀0 : m₀ 0 0 = v := by rw [hv]; exact zero_add v
  have hinit : ∀ p ∈ s, p 0 + v 0 ≤ 1 ∧ 0 ≤ p 1 + v 1 ∧ p 1 + v 1 ≤ 1 := by
    intro p hp
    exact mem_horizontalHallway_coordinates (hm₀.2.2.2.2.2.1 ⟨p, hp, hv p⟩)
  have hmcam : Continuous
      (fun t : unitInterval ↦ (m₀ t).toAffineIsometry.toContinuousAffineMap) :=
    continuous_induced_dom.comp hm₀.2.2.1
  -- the reparametrized motion of the rotated sofa
  have hτmem : ∀ r : unitInterval, max (3 * (r : ℝ) - 2) 0 ∈ unitInterval :=
    fun r ↦ ⟨le_max_right _ _, max_le (by linarith [r.2.2]) (by norm_num)⟩
  set τ : unitInterval → unitInterval := fun r ↦ ⟨max (3 * (r : ℝ) - 2) 0, hτmem r⟩ with hτdef
  set Θ : unitInterval → ℝ := fun r ↦ -δ₀ * min (3 * (r : ℝ)) 1 + α₀ (τ r) with hΘdef
  set dd : unitInterval → ℝ := fun r ↦ δ₀ * (1 - min (3 * (r : ℝ)) 1) with hdddef
  set σ : unitInterval → ℝ := fun r ↦ min (max (3 * (r : ℝ) - 1) 0) 1 with hσdef
  set C : unitInterval → Point := fun r ↦
    (1 - σ r) • (!₂[-M, -low (dd r)] : Point) + σ r • v + (m₀ (τ r) 0 - v) with hCdef
  set n : unitInterval → Point ≃ᵃⁱ[ℝ] Point := fun r ↦
    (EuclideanGeometry.o.rotation ((Θ r : ℝ) : Real.Angle)).toAffineIsometryEquiv.trans
      (AffineIsometryEquiv.vaddConst ℝ (C r)) with hndef
  have hnapp : ∀ (r : unitInterval) (p : Point),
      n r p = rotationMap ((Θ r : ℝ) : Real.Angle) p + C r := fun _ _ ↦ rfl
  have hn0eq : ∀ r : unitInterval, n r 0 = C r := by
    intro r
    rw [hnapp, rotationMap]
    simp
  have hcompose : ∀ (r : unitInterval) (p : Point),
      n r (rotationMap ((δ₀ : ℝ) : Real.Angle) p) =
        rotationMap ((dd r + α₀ (τ r) : ℝ) : Real.Angle) p + C r := by
    intro r p
    have hΘsum : Θ r + δ₀ = dd r + α₀ (τ r) := by
      show -δ₀ * min (3 * (r : ℝ)) 1 + α₀ (τ r) + δ₀ =
        δ₀ * (1 - min (3 * (r : ℝ)) 1) + α₀ (τ r)
      ring
    rw [hnapp]
    congr 1
    show (EuclideanGeometry.o.rotation ((Θ r : ℝ) : Real.Angle))
        ((EuclideanGeometry.o.rotation ((δ₀ : ℝ) : Real.Angle)) p) =
      (EuclideanGeometry.o.rotation ((dd r + α₀ (τ r) : ℝ) : Real.Angle)) p
    rw [Orientation.rotation_rotation, ← Real.Angle.coe_add, hΘsum]
  have hτzero : ∀ r : unitInterval, 3 * (r : ℝ) ≤ 2 → τ r = 0 := by
    intro r hr
    apply Subtype.ext
    show max (3 * (r : ℝ) - 2) 0 = 0
    exact max_eq_right (by linarith)
  -- phase one: rotating down to the horizontal position
  have hphaseA : ∀ r : unitInterval, 3 * (r : ℝ) ≤ 1 → ∀ p ∈ s,
      n r (rotationMap ((δ₀ : ℝ) : Real.Angle) p) ∈ horizontalHallway := by
    intro r hr p hp
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := r.2.1
    have hτ0 : τ r = 0 := hτzero r (by linarith)
    have hσ0 : σ r = 0 := by
      show min (max (3 * (r : ℝ) - 1) 0) 1 = 0
      rw [max_eq_right (by linarith)]
      exact min_eq_left (by norm_num)
    have hdd : dd r = δ₀ * (1 - 3 * (r : ℝ)) := by
      show δ₀ * (1 - min (3 * (r : ℝ)) 1) = _
      rw [min_eq_left hr]
    have hdd0 : 0 ≤ dd r := by
      rw [hdd]
      exact mul_nonneg hδ₀pos.le (by linarith)
    have hdd1 : dd r ≤ δ₀ := by
      have h := mul_le_mul_of_nonneg_left (show 1 - 3 * (r : ℝ) ≤ 1 by linarith) hδ₀pos.le
      rw [hdd]
      linarith [h]
    have hC : C r = (!₂[-M, -low (dd r)] : Point) := by
      show (1 - σ r) • (!₂[-M, -low (dd r)] : Point) + σ r • v + (m₀ (τ r) 0 - v) = _
      rw [hσ0, hτ0, hm₀0]
      simp
    have heval : n r (rotationMap ((δ₀ : ℝ) : Real.Angle) p) =
        rotationMap ((dd r : ℝ) : Real.Angle) p + (!₂[-M, -low (dd r)] : Point) := by
      rw [hcompose, hτ0, hα₀0, add_zero, hC]
    rw [heval]
    refine mem_horizontalHallway_of_coordinates _ ?_ ⟨?_, ?_⟩
    · show (rotationMap ((dd r : ℝ) : Real.Angle) p) 0 + -M ≤ 1
      have h := hhoriz (dd r) p hp
      linarith
    · show (0 : ℝ) ≤ (rotationMap ((dd r : ℝ) : Real.Angle) p) 1 + -low (dd r)
      have h := hloleq (dd r) p hp
      linarith
    · show (rotationMap ((dd r : ℝ) : Real.Angle) p) 1 + -low (dd r) ≤ 1
      have h := hupleq (dd r) hdd0 hdd1 p hp
      linarith
  -- phase two: translating to the initial placement of the original motion
  have hphaseB : ∀ r : unitInterval, 1 ≤ 3 * (r : ℝ) → 3 * (r : ℝ) ≤ 2 → ∀ p ∈ s,
      n r (rotationMap ((δ₀ : ℝ) : Real.Angle) p) ∈ horizontalHallway := by
    intro r hr hr' p hp
    have hτ0 : τ r = 0 := hτzero r hr'
    have hσ : σ r = 3 * (r : ℝ) - 1 := by
      show min (max (3 * (r : ℝ) - 1) 0) 1 = _
      rw [max_eq_left (by linarith)]
      exact min_eq_left (by linarith)
    have hσ0 : 0 ≤ σ r := by rw [hσ]; linarith
    have hσ1 : σ r ≤ 1 := by rw [hσ]; linarith
    have hdd : dd r = 0 := by
      show δ₀ * (1 - min (3 * (r : ℝ)) 1) = 0
      rw [min_eq_right hr]
      ring
    have hC : C r = (1 - σ r) • (!₂[-M, -low 0] : Point) + σ r • v := by
      show (1 - σ r) • (!₂[-M, -low (dd r)] : Point) + σ r • v + (m₀ (τ r) 0 - v) = _
      rw [hdd, hτ0, hm₀0]
      simp
    have heval : n r (rotationMap ((δ₀ : ℝ) : Real.Angle) p) =
        p + ((1 - σ r) • (!₂[-M, -low 0] : Point) + σ r • v) := by
      rw [hcompose, hτ0, hα₀0, add_zero, hdd, hrot0, hC]
    have h1 := hloleq 0 p hp
    have h2 := hupleq 0 le_rfl hδ₀pos.le p hp
    have hhz := hhoriz 0 p hp
    rw [hrot0] at h1 h2 hhz
    obtain ⟨hi1, hi2, hi3⟩ := hinit p hp
    rw [heval]
    refine mem_horizontalHallway_of_coordinates _ ?_ ⟨?_, ?_⟩
    · show p 0 + ((1 - σ r) * -M + σ r * v 0) ≤ 1
      have k1 : 0 ≤ (1 - σ r) * (M - p 0) := mul_nonneg (by linarith) (by linarith)
      have k2 : 0 ≤ σ r * (1 - (p 0 + v 0)) := mul_nonneg hσ0 (by linarith)
      nlinarith only [k1, k2, hσ1]
    · show (0 : ℝ) ≤ p 1 + ((1 - σ r) * -low 0 + σ r * v 1)
      have k3 : 0 ≤ (1 - σ r) * (p 1 - low 0) := mul_nonneg (by linarith) (by linarith)
      have k4 : 0 ≤ σ r * (p 1 + v 1) := mul_nonneg hσ0 (by linarith)
      nlinarith only [k3, k4]
    · show p 1 + ((1 - σ r) * -low 0 + σ r * v 1) ≤ 1
      have k5 : 0 ≤ (1 - σ r) * (1 - (p 1 - low 0)) := mul_nonneg (by linarith) (by linarith)
      have k6 : 0 ≤ σ r * (1 - (p 1 + v 1)) := mul_nonneg hσ0 (by linarith)
      nlinarith only [k5, k6]
  -- phase three: the original motion
  have hphaseC : ∀ r : unitInterval, 2 ≤ 3 * (r : ℝ) → ∀ p : Point,
      n r (rotationMap ((δ₀ : ℝ) : Real.Angle) p) = m₀ (τ r) p := by
    intro r hr p
    have hσ1 : σ r = 1 := by
      show min (max (3 * (r : ℝ) - 1) 0) 1 = 1
      rw [max_eq_left (by linarith)]
      exact min_eq_right (by linarith)
    have hdd : dd r = 0 := by
      show δ₀ * (1 - min (3 * (r : ℝ)) 1) = 0
      rw [min_eq_right (by linarith)]
      ring
    have hC : C r = m₀ (τ r) 0 := by
      show (1 - σ r) • (!₂[-M, -low (dd r)] : Point) + σ r • v + (m₀ (τ r) 0 - v) = _
      rw [hσ1]
      simp
    rw [hcompose, hC, hdd, zero_add, hm₀lift (τ r) p]
  -- continuity of the reparametrized motion
  have hτcont : Continuous τ := by
    rw [hτdef]
    exact Continuous.subtype_mk (by fun_prop) _
  have hσcont : Continuous σ := by rw [hσdef]; fun_prop
  have hddcont : Continuous dd := by rw [hdddef]; fun_prop
  have hΘcont : Continuous Θ := by
    rw [hΘdef]
    exact (continuous_const.mul (by fun_prop)).add (hα₀c.comp hτcont)
  have hbasecont : Continuous (fun r : unitInterval ↦ (!₂[-M, -low (dd r)] : Point)) := by
    have h : Continuous (fun r : unitInterval ↦ -low (dd r)) := (hlowcont.comp hddcont).neg
    fun_prop
  have hCcont : Continuous C := by
    rw [hCdef]
    exact (((continuous_const.sub hσcont).smul hbasecont).add
        (hσcont.smul continuous_const)).add
      (((hmcam.eval_const 0).comp hτcont).sub continuous_const)
  have hncont : Continuous n := by
    rw [hndef]
    exact continuous_rotation_trans_vaddConst (Real.Angle.continuous_coe.comp hΘcont) hCcont
  -- endpoint values
  have hτ1 : τ 1 = 1 := by
    apply Subtype.ext
    show max (3 * ((1 : unitInterval) : ℝ) - 2) 0 = ((1 : unitInterval) : ℝ)
    norm_num
  have hΘ0 : Θ 0 = 0 := by
    show -δ₀ * min (3 * ((0 : unitInterval) : ℝ)) 1 + α₀ (τ 0) = 0
    rw [hτzero 0 (by norm_num), hα₀0]
    norm_num
  have hΘ1 : Θ 1 = -(Real.pi / 2) := by
    show -δ₀ * min (3 * ((1 : unitInterval) : ℝ)) 1 + α₀ (τ 1) = -(Real.pi / 2)
    rw [hτ1, hα₀1, show (3 : ℝ) * ((1 : unitInterval) : ℝ) = 3 by norm_num,
      min_eq_right (by norm_num : (1 : ℝ) ≤ 3), hδ₀def]
    ring
  have hrotcont : Continuous (rotationMap ((δ₀ : ℝ) : Real.Angle)) :=
    (EuclideanGeometry.o.rotation ((δ₀ : ℝ) : Real.Angle)).continuous
  refine ⟨n, ⟨hconn.image _ hrotcont.continuousOn, (hcpt.image hrotcont).isClosed, hncont,
    ⟨C 0, ?_⟩, ?_, ?_, ?_, ?_⟩, Θ, hΘcont, hΘ0, hΘ1, ?_⟩
  · intro p
    rw [hnapp, hΘ0, hrot0]
  · intro t
    exact ⟨((Θ t : ℝ) : Real.Angle), fun p ↦ by rw [hnapp, hn0eq]⟩
  · rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact hphaseA 0 (by norm_num) p hp
  · intro r
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    rcases le_total (3 * (r : ℝ)) 1 with h | h
    · exact Set.subset_union_left (hphaseA r h p hp)
    · rcases le_total (3 * (r : ℝ)) 2 with h' | h'
      · exact Set.subset_union_left (hphaseB r h h' p hp)
      · rw [hphaseC r h' p]
        exact hm₀.2.2.2.2.2.2.1 (τ r) ⟨p, hp, rfl⟩
  · rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    rw [hphaseC 1 (by norm_num) p, hτ1]
    exact hm₀.2.2.2.2.2.2.2 ⟨p, hp, rfl⟩
  · intro r p
    rw [hnapp, hn0eq]

theorem balancedMaximumSofa_rightAngle (s : Set Point) (ω : ℝ)
    (hs : IsBalancedMaximumSofa s ω)
    (hω : ω ∈ Set.Icc (Real.arccos (5 / 11 : ℝ)) (Real.pi / 2))
    (hArea : 11 / 5 ≤ ClassicalResults.area s) :
    ∃ α : Real.Angle, HasRotationAngle (rotationMap α '' s) (Real.pi / 2) := by
  have hpi := Real.pi_pos
  obtain ⟨⟨s₀, hs₀, hsdef⟩, K, hKcap, hKbal⟩ := hs
  have hstd : IsStandardPosition s ω := by
    rw [hsdef]
    exact (standardPosition_monotonization_standard s₀ ω hs₀).1
  have hω0 : 0 < ω := hstd.2.2.1
  have hconn : IsConnected s := by
    rw [hsdef]
    exact standardPosition_monotonization_connected s₀ ω hs₀
  have hcpt : IsCompact s := hstd.1
  have hrot : HasRotationAngle s ω := hstd.2.1
  rcases eq_or_lt_of_le hω.2 with heq | hlt
  · refine ⟨((0 : ℝ) : Real.Angle), ?_⟩
    have hrot0 : ∀ p : Point, rotationMap ((0 : ℝ) : Real.Angle) p = p := by
      intro p
      rw [rotationMap, Real.Angle.coe_zero, Orientation.rotation_zero]
      rfl
    rw [show rotationMap ((0 : ℝ) : Real.Angle) = id from funext hrot0, Set.image_id]
    exact heq ▸ hrot
  -- the consumed corner triangle of the balanced maximum cap
  have hcos : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo ⟨by linarith, hlt⟩
  have hstrip : s ⊆ (stripParallelogram ω).1 := by
    rw [hsdef]
    exact Set.inter_subset_left
  have hareaK : (11 : ℝ) / 5 ≤ capAreaFunctional K := by
    rw [capAreaFunctional_eq_sofaArea s ω ⟨s₀, hs₀, hsdef⟩ K hKcap]
    exact hArea
  have hsK : s = (K.val : Set Point) \ capNiche K :=
    monotoneSofa_structure s ω ⟨s₀, hs₀, hsdef⟩ K hKcap
  obtain ⟨t₀, ht₀, hsub3⟩ := balancedMaximumCap_consumed K hω.1 hlt hKbal hareaK
  rw [rotatingHallwayParts_innerQuadrant] at hsub3
  have hgap := parallelogram_gap ω ⟨hω0.le, hlt⟩
  have hccos : Real.tan ((Real.pi / 2 - ω) / 2) * Real.cos ω = 1 - Real.sin ω := by
    rw [hgap.2.2.2.2, Real.tan_eq_sin_div_cos]
    field_simp
  have hsinlt : Real.sin ω < 1 := by nlinarith [Real.sin_sq_add_cos_sq ω]
  have hcpos : 0 < Real.tan ((Real.pi / 2 - ω) / 2) := by nlinarith
  have hmem_capFan : ∀ z : Point, 0 ≤ inner ℝ z (normalVector (ω : Real.Angle)) →
      0 ≤ inner ℝ z (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) → z ∈ capFan ω :=
    fun _ h1 h2 ↦ ⟨h1, h2⟩
  have hfan0 : (0 : Point) ∈ capFan ω := hmem_capFan 0 (by simp) (by simp)
  have hfana : (stripParallelogram ω).2.2 - tangentVector 0 ∈ capFan ω := by
    rw [hgap.1]
    refine hmem_capFan _ ?_ ?_
    · rw [real_inner_smul_left, ← Real.Angle.coe_zero, inner_normalVector_normalVector,
        zero_sub, Real.cos_neg]
      exact mul_nonneg hcpos.le hcos.le
    · rw [real_inner_smul_left, ← Real.Angle.coe_zero, inner_normalVector_normalVector,
        zero_sub, Real.cos_neg, Real.cos_pi_div_two, mul_zero]
  have hfanb : (stripParallelogram ω).2.2 - normalVector (ω : Real.Angle) ∈ capFan ω := by
    rw [hgap.2.1]
    refine hmem_capFan _ ?_ ?_
    · rw [real_inner_smul_left, inner_tangentVector_normalVector_real, sub_self,
        Real.sin_zero, mul_zero]
    · rw [real_inner_smul_left, inner_tangentVector_normalVector_real,
        Real.sin_pi_div_two_sub]
      exact mul_nonneg hcpos.le hcos.le
  have hUconv : Convex ℝ (capFan ω ∩ innerQuadrant (K.val : Set Point) t₀) :=
    (convex_capFan ω).inter (convex_innerQuadrant _ _)
  have hUniche : capFan ω ∩ innerQuadrant (K.val : Set Point) t₀ ⊆ capNiche K :=
    fun z hz ↦ ⟨hz.1, Set.mem_iUnion₂.mpr ⟨t₀, ht₀, hz.2⟩⟩
  have h0U : (0 : Point) ∈ capFan ω ∩ innerQuadrant (K.val : Set Point) t₀ :=
    ⟨hfan0, hsub3 (by simp)⟩
  have haU : (stripParallelogram ω).2.2 - tangentVector 0 ∈
      capFan ω ∩ innerQuadrant (K.val : Set Point) t₀ := ⟨hfana, hsub3 (by simp)⟩
  have hbU : (stripParallelogram ω).2.2 - normalVector (ω : Real.Angle) ∈
      capFan ω ∩ innerQuadrant (K.val : Set Point) t₀ := ⟨hfanb, hsub3 (by simp)⟩
  have hlowbd : ∀ p ∈ s, 1 - Real.sin ω ≤ inner ℝ p (normalVector (ω : Real.Angle)) + p 1 := by
    intro p hp
    by_contra hcon
    push Not at hcon
    obtain ⟨hy, hx⟩ := (mem_stripParallelogram_iff ω p).1 (hstrip hp)
    have hmem := hUniche (mem_of_inner_add_le_one_sub_sin hω0 hlt hUconv h0U haU hbU
      hy.1 hx.1 hcon.le)
    rw [hsK] at hp
    exact hp.2 hmem
  have hwidth : ∀ t : ℝ, ω ≤ t → t ≤ Real.pi / 2 → ∀ p ∈ s, ∀ q ∈ s,
      inner ℝ p (normalVector (t : Real.Angle)) -
        inner ℝ q (normalVector (t : Real.Angle)) ≤ 1 := by
    intro t ht ht' p hp q hq
    obtain ⟨hp1, hp2⟩ := (mem_stripParallelogram_iff ω p).1 (hstrip hp)
    obtain ⟨hq1, hq2⟩ := (mem_stripParallelogram_iff ω q).1 (hstrip hq)
    exact inner_sub_inner_le_one_of_clipped hω0.le hcos hp2.2 hp1.2 hq2.1 hq1.1
      (hlowbd q hq) ht ht'
  obtain ⟨low, M, hlowcont, hhoriz, hloleq, hupleq⟩ :=
    exists_normalization_of_width hcpt hconn.nonempty hwidth
  exact ⟨((Real.pi / 2 - ω : ℝ) : Real.Angle),
    hasRotationAngle_rotationMap_of_normalization hlt hconn hcpt hrot low M hlowcont
      hhoriz hloleq hupleq⟩

private theorem hasRotationAngle_right_of_reaches_right (S : Set Point)
    (m : unitInterval → Point ≃ᵃⁱ[ℝ] Point) (hm : IsMovingSofa S m)
    (α : unitInterval → ℝ) (e : unitInterval → Point)
    (hαc : Continuous α) (hα0 : α 0 = 0)
    (hlift : ∀ t p, m t p = rotationMap (α t : Real.Angle) p + e t)
    (ts : unitInterval) (hts : α ts = -(Real.pi / 2)) :
    HasRotationAngle S (Real.pi / 2) := by
  have hcoord : ∀ (u v : Point) (i : Fin 2), (u + v) i = u i + v i := fun _ _ _ ↦ rfl
  have hH : ∀ p ∈ S, 0 ≤ p 1 ∧ p 1 ≤ 1 := by
    intro p hp
    obtain ⟨-, h1, h2⟩ := mem_horizontalHallway_coordinates (hm.initial hp)
    exact ⟨h1, h2⟩
  have hLt : ∀ (t : unitInterval) (p : Point), p ∈ S →
      (m t p) 0 ≤ 1 ∧ (m t p) 1 ≤ 1 ∧ (0 ≤ (m t p) 0 ∨ 0 ≤ (m t p) 1) := by
    intro t p hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := (mem_hallway_iff _).mp (hm.subset_hallway t ⟨p, hp, rfl⟩)
    exact ⟨h1, h2, h3⟩
  have hcs : ((α ts : ℝ) : Real.Angle).cos = 0 := by
    rw [Real.Angle.cos_coe, hts]
    simp
  have hsns : ((α ts : ℝ) : Real.Angle).sin = -1 := by
    rw [Real.Angle.sin_coe, hts]
    simp
  have hmts0 : ∀ p : Point, (m ts p) 0 = p 1 + (e ts) 0 := by
    intro p
    rw [hlift ts p, hcoord, rotationMap_apply_zero, hcs, hsns]
    ring
  have hmts1 : ∀ p : Point, (m ts p) 1 = -p 0 + (e ts) 1 := by
    intro p
    rw [hlift ts p, hcoord, rotationMap_apply_one, hcs, hsns]
    ring
  -- the supremum of the vertical coordinates of the initial placement
  obtain ⟨p₀, hp₀⟩ := hm.isConnected.nonempty
  have hTne : ((fun p : Point ↦ p 1) '' S).Nonempty := ⟨p₀ 1, p₀, hp₀, rfl⟩
  have hTbdd : BddAbove ((fun p : Point ↦ p 1) '' S) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    exact (hH p hp).2
  set N : ℝ := sSup ((fun p : Point ↦ p 1) '' S) with hNdef
  have hNub : ∀ p ∈ S, p 1 ≤ N := fun p hp ↦ le_csSup hTbdd ⟨p, hp, rfl⟩
  have hNle : N ≤ 1 := by
    refine csSup_le hTne ?_
    rintro _ ⟨p, hp, rfl⟩
    exact (hH p hp).2
  have hNd : N + (e ts) 0 ≤ 1 := by
    have hle : N ≤ 1 - (e ts) 0 := by
      refine csSup_le hTne ?_
      rintro _ ⟨p, hp, rfl⟩
      have hx := (hLt ts p hp).1
      rw [hmts0 p] at hx
      linarith
    linarith
  set δ : ℝ := 1 - N - (e ts) 0 with hδdef
  have hδ : 0 ≤ δ := by
    rw [hδdef]
    linarith
  -- the reparametrized motion, followed by the horizontal translation
  have hφmem : ∀ r : unitInterval, min (2 * (r : ℝ)) 1 * (ts : ℝ) ∈ unitInterval := by
    intro r
    constructor
    · exact mul_nonneg (le_min (by linarith [r.2.1]) (by norm_num)) ts.2.1
    · calc min (2 * (r : ℝ)) 1 * (ts : ℝ) ≤ 1 * 1 :=
            mul_le_mul (min_le_right _ _) ts.2.2 ts.2.1 (by norm_num)
      _ = 1 := one_mul 1
  set φ : unitInterval → unitInterval :=
    fun r ↦ ⟨min (2 * (r : ℝ)) 1 * (ts : ℝ), hφmem r⟩ with hφdef
  set ψ : unitInterval → ℝ := fun r ↦ max (2 * (r : ℝ) - 1) 0 with hψdef
  set w : Point := !₂[δ, 0] with hwdef
  have hw0 : w 0 = δ := rfl
  have hw1 : w 1 = 0 := rfl
  set n : unitInterval → Point ≃ᵃⁱ[ℝ] Point :=
    fun r ↦ (m (φ r)).trans (AffineIsometryEquiv.vaddConst ℝ (ψ r • w)) with hndef
  have hnapp : ∀ (r : unitInterval) (p : Point), n r p = m (φ r) p + ψ r • w := fun _ _ ↦ rfl
  have hφcont : Continuous φ := by
    rw [hφdef]
    exact Continuous.subtype_mk (by fun_prop) _
  have hψcont : Continuous ψ := by
    rw [hψdef]
    fun_prop
  have hφ0 : φ 0 = 0 := by
    apply Subtype.ext
    show min (2 * ((0 : unitInterval) : ℝ)) 1 * (ts : ℝ) = 0
    norm_num
  have hφ1 : φ 1 = ts := by
    apply Subtype.ext
    show min (2 * ((1 : unitInterval) : ℝ)) 1 * (ts : ℝ) = (ts : ℝ)
    norm_num
  have hψ0 : ψ 0 = 0 := by
    show max (2 * ((0 : unitInterval) : ℝ) - 1) 0 = 0
    norm_num
  have hψ1 : ψ 1 = 1 := by
    show max (2 * ((1 : unitInterval) : ℝ) - 1) 0 = 1
    norm_num
  have hψnn : ∀ r : unitInterval, 0 ≤ ψ r := fun r ↦ le_max_right _ _
  have hψle : ∀ r : unitInterval, ψ r ≤ 1 := by
    intro r
    exact max_le (by linarith [r.2.2]) (by norm_num)
  have hψpos : ∀ r : unitInterval, ψ r ≠ 0 → φ r = ts := by
    intro r hr
    have hlt : 1 < 2 * (r : ℝ) := by
      by_contra hcon
      push Not at hcon
      apply hr
      show max (2 * (r : ℝ) - 1) 0 = 0
      exact max_eq_right (by linarith)
    apply Subtype.ext
    show min (2 * (r : ℝ)) 1 * (ts : ℝ) = (ts : ℝ)
    rw [min_eq_right hlt.le, one_mul]
  -- the hallway containment of the new motion
  have hnhall : ∀ (r : unitInterval), n r '' S ⊆ hallway := by
    rintro r _ ⟨p, hp, rfl⟩
    obtain ⟨hy0, hy1⟩ := hH p hp
    obtain ⟨hx1, hx2, hx3⟩ := hLt (φ r) p hp
    by_cases hr : ψ r = 0
    · have heq : n r p = m (φ r) p := by
        rw [hnapp, hr, zero_smul, add_zero]
      rw [heq]
      exact (mem_hallway_iff _).mpr ⟨⟨hx1, hx2⟩, hx3⟩
    · have hφr := hψpos r hr
      obtain ⟨hz1, hz2, hz3⟩ := hLt ts p hp
      have hc0 : (n r p) 0 = p 1 + (e ts) 0 + ψ r * δ := by
        rw [hnapp, hcoord, hφr, hmts0 p]
        show p 1 + (e ts) 0 + ψ r * w 0 = _
        rw [hw0]
      have hc1 : (n r p) 1 = -p 0 + (e ts) 1 := by
        rw [hnapp, hcoord, hφr, hmts1 p]
        show -p 0 + (e ts) 1 + ψ r * w 1 = _
        rw [hw1]
        ring
      rw [hmts0 p] at hz1 hz3
      rw [hmts1 p] at hz2 hz3
      refine (mem_hallway_iff _).mpr ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hc0]
        have hmul : ψ r * δ ≤ 1 * δ := mul_le_mul_of_nonneg_right (hψle r) hδ
        have := hNub p hp
        rw [hδdef] at hmul
        linarith
      · rw [hc1]
        linarith
      · rcases hz3 with h | h
        · left
          rw [hc0]
          have : 0 ≤ ψ r * δ := mul_nonneg (hψnn r) hδ
          linarith
        · right
          rw [hc1]
          linarith
  have hnfinal : n 1 '' S ⊆ verticalHallway := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨hy0, hy1⟩ := hH p hp
    obtain ⟨hz1, hz2, hz3⟩ := hLt ts p hp
    rw [hmts1 p] at hz2
    have hc0 : (n 1 p) 0 = p 1 + (e ts) 0 + δ := by
      rw [hnapp, hcoord, hφ1, hmts0 p, hψ1]
      show p 1 + (e ts) 0 + 1 * w 0 = _
      rw [hw0]
      ring
    have hc1 : (n 1 p) 1 = -p 0 + (e ts) 1 := by
      rw [hnapp, hcoord, hφ1, hmts1 p, hψ1]
      show -p 0 + (e ts) 1 + 1 * w 1 = _
      rw [hw1]
      ring
    refine mem_verticalHallway_of_coordinates _ ⟨?_, ?_⟩ ?_
    · rw [hc0, hδdef]
      linarith
    · rw [hc0, hδdef]
      have := hNub p hp
      linarith
    · rw [hc1]
      linarith
  have hmcam : Continuous (fun t : unitInterval ↦ (m t).toAffineIsometry.toContinuousAffineMap) :=
    continuous_induced_dom.comp hm.continuous
  have hncont : Continuous n := by
    rw [continuous_induced_rng]
    refine ContinuousAffineMap.continuous_rng (fun p ↦ ?_) ?_
    · show Continuous fun r : unitInterval ↦ m (φ r) p + ψ r • w
      exact ((hmcam.comp hφcont).eval_const p).add (hψcont.smul continuous_const)
    · show Continuous fun r : unitInterval ↦
        ((m (φ r)).toAffineIsometry.toContinuousAffineMap).contLinear
      exact ContinuousAffineMap.continuous_contLinear.comp (hmcam.comp hφcont)
  refine ⟨n, ⟨hm.isConnected, hm.isClosed, hncont, ⟨0, ?_⟩, ?_, ?_, hnhall, hnfinal⟩,
    fun r ↦ α (φ r), hαc.comp hφcont, ?_, ?_, ?_⟩
  · intro p
    rw [hnapp, hφ0, hψ0, zero_smul, add_zero, hm.zero]
    simp
  · intro r
    exact ⟨((α (φ r) : ℝ) : Real.Angle), fun p ↦ by
      rw [hnapp, hnapp, hlift (φ r) p, hlift (φ r) 0]
      simp [rotationMap]
      abel⟩
  · rintro _ ⟨p, hp, rfl⟩
    have hid : n 0 p = p := by
      rw [hnapp, hφ0, hψ0, zero_smul, add_zero, hm.zero]
      rfl
    rw [hid]
    exact hm.initial hp
  · show α (φ 0) = 0
    rw [hφ0, hα0]
  · show α (φ 1) = -(Real.pi / 2)
    rw [hφ1, hts]
  · intro r p
    rw [hnapp, hnapp, hlift (φ r) p, hlift (φ r) 0]
    simp [rotationMap]
    abel

theorem movingSofa_rotationAngle_bound (s : Set Point)
    (hs : IsPaperMovingSofa s) (hArea : 11 / 5 ≤ ClassicalResults.area s) :
    ∃ ω ∈ Set.Icc (Real.arccos (5 / 11 : ℝ)) (Real.pi / 2),
      HasRotationAngle s ω := by
  obtain ⟨q, m, hm, hvol⟩ := canonical_paper_motion_bridge.1 s hs
  set S : Set Point := (fun p ↦ p + q) '' s with hSdef
  obtain ⟨α, e, hαc, hec, hα0, he0, hlift⟩ :=
    exists_continuous_motion_angle_lift m hm.continuous hm.zero
  have hcoord : ∀ (u v : Point) (i : Fin 2), (u + v) i = u i + v i := fun _ _ _ ↦ rfl
  have htransfer : ∀ ω : ℝ, HasRotationAngle S ω → HasRotationAngle s ω := by
    intro ω hω
    have h := hasRotationAngle_image_add S (-q) ω hω
    have himg : (fun p : Point ↦ p + -q) '' S = s := by
      rw [hSdef, Set.image_image]
      simp
    rwa [himg] at h
  have harea : (11 : ℝ) / 5 ≤ (MeasureTheory.volume S).toReal := by
    rw [hSdef, hvol]
    exact hArea
  have hH : ∀ p ∈ S, 0 ≤ p 1 ∧ p 1 ≤ 1 := by
    intro p hp
    obtain ⟨-, h1, h2⟩ := mem_horizontalHallway_coordinates (hm.initial hp)
    exact ⟨h1, h2⟩
  have hLt : ∀ (t : unitInterval) (p : Point), p ∈ S →
      (m t p) 0 ≤ 1 ∧ (m t p) 1 ≤ 1 ∧ (0 ≤ (m t p) 0 ∨ 0 ≤ (m t p) 1) := by
    intro t p hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := (mem_hallway_iff _).mp (hm.subset_hallway t ⟨p, hp, rfl⟩)
    exact ⟨h1, h2, h3⟩
  have hVf : ∀ p ∈ S, 0 ≤ (m 1 p) 0 ∧ (m 1 p) 0 ≤ 1 ∧ (m 1 p) 1 ≤ 1 :=
    fun p hp ↦ mem_verticalHallway_coordinates (hm.final ⟨p, hp, rfl⟩)
  -- the clockwise angle never reaches a counterclockwise quarter of a right angle
  have hquarter : ∀ t : unitInterval, α t ≠ Real.pi / 4 := by
    intro t ht
    set r := Real.sqrt 2 with hrdef
    have hrsq : r * r = 2 := Real.mul_self_sqrt (by norm_num)
    have hrpos : 0 < r := by rw [hrdef]; positivity
    have hc : ((α t : ℝ) : Real.Angle).cos = r / 2 := by
      rw [Real.Angle.cos_coe, ht, Real.cos_pi_div_four]
    have hsn : ((α t : ℝ) : Real.Angle).sin = r / 2 := by
      rw [Real.Angle.sin_coe, ht, Real.sin_pi_div_four]
    have hmul : ∀ x : ℝ, r * (r / 2 * x) = x := by
      intro x
      linear_combination x / 2 * hrsq
    have hbound : MeasureTheory.volume S ≤ ENNReal.ofReal r := by
      refine volume_le_of_subset_horizontalBand
        (f := fun y ↦ min (y + (r - r * (e t) 0)) (-y + (r - r * (e t) 1)) - r)
        (c := r) (by fun_prop) hrpos.le ?_
      intro p hp
      obtain ⟨hy0, hy1⟩ := hH p hp
      obtain ⟨hx1, hx2, hx3⟩ := hLt t p hp
      have hm0 : (m t p) 0 = r / 2 * p 0 - r / 2 * p 1 + (e t) 0 := by
        rw [hlift t p, hcoord, rotationMap_apply_zero, hc, hsn]
      have hm1 : (m t p) 1 = r / 2 * p 0 + r / 2 * p 1 + (e t) 1 := by
        rw [hlift t p, hcoord, rotationMap_apply_one, hc, hsn]
      rw [hm0] at hx1
      rw [hm1] at hx2
      rw [hm0, hm1] at hx3
      have g1 : p 0 - p 1 + r * (e t) 0 ≤ r := by
        have h := mul_le_mul_of_nonneg_left hx1 hrpos.le
        rwa [mul_add, mul_sub, hmul, hmul, mul_one] at h
      have g2 : p 0 + p 1 + r * (e t) 1 ≤ r := by
        have h := mul_le_mul_of_nonneg_left hx2 hrpos.le
        rwa [mul_add, mul_add, hmul, hmul, mul_one] at h
      have hmin := min_le_left (p 1 + (r - r * (e t) 0)) (-p 1 + (r - r * (e t) 1))
      have hmin' := min_le_right (p 1 + (r - r * (e t) 0)) (-p 1 + (r - r * (e t) 1))
      refine ⟨⟨hy0, hy1⟩, ?_, ?_⟩
      · simp only
        rcases hx3 with h | h
        · have h' := mul_le_mul_of_nonneg_left h hrpos.le
          rw [mul_zero, mul_add, mul_sub, hmul, hmul] at h'
          linarith
        · have h' := mul_le_mul_of_nonneg_left h hrpos.le
          rw [mul_zero, mul_add, mul_add, hmul, hmul] at h'
          linarith
      · simp only
        have hle' : p 0 ≤ min (p 1 + (r - r * (e t) 0)) (-p 1 + (r - r * (e t) 1)) :=
          le_min (by linarith) (by linarith)
        linarith
    have hle : (MeasureTheory.volume S).toReal ≤ r := ENNReal.toReal_le_of_le_ofReal hrpos.le hbound
    nlinarith [hrsq, hrpos, harea, hle, sq_nonneg (r - 11 / 5)]
  have hquarter' : ∀ t : unitInterval, α t < Real.pi / 4 := by
    intro t
    rcases lt_trichotomy (α t) (Real.pi / 4) with h | h | h
    · exact h
    · exact absurd h (hquarter t)
    · exfalso
      have hmem : Real.pi / 4 ∈ Set.range α := by
        refine intermediate_value_univ 0 t hαc ?_
        rw [hα0]
        exact ⟨by positivity, h.le⟩
      obtain ⟨u, hu⟩ := hmem
      exact hquarter u hu
  -- the final clockwise angle has small cosine
  have hcosbound : |Real.cos (α 1)| ≤ 5 / 11 := by
    by_contra hcon
    push Not at hcon
    have habs : (0 : ℝ) < |Real.cos (α 1)| := by linarith
    have hne : Real.cos (α 1) ≠ 0 := by
      intro h0
      rw [h0] at habs
      simp at habs
    have hbound : MeasureTheory.volume S ≤ ENNReal.ofReal (1 / |Real.cos (α 1)|) := by
      refine le_trans (MeasureTheory.measure_mono ?_)
        (volume_horizontalBand_inter_le (Real.cos (α 1)) (-Real.sin (α 1)) (-(e 1) 0) hne)
      intro p hp
      obtain ⟨hy0, hy1⟩ := hH p hp
      obtain ⟨hv0, hv1, -⟩ := hVf p hp
      have hm0 : (m 1 p) 0 = Real.cos (α 1) * p 0 - Real.sin (α 1) * p 1 + (e 1) 0 := by
        rw [hlift 1 p, hcoord, rotationMap_apply_zero, Real.Angle.cos_coe, Real.Angle.sin_coe]
      rw [hm0] at hv0 hv1
      exact ⟨⟨hy0, hy1⟩, by linarith, by linarith⟩
    have hle : (MeasureTheory.volume S).toReal ≤ 1 / |Real.cos (α 1)| :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hbound
    have hlt : 1 / |Real.cos (α 1)| < 11 / 5 := by
      rw [div_lt_iff₀ habs]
      linarith
    linarith
  -- the angle constants
  set A := Real.arccos (5 / 11 : ℝ) with hAdef
  have hcosA : Real.cos A = 5 / 11 := Real.cos_arccos (by norm_num) (by norm_num)
  have hApi2 : A ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.mpr (by norm_num)
  have hApi : A ≤ Real.pi := Real.arccos_le_pi _
  have hAquarter : Real.pi / 4 < A := by
    have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hs2pos : (0 : ℝ) < Real.sqrt 2 := by positivity
    have hlt : (5 : ℝ) / 11 < Real.sqrt 2 / 2 := by nlinarith
    have h4 : Real.arccos (Real.sqrt 2 / 2) = Real.pi / 4 := by
      rw [← Real.cos_pi_div_four, Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]
    rw [hAdef, ← h4]
    exact Real.arccos_lt_arccos (by norm_num) hlt (by nlinarith)
  have hfinal : α 1 ≤ -A := by
    by_contra hcon
    push Not at hcon
    have habs : |α 1| < A := by
      rw [abs_lt]
      exact ⟨by linarith, lt_trans (hquarter' 1) hAquarter⟩
    have hmono : Real.cos A < Real.cos |α 1| :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) hApi habs
    rw [Real.cos_abs] at hmono
    have := le_abs_self (Real.cos (α 1))
    linarith
  have hm0e : ∀ t : unitInterval, m t 0 = e t := by
    intro t
    rw [hlift t 0]
    simp [rotationMap]
  have hrot : HasRotationAngle S (-α 1) := by
    refine ⟨m, hm.isPaperMotion, α, hαc, hα0, by ring, fun t p ↦ ?_⟩
    rw [hlift t p, hm0e t]
  by_cases hbig : -α 1 ≤ Real.pi / 2
  · exact ⟨-α 1, ⟨by linarith, hbig⟩, htransfer _ hrot⟩
  · push Not at hbig
    refine ⟨Real.pi / 2, ⟨hApi2, le_refl _⟩, htransfer _ ?_⟩
    -- the intermediate right-angle time
    have hmemr : -(Real.pi / 2) ∈ Set.range α := by
      refine intermediate_value_univ 1 0 hαc ?_
      rw [hα0]
      exact ⟨by linarith, by linarith [Real.pi_pos]⟩
    obtain ⟨ts, hts⟩ := hmemr
    exact hasRotationAngle_right_of_reaches_right S m hm α e hαc hα0 hlift ts hts

end MovingSofa

end

end

end
