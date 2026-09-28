/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Bounds.Applications.Development001
public import LeanPool.MovingSofa.Cap.Applications.Development002
public import LeanPool.MovingSofa.Cap.Foundations.Development004
public import LeanPool.MovingSofa.Cap.Foundations.Development002
public import LeanPool.MovingSofa.Cap.Foundations.Development008
public import LeanPool.MovingSofa.Motion.Foundations.Development002
/-!
# Moving sofa: related mathematical developments

* `Sofa.Balanced`.
* `Sofa.BalancedConsumed`.
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
# Sofa / Balanced
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- A monotonized standard-position sofa whose associated cap is a balanced maximum cap. -/
def IsBalancedMaximumSofa (s : Set Point) (ω : ℝ) : Prop :=
  (∃ s₀ : Set Point, IsStandardPosition s₀ ω ∧ s = monotonization s₀ ω) ∧
    ∃ K : CapSpace ω, (K.val : Set Point) = capOfSofa s ω ∧ IsBalancedMaximumCap K

theorem exists_balancedMaximumSofa (ω : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) :
    ∃ K : CapSpace ω, IsBalancedMaximumCap K ∧
      IsBalancedMaximumSofa ((K.val : Set Point) \ capNiche K) ω ∧
      ∀ s : Set Point, HasRotationAngle s ω →
        ClassicalResults.area s ≤ ClassicalResults.area ((K.val : Set Point) \ capNiche K) := by
  obtain ⟨K, hK⟩ := exists_balancedMaximumCap ω hω hω'
  obtain ⟨s₀, hs₀, hcap⟩ := (cap_isMonotoneCap_iff_niche_subset K).mpr
    (balancedMaximumCap_niche_subset K hK)
  have hshape := monotoneSofa_structure (monotonization s₀ ω) ω ⟨s₀, hs₀, rfl⟩ K hcap
  have hmonoS : ∃ s₀ : Set Point, IsStandardPosition s₀ ω ∧
      (K.val : Set Point) \ capNiche K = monotonization s₀ ω := ⟨s₀, hs₀, hshape.symm⟩
  have hcapS : (K.val : Set Point) = capOfSofa ((K.val : Set Point) \ capNiche K) ω := by
    rwa [← hshape]
  have hareaK := capAreaFunctional_eq_sofaArea _ ω hmonoS K hcapS
  refine ⟨K, hK, ⟨hmonoS, K, hcapS, hK⟩, ?_⟩
  intro s hs
  obtain ⟨v, hv⟩ := (exists_standardPosition_translation s ω hs ⟨hω, hω'⟩).1
  let s₁ := (fun p ↦ p + v) '' s
  have hstd := standardPosition_monotonization_standard s₁ ω hv
  obtain ⟨L, hL⟩ := standardPosition_cap (monotonization s₁ ω) ω hstd.1
  calc
    ClassicalResults.area s = ClassicalResults.area s₁ :=
      (ClassicalResults.area_image_add s v).symm
    _ ≤ ClassicalResults.area (monotonization s₁ ω) :=
      MeasureTheory.measureReal_mono hstd.2 hstd.1.1.measure_lt_top.ne
    _ = capAreaFunctional L :=
      (capAreaFunctional_eq_sofaArea _ ω ⟨s₁, hv, rfl⟩ L hL).symm
    _ ≤ capAreaFunctional K := balancedMaximumCap_maximizes_area K hK L
    _ = _ := hareaK

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Sofa / Balanced Consumed
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The right wedge gap is bounded below by the calculation variable `g`. -/
private theorem le_wedgeGaps_fst_of_calculationVariables {ω : ℝ} (K : CapSpace ω)
    (hω' : ω < Real.pi / 2) {c d r g : ℝ}
    (hccos : c * Real.cos ω = 1 - Real.sin ω)
    (hsupp : supportValue K.val (0 : Real.Angle) = c + d)
    (hrsin : r * Real.sin ω = Real.sin ω - d * Real.cos ω)
    (hgsq : g ^ 2 = 1 - r ^ 2)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 ω) :
    g ≤ (wedgeGaps K t).1 := by
  have hpi := Real.pi_pos
  have hω0 : 0 < ω := K.property.1
  have hcos : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo ⟨by linarith, hω'⟩
  have hsin : 0 < Real.sin ω := Real.sin_pos_of_pos_of_lt_pi hω0 (by linarith)
  have hcost : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hsint : 0 ≤ Real.sin t := (Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2])).le
  have hsinδ : 0 ≤ Real.sin ω * Real.cos t - Real.cos ω * Real.sin t := by
    rw [← Real.sin_sub]
    exact (Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.2]) (by linarith [ht.1])).le
  have hcs : r * Real.sin t + g * Real.cos t ≤ 1 := by
    nlinarith [sq_nonneg (r - Real.sin t), sq_nonneg (g - Real.cos t),
      Real.sin_sq_add_cos_sq t]
  -- the support value at `t` is bounded by the value at the intersection point `R`
  have hbound : Real.sin ω * supportValue K.val (t : Real.Angle) ≤
      Real.sin (ω - t) * (c + d) + Real.sin t := by
    rw [mul_comm, ← le_div_iff₀ hsin]
    apply csSup_le (K.val.nonempty.image _)
    rintro _ ⟨p, hp, rfl⟩
    have hx : p 0 ≤ c + d := by
      rw [← hsupp]
      simpa [normalVector, frame, PiLp.inner_apply] using
        inner_le_supportValue K.val hp (0 : Real.Angle)
    have hu : Real.cos ω * p 0 + Real.sin ω * p 1 ≤ 1 := by
      have hle := inner_le_supportValue K.val hp (ω : Real.Angle)
      rw [K.property.2.2.1] at hle
      simpa [normalVector, frame, PiLp.inner_apply] using hle
    have hval : inner ℝ p (normalVector (t : Real.Angle)) =
        Real.cos t * p 0 + Real.sin t * p 1 := by
      simp [normalVector, frame, PiLp.inner_apply]
    simp only [le_div_iff₀ hsin, hval, Real.sin_sub]
    nlinarith [mul_nonneg hsinδ (sub_nonneg.2 hx), mul_nonneg hsint (sub_nonneg.2 hu)]
  have hRu : Real.sin ω * ((c + d) * Real.cos t + r * Real.sin t) =
      Real.sin (ω - t) * (c + d) + Real.sin t := by
    rw [Real.sin_sub]
    linear_combination Real.sin t * hrsin + Real.sin t * hccos
  have hSle : supportValue K.val (t : Real.Angle) ≤ (c + d) * Real.cos t + r * Real.sin t := by
    rw [← hRu] at hbound
    exact le_of_mul_le_mul_left hbound hsin
  have hkey : supportValue K.val (t : Real.Angle) - 1 ≤ (c + d - g) * Real.cos t := by
    nlinarith
  rw [wedgeGaps_fst_eq_supportValue, hsupp, ← sub_nonneg]
  have := (div_le_iff₀ hcost).2 hkey
  linarith

/-- The exposed top face of a cap contains the horizontal segment of its own atomic
surface mass, measured leftwards from the upper distinguished point. -/
private theorem topFace_sub_smul_normalVector_mem {ω : ℝ} (K : CapSpace ω)
    (ho : (stripParallelogram ω).2.2 ∈ (K.val : Set Point)) {c g : ℝ}
    (hccos : c * Real.cos ω = 1 - Real.sin ω)
    (hcoord : (stripParallelogram ω).2.2 = !₂[c, 1]) (hcos : 0 < Real.cos ω)
    (hgnn : 0 ≤ g)
    (hg : g ≤ (surfaceAreaMeasure K.val {((Real.pi / 2 : ℝ) : Real.Angle)}).toReal) :
    (stripParallelogram ω).2.2 - g • normalVector (0 : Real.Angle) ∈ (K.val : Set Point) := by
  have hT1 : supportValue K.val ((Real.pi / 2 : ℝ) : Real.Angle) = 1 := K.property.2.2.2.1
  have htan : tangentVector ((Real.pi / 2 : ℝ) : Real.Angle) = -normalVector (0 : Real.Angle) := by
    ext i
    fin_cases i <;> simp [tangentVector, normalVector, frame]
  have hface : ∀ p ∈ exposedEdge K.val ((Real.pi / 2 : ℝ) : Real.Angle), p 1 = 1 ∧ p 0 ≤ c := by
    intro p hp
    have hpe : inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) =
        supportValue K.val ((Real.pi / 2 : ℝ) : Real.Angle) := hp.2
    rw [hT1] at hpe
    have h1 : p 1 = 1 := by simpa [normalVector, frame, PiLp.inner_apply] using hpe
    refine ⟨h1, ?_⟩
    have hle := inner_le_supportValue K.val hp.1 (ω : Real.Angle)
    rw [K.property.2.2.1] at hle
    simp [normalVector, frame, PiLp.inner_apply, h1] at hle
    nlinarith
  have hoedge : (stripParallelogram ω).2.2 ∈
      exposedEdge K.val ((Real.pi / 2 : ℝ) : Real.Angle) := by
    refine ⟨ho, ?_⟩
    show inner ℝ (stripParallelogram ω).2.2 (normalVector _) = _
    rw [hT1, hcoord]
    simp [normalVector, frame, PiLp.inner_apply]
  have hsnd := edgeVertices_snd_mem K.val ((Real.pi / 2 : ℝ) : Real.Angle)
  have hsndle : inner ℝ (edgeVertices K.val ((Real.pi / 2 : ℝ) : Real.Angle)).2
      (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) ≤
      inner ℝ (stripParallelogram ω).2.2 (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) := by
    rw [inner_edgeVertices_snd_tangent]
    refine csInf_le ?_ ⟨_, hoedge, rfl⟩
    exact ((isCompact_exposedEdge K.val _).image (continuous_id.inner continuous_const)).bddBelow
  have hsndeq : (edgeVertices K.val ((Real.pi / 2 : ℝ) : Real.Angle)).2 =
      (stripParallelogram ω).2.2 := by
    obtain ⟨hy, hx⟩ := hface _ hsnd
    have hocx : inner ℝ (stripParallelogram ω).2.2
        (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) = -c := by
      rw [htan, inner_neg_right, hcoord]
      simp [normalVector, frame, PiLp.inner_apply]
    have hvx : inner ℝ (edgeVertices K.val ((Real.pi / 2 : ℝ) : Real.Angle)).2
        (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) =
        -(edgeVertices K.val ((Real.pi / 2 : ℝ) : Real.Angle)).2 0 := by
      rw [htan, inner_neg_right]
      simp [normalVector, frame, PiLp.inner_apply]
    rw [hocx, hvx] at hsndle
    have hx0 : (edgeVertices K.val ((Real.pi / 2 : ℝ) : Real.Angle)).2 0 = c := by linarith
    rw [hcoord]
    ext i
    fin_cases i
    · simpa using hx0
    · simpa using hy
  obtain ⟨L, hL⟩ : ∃ L, (surfaceAreaMeasure K.val {((Real.pi / 2 : ℝ) : Real.Angle)}).toReal = L :=
    ⟨_, rfl⟩
  rw [hL] at hg
  have hatom := surfaceAreaMeasure_atom_length K.val ((Real.pi / 2 : ℝ) : Real.Angle)
  rw [hL] at hatom
  have hfstK : (stripParallelogram ω).2.2 - L • normalVector (0 : Real.Angle) ∈
      (K.val : Set Point) := by
    rw [show (stripParallelogram ω).2.2 - L • normalVector (0 : Real.Angle) =
        (edgeVertices K.val ((Real.pi / 2 : ℝ) : Real.Angle)).1 from by
      rw [hatom.2.2, hsndeq, htan, smul_neg, ← sub_eq_add_neg]]
    exact (edgeVertices_fst_mem K.val _).1
  rcases eq_or_lt_of_le (hgnn.trans hg) with hL0 | hLpos
  · have hg0 : g = 0 := le_antisymm (hg.trans hL0.symm.le) hgnn
    simpa [hg0] using ho
  · have hkey := K.val.convex ho hfstK (a := 1 - g / L) (b := g / L)
      (by
        have : g / L ≤ 1 := (div_le_one hLpos).2 hg
        linarith)
      (div_nonneg hgnn hLpos.le) (by ring)
    have hsmul : (1 - g / L) • (stripParallelogram ω).2.2 +
        (g / L) • ((stripParallelogram ω).2.2 - L • normalVector (0 : Real.Angle)) =
        (stripParallelogram ω).2.2 - g • normalVector (0 : Real.Angle) := by
      rw [smul_sub, smul_smul, div_mul_cancel₀ _ hLpos.ne']
      module
    rwa [hsmul] at hkey

/-- The three distinguished points lie in the inward quadrant at the angle `π / 2 - ω`
once the two contact points realize the strict calculation inequalities. -/
private theorem consumed_points_subset_innerQuadrant {ω : ℝ} (K : CapSpace ω)
    (hω4 : Real.pi / 4 < ω) (hω' : ω < Real.pi / 2) {c : ℝ} (hcpos : 0 < c)
    (hc0 : (stripParallelogram ω).2.2 - tangentVector 0 = c • normalVector (0 : Real.Angle))
    (hcω : (stripParallelogram ω).2.2 - normalVector (ω : Real.Angle) =
      c • tangentVector (ω : Real.Angle))
    {p q : Point} (hp : p ∈ (K.val : Set Point)) (hq : q ∈ (K.val : Set Point))
    (h1 : 1 < inner ℝ (p - ((stripParallelogram ω).2.2 - tangentVector 0))
      (normalVector ((Real.pi / 2 - ω : ℝ) : Real.Angle)))
    (h2 : 1 < inner ℝ (q - ((stripParallelogram ω).2.2 - normalVector (ω : Real.Angle)))
      (tangentVector ((Real.pi / 2 - ω : ℝ) : Real.Angle))) :
    ({0, (stripParallelogram ω).2.2 - tangentVector 0,
      (stripParallelogram ω).2.2 - normalVector (ω : Real.Angle)} : Set Point) ⊆
      innerQuadrant (K.val : Set Point) (Real.pi / 2 - ω) := by
  have hpi := Real.pi_pos
  have hcos : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo ⟨by linarith, hω'⟩
  have hsin : 0 < Real.sin ω := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hcslt : Real.cos ω < Real.sin ω := by
    rw [← Real.sin_pi_div_two_sub]
    exact Real.strictMonoOn_sin ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
  have hnt : normalVector ((Real.pi / 2 - ω + Real.pi / 2 : ℝ) : Real.Angle) =
      tangentVector ((Real.pi / 2 - ω : ℝ) : Real.Angle) := by
    ext i
    fin_cases i <;>
      simp [normalVector, tangentVector, frame, Real.cos_add, Real.sin_add,
        -Real.Angle.coe_sub, -Real.Angle.coe_add]
  have hnn : inner ℝ (normalVector (0 : Real.Angle))
      (normalVector ((Real.pi / 2 - ω : ℝ) : Real.Angle)) = Real.sin ω := by
    simp [normalVector, frame, PiLp.inner_apply, Real.cos_pi_div_two_sub, -Real.Angle.coe_sub]
  have hnt' : inner ℝ (normalVector (0 : Real.Angle))
      (tangentVector ((Real.pi / 2 - ω : ℝ) : Real.Angle)) = -Real.cos ω := by
    simp [normalVector, tangentVector, frame, PiLp.inner_apply, Real.sin_pi_div_two_sub,
      -Real.Angle.coe_sub]
  have htn : inner ℝ (tangentVector (ω : Real.Angle))
      (normalVector ((Real.pi / 2 - ω : ℝ) : Real.Angle)) =
      Real.cos ω ^ 2 - Real.sin ω ^ 2 := by
    simp [tangentVector, normalVector, frame, PiLp.inner_apply, Real.cos_pi_div_two_sub,
      Real.sin_pi_div_two_sub, -Real.Angle.coe_sub]
    ring
  have htt : inner ℝ (tangentVector (ω : Real.Angle))
      (tangentVector ((Real.pi / 2 - ω : ℝ) : Real.Angle)) =
      2 * (Real.sin ω * Real.cos ω) := by
    simp [tangentVector, frame, PiLp.inner_apply, Real.cos_pi_div_two_sub,
      Real.sin_pi_div_two_sub, -Real.Angle.coe_sub]
    ring
  have hA := inner_le_supportValue K.val hp ((Real.pi / 2 - ω : ℝ) : Real.Angle)
  have hB := inner_le_supportValue K.val hq ((Real.pi / 2 - ω + Real.pi / 2 : ℝ) : Real.Angle)
  rw [hnt] at hB
  have hstrict1 : c * Real.sin ω <
      supportValue K.val ((Real.pi / 2 - ω : ℝ) : Real.Angle) - 1 := by
    rw [inner_sub_left, hc0, real_inner_smul_left, hnn] at h1
    linarith
  have hstrict2 : c * (2 * (Real.sin ω * Real.cos ω)) <
      supportValue K.val ((Real.pi / 2 - ω + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
    rw [inner_sub_left, hcω, real_inner_smul_left, htt] at h2
    linarith
  have hmem : ∀ x : Point,
      inner ℝ x (normalVector ((Real.pi / 2 - ω : ℝ) : Real.Angle)) <
        supportValue K.val ((Real.pi / 2 - ω : ℝ) : Real.Angle) - 1 →
      inner ℝ x (tangentVector ((Real.pi / 2 - ω : ℝ) : Real.Angle)) <
        supportValue K.val ((Real.pi / 2 - ω + Real.pi / 2 : ℝ) : Real.Angle) - 1 →
      x ∈ innerQuadrant (K.val : Set Point) (Real.pi / 2 - ω) := by
    intro x hx1 hx2
    refine ⟨hx1, ?_⟩
    show inner ℝ x (normalVector ((Real.pi / 2 - ω + Real.pi / 2 : ℝ) : Real.Angle)) < _
    rwa [hnt]
  have hpos1 : 0 < c * Real.sin ω := mul_pos hcpos hsin
  have hpos2 : 0 < c * (2 * (Real.sin ω * Real.cos ω)) := by
    have := mul_pos hsin hcos
    nlinarith
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact hmem _ (by rw [inner_zero_left]; linarith) (by rw [inner_zero_left]; linarith)
  · refine hmem _ ?_ ?_
    · rw [hc0, real_inner_smul_left, hnn]
      exact hstrict1
    · rw [hc0, real_inner_smul_left, hnt']
      nlinarith
  · refine hmem _ ?_ ?_
    · rw [hcω, real_inner_smul_left, htn]
      have hneg : c * (Real.cos ω ^ 2 - Real.sin ω ^ 2) < 0 :=
        mul_neg_of_pos_of_neg hcpos (by nlinarith)
      linarith
    · rw [hcω, real_inner_smul_left, htt]
      exact hstrict2

/-- Auxiliary form of the consumption theorem under the right-hand support bound. -/
private theorem consumed_of_le_supportValue_zero {ω : ℝ}
    (hω : Real.arccos (5 / 11 : ℝ) ≤ ω) (hω' : ω < Real.pi / 2)
    (K : CapSpace ω) (hBalanced : IsBalancedMaximumCap K)
    (ho : (stripParallelogram ω).2.2 ∈ (K.val : Set Point))
    (hd : rotationCalculationMinimum ⟨ω, hω, hω'⟩ + Real.tan ((Real.pi / 2 - ω) / 2) ≤
      supportValue K.val (0 : Real.Angle)) :
    ({0, (stripParallelogram ω).2.2 - tangentVector 0,
      (stripParallelogram ω).2.2 - normalVector (ω : Real.Angle)} : Set Point) ⊆
      innerQuadrant (K.val : Set Point) (Real.pi / 2 - ω) := by
  have hpi := Real.pi_pos
  have hω4 : Real.pi / 4 < ω := rotationCalculation_angle_bounds.1.trans_le hω
  have hω0 : 0 < ω := by linarith
  have hcos : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo ⟨by linarith, hω'⟩
  have hsin : 0 < Real.sin ω := Real.sin_pos_of_pos_of_lt_pi hω0 (by linarith)
  have hgap := parallelogram_gap ω ⟨hω0.le, hω'⟩
  have hcpos : 0 < Real.tan ((Real.pi / 2 - ω) / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)
  have hccos : Real.tan ((Real.pi / 2 - ω) / 2) * Real.cos ω = 1 - Real.sin ω := by
    rw [hgap.2.2.2.2, Real.tan_eq_sin_div_cos]
    field_simp
  obtain ⟨d, hsupp⟩ : ∃ d, supportValue K.val (0 : Real.Angle) =
      Real.tan ((Real.pi / 2 - ω) / 2) + d :=
    ⟨supportValue K.val (0 : Real.Angle) - Real.tan ((Real.pi / 2 - ω) / 2), by ring⟩
  have hdmin : rotationCalculationMinimum ⟨ω, hω, hω'⟩ ≤ d := by
    rw [hsupp] at hd; linarith
  have hdpos : 0 < d := (rotationCalculationMinimum_pos _).trans_le hdmin
  have hq0K : supportValue K.val (0 : Real.Angle) • normalVector (0 : Real.Angle) ∈
      (K.val : Set Point) := supportValue_zero_smul_normalVector_mem K
  have hdtan : d ≤ Real.tan ω := by
    have hle := inner_le_supportValue K.val hq0K (ω : Real.Angle)
    rw [K.property.2.2.1, real_inner_smul_left] at hle
    have hinner : inner ℝ (normalVector (0 : Real.Angle))
        (normalVector (ω : Real.Angle)) = Real.cos ω := by
      simp [normalVector, frame, PiLp.inner_apply]
    rw [hinner, hsupp] at hle
    rw [Real.tan_eq_sin_div_cos, le_div_iff₀ hcos]
    linarith
  have hrnn : 0 ≤ (rotationCalculationValues ⟨ω, hω, hω'⟩ ⟨d, hdmin, hdtan⟩).1 := by
    show 0 ≤ 1 - d * (Real.cos ω / Real.sin ω)
    rw [sub_nonneg, mul_div_assoc', div_le_one hsin]
    rw [Real.tan_eq_sin_div_cos, le_div_iff₀ hcos] at hdtan
    exact hdtan
  obtain ⟨r, hr⟩ :
      ∃ r, (rotationCalculationValues ⟨ω, hω, hω'⟩ ⟨d, hdmin, hdtan⟩).1 = r := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ :
      ∃ g, (rotationCalculationValues ⟨ω, hω, hω'⟩ ⟨d, hdmin, hdtan⟩).2.1 = g := ⟨_, rfl⟩
  have hrval : r = 1 - d * (Real.cos ω / Real.sin ω) := by rw [← hr]; rfl
  have hgval : g = Real.sqrt (1 - r ^ 2) := by rw [← hg, ← hr]; rfl
  have hrnn' : 0 ≤ r := by rw [← hr]; exact hrnn
  have hrle : r ≤ 1 := by
    rw [hrval]
    have := mul_nonneg hdpos.le (div_nonneg hcos.le hsin.le)
    linarith
  have hgnn : 0 ≤ g := by rw [hgval]; exact Real.sqrt_nonneg _
  have hgsq : g ^ 2 = 1 - r ^ 2 := by
    rw [hgval]
    exact Real.sq_sqrt (by nlinarith)
  have hrsin : r * Real.sin ω = Real.sin ω - d * Real.cos ω := by
    rw [hrval]
    field_simp
  -- the wedge-gap infimum, hence the vertical surface atom, is at least `g`
  have hinf : g ≤ (wedgeGapInfimum K).1 := by
    apply le_csInf ((Set.nonempty_Ioo.mpr hω0).image _)
    rintro _ ⟨t, ht, rfl⟩
    exact le_wedgeGaps_fst_of_calculationVariables K hω' hccos hsupp hrsin hgsq ht
  have hsurf := hinf.trans (balancedMaximumCap_gap_le_surface K hBalanced hω').1
  have hcoord : (stripParallelogram ω).2.2 = !₂[Real.tan ((Real.pi / 2 - ω) / 2), 1] := by
    have harg : Real.pi / 4 - ω / 2 = (Real.pi / 2 - ω) / 2 := by ring
    simp only [stripParallelogram, harg]
  have hq1K := topFace_sub_smul_normalVector_mem K ho hccos hcoord hcos hgnn hsurf
  have hineq := rotationCalculation_inequalities ⟨ω, hω, hω'⟩ ⟨d, hdmin, hdtan⟩ hrnn
  have hP0 : (rotationCalculationValues ⟨ω, hω, hω'⟩ ⟨d, hdmin, hdtan⟩).2.2.1 ∈
      (K.val : Set Point) := by
    have hq : (rotationCalculationValues ⟨ω, hω, hω'⟩ ⟨d, hdmin, hdtan⟩).2.2.1 =
        (stripParallelogram ω).2.2 - tangentVector 0 + d • normalVector (0 : Real.Angle) := rfl
    rw [hq, hgap.1, ← add_smul, ← hsupp]
    exact hq0K
  have hP1 : (rotationCalculationValues ⟨ω, hω, hω'⟩ ⟨d, hdmin, hdtan⟩).2.2.2 ∈
      (K.val : Set Point) := by
    have hq : (rotationCalculationValues ⟨ω, hω, hω'⟩ ⟨d, hdmin, hdtan⟩).2.2.2 =
        (stripParallelogram ω).2.2 -
          (rotationCalculationValues ⟨ω, hω, hω'⟩ ⟨d, hdmin, hdtan⟩).2.1 •
            normalVector (0 : Real.Angle) := rfl
    rw [hq, hg]
    exact hq1K
  exact consumed_points_subset_innerQuadrant K hω4 hω' hcpos hgap.1 hgap.2.1 hP0 hP1
    hineq.1 hineq.2

theorem balancedMaximumCap_consumed {ω : ℝ} (K : CapSpace ω)
    (hω : Real.arccos (5 / 11 : ℝ) ≤ ω) (hω' : ω < Real.pi / 2)
    (hBalanced : IsBalancedMaximumCap K) (hArea : 11 / 5 ≤ capAreaFunctional K) :
    ∃ t ∈ Set.Ioo 0 ω,
      ({0, (stripParallelogram ω).2.2 - tangentVector 0,
        (stripParallelogram ω).2.2 - normalVector (ω : Real.Angle)} : Set Point) ⊆
        (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerQuadrant := by
  have hpi := Real.pi_pos
  have hω4 : Real.pi / 4 < ω := rotationCalculation_angle_bounds.1.trans_le hω
  have hω0 : 0 < ω := by linarith
  have hcos : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo ⟨by linarith, hω'⟩
  have hsin : 0 < Real.sin ω := Real.sin_pos_of_pos_of_lt_pi hω0 (by linarith)
  have hgap := parallelogram_gap ω ⟨hω0.le, hω'⟩
  have hccos : Real.tan ((Real.pi / 2 - ω) / 2) * Real.cos ω = 1 - Real.sin ω := by
    rw [hgap.2.2.2.2, Real.tan_eq_sin_div_cos]
    field_simp
  have hcoord : (stripParallelogram ω).2.2 = !₂[Real.tan ((Real.pi / 2 - ω) / 2), 1] := by
    have harg : Real.pi / 4 - ω / 2 = (Real.pi / 2 - ω) / 2 := by ring
    simp only [stripParallelogram, harg]
  -- the upper distinguished point belongs to the limiting cap
  have ho : (stripParallelogram ω).2.2 ∈ (K.val : Set Point) := by
    obtain ⟨n, hn, -, -, P, hmax, hlim⟩ := hBalanced
    exact ConvexBody.mem_of_tendsto_hausdorffDist _ (fun i ↦ (P i).val.val) K.val
      (Filter.Eventually.of_forall fun i ↦ (hmax i).1) hlim
  by_cases hcase : rotationCalculationMinimum ⟨ω, hω, hω'⟩ +
      Real.tan ((Real.pi / 2 - ω) / 2) ≤ supportValue K.val (0 : Real.Angle)
  · refine ⟨Real.pi / 2 - ω, ⟨by linarith, by linarith⟩, ?_⟩
    rw [rotatingHallwayParts_innerQuadrant]
    exact consumed_of_le_supportValue_zero hω hω' K hBalanced ho hcase
  push Not at hcase
  -- otherwise the clipped-cap area bound forces the left support value to be large
  have hother : rotationCalculationMinimum ⟨ω, hω, hω'⟩ + Real.tan ((Real.pi / 2 - ω) / 2) ≤
      supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) := by
    by_contra hcon
    push Not at hcon
    have hsub : (K.val : Set Point) ⊆
        clippedCap ω (rotationCalculationMinimum ⟨ω, hω, hω'⟩) := by
      intro p hp
      exact ⟨⟨K.subset_stripParallelogram hp,
        (inner_le_supportValue K.val hp (0 : Real.Angle)).trans hcase.le⟩,
        (inner_le_supportValue K.val hp ((ω + Real.pi / 2 : ℝ) : Real.Angle)).trans hcon.le⟩
    have hbdd : Bornology.IsBounded
        (clippedCap ω (rotationCalculationMinimum ⟨ω, hω, hω'⟩)) := by
      refine (EuclideanSpace.isBounded_coordinate_rectangle
        (-((rotationCalculationMinimum ⟨ω, hω, hω'⟩ +
            Real.tan ((Real.pi / 2 - ω) / 2)) / Real.sin ω))
        (rotationCalculationMinimum ⟨ω, hω, hω'⟩ + Real.tan ((Real.pi / 2 - ω) / 2))
        0 1).subset ?_
      intro p hp
      obtain ⟨⟨hy0, hy1⟩, -, hx, hz⟩ := (mem_clippedCap_iff _ _ p).1 hp
      refine ⟨?_, hx, hy0, hy1⟩
      have h2 : -(rotationCalculationMinimum ⟨ω, hω, hω'⟩ +
          Real.tan ((Real.pi / 2 - ω) / 2)) ≤ p 0 * Real.sin ω := by
        nlinarith [mul_nonneg hcos.le hy0]
      have h3 := (div_le_iff₀ hsin).2 h2
      rwa [neg_div] at h3
    have harea : ClassicalResults.area (K.val : Set Point) ≤
        ClassicalResults.area (clippedCap ω (rotationCalculationMinimum ⟨ω, hω, hω'⟩)) :=
      ENNReal.toReal_mono hbdd.measure_lt_top.ne (MeasureTheory.measure_mono hsub)
    have hmin : ClassicalResults.area
        (clippedCap ω (rotationCalculationMinimum ⟨ω, hω, hω'⟩)) < 11 / 5 :=
      clippedCap_minimum_area ⟨ω, hω, hω'⟩
    have hniche : 0 ≤ ClassicalResults.area (capNiche K) := ENNReal.toReal_nonneg
    rw [capAreaFunctional] at hArea
    linarith
  -- pass to the mirror cap, whose zero-angle support value is the left one
  have hMeq : mirrorReflection ω = ((capReflection ω : Point ≃ₗᵢ[ℝ] Point) : Point → Point) :=
    stripTopReflection_eq_capReflection ω hω0 K.property.2.1
  have htanω : normalVector ((ω + Real.pi / 2 : ℝ) : Real.Angle) =
      tangentVector (ω : Real.Angle) := by
    ext i
    fin_cases i <;>
      simp [normalVector, tangentVector, frame, Real.cos_add, Real.sin_add, -Real.Angle.coe_add]
  have htanT : tangentVector ((Real.pi / 2 : ℝ) : Real.Angle) = -normalVector (0 : Real.Angle) := by
    ext i
    fin_cases i <;> simp [tangentVector, normalVector, frame]
  have hu0 : capReflection ω (normalVector (0 : Real.Angle)) = tangentVector (ω : Real.Angle) := by
    rw [capReflection_normalVector_angle,
      show reflectedAngle ω (0 : Real.Angle) = ((ω + Real.pi / 2 : ℝ) : Real.Angle) from by
        simp [reflectedAngle]]
    exact htanω
  have hvω : capReflection ω (tangentVector (ω : Real.Angle)) = normalVector (0 : Real.Angle) := by
    rw [capReflection_tangentVector_angle,
      show reflectedAngle ω (ω : Real.Angle) = ((Real.pi / 2 : ℝ) : Real.Angle) from by
        simp [reflectedAngle, Real.Angle.coe_add],
      htanT, neg_neg]
  have hc1 : Real.tan ((Real.pi / 2 - ω) / 2) * (1 + Real.sin ω) = Real.cos ω := by
    apply mul_right_cancel₀ hcos.ne'
    nlinarith [hccos, Real.sin_sq_add_cos_sq ω]
  have hfix : capReflection ω (stripParallelogram ω).2.2 = (stripParallelogram ω).2.2 := by
    have hx0 : capReflection ω (stripParallelogram ω).2.2 0 = (stripParallelogram ω).2.2 0 := by
      rw [capReflection_apply_zero, hcoord]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      linarith
    have hx1 : capReflection ω (stripParallelogram ω).2.2 1 = (stripParallelogram ω).2.2 1 := by
      rw [capReflection_apply_one, hcoord]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      linarith
    ext i
    fin_cases i
    · exact hx0
    · exact hx1
  have hQbal : IsBalancedMaximumCap
      (⟨reflectedBody ω K.val, reflectedBody_isCap K⟩ : CapSpace ω) := by
    obtain ⟨P, hPset, hPbal⟩ := balancedMaximumCap_mirror K hBalanced
    have hPQ : P = (⟨reflectedBody ω K.val, reflectedBody_isCap K⟩ : CapSpace ω) := by
      apply Subtype.ext
      apply ConvexBody.ext
      rw [hPset, hMeq]
      rfl
    exact hPQ ▸ hPbal
  have hoQ : (stripParallelogram ω).2.2 ∈ (reflectedBody ω K.val : Set Point) :=
    ⟨_, ho, hfix⟩
  have hQsupp : supportValue (reflectedBody ω K.val) (0 : Real.Angle) =
      supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) := by
    rw [supportValue_reflectedBody]
    congr 1
    simp [reflectedAngle]
  have hmain : ({0, (stripParallelogram ω).2.2 - tangentVector 0,
      (stripParallelogram ω).2.2 - normalVector (ω : Real.Angle)} : Set Point) ⊆
      innerQuadrant (reflectedBody ω K.val : Set Point) (Real.pi / 2 - ω) :=
    consumed_of_le_supportValue_zero hω hω' ⟨reflectedBody ω K.val, reflectedBody_isCap K⟩
      hQbal hoQ (by rw [hQsupp]; exact hother)
  have hR1 : capReflection ω ((stripParallelogram ω).2.2 - tangentVector 0) =
      (stripParallelogram ω).2.2 - normalVector (ω : Real.Angle) := by
    rw [hgap.1, hgap.2.1, map_smul, hu0]
  have hR2 : capReflection ω ((stripParallelogram ω).2.2 - normalVector (ω : Real.Angle)) =
      (stripParallelogram ω).2.2 - tangentVector 0 := by
    rw [hgap.1, hgap.2.1, map_smul, hvω]
  refine ⟨ω - (Real.pi / 2 - ω), ⟨by linarith, by linarith⟩, ?_⟩
  rw [rotatingHallwayParts_innerQuadrant]
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  have hyR : capReflection ω y ∈ ({0, (stripParallelogram ω).2.2 - tangentVector 0,
      (stripParallelogram ω).2.2 - normalVector (ω : Real.Angle)} : Set Point) := by
    rcases hy with rfl | rfl | rfl
    · simp
    · rw [hR1]; simp
    · rw [hR2]; simp
  have h1 := hmain hyR
  rw [innerQuadrant_reflection, ← capReflection_preimage_eq_image] at h1
  simpa [capReflection_involutive] using h1

end MovingSofa

end

end

end
