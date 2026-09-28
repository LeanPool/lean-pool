/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Infrastructure.Geometry.Foundations.Development002
public import LeanPool.MovingSofa.Cap.Foundations.Development002
public import LeanPool.MovingSofa.Cap.Foundations.Development003
public import LeanPool.MovingSofa.Infrastructure.Geometry.Foundations.Development001
public import LeanPool.MovingSofa.Infrastructure.Geometry.Foundations.Development003
public import LeanPool.MovingSofa.Infrastructure.MathlibExtensions.Foundations.Development001

public import LeanPool.MovingSofa.Geometry.Foundations.Development003
public import LeanPool.MovingSofa.Motion.Foundations.Development001

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.MetricSpace.HausdorffDistance
/-!
# Moving sofa: related mathematical developments

* `Cap.Balanced`.
* `Cap.Clipped.Estimates`.
* `Cap.Clipped`.
* `Cap.Densities`.
* `Cap.UpperBoundary`.
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
# Cap / Balanced
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace MovingSofa

/-- The polygonal cap area minus the area of its polygonal niche. -/
def polygonAreaFunctional (Θ : AngleSet) (K : CapSpace Θ.angle) : ℝ :=
  ClassicalResults.area (angleCap Θ K) - ClassicalResults.area (polygonNiche Θ K)

/-- A cap containing the distinguished fan point maximizes the polygonal area functional. -/
def IsMaximumPolygonCap (Θ : AngleSet) (K : PolygonCapSpace Θ) : Prop :=
  (stripParallelogram Θ.angle).2.2 ∈ (K.val.val : Set Point) ∧
    ∀ L : PolygonCapSpace Θ, polygonAreaFunctional Θ L.val ≤ polygonAreaFunctional Θ K.val

/-- The cap is a Hausdorff limit of polygonal maxima on increasingly fine dyadic meshes. -/
def IsBalancedMaximumCap {ω : ℝ} (K : CapSpace ω) : Prop :=
  ∃ (n : ℕ → ℕ) (hn : ∀ i, 2 ≤ n i), StrictMono n ∧
    (∀ i, ∃ k : ℕ, n i = 2 ^ k) ∧
    ∃ P : ∀ i, PolygonCapSpace (uniformAngleSet ω K.property.1 K.property.2.1 (n i) (hn i)),
      (∀ i, IsMaximumPolygonCap _ (P i)) ∧
      Tendsto (fun i ↦ Metric.hausdorffDist ((P i).val.val : Set Point) (K.val : Set Point))
        atTop (𝓝 0)

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
# Cap / Clipped / Estimates
-/

@[expose] public section

noncomputable section

namespace MovingSofa

private theorem clippedArea_bound_low {u t : ℝ}
    (ht : 39 / 20 < t) (ht' : t ≤ 11 / 5) (hu : u < 121 / 50) :
    u - (t - 5 / 4) ^ 2 / t < 11 / 5 := by
  have ht0 : 0 < t := by linarith
  have hsq : 49 / 100 < (t - 5 / 4) ^ 2 := by nlinarith
  have hquot : 49 / 220 < (t - 5 / 4) ^ 2 / t := by
    apply (lt_div_iff₀ ht0).2
    nlinarith
  linarith

private theorem clippedArea_bound {C S : ℝ} (hC : 0 < C) (hS : 0 < S)
    (hcircle : S ^ 2 + C ^ 2 = 1) (hC' : C ≤ 5 / 11) :
    let d : ℝ := if S / C < 11 / 5 then 5 / 4 else 11 / 10
    1 / C - (S / C - d) ^ 2 * (C / S) < 11 / 5 := by
  dsimp
  split_ifs with h
  · have ht : 0 < S / C := div_pos hS hC
    have hid : (1 / C) ^ 2 = 1 + (S / C) ^ 2 := by
      field_simp
      nlinarith
    have hu : 11 / 5 ≤ 1 / C := by
      apply (le_div_iff₀ hC).2
      linarith
    have hlo : 39 / 20 < S / C := by nlinarith
    have hhi : 1 / C < 121 / 50 := by
      have hu0 : 0 < 1 / C := by positivity
      nlinarith
    have hb := clippedArea_bound_low hlo h.le hhi
    convert hb using 1
    field_simp
  · have hs1 : S ≤ 1 := by nlinarith [sq_nonneg C]
    have hc : C / (1 + S) ≤ C / S / 2 := by
      have hs' : 0 < 1 + S := by linarith
      apply (div_le_iff₀ hs').2
      field_simp
      nlinarith [mul_nonneg hC.le (sub_nonneg.mpr hs1)]
    have hid : 1 / C - (S / C - 11 / 10) ^ 2 * (C / S) =
        C / (1 + S) + 11 / 5 - (121 / 100) * (C / S) := by
      field_simp
      nlinarith [hcircle]
    rw [hid]
    have hp : 0 < C / S := div_pos hC hS
    linarith

theorem rotationCalculation_area_estimate (ω : RotationCalculationAngle) :
    1 / Real.cos ω.val - (Real.tan ω.val - rotationCalculationMinimum ω) ^ 2 *
      (Real.cos ω.val / Real.sin ω.val) < 11 / 5 := by
  have hw0 : 0 < ω.val :=
    (Real.arccos_pos.mpr (by norm_num : (5 / 11 : ℝ) < 1)).trans_le ω.property.1
  have hC : 0 < Real.cos ω.val :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ω.property.2⟩
  have hS : 0 < Real.sin ω.val :=
    Real.sin_pos_of_pos_of_lt_pi hw0 (by linarith [ω.property.2, Real.pi_pos])
  have hC' : Real.cos ω.val ≤ 5 / 11 := by
    have h := Real.strictAntiOn_cos.antitoneOn
      (show Real.arccos (5 / 11 : ℝ) ∈ Set.Icc 0 Real.pi from
        ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩)
      (show ω.val ∈ Set.Icc 0 Real.pi from
        ⟨hw0.le, by linarith [ω.property.2, Real.pi_pos]⟩) ω.property.1
    simpa only [Real.cos_arccos (by norm_num : (-1 : ℝ) ≤ 5 / 11)
      (by norm_num : (5 / 11 : ℝ) ≤ 1)] using h
  have hs : (Real.sin ω.val / Real.cos ω.val < 11 / 5) ↔
      ω.val < Real.arctan (11 / 5 : ℝ) := by
    rw [← Real.tan_eq_sin_div_cos, ← Real.arctan_lt_arctan_iff]
    rw [Real.arctan_tan (by linarith [Real.pi_pos]) ω.property.2]
  have hb := clippedArea_bound hC hS (Real.sin_sq_add_cos_sq ω.val) hC'
  dsimp at hb
  simp only [hs] at hb
  simpa only [← Real.tan_eq_sin_div_cos, rotationCalculationMinimum] using hb

theorem rotationCalculationMinimum_pos (ω : RotationCalculationAngle) :
    0 < rotationCalculationMinimum ω := by
  unfold rotationCalculationMinimum
  split_ifs <;> norm_num

theorem rotationCalculationMinimum_lt_tan (ω : RotationCalculationAngle) :
    rotationCalculationMinimum ω < Real.tan ω.val := by
  have hw0 : 0 < ω.val :=
    (Real.arccos_pos.mpr (by norm_num : (5 / 11 : ℝ) < 1)).trans_le ω.property.1
  have hC : 0 < Real.cos ω.val :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ω.property.2⟩
  have hS : 0 < Real.sin ω.val :=
    Real.sin_pos_of_pos_of_lt_pi hw0 (by linarith [ω.property.2, Real.pi_pos])
  have hC' : Real.cos ω.val ≤ 5 / 11 := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (Real.arccos_nonneg (5 / 11))
      (by linarith [ω.property.2, Real.pi_pos] : ω.val ≤ Real.pi) ω.property.1
    simpa only [Real.cos_arccos (by norm_num : (-1 : ℝ) ≤ 5 / 11)
      (by norm_num : (5 / 11 : ℝ) ≤ 1)] using h
  have hsq : Real.cos ω.val ^ 2 ≤ (5 / 11 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hC.le hC' 2
  have ht : (5 / 4 : ℝ) < Real.tan ω.val := by
    rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hC]
    nlinarith [Real.sin_sq_add_cos_sq ω.val]
  unfold rotationCalculationMinimum
  split_ifs <;> linarith

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
# Cap / Clipped
-/

@[expose] public section

noncomputable section

namespace MovingSofa

open MeasureTheory Set

/-- Clip the strip parallelogram by the two additional symmetric wall constraints. -/
def clippedCap (ω d : ℝ) : Set Point :=
  (stripParallelogram ω).1 ∩
    normalHalfPlane 0 (d + Real.tan ((Real.pi / 2 - ω) / 2)) false false ∩
    normalHalfPlane ((ω + Real.pi / 2 : ℝ) : Real.Angle)
      (d + Real.tan ((Real.pi / 2 - ω) / 2)) false false

theorem mem_clippedCap_iff (ω d : ℝ) (p : Point) :
    p ∈ clippedCap ω d ↔
      (0 ≤ p 1 ∧ p 1 ≤ 1) ∧
      (0 ≤ Real.cos ω * p 0 + Real.sin ω * p 1 ∧
        Real.cos ω * p 0 + Real.sin ω * p 1 ≤ 1) ∧
      p 0 ≤ d + Real.tan ((Real.pi / 2 - ω) / 2) ∧
      -Real.sin ω * p 0 + Real.cos ω * p 1 ≤
        d + Real.tan ((Real.pi / 2 - ω) / 2) := by
  simp only [clippedCap, Set.mem_inter_iff, mem_stripParallelogram_iff]
  simp [normalHalfPlane, normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
    Real.cos_add, Real.sin_add, -Real.Angle.coe_add, and_assoc, mul_comm]

theorem clippedCap_removed_pieces_disjoint {C S c d : ℝ}
    (hC : 0 < C) (hS : 0 ≤ S) (hd : 0 ≤ d) (hc : c * (1 + S) = C) :
    Disjoint {p : Point | p 1 ≤ 1 ∧ c + d < p 0}
      {p : Point | c + d < -S * p 0 + C * p 1} := by
  rw [Set.disjoint_left]
  intro p hp hq
  change p 1 ≤ 1 ∧ c + d < p 0 at hp
  change c + d < -S * p 0 + C * p 1 at hq
  have hmul := mul_le_mul_of_nonneg_left hp.1 hC.le
  have hmul' := mul_le_mul_of_nonneg_left (le_of_lt hp.2) hS
  have hprod := mul_nonneg hd (by linarith : 0 ≤ 1 + S)
  nlinarith

private theorem mem_stripParallelogram_coordinates (ω : ℝ) (p : Point) :
    p ∈ (stripParallelogram ω).1 ↔
      (0 ≤ p 1 ∧ p 1 ≤ 1) ∧
      (0 ≤ Real.cos ω * p 0 + Real.sin ω * p 1 ∧
        Real.cos ω * p 0 + Real.sin ω * p 1 ≤ 1) := by
  rw [mem_stripParallelogram_iff]
  simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]

private theorem capReflection_rotatedCoordinate (ω : ℝ) (p : Point) :
    Real.cos ω * capReflection ω p 0 +
        Real.sin ω * capReflection ω p 1 = p 1 := by
  rw [capReflection_apply_zero, capReflection_apply_one]
  calc
    _ = (Real.sin ω ^ 2 + Real.cos ω ^ 2) * p 1 := by ring
    _ = p 1 := by rw [Real.sin_sq_add_cos_sq]; ring

private def rightRemovedTriangle (ω d : ℝ) : Set Point :=
  (stripParallelogram ω).1 ∩
    {p | d + Real.tan ((Real.pi / 2 - ω) / 2) < p 0}

private def leftRemovedTriangle (ω d : ℝ) : Set Point :=
  (stripParallelogram ω).1 ∩
    {p | d + Real.tan ((Real.pi / 2 - ω) / 2) <
      -Real.sin ω * p 0 + Real.cos ω * p 1}

private theorem leftRemovedTriangle_eq_preimage (ω d : ℝ) :
    leftRemovedTriangle ω d =
      capReflection ω ⁻¹' rightRemovedTriangle ω d := by
  ext p
  simp only [leftRemovedTriangle, rightRemovedTriangle, Set.mem_inter_iff,
    Set.mem_ofPred_eq, Set.mem_preimage]
  rw [mem_stripParallelogram_coordinates,
    mem_stripParallelogram_coordinates,
    capReflection_rotatedCoordinate, capReflection_apply_zero,
    capReflection_apply_one]
  tauto

private theorem volume_stripParallelogram (ω : ℝ) (hC : 0 < Real.cos ω) :
    volume (stripParallelogram ω).1 = ENNReal.ofReal (1 / Real.cos ω) := by
  let f : ℝ → ℝ := fun y ↦ (-Real.sin ω * y) / Real.cos ω
  let g : ℝ → ℝ := fun y ↦ (1 - Real.sin ω * y) / Real.cos ω
  have hf : Measurable f := by fun_prop
  have hg : Measurable g := by fun_prop
  have hfi : IntegrableOn f (Icc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp
      ((by fun_prop : Continuous f).intervalIntegrable 0 1)
  have hgi : IntegrableOn g (Icc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp
      ((by fun_prop : Continuous g).intervalIntegrable 0 1)
  have hfg : ∀ y ∈ Icc (0 : ℝ) 1, f y ≤ g y := by
    intro y _
    dsimp [f, g]
    rw [div_le_div_iff_of_pos_right hC]
    linarith
  have hset : (stripParallelogram ω).1 =
      {p : Point | p 1 ∈ Icc (0 : ℝ) 1 ∧ p 0 ∈ Icc (f (p 1)) (g (p 1))} := by
    ext p
    rw [mem_stripParallelogram_coordinates]
    simp only [Set.mem_ofPred_eq, Set.mem_Icc]
    constructor
    · rintro ⟨hy, hz⟩
      refine ⟨hy, ?_, ?_⟩
      · dsimp [f]
        apply (div_le_iff₀ hC).2
        linarith [hz.1]
      · dsimp [g]
        apply (le_div_iff₀ hC).2
        linarith [hz.2]
    · rintro ⟨hy, hx0, hx1⟩
      refine ⟨hy, ?_, ?_⟩
      · dsimp [f] at hx0
        have := (div_le_iff₀ hC).1 hx0
        linarith
      · dsimp [g] at hx1
        have := (le_div_iff₀ hC).1 hx1
        linarith
  rw [hset, volume_horizontalIcc hf hg measurableSet_Icc hfi hgi hfg]
  have hdiff : g - f = fun _ ↦ 1 / Real.cos ω := by
    funext y
    dsimp [f, g]
    field_simp [hC.ne']
    ring
  rw [hdiff, setIntegral_const]
  simp

private theorem volume_rightRemovedTriangle (ω d : ℝ)
    (hω : ω ∈ Ioo 0 (Real.pi / 2)) (hd0 : 0 ≤ d) (hdt : d ≤ Real.tan ω) :
    volume (rightRemovedTriangle ω d) =
      ENNReal.ofReal ((Real.tan ω - d) ^ 2 *
        (Real.cos ω / Real.sin ω) / 2) := by
  let C := Real.cos ω
  let S := Real.sin ω
  let c := Real.tan ((Real.pi / 2 - ω) / 2)
  let A := c + d
  let b := Real.tan ω - d
  let H := b * C / S
  let f : ℝ → ℝ := fun _ ↦ A
  let g : ℝ → ℝ := fun y ↦ (1 - S * y) / C
  have hC : 0 < C :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hω.1], hω.2⟩
  have hS : 0 < S := Real.sin_pos_of_pos_of_lt_pi hω.1
    (by linarith [hω.2, Real.pi_pos])
  have hcircle : S ^ 2 + C ^ 2 = 1 := Real.sin_sq_add_cos_sq ω
  have hgap : c = C⁻¹ - Real.tan ω :=
    (parallelogram_gap ω ⟨hω.1.le, hω.2⟩).2.2.2.2
  have htan : Real.tan ω = S / C := Real.tan_eq_sin_div_cos ω
  have hcC : c * C = 1 - S := by
    rw [hgap, htan]
    field_simp [hC.ne']
  have hS1 : S < 1 := by nlinarith [sq_pos_of_pos hC]
  have hc0 : 0 < c := by
    have hcdiv : c = (1 - S) / C := by
      apply (eq_div_iff hC.ne').2
      exact hcC
    rw [hcdiv]
    exact div_pos (sub_pos.mpr hS1) hC
  have hb0 : 0 ≤ b := by dsimp [b]; linarith
  have hbC : b * C = S - d * C := by
    dsimp [b]
    rw [htan]
    field_simp [hC.ne']
  have hAC : A * C = 1 - b * C := by
    dsimp [A]
    nlinarith [hcC, hbC]
  have hH0 : 0 ≤ H := by positivity
  have hH1 : H ≤ 1 := by
    dsimp [H, b]
    apply (div_le_iff₀ hS).2
    dsimp [b] at hbC
    nlinarith
  have hf : Measurable f := measurable_const
  have hg : Measurable g := by fun_prop
  have hfi : IntegrableOn f (Icc (0 : ℝ) H) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hH0).mp
      ((by fun_prop : Continuous f).intervalIntegrable 0 H)
  have hgi : IntegrableOn g (Icc (0 : ℝ) H) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hH0).mp
      ((by fun_prop : Continuous g).intervalIntegrable 0 H)
  have hfg : ∀ y ∈ Icc (0 : ℝ) H, f y ≤ g y := by
    intro y hy
    dsimp [f, g, A]
    apply (le_div_iff₀ hC).2
    dsimp [H, b] at hy
    dsimp [b] at hbC hAC
    have hy' := (le_div_iff₀ hS).1 hy.2
    nlinarith
  have hset : rightRemovedTriangle ω d =
      {p : Point | p 1 ∈ Icc (0 : ℝ) H ∧ p 0 ∈ Ioc (f (p 1)) (g (p 1))} := by
    ext p
    simp only [rightRemovedTriangle, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Set.mem_Icc, Set.mem_Ioc]
    rw [mem_stripParallelogram_coordinates]
    constructor
    · rintro ⟨⟨hy, hz⟩, hxA⟩
      refine ⟨⟨hy.1, ?_⟩, ?_, ?_⟩
      · dsimp [H, b]
        have hu : C * A + S * p 1 < 1 := by
          dsimp [A]
          nlinarith [mul_lt_mul_of_pos_left hxA hC]
        apply (le_div_iff₀ hS).2
        nlinarith [hAC]
      · simpa [f, A, add_comm]
      · dsimp [g]
        apply (le_div_iff₀ hC).2
        linarith [hz.2]
    · rintro ⟨hy, hxA, hxU⟩
      refine ⟨⟨⟨hy.1, hy.2.trans hH1⟩, ?_, ?_⟩, ?_⟩
      · have hA0 : 0 < A := by dsimp [A]; linarith
        dsimp [f, A] at hxA
        nlinarith [mul_pos hC (lt_trans hA0 hxA)]
      · dsimp [g] at hxU
        have := (le_div_iff₀ hC).1 hxU
        linarith
      · simpa [f, A, add_comm] using hxA
  rw [hset, volume_horizontalIoc hf hg measurableSet_Icc hfi hgi hfg]
  have hdiff : g - f = fun y ↦ b - S / C * y := by
    funext y
    dsimp [f, g, A, b]
    rw [hgap, htan]
    field_simp [hC.ne']
    ring
  rw [hdiff, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hH0]
  have hconst : IntervalIntegrable (fun _ : ℝ ↦ b) volume 0 H :=
    continuous_const.intervalIntegrable 0 H
  have hlinear : IntervalIntegrable (fun y : ℝ ↦ S / C * y) volume 0 H :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 H
  rw [intervalIntegral.integral_sub hconst hlinear,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_id]
  simp only [sub_zero, smul_eq_mul]
  congr 1
  norm_num
  change H * b - S / C * (H ^ 2 / 2) = b ^ 2 * (C / S) / 2
  dsimp [H]
  field_simp [hC.ne', hS.ne']
  ring

private theorem measurableSet_stripParallelogram (ω : ℝ) :
    MeasurableSet (stripParallelogram ω).1 := by
  rw [show (stripParallelogram ω).1 =
      {p : Point |
        (0 ≤ p 1 ∧ p 1 ≤ 1) ∧
        (0 ≤ Real.cos ω * p 0 + Real.sin ω * p 1 ∧
          Real.cos ω * p 0 + Real.sin ω * p 1 ≤ 1)} by
    ext p
    exact mem_stripParallelogram_coordinates ω p]
  measurability

private theorem measurableSet_rightRemovedTriangle (ω d : ℝ) :
    MeasurableSet (rightRemovedTriangle ω d) := by
  unfold rightRemovedTriangle
  apply (measurableSet_stripParallelogram ω).inter
  measurability

private theorem measurableSet_leftRemovedTriangle (ω d : ℝ) :
    MeasurableSet (leftRemovedTriangle ω d) := by
  unfold leftRemovedTriangle
  apply (measurableSet_stripParallelogram ω).inter
  measurability

private theorem volume_leftRemovedTriangle_eq_right (ω d : ℝ) :
    volume (leftRemovedTriangle ω d) = volume (rightRemovedTriangle ω d) := by
  rw [leftRemovedTriangle_eq_preimage]
  exact (LinearIsometryEquiv.measurePreserving (capReflection ω)).measure_preimage
    (measurableSet_rightRemovedTriangle ω d).nullMeasurableSet

private theorem stripParallelogram_decomposition (ω d : ℝ) :
    (stripParallelogram ω).1 =
      (clippedCap ω d ∪ rightRemovedTriangle ω d) ∪ leftRemovedTriangle ω d := by
  ext p
  simp only [Set.mem_union]
  constructor
  · intro hp
    by_cases hx : p 0 ≤ d + Real.tan ((Real.pi / 2 - ω) / 2)
    · by_cases hz : -Real.sin ω * p 0 + Real.cos ω * p 1 ≤
          d + Real.tan ((Real.pi / 2 - ω) / 2)
      · exact Or.inl (Or.inl ((mem_clippedCap_iff ω d p).2
          ⟨((mem_stripParallelogram_coordinates ω p).1 hp).1,
            ((mem_stripParallelogram_coordinates ω p).1 hp).2, hx, hz⟩))
      · exact Or.inr ⟨hp, by
          change d + Real.tan ((Real.pi / 2 - ω) / 2) <
            -Real.sin ω * p 0 + Real.cos ω * p 1
          exact lt_of_not_ge hz⟩
    · exact Or.inl (Or.inr ⟨hp, by
        change d + Real.tan ((Real.pi / 2 - ω) / 2) < p 0
        exact lt_of_not_ge hx⟩)
  · rintro (hp | hp)
    · rcases hp with hp | hp
      · exact (mem_stripParallelogram_coordinates ω p).2
          ⟨((mem_clippedCap_iff ω d p).1 hp).1,
            ((mem_clippedCap_iff ω d p).1 hp).2.1⟩
      · exact hp.1
    · exact hp.1

private theorem clippedCap_disjoint_rightRemovedTriangle (ω d : ℝ) :
    Disjoint (clippedCap ω d) (rightRemovedTriangle ω d) := by
  rw [Set.disjoint_left]
  intro p hp hq
  have hp' := ((mem_clippedCap_iff ω d p).1 hp).2.2.1
  exact (not_lt_of_ge hp') hq.2

private theorem clippedCap_disjoint_leftRemovedTriangle (ω d : ℝ) :
    Disjoint (clippedCap ω d) (leftRemovedTriangle ω d) := by
  rw [Set.disjoint_left]
  intro p hp hq
  have hp' := ((mem_clippedCap_iff ω d p).1 hp).2.2.2
  exact (not_lt_of_ge hp') hq.2

private theorem rightRemovedTriangle_disjoint_leftRemovedTriangle
    {ω d : ℝ} (hC : 0 < Real.cos ω) (hS : 0 ≤ Real.sin ω) (hd : 0 ≤ d)
    (hc : Real.tan ((Real.pi / 2 - ω) / 2) * (1 + Real.sin ω) = Real.cos ω) :
    Disjoint (rightRemovedTriangle ω d) (leftRemovedTriangle ω d) := by
  apply (clippedCap_removed_pieces_disjoint hC hS hd hc).mono
  · rintro p ⟨hp, hright⟩
    change d + Real.tan ((Real.pi / 2 - ω) / 2) < p 0 at hright
    exact ⟨((mem_stripParallelogram_coordinates ω p).1 hp).1.2,
      by simpa [add_comm] using hright⟩
  · rintro p ⟨_, hleft⟩
    change d + Real.tan ((Real.pi / 2 - ω) / 2) <
      -Real.sin ω * p 0 + Real.cos ω * p 1 at hleft
    simpa [add_comm] using hleft

theorem clippedCap_area_formula (ω d : ℝ)
    (hω : ω ∈ Ioo 0 (Real.pi / 2)) (hd0 : 0 ≤ d) (hdt : d ≤ Real.tan ω) :
    ClassicalResults.area (clippedCap ω d) =
      1 / Real.cos ω - (Real.tan ω - d) ^ 2 *
        (Real.cos ω / Real.sin ω) := by
  let C := Real.cos ω
  let S := Real.sin ω
  let c := Real.tan ((Real.pi / 2 - ω) / 2)
  let T := (Real.tan ω - d) ^ 2 * (C / S) / 2
  have hC : 0 < C :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hω.1], hω.2⟩
  have hS : 0 < S := Real.sin_pos_of_pos_of_lt_pi hω.1
    (by linarith [hω.2, Real.pi_pos])
  have hgap : c = C⁻¹ - Real.tan ω :=
    (parallelogram_gap ω ⟨hω.1.le, hω.2⟩).2.2.2.2
  have htan : Real.tan ω = S / C := Real.tan_eq_sin_div_cos ω
  have hcC : c * C = 1 - S := by
    rw [hgap, htan]
    field_simp [hC.ne']
  have hc : c * (1 + S) = C := by
    apply (mul_right_cancel₀ hC.ne')
    nlinarith [hcC, Real.sin_sq_add_cos_sq ω]
  have hP := volume_stripParallelogram ω hC
  have hR := volume_rightRemovedTriangle ω d hω hd0 hdt
  have hL : volume (leftRemovedTriangle ω d) = ENNReal.ofReal T := by
    rw [volume_leftRemovedTriangle_eq_right, hR]
  have hR' : volume (rightRemovedTriangle ω d) = ENNReal.ofReal T := by
    simpa [T, C, S] using hR
  have hCR := clippedCap_disjoint_rightRemovedTriangle ω d
  have hCL := clippedCap_disjoint_leftRemovedTriangle ω d
  have hRL := rightRemovedTriangle_disjoint_leftRemovedTriangle hC hS.le hd0 hc
  have hdecomp : volume (stripParallelogram ω).1 =
      (volume (clippedCap ω d) + volume (rightRemovedTriangle ω d)) +
        volume (leftRemovedTriangle ω d) := by
    rw [stripParallelogram_decomposition,
      measure_union (hCL.union_left hRL) (measurableSet_leftRemovedTriangle ω d),
      measure_union hCR (measurableSet_rightRemovedTriangle ω d)]
  rw [hP, hR', hL] at hdecomp
  have hclip_subset : clippedCap ω d ⊆ (stripParallelogram ω).1 := by
    intro p hp
    exact (mem_stripParallelogram_coordinates ω p).2
      ⟨((mem_clippedCap_iff ω d p).1 hp).1,
        ((mem_clippedCap_iff ω d p).1 hp).2.1⟩
  have hclip_ne : volume (clippedCap ω d) ≠ ⊤ := by
    apply ne_of_lt
    refine lt_of_le_of_lt (measure_mono hclip_subset) ?_
    rw [hP]
    exact ENNReal.ofReal_lt_top
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hTne : ENNReal.ofReal T ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsum_ne : volume (clippedCap ω d) + ENNReal.ofReal T ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hclip_ne, hTne⟩
  have hreal := congrArg ENNReal.toReal hdecomp
  rw [ENNReal.toReal_add hsum_ne hTne,
    ENNReal.toReal_add hclip_ne hTne,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / Real.cos ω),
    ENNReal.toReal_ofReal hT0] at hreal
  unfold ClassicalResults.area
  dsimp [T, C, S] at hreal ⊢
  linarith

theorem clippedCap_minimum_area (ω : RotationCalculationAngle) :
    ClassicalResults.area (clippedCap ω.val (rotationCalculationMinimum ω)) < 11 / 5 := by
  have hω0 : 0 < ω.val :=
    (Real.arccos_pos.mpr (by norm_num : (5 / 11 : ℝ) < 1)).trans_le ω.property.1
  calc
    ClassicalResults.area (clippedCap ω.val (rotationCalculationMinimum ω)) =
        1 / Real.cos ω.val -
          (Real.tan ω.val - rotationCalculationMinimum ω) ^ 2 *
            (Real.cos ω.val / Real.sin ω.val) :=
      clippedCap_area_formula ω.val (rotationCalculationMinimum ω)
        ⟨hω0, ω.property.2⟩ (rotationCalculationMinimum_pos ω).le
        (rotationCalculationMinimum_lt_tan ω).le
    _ < 11 / 5 := rotationCalculation_area_estimate ω

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
# Cap / Densities
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace MovingSofa

private theorem coe_injOn_halfTurn :
    Set.InjOn (fun t : ℝ ↦ (t : Real.Angle)) (Icc 0 Real.pi) := by
  let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  intro x hx y hy heq
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (show x ∈ Ico 0 (0 + 2 * Real.pi) from ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩)
    (show y ∈ Ico 0 (0 + 2 * Real.pi) from ⟨hy.1, by linarith [hy.2, Real.pi_pos]⟩)).mp heq

/-- A right-angle cap whose surface area measure has angular densities on the two upper quarter
circles has no atom at a normal direction of the right upper quarter. -/
theorem HasCapDensities.surfaceAreaMeasure_singleton_eq_zero_of_mem_Ico
    {K : RightAngleCapSpace} {r s : ℝ → ℝ≥0} (hK : HasCapDensities K r s) {t : ℝ}
    (ht : t ∈ Ico 0 (Real.pi / 2)) :
    surfaceAreaMeasure K.1 {(t : Real.Angle)} = 0 := by
  have he := congrArg (fun μ : Measure Real.Angle ↦ μ {(t : Real.Angle)}) hK.2.2.1
  have hm : (t : Real.Angle) ∈
      (fun x : ℝ ↦ (x : Real.Angle)) '' Ico 0 (Real.pi / 2) := ⟨t, ht, rfl⟩
  rw [Measure.restrict_apply (measurableSet_singleton _),
    inter_eq_left.mpr (singleton_subset_iff.mpr hm)] at he
  rw [he]
  apply Measure.map_restrict_withDensity_singleton volume _ Real.Angle.continuous_coe.measurable
    _ (coe_injOn_halfTurn.mono ?_) _ ht
  intro x hx
  exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩

/-- A right-angle cap whose surface area measure has angular densities on the two upper quarter
circles has no atom at a normal direction of the left upper quarter. -/
theorem HasCapDensities.surfaceAreaMeasure_singleton_eq_zero_of_mem_Ioc
    {K : RightAngleCapSpace} {r s : ℝ → ℝ≥0} (hK : HasCapDensities K r s) {t : ℝ}
    (ht : t ∈ Ioc 0 (Real.pi / 2)) :
    surfaceAreaMeasure K.1 {((t + Real.pi / 2 : ℝ) : Real.Angle)} = 0 := by
  have he := congrArg (fun μ : Measure Real.Angle ↦
    μ {((t + Real.pi / 2 : ℝ) : Real.Angle)}) hK.2.2.2
  have hm : ((t + Real.pi / 2 : ℝ) : Real.Angle) ∈
      (fun x : ℝ ↦ (x : Real.Angle)) '' Ioc (Real.pi / 2) Real.pi :=
    ⟨t + Real.pi / 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩
  rw [Measure.restrict_apply (measurableSet_singleton _),
    inter_eq_left.mpr (singleton_subset_iff.mpr hm)] at he
  rw [he]
  apply Measure.map_restrict_withDensity_singleton volume _
    (Real.Angle.continuous_coe.comp (continuous_id.add continuous_const)).measurable
    _ ?_ _ ht
  intro x hx y hy hxy
  have heq := coe_injOn_halfTurn
    (show x + Real.pi / 2 ∈ Icc 0 Real.pi from
      ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2]⟩)
    (show y + Real.pi / 2 ∈ Icc 0 Real.pi from
      ⟨by linarith [hy.1, Real.pi_pos], by linarith [hy.2]⟩) hxy
  linarith

theorem capDensities_contact_eq (K : RightAngleCapSpace)
    (hK : ∃ r s, HasCapDensities K r s) :
    (∀ t ∈ Set.Ico (0 : ℝ) (Real.pi / 2),
      (capVertices K t).1.1 = (capVertices K t).1.2 ∧
      (tangentArmLengths K t).1.1 = (tangentArmLengths K t).1.2) ∧
    (∀ t ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      (capVertices K t).2.1 = (capVertices K t).2.2 ∧
      (tangentArmLengths K t).2.1 = (tangentArmLengths K t).2.2) := by
  obtain ⟨r, s, hK⟩ := hK
  constructor
  · intro t ht
    have h := (surfaceAreaMeasure_atom_length K.1 (t : Real.Angle)).2.2
    rw [hK.surfaceAreaMeasure_singleton_eq_zero_of_mem_Ico ht] at h
    simp only [ENNReal.toReal_zero, zero_smul, add_zero] at h
    have h' : (capVertices K t).1.1 = (capVertices K t).1.2 := h
    exact ⟨h', by simp only [tangentArmLengths, h']⟩
  · intro t ht
    have h := (surfaceAreaMeasure_atom_length K.1
      ((t + Real.pi / 2 : ℝ) : Real.Angle)).2.2
    rw [hK.surfaceAreaMeasure_singleton_eq_zero_of_mem_Ioc ht] at h
    simp only [ENNReal.toReal_zero, zero_smul, add_zero] at h
    have h' : (capVertices K t).2.1 = (capVertices K t).2.2 := h
    exact ⟨h', by simp only [tangentArmLengths, h']⟩

/-- A right-angle cap carrying angular densities has singleton extreme faces at every upper normal
direction except possibly the vertical one: the densities exclude atoms of the surface area measure
on the two open quarter circles, so the corresponding faces have zero side length. -/
theorem capDensities_edgeVertices_eq (K : RightAngleCapSpace)
    (hK : ∃ r s, HasCapDensities K r s) {t : ℝ} (ht : t ∈ Icc 0 Real.pi)
    (htop : t ≠ Real.pi / 2) :
    (edgeVertices K.val (t : Real.Angle)).1 = (edgeVertices K.val (t : Real.Angle)).2 := by
  rcases lt_or_gt_of_ne htop with h | h
  · exact ((capDensities_contact_eq K hK).1 t ⟨ht.1, h⟩).1
  · have hmem : t - Real.pi / 2 ∈ Ioc (0 : ℝ) (Real.pi / 2) := ⟨by linarith, by linarith [ht.2]⟩
    have h' : (edgeVertices K.val ((t - Real.pi / 2 + Real.pi / 2 : ℝ) : Real.Angle)).1 =
        (edgeVertices K.val ((t - Real.pi / 2 + Real.pi / 2 : ℝ) : Real.Angle)).2 :=
      ((capDensities_contact_eq K hK).2 (t - Real.pi / 2) hmem).1
    rwa [show t - Real.pi / 2 + Real.pi / 2 = t from by ring] at h'

/-- The two cap contact paths and their scalar density functions on the quarter-turn interval. -/
def nondegenerateCapData (K : RightAngleCapSpace)
    (_hK : ∃ r s, HasCapDensities K r s) :
    ((Set.Icc (0 : ℝ) (Real.pi / 2) → Point) ×
      (Set.Icc (0 : ℝ) (Real.pi / 2) → Point)) ×
    ((Set.Icc (0 : ℝ) (Real.pi / 2) → ℝ) ×
      (Set.Icc (0 : ℝ) (Real.pi / 2) → ℝ)) := by
  classical
  exact ((fun t ↦ if (t : ℝ) = Real.pi / 2 then (capVertices K t).1.2
      else (capVertices K t).1.1,
    fun t ↦ (capVertices K t).2.1),
    (fun t ↦ if (t : ℝ) = Real.pi / 2 then (tangentArmLengths K t).1.2
      else (tangentArmLengths K t).1.1,
    fun t ↦ (tangentArmLengths K t).2.1))

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
# Cap / Upper Boundary
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The union of exposed cap edges over the upper range of normal directions. -/
def capUpperBoundary {ω : ℝ} (K : CapSpace ω) : Set Point :=
  ⋃ t ∈ Set.Icc 0 (ω + Real.pi / 2), exposedEdge K.val (t : Real.Angle)

theorem capUpperBoundary_connected {ω : ℝ} (K : CapSpace ω) :
    IsConnected (capUpperBoundary K) := by
  let I : Set ℝ := Set.Icc 0 (ω + Real.pi / 2)
  let G : Set (I × Point) :=
    {q | q.2 ∈ exposedEdge K.val ((q.1 : ℝ) : Real.Angle)}
  have hω : 0 ≤ ω + Real.pi / 2 := by
    have := K.property.1
    positivity
  have hI : IsConnected I := isConnected_Icc hω
  let _ : ConnectedSpace I := Subtype.connectedSpace hI
  have hnormal : Continuous (fun q : I × Point ↦
      normalVector (((q.1 : I) : ℝ) : Real.Angle)) :=
    continuous_normalVector_real.comp (continuous_subtype_val.comp continuous_fst)
  have hsupport : Continuous (fun q : I × Point ↦
      supportValue K.val (((q.1 : I) : ℝ) : Real.Angle)) :=
    (continuous_supportValue_real K.val).comp (continuous_subtype_val.comp continuous_fst)
  have heq : IsClosed {q : I × Point |
      inner ℝ q.2 (normalVector (((q.1 : I) : ℝ) : Real.Angle)) =
        supportValue K.val (((q.1 : I) : ℝ) : Real.Angle)} :=
    isClosed_eq (continuous_snd.inner hnormal) hsupport
  have hG : IsCompact G := by
    rw [show G = Set.univ ×ˢ (K.val : Set Point) ∩
        {q : I × Point | inner ℝ q.2 (normalVector (((q.1 : I) : ℝ) : Real.Angle)) =
          supportValue K.val (((q.1 : I) : ℝ) : Real.Angle)} by
      ext q
      simp only [G, exposedEdge, supportingLineHalfPlane, normalLine, Set.mem_ofPred_eq,
        Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and]]
    exact (isCompact_univ.prod K.val.isCompact).inter_right heq
  let _ : CompactSpace G := isCompact_iff_compactSpace.mp hG
  let π : G → I := fun q ↦ q.1.1
  have hπcont : Continuous π := continuous_fst.comp continuous_subtype_val
  have hπsurj : Function.Surjective π := by
    intro t
    obtain ⟨x, hx⟩ := exposedEdge_nonempty K.val ((t : ℝ) : Real.Angle)
    exact ⟨⟨(t, x), hx⟩, rfl⟩
  have hπquot : Topology.IsQuotientMap π :=
    Topology.IsQuotientMap.of_surjective_continuous hπsurj hπcont
  have hfiber (t : I) : IsConnected (π ⁻¹' {t}) := by
    let E := exposedEdge K.val ((t : ℝ) : Real.Angle)
    let e : E → G := fun x ↦ ⟨(t, x), x.property⟩
    have hecont : Continuous e := by
      apply Continuous.subtype_mk
      exact continuous_const.prodMk continuous_subtype_val
    have himage : e '' Set.univ = π ⁻¹' {t} := by
      ext q
      constructor
      · rintro ⟨x, -, rfl⟩
        simp [π, e]
      · intro hq
        have hqt : q.1.1 = t := by simpa [π] using hq
        have hqx : q.1.2 ∈ exposedEdge K.val ((t : ℝ) : Real.Angle) := by
          have hqG := q.property
          change q.1.2 ∈ exposedEdge K.val (((q.1.1 : I) : ℝ) : Real.Angle) at hqG
          simpa [hqt] using hqG
        let x : E := ⟨q.1.2, hqx⟩
        refine ⟨x, Set.mem_univ x, ?_⟩
        apply Subtype.ext
        apply Prod.ext
        · exact hqt.symm
        · rfl
    rw [← himage]
    let _ : ConnectedSpace E :=
      Subtype.connectedSpace (isConnected_exposedEdge K.val ((t : ℝ) : Real.Angle))
    exact isConnected_univ.image e hecont.continuousOn
  have hGconn : IsConnected (Set.univ : Set G) := by
    exact hπquot.isCoinducing.isConnected_preimage_of_isClosed hfiber isClosed_univ
      isConnected_univ
  have himage : (fun q : G ↦ q.1.2) '' Set.univ = capUpperBoundary K := by
    ext x
    simp only [Set.mem_image, Set.mem_univ, true_and, capUpperBoundary, Set.mem_iUnion]
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q.1.1, q.1.1.property, q.property⟩
    · rintro ⟨t, ht, hx⟩
      exact ⟨⟨(⟨t, ht⟩, x), hx⟩, rfl⟩
  rw [← himage]
  exact hGconn.image _ (continuous_snd.comp continuous_subtype_val).continuousOn

private theorem CapSpace.mem_interior_of_mem_not_upperBoundary {ω : ℝ}
    (K : CapSpace ω) {p : Point} (hpK : p ∈ (K.val : Set Point))
    (hpδ : p ∉ ⋃ t ∈ Set.Icc 0 (ω + Real.pi / 2),
      exposedEdge K.val (t : Real.Angle)) :
    (⟨p, K.subset_capFan hpK⟩ : capFan ω) ∈
      interior {q : capFan ω | (q : Point) ∈ (K.val : Set Point)} := by
  let I := Set.Icc 0 (ω + Real.pi / 2)
  let gap : ℝ → ℝ := fun t ↦
    supportValue K.val (t : Real.Angle) - inner ℝ p (normalVector (t : Real.Angle))
  have hgap_cont : Continuous gap := (continuous_supportValue_real K.val).sub
    (continuous_const.inner continuous_normalVector_real)
  have hgap_pos : ∀ t ∈ I, 0 < gap t := by
    intro t ht
    have hle := inner_le_supportValue K.val hpK (t : Real.Angle)
    have hne : inner ℝ p (normalVector (t : Real.Angle)) ≠
        supportValue K.val (t : Real.Angle) := by
      intro heq
      apply hpδ
      exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨ht,
        ⟨hpK, by simpa [supportingLineHalfPlane, normalLine]⟩⟩⟩
    dsimp [gap]
    exact sub_pos.mpr (lt_of_le_of_ne hle hne)
  have hIne : I.Nonempty := ⟨0, by
    change 0 ∈ Set.Icc 0 (ω + Real.pi / 2)
    exact ⟨le_rfl, by linarith [K.property.1, Real.pi_pos]⟩⟩
  have hIcompact : IsCompact I := by
    dsimp [I]
    exact isCompact_Icc
  obtain ⟨m, hm, hmle⟩ := IsCompact.exists_pos_forall_le hIcompact hIne
    hgap_cont.continuousOn hgap_pos
  apply mem_interior_iff_mem_nhds.mpr
  refine Filter.mem_of_superset (Metric.ball_mem_nhds _ (half_pos hm)) ?_
  intro q hq
  change (q : Point) ∈ (K.val : Set Point)
  apply K.mem_of_mem_capFan_of_lt_supportValue q.property
  intro t ht
  have hdist : ‖(q : Point) - p‖ < m / 2 := by
    change dist (q : Point) p < m / 2 at hq
    simpa [dist_eq_norm] using hq
  have hnorm := norm_normalVector_real t
  have hinner : inner ℝ ((q : Point) - p) (normalVector (t : Real.Angle)) < m / 2 := by
    calc
      inner ℝ ((q : Point) - p) (normalVector (t : Real.Angle))
          ≤ ‖(q : Point) - p‖ * ‖normalVector (t : Real.Angle)‖ := real_inner_le_norm _ _
      _ < m / 2 := by simpa [hnorm] using hdist
  have := hmle t ht
  dsimp [gap] at this
  rw [inner_sub_left] at hinner
  linarith

private theorem CapSpace.mem_frontier_of_mem_upperBoundary {ω : ℝ}
    (K : CapSpace ω) {p : Point}
    (hp : p ∈ ⋃ t ∈ Set.Icc 0 (ω + Real.pi / 2), exposedEdge K.val (t : Real.Angle)) :
    ∃ z : capFan ω, (z : Point) = p ∧
      z ∈ frontier {q : capFan ω | (q : Point) ∈ (K.val : Set Point)} := by
  obtain ⟨t, hp⟩ := Set.mem_iUnion.mp hp
  obtain ⟨htI, hpedge⟩ := Set.mem_iUnion.mp hp
  let z : capFan ω := ⟨p, K.subset_capFan hpedge.1⟩
  have hzK : z ∈ {q : capFan ω | (q : Point) ∈ (K.val : Set Point)} := hpedge.1
  refine ⟨z, rfl, (mem_frontier_iff_notMem_interior hzK).2 ?_⟩
  intro hzint
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hzint
  let e := ε / 2
  have he : 0 < e := half_pos hε
  let q : Point := p + e • normalVector (t : Real.Angle)
  have hsin : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi htI.1
    (htI.2.trans (by linarith [K.property.2.1, Real.pi_pos]))
  have hcos : 0 ≤ Real.cos (t - ω) := Real.cos_nonneg_of_mem_Icc ⟨by
    linarith [htI.1, K.property.2.1, Real.pi_pos], by linarith [htI.2]⟩
  have hqfan : q ∈ capFan ω := by
    constructor
    · change 0 ≤ inner ℝ q (normalVector (ω : Real.Angle))
      dsimp [q]
      rw [inner_add_left, inner_smul_left, inner_normalVector_normalVector]
      have hpω := (K.subset_capFan hpedge.1).1
      change 0 ≤ inner ℝ p (normalVector (ω : Real.Angle)) at hpω
      simp at *
      nlinarith
    · change 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
      dsimp [q]
      rw [inner_add_left, inner_smul_left, inner_normalVector_normalVector]
      have hpT := (K.subset_capFan hpedge.1).2
      change 0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hpT
      rw [Real.cos_sub]
      simp
      nlinarith
  have hqball : (⟨q, hqfan⟩ : capFan ω) ∈ Metric.ball z ε := by
    change dist q p < ε
    simp only [q, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_normalVector_real,
      mul_one]
    rw [Real.norm_eq_abs, abs_of_pos he]
    dsimp [e]
    linarith
  have hqK := interior_subset (hball hqball)
  change q ∈ (K.val : Set Point) at hqK
  have hqle := inner_le_supportValue K.val hqK (t : Real.Angle)
  have hpedge_eq := hpedge.2
  change inner ℝ p (normalVector (t : Real.Angle)) = supportValue K.val (t : Real.Angle)
    at hpedge_eq
  dsimp [q] at hqle
  rw [inner_add_left, inner_smul_left, inner_normalVector_self, hpedge_eq] at hqle
  simp at hqle
  nlinarith

theorem capUpperBoundary_relativeBoundary {ω : ℝ} (K : CapSpace ω) :
    capUpperBoundary K =
      Subtype.val '' frontier {p : capFan ω | (p : Point) ∈ (K.val : Set Point)} := by
  ext p
  constructor
  · intro hp
    obtain ⟨z, rfl, hz⟩ := K.mem_frontier_of_mem_upperBoundary hp
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hzfront, rfl⟩
    let S : Set (capFan ω) := {p | (p : Point) ∈ (K.val : Set Point)}
    have hSclosed : IsClosed S := K.val.isClosed.preimage continuous_subtype_val
    have hzS : z ∈ S := by
      apply hSclosed.closure_subset
      exact frontier_subset_closure hzfront
    by_contra hzupper
    have hzint := K.mem_interior_of_mem_not_upperBoundary hzS hzupper
    exact ((mem_frontier_iff_notMem_interior hzS).1 hzfront) hzint

end MovingSofa

end

end

end
