/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Cap.Foundations.Development006
public import LeanPool.MovingSofa.Geometry.Foundations.Development005
public import LeanPool.MovingSofa.Geometry.Foundations.Development003
/-!
# Moving sofa: related mathematical developments

* `Bounds.Arm.Geometry`.
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
# Bounds / Arm / Geometry
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace MovingSofa

private theorem mirrorReflection_rightAngle_apply (p : Point) :
    mirrorReflection (Real.pi / 2) p = !₂[-p 0, p 1] := by
  have harg : Real.pi / 4 - (Real.pi / 2) / 2 = 0 := by ring
  have hnorm : ‖(!₂[0, 1] : Point)‖ ^ 2 = 1 := by
    simpa [Fin.sum_univ_two] using EuclideanSpace.norm_sq_eq (!₂[0, 1] : Point)
  ext i
  fin_cases i <;>
    simp [mirrorReflection, stripParallelogram, harg, PiLp.inner_apply,
      Fin.sum_univ_two, hnorm]
  ring

private theorem inner_mirror_sub_tangent (p q : Point) (t : ℝ) :
    inner ℝ (mirrorReflection (Real.pi / 2) p - mirrorReflection (Real.pi / 2) q)
      (tangentVector (t : Real.Angle)) =
    inner ℝ (p - q) (normalVector ((Real.pi / 2 - t : ℝ) : Real.Angle)) := by
  rw [mirrorReflection_rightAngle_apply, mirrorReflection_rightAngle_apply]
  simp [tangentVector, normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
    Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, -Real.Angle.coe_sub]
  ring

private theorem inner_mirror_sub_normal (p q : Point) (t : ℝ) :
    inner ℝ (mirrorReflection (Real.pi / 2) p - mirrorReflection (Real.pi / 2) q)
      (normalVector (t : Real.Angle)) =
    inner ℝ (p - q) (tangentVector ((Real.pi / 2 - t : ℝ) : Real.Angle)) := by
  rw [mirrorReflection_rightAngle_apply, mirrorReflection_rightAngle_apply]
  simp [tangentVector, normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
    Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, -Real.Angle.coe_sub]
  ring

theorem tangentArms_mirror (K P : RightAngleCapSpace)
    (hP : (P.val : Set Point) = mirrorReflection (Real.pi / 2) '' (K.val : Set Point))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    (tangentArmLengths P t).1.1 = (tangentArmLengths K (Real.pi / 2 - t)).2.2 ∧
    (tangentArmLengths P t).1.2 = (tangentArmLengths K (Real.pi / 2 - t)).2.1 ∧
    (tangentArmLengths P t).2.1 = (tangentArmLengths K (Real.pi / 2 - t)).1.2 ∧
    (tangentArmLengths P t).2.2 = (tangentArmLengths K (Real.pi / 2 - t)).1.1 := by
  obtain ⟨Q, hQ, hfeatures, _⟩ := cap_mirror_features K
  have hPQ : P = Q := by
    apply Subtype.ext
    apply ConvexBody.ext
    exact hP.trans hQ.symm
  subst P
  obtain ⟨_, _, hy, _, _, _, _, _, _, _, _, hA₁, hA₂, hC₁, hC₂⟩ := hfeatures t ht
  dsimp only [tangentArmLengths]
  rw [hy, hA₁, hA₂, hC₁, hC₂]
  exact ⟨inner_mirror_sub_tangent _ _ _, inner_mirror_sub_tangent _ _ _,
    inner_mirror_sub_normal _ _ _, inner_mirror_sub_normal _ _ _⟩

private theorem tendsto_tan_sub_div (t : ℝ) :
    Tendsto (fun s : ℝ ↦ Real.tan (s - t) / (s - t)) (𝓝[≠] t) (𝓝 1) := by
  have hd : HasDerivAt (fun s : ℝ ↦ Real.tan (s - t)) 1 t := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_tan (x := t - t) (by simp)).comp (h := fun s : ℝ ↦ s - t) t
        ((hasDerivAt_id t).sub_const t)
  convert hd.tendsto_slope using 1
  funext s
  simp [slope_def_field]

private theorem tendsto_normal_slope {F : Filter ℝ} {t : ℝ}
    (hF : F ≤ 𝓝[≠] t) (a : ℝ) (y q : ℝ → Point) (p : Point)
    (hy : Tendsto y F (𝓝 (y t))) (hq : Tendsto q F (𝓝 p))
    (hfixed : ∀ᶠ s in F, inner ℝ (q s) (normalVector ((t + a : ℝ) : Real.Angle)) =
      inner ℝ (y t) (normalVector ((t + a : ℝ) : Real.Angle)))
    (hmoving : ∀ᶠ s in F, inner ℝ (q s) (normalVector ((s + a : ℝ) : Real.Angle)) =
      inner ℝ (y s) (normalVector ((s + a : ℝ) : Real.Angle))) :
    Tendsto (fun s : ℝ ↦ inner ℝ ((s - t)⁻¹ • (y s - y t))
      (normalVector ((t + a : ℝ) : Real.Angle))) F
      (𝓝 (inner ℝ (p - y t) (tangentVector ((t + a : ℝ) : Real.Angle)))) := by
  have htan := (tendsto_tan_sub_div t).mono_left hF
  have hpair := htan.mul ((hq.sub hy).inner (𝕜 := ℝ)
    (tendsto_const_nhds (x := tangentVector ((t + a : ℝ) : Real.Angle))))
  simp only [one_mul] at hpair
  apply hpair.congr'
  have hnear : ∀ᶠ s in F, s - t ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    have hc : Tendsto (fun s : ℝ ↦ s - t) F (𝓝 0) := by
      simpa using (tendsto_id.mono_right (hF.trans nhdsWithin_le_nhds)).sub_const t
    exact hc.eventually (Ioo_mem_nhds (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
  filter_upwards [hfixed, hmoving, hnear] with s hf hm hs
  have hn : normalVector ((s + a : ℝ) : Real.Angle) =
      Real.cos (s - t) • normalVector ((t + a : ℝ) : Real.Angle) +
      Real.sin (s - t) • tangentVector ((t + a : ℝ) : Real.Angle) := by
    convert normalVector_add_real (t + a) (s - t) using 1
    congr 2
    ring
  rw [hn] at hm
  simp only [inner_add_right, inner_smul_right] at hm
  rw [hf] at hm
  have hc : Real.cos (s - t) ≠ 0 := (Real.cos_pos_of_mem_Ioo hs).ne'
  simp only [real_inner_smul_left, inner_sub_left, Real.tan_eq_sin_div_cos]
  have heq : Real.sin (s - t) *
      (inner ℝ (q s) (tangentVector ((t + a : ℝ) : Real.Angle)) -
        inner ℝ (y s) (tangentVector ((t + a : ℝ) : Real.Angle))) =
      Real.cos (s - t) * (inner ℝ (y s) (normalVector ((t + a : ℝ) : Real.Angle)) -
        inner ℝ (y t) (normalVector ((t + a : ℝ) : Real.Angle))) := by linarith
  field_simp
  rw [heq]

private theorem outerCorner_inner_normal (K : ConvexBody Point) (t : ℝ) :
    inner ℝ (rotatingHallwayParts (K : Set Point) (t : Real.Angle)).outerCorner
      (normalVector (t : Real.Angle)) = supportValue K (t : Real.Angle) := by
  change inner ℝ (supportingPlacement (K : Set Point) (t : Real.Angle) (!₂[1, 1] : Point))
    (normalVector (t : Real.Angle)) = _
  rw [inner_supportingPlacement_normalVector]
  simp

private theorem outerCorner_inner_tangent (K : ConvexBody Point) (t : ℝ) :
    inner ℝ (rotatingHallwayParts (K : Set Point) (t : Real.Angle)).outerCorner
      (tangentVector (t : Real.Angle)) = supportValue K ((t + Real.pi / 2 : ℝ) : Real.Angle) := by
  change inner ℝ (supportingPlacement (K : Set Point) (t : Real.Angle) (!₂[1, 1] : Point))
    (tangentVector (t : Real.Angle)) = _
  rw [inner_supportingPlacement_tangentVector]
  simp

private theorem eventually_sin_sub_ne_zero {F : Filter ℝ} {t : ℝ}
    (hF : F ≤ 𝓝[≠] t) : ∀ᶠ s in F, Real.sin (s - t) ≠ 0 := by
  have hn : Tendsto (fun s : ℝ ↦ s - t) F (𝓝 0) := by
    simpa using (tendsto_id.mono_right (hF.trans nhdsWithin_le_nhds)).sub_const t
  have hnear := hn.eventually (Ioo_mem_nhds (neg_neg_of_pos Real.pi_pos) Real.pi_pos)
  have hne : ∀ᶠ s in F, s ≠ t := hF self_mem_nhdsWithin
  filter_upwards [hnear, hne] with s hs hst
  exact mt (Real.sin_eq_zero_iff_of_lt_of_lt hs.1 hs.2).mp (sub_ne_zero.mpr hst)

private theorem tendsto_outerCorner_slope {F : Filter ℝ} {t : ℝ}
    (K : ConvexBody Point) (hF : F ≤ 𝓝[≠] t) (p q : Point)
    (hp : Tendsto (fun s : ℝ ↦ supportingIntersection K (t : Real.Angle) (s : Real.Angle))
      F (𝓝 p))
    (hq : Tendsto (fun s : ℝ ↦ supportingIntersection K
      ((t + Real.pi / 2 : ℝ) : Real.Angle) ((s + Real.pi / 2 : ℝ) : Real.Angle)) F (𝓝 q)) :
    Tendsto (fun s : ℝ ↦ (s - t)⁻¹ •
      ((rotatingHallwayParts (K : Set Point) (s : Real.Angle)).outerCorner -
        (rotatingHallwayParts (K : Set Point) (t : Real.Angle)).outerCorner)) F
      (𝓝 (inner ℝ (p - (rotatingHallwayParts (K : Set Point) (t : Real.Angle)).outerCorner)
          (tangentVector (t : Real.Angle)) • normalVector (t : Real.Angle) +
        inner ℝ (q - (rotatingHallwayParts (K : Set Point) (t : Real.Angle)).outerCorner)
          (-normalVector (t : Real.Angle)) • tangentVector (t : Real.Angle))) := by
  let y (s : ℝ) := (rotatingHallwayParts (K : Set Point) (s : Real.Angle)).outerCorner
  have hy : Tendsto y F (𝓝 (y t)) :=
    (continuous_outerCorner K).continuousAt.tendsto.mono_left (hF.trans nhdsWithin_le_nhds)
  have hA := tendsto_normal_slope hF 0 y
    (fun s ↦ supportingIntersection K (t : Real.Angle) (s : Real.Angle)) p hy hp
    (Eventually.of_forall fun s ↦ by
      simp only [add_zero, supportingIntersection_inner_left, y, outerCorner_inner_normal])
    (by
      filter_upwards [eventually_sin_sub_ne_zero hF] with s hs
      simp only [add_zero, y, outerCorner_inner_normal]
      exact supportingIntersection_inner_right K t s hs)
  simp only [add_zero] at hA
  have hC := tendsto_normal_slope hF (Real.pi / 2) y
    (fun s ↦ supportingIntersection K ((t + Real.pi / 2 : ℝ) : Real.Angle)
      ((s + Real.pi / 2 : ℝ) : Real.Angle)) q hy hq
    (Eventually.of_forall fun s ↦ by
      rw [supportingIntersection_inner_left]
      simp only [Real.Angle.coe_add, normalVector_add_pi_div_two, y, outerCorner_inner_tangent])
    (by
      filter_upwards [eventually_sin_sub_ne_zero hF] with s hs
      rw [supportingIntersection_inner_right K (t + Real.pi / 2) (s + Real.pi / 2)
        (by simpa only [add_sub_add_right_eq_sub] using hs)]
      simp only [Real.Angle.coe_add, normalVector_add_pi_div_two, y, outerCorner_inner_tangent])
  simp only [Real.Angle.coe_add, normalVector_add_pi_div_two] at hC
  have hCt : tangentVector ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle)) =
      -normalVector (t : Real.Angle) := tangentVector_add_pi_div_two t
  rw [hCt] at hC
  have hsum := (hA.smul (tendsto_const_nhds (x := normalVector (t : Real.Angle)))).add
    (hC.smul (tendsto_const_nhds (x := tangentVector (t : Real.Angle))))
  simpa only [inner_normalVector_smul_add_inner_tangentVector_smul] using hsum

private theorem hasDerivWithinAt_outerCorner_right (K : RightAngleCapSpace) (t : ℝ) :
    HasDerivWithinAt
      (fun s : ℝ ↦ (rotatingHallwayParts (K.val : Set Point) (s : Real.Angle)).outerCorner)
      (-(tangentArmLengths K t).1.1 • normalVector (t : Real.Angle) +
        (tangentArmLengths K t).2.1 • tangentVector (t : Real.Angle)) (Set.Ici t) t := by
  have hshift : Tendsto (fun s : ℝ ↦ s + Real.pi / 2) (𝓝[>] t) (𝓝[>] (t + Real.pi / 2)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨((continuous_id.add_const _).continuousAt.tendsto.mono_left nhdsWithin_le_nhds), ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    change t + Real.pi / 2 < s + Real.pi / 2
    linarith [show t < s from hs]
  have h := tendsto_outerCorner_slope K.val (nhdsGT_le_nhdsNE t)
    (edgeVertices K.val (t : Real.Angle)).1
    (edgeVertices K.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).1
    (contact_oneSided_limits K.val t).2.2.1
    (((contact_oneSided_limits K.val (t + Real.pi / 2)).2.2.1).comp hshift)
  rw [hasDerivWithinAt_iff_tendsto_slope, Set.Ici_sdiff_left]
  have heq :
      inner ℝ ((edgeVertices K.val (t : Real.Angle)).1 -
        (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).outerCorner)
          (tangentVector (t : Real.Angle)) • normalVector (t : Real.Angle) +
        inner ℝ ((edgeVertices K.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).1 -
          (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).outerCorner)
          (-normalVector (t : Real.Angle)) • tangentVector (t : Real.Angle) =
      -(tangentArmLengths K t).1.1 • normalVector (t : Real.Angle) +
        (tangentArmLengths K t).2.1 • tangentVector (t : Real.Angle) := by
    simp only [tangentArmLengths, capVertices, inner_sub_left, inner_neg_right]
    module
  rw [heq] at h
  convert h using 1
  funext s
  exact slope_def_module _ _ _

private theorem tendsto_supportingIntersection_left_ordered (K : ConvexBody Point) (t : ℝ) :
    Tendsto (fun s : ℝ ↦ supportingIntersection K (t : Real.Angle) (s : Real.Angle))
      (𝓝[<] t) (𝓝 (edgeVertices K (t : Real.Angle)).2) := by
  apply (contact_oneSided_limits K t).2.2.2.2.2.congr'
  filter_upwards [eventually_sin_sub_ne_zero (nhdsLT_le_nhdsNE t)] with s hs
  exact (supportingIntersection_comm K t s hs).symm

private theorem hasDerivWithinAt_outerCorner_left (K : RightAngleCapSpace) (t : ℝ) :
    HasDerivWithinAt
      (fun s : ℝ ↦ (rotatingHallwayParts (K.val : Set Point) (s : Real.Angle)).outerCorner)
      (-(tangentArmLengths K t).1.2 • normalVector (t : Real.Angle) +
        (tangentArmLengths K t).2.2 • tangentVector (t : Real.Angle)) (Set.Iic t) t := by
  have hshift : Tendsto (fun s : ℝ ↦ s + Real.pi / 2) (𝓝[<] t) (𝓝[<] (t + Real.pi / 2)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨((continuous_id.add_const _).continuousAt.tendsto.mono_left nhdsWithin_le_nhds), ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    change s + Real.pi / 2 < t + Real.pi / 2
    linarith [show s < t from hs]
  have h := tendsto_outerCorner_slope K.val (nhdsLT_le_nhdsNE t)
    (edgeVertices K.val (t : Real.Angle)).2
    (edgeVertices K.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).2
    (tendsto_supportingIntersection_left_ordered K.val t)
    ((tendsto_supportingIntersection_left_ordered K.val (t + Real.pi / 2)).comp hshift)
  rw [hasDerivWithinAt_iff_tendsto_slope, Set.Iic_sdiff_right]
  have heq :
      inner ℝ ((edgeVertices K.val (t : Real.Angle)).2 -
        (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).outerCorner)
          (tangentVector (t : Real.Angle)) • normalVector (t : Real.Angle) +
        inner ℝ ((edgeVertices K.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).2 -
          (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).outerCorner)
          (-normalVector (t : Real.Angle)) • tangentVector (t : Real.Angle) =
      -(tangentArmLengths K t).1.2 • normalVector (t : Real.Angle) +
        (tangentArmLengths K t).2.2 • tangentVector (t : Real.Angle) := by
    simp only [tangentArmLengths, capVertices, inner_sub_left, inner_neg_right]
    module
  rw [heq] at h
  convert h using 1
  funext s
  exact slope_def_module _ _ _

theorem capCorners_oneSided_derivatives (K : RightAngleCapSpace) :
    (∀ t ∈ Set.Ico (0 : ℝ) (Real.pi / 2),
      HasDerivWithinAt
        (fun s : ℝ ↦ (rotatingHallwayParts (K.val : Set Point) (s : Real.Angle)).outerCorner)
        (-(tangentArmLengths K t).1.1 • normalVector (t : Real.Angle) +
          (tangentArmLengths K t).2.1 • tangentVector (t : Real.Angle)) (Set.Ici t) t ∧
      HasDerivWithinAt
        (fun s : ℝ ↦ (rotatingHallwayParts (K.val : Set Point) (s : Real.Angle)).innerCorner)
        (-((tangentArmLengths K t).1.1 - 1) • normalVector (t : Real.Angle) +
          ((tangentArmLengths K t).2.1 - 1) • tangentVector (t : Real.Angle)) (Set.Ici t) t) ∧
    (∀ t ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      HasDerivWithinAt
        (fun s : ℝ ↦ (rotatingHallwayParts (K.val : Set Point) (s : Real.Angle)).outerCorner)
        (-(tangentArmLengths K t).1.2 • normalVector (t : Real.Angle) +
          (tangentArmLengths K t).2.2 • tangentVector (t : Real.Angle)) (Set.Iic t) t ∧
      HasDerivWithinAt
        (fun s : ℝ ↦ (rotatingHallwayParts (K.val : Set Point) (s : Real.Angle)).innerCorner)
        (-((tangentArmLengths K t).1.2 - 1) • normalVector (t : Real.Angle) +
          ((tangentArmLengths K t).2.2 - 1) • tangentVector (t : Real.Angle)) (Set.Iic t) t) := by
  constructor
  · intro t _
    have hout := hasDerivWithinAt_outerCorner_right K t
    refine ⟨hout, ?_⟩
    convert hout.sub ((hasDerivAt_normalVector t).hasDerivWithinAt.add
      (hasDerivAt_tangentVector t).hasDerivWithinAt) using 1
    · funext s
      exact eq_sub_of_add_eq (outerCorner_eq_innerCorner_add K.val s).symm
    · module
  · intro t _
    have hout := hasDerivWithinAt_outerCorner_left K t
    refine ⟨hout, ?_⟩
    convert hout.sub ((hasDerivAt_normalVector t).hasDerivWithinAt.add
      (hasDerivAt_tangentVector t).hasDerivWithinAt) using 1
    · funext s
      exact eq_sub_of_add_eq (outerCorner_eq_innerCorner_add K.val s).symm
    · module

end MovingSofa

end

end

end
