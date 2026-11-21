/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsCompactApproximation
public import LeanPool.CutoffRigidity.GibbsResolventBounds
public import LeanPool.CutoffRigidity.EuclideanMollifiedCompactness
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Compactness of the genuine weighted Gibbs Sobolev inclusion

Uniform convexity gives spatial confinement. Actual compact cutoffs have
uniform local translation bounds; actual mollification gives quantitative
approximation and compact smoothing families. These proved ingredients are
assembled into compactness of the actual H¹ inclusion and its resolvent.
No compact-embedding or discrete-spectrum hypothesis is introduced.
-/

public section

namespace CutoffRigidity

open MeasureTheory Set

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem isCompact_closure_gibbsSobolevInclusion_unitBall {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    IsCompact (closure ((gibbsSobolevInclusion hV hprob) ''
      Metric.closedBall (0 : gibbsSobolevGraph hV hprob) 1)) := by
  let J := gibbsSobolevInclusion hV hprob
  let W := volumeToGibbsL2 hV ρ hρ hHess
  let U := {u : gibbsSobolevGraph hV hprob // ‖u‖ ≤ 1}
  apply isCompact_closure_of_uniform_precompact_approximation
  intro ε hε
  let Ctail := Real.sqrt (gibbsFormConfinementConstant V ρ)
  have hCtail : 0 ≤ Ctail := Real.sqrt_nonneg _
  let R := 4 * Ctail / ε + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have htail : Ctail / R < ε / 4 := by
    apply (div_lt_iff₀ hR).mpr
    dsimp only [R]
    field_simp
    nlinarith
  let χ : E → ℝ := gibbsSpatialCutoff R hR
  have hχ : ContDiff ℝ 2 χ := gibbsSpatialCutoff_contDiff R hR
  have hχc : HasCompactSupport χ := gibbsSpatialCutoff_hasCompactSupport R hR
  obtain ⟨C, hC, htranslation⟩ := exists_gibbsSobolev_cutoff_translation_integral_bound hV hprob hχ
    hχc
  obtain ⟨A, hA, hAbound⟩ :=
    exists_compact_cutoff_gibbsLp_L2_norm_bound hV.continuous hprob hχ.continuous hχc
  let f : U → E → ℝ := fun u x => χ x * J u x
  have hfm (u : U) : Measurable (f u) :=
    hχ.continuous.measurable.mul (Lp.stronglyMeasurable (J u)).measurable
  have hf (u : U) : MemLp (f u) 2 volume :=
    compact_cutoff_gibbsLp_memLp_volume hV.continuous hprob hχ.continuous hχc (J u)
  have hbound (u : U) : ‖(hf u).toLp (f u)‖ ≤ A := by
    have hi := norm_gibbsSobolevInclusion_apply_le hV hprob (u : gibbsSobolevGraph hV hprob)
    have hu : ‖J u‖ ≤ 1 := hi.trans u.property
    exact (hAbound (J u)).trans (by nlinarith)
  have htrans (u : U) (h : E) :
      (∫ x, (f u (x + h) - f u x) ^ 2) ≤ (Real.sqrt C) ^ 2 * ‖h‖ ^ 2 := by
    have ht := htranslation (u : gibbsSobolevGraph hV hprob) h
    have hu : ‖(u : gibbsSobolevGraph hV hprob)‖ ^ 2 ≤ 1 := by
      nlinarith [norm_nonneg (u : gibbsSobolevGraph hV hprob), u.property]
    rw [Real.sq_sqrt hC.le]
    exact ht.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hu (mul_nonneg hC.le (sq_nonneg ‖h‖)))
  let P := ‖W‖ * Real.sqrt C
  have hP : 0 ≤ P := mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  let η := ε / (4 * (P + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  let φ : ContDiffBump (0 : E) := euclideanMollifierBump η hη
  have hηP : ‖W‖ * (η * Real.sqrt C) ≤ ε / 4 := by
    have he : η * (P + 1) = ε / 4 := by dsimp only [η]; field_simp
    calc
      ‖W‖ * (η * Real.sqrt C) = P * η := by dsimp only [P]; ring
      _ ≤ η * (P + 1) := by nlinarith [hη.le]
      _ = ε / 4 := he
  have hsupp (u : U) (x : E) (hx : x ∉ tsupport χ) : f u x = 0 := by
    dsimp only [f]
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  let m (u : U) : E →₂[volume] ℝ :=
    (bumpMollification_memLp_of_commonSupport φ (hf u) hχc (hsupp u)).toLp (bumpMollification φ (f
      u))
  have hcompact : IsCompact (closure (Set.range m)) :=
    isCompact_closure_bumpMollification_L2_family φ f hf hχc hsupp A hA.le hbound
  let T := W '' closure (Set.range m)
  have hT : IsCompact T := hcompact.image W.continuous
  refine ⟨T, hT.totallyBounded, ?_⟩
  rintro x ⟨u, hu, rfl⟩
  have hun : ‖u‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hu
  let u' : U := ⟨u, hun⟩
  refine ⟨W (m u'), ⟨m u', subset_closure ⟨u', rfl⟩, rfl⟩, ?_⟩
  have hcut := gibbsSobolev_spatial_cutoff_transferred_error_L2_norm_le hV hprob ρ hρ hHess R hR u
  have hcut' : dist (J u) (W ((hf u').toLp (f u'))) < ε / 4 := by
    rw [dist_eq_norm]
    change ‖J u - W ((hf u').toLp (f u'))‖ ≤ Ctail / R * ‖u‖ at hcut
    have hb : Ctail / R * ‖u‖ ≤ Ctail / R := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hun (div_nonneg hCtail hR.le)
    exact (hcut.trans hb).trans_lt htail
  have hmoll : ‖m u' - (hf u').toLp (f u')‖ ≤ η * Real.sqrt C :=
    bumpMollification_L2_dist_le_of_translation_bound φ (hfm u') (hf u')
      (Real.sqrt C) (Real.sqrt_nonneg _) (htrans u')
  have hnear : dist (W ((hf u').toLp (f u'))) (W (m u')) ≤ ε / 4 := by
    calc
      _ ≤ ‖W‖ * dist ((hf u').toLp (f u')) (m u') := W.lipschitzWith.dist_le_mul _ _
      _ ≤ ‖W‖ * (η * Real.sqrt C) := by
        gcongr
        rw [dist_eq_norm]
        change ‖(hf u').toLp (f u') - m u'‖ ≤ η * Real.sqrt C
        rw [norm_sub_rev]
        exact hmoll
      _ ≤ ε / 4 := hηP
  exact lt_of_le_of_lt (dist_triangle (J u) _ _) (by linarith)

/-- The actual closed Gibbs H¹ inclusion is a compact operator. -/
theorem gibbsSobolevInclusion_isCompactOperator {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    IsCompactOperator (gibbsSobolevInclusion hV hprob) := by
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall
    (gibbsSobolevInclusion hV hprob).toLinearMap (by norm_num : (0 : ℝ) < 1)).mpr
  exact isCompact_closure_gibbsSobolevInclusion_unitBall hV hprob ρ hρ hHess

/-- The actual self-adjoint form operator has compact variational resolvent. -/
theorem gibbsL2Resolvent_isCompactOperator {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    IsCompactOperator (gibbsL2Resolvent hV hprob) := by
  exact (gibbsSobolevInclusion_isCompactOperator hV hprob ρ hρ hHess).comp_clm
    (gibbsWeakResolvent hV hprob)

end CutoffRigidity
