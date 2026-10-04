/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Embedding.H01Sobolev


/-!
# Sobolev embedding of `H₀¹(Ω)` in dimension two

In dimension two the critical exponent of `H¹` is infinite and the Gagliardo-Nirenberg-Sobolev
inequality at `p = 2` is unavailable, since it asks `p < d`. On a bounded domain the embedding
into `L⁴` still follows from the inequality at `p = 3/2 < 2`, whose conjugate exponent is `6`,
together with Hölder's inequality `‖∇u‖_{L^{3/2}(Ω)} ≤ |Ω|^{1/6} ‖∇u‖_{L²(Ω)}`. This is the
remark on `n = 2` in the proof of Gilbarg and Trudinger's Theorem 8.1, where any exponent above
`2` serves.

## Main declarations

* `EllipticPdes.Embedding.sobolevConstTwo`: the constant.
* `EllipticPdes.Embedding.eLpNorm_testGraph_le_two`: the estimate on a test function.
* `EllipticPdes.Embedding.eLpNorm_le_of_mem_H01_two`: the estimate on `H₀¹(Ω)`.

## References

D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
§8.1 Theorem 8.1 (p. 180), the remark on `n = 2`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace EllipticPdes.Embedding

open EllipticPdes.Sobolev

variable {Ω : Set (EuclideanSpace ℝ (Fin 2))}

/-- The constant of the two-dimensional embedding into `L⁴`: Mathlib's constant at `p = 3/2`,
`q = 4`, times the Hölder factor `|Ω|^{1/6}`. -/
noncomputable def sobolevConstTwo (Ω : Set (EuclideanSpace ℝ (Fin 2))) : ℝ≥0 :=
  eLpNormLESNormFDerivOfLeConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω (3 / 2) 4
    * (volume Ω).toNNReal ^ (1 / 6 : ℝ)

/-- A function supported in `Ω` has the same `Lᵖ` seminorm over `Ω` as over the whole space,
for functions into any normed group. -/
lemma eLpNorm_restrict_eq_of_tsupport_subset' {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩm : MeasurableSet Ω) {F : Type*} [NormedAddCommGroup F]
    {f : EuclideanSpace ℝ (Fin d) → F} (hf : tsupport f ⊆ Ω) (p : ℝ≥0∞) :
    eLpNorm f p (volume.restrict Ω) = eLpNorm f p volume := by
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict hΩm]
  refine eLpNorm_congr_ae (EventuallyEq.of_eq (funext fun x => ?_))
  by_cases hx : x ∈ Ω
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport (fun hc => hx (hf hc))]

/-- **Two-dimensional Sobolev inequality on a test function**: the `L⁴(Ω)` seminorm of the
function coordinate is bounded by the sum of the `L²(Ω)` norms of the gradient coordinates. -/
theorem eLpNorm_testGraph_le_two (hΩm : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω)
    {φ : EuclideanSpace ℝ (Fin 2) → ℝ} (h : IsTestFn Ω φ) :
    eLpNorm (h.testGraph 0 : L2D Ω) 4 (volume.restrict Ω)
      ≤ sobolevConstTwo Ω * ∑ i : Fin 2, ‖h.testGraph i.succ‖ₑ := by
  have hrank : ((3 / 2 : ℝ≥0)) < (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) : ℝ≥0) := by
    rw [finrank_euclideanSpace_fin]
    norm_num
  have hpq : ((3 / 2 : ℝ≥0) : ℝ)⁻¹ - (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) : ℝ)⁻¹
      ≤ ((4 : ℝ≥0) : ℝ)⁻¹ := by
    rw [finrank_euclideanSpace_fin]
    norm_num
  have hΩfin : volume Ω ≠ ⊤ := hΩb.measure_lt_top.ne
  -- Hölder on the bounded domain, from `L²` to `L^{3/2}`
  have hfd : tsupport (fderiv ℝ φ) ⊆ Ω := (tsupport_fderiv_subset ℝ).trans h.2.2
  have hmeas : AEStronglyMeasurable (fderiv ℝ φ) (volume.restrict Ω) :=
    (h.1.continuous_fderiv (by simp)).aestronglyMeasurable
  have hexp : 1 / ((3 / 2 : ℝ≥0) : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal = (1 / 6 : ℝ) := by
    rw [ENNReal.coe_toReal, ENNReal.toReal_ofNat]
    push_cast
    norm_num
  have hle : ((3 / 2 : ℝ≥0) : ℝ≥0∞) ≤ 2 := by
    have h2 : (2 : ℝ≥0∞) = ((2 : ℝ≥0) : ℝ≥0∞) := (ENNReal.coe_ofNat 2).symm
    rw [h2]
    exact ENNReal.coe_le_coe.mpr (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have hholder : eLpNorm (fderiv ℝ φ) ((3 / 2 : ℝ≥0) : ℝ≥0∞) volume
      ≤ eLpNorm (fderiv ℝ φ) 2 volume * (volume Ω) ^ (1 / 6 : ℝ) := by
    rw [← eLpNorm_restrict_eq_of_tsupport_subset' hΩm hfd, ← eLpNorm_restrict_eq_of_tsupport_subset'
      hΩm hfd 2]
    have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict Ω) hle hmeas
    rwa [Measure.restrict_apply_univ, hexp] at this
  calc eLpNorm (h.testGraph 0 : L2D Ω) 4 (volume.restrict Ω)
      = eLpNorm φ 4 (volume.restrict Ω) := eLpNorm_testGraph_zero _ h
    _ ≤ eLpNorm φ 4 volume := eLpNorm_mono_measure _ Measure.restrict_le_self
    _ = eLpNorm φ ((4 : ℝ≥0) : ℝ≥0∞) volume := by rw [ENNReal.coe_ofNat]
    _ ≤ eLpNormLESNormFDerivOfLeConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω (3 / 2) 4
          * eLpNorm (fderiv ℝ φ) ((3 / 2 : ℝ≥0) : ℝ≥0∞) volume :=
        eLpNorm_le_eLpNorm_fderiv_of_le volume (h.1.of_le (by simp))
          ((subset_tsupport φ).trans h.2.2) (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
          hrank hpq hΩb
    _ ≤ eLpNormLESNormFDerivOfLeConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω (3 / 2) 4
          * (eLpNorm (fderiv ℝ φ) 2 volume * (volume Ω) ^ (1 / 6 : ℝ)) := by
        gcongr
    _ ≤ eLpNormLESNormFDerivOfLeConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω (3 / 2) 4
          * ((∑ i : Fin 2, ‖h.testGraph i.succ‖ₑ) * (volume Ω) ^ (1 / 6 : ℝ)) := by
        gcongr
        exact eLpNorm_fderiv_le_sum hΩm h
    _ = sobolevConstTwo Ω * ∑ i : Fin 2, ‖h.testGraph i.succ‖ₑ := by
        rw [sobolevConstTwo, ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg _ (by norm_num),
          ENNReal.coe_toNNReal hΩfin]
        ring

/-- **Sobolev estimate on `H₀¹(Ω)` in dimension two**, into `L⁴(Ω)`. -/
theorem eLpNorm_le_of_mem_H01_two (hΩm : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω)
    {U : H1amb Ω} (hU : U ∈ H01 Ω) :
    eLpNorm (U 0) 4 (volume.restrict Ω) ≤ sobolevConstTwo Ω * ∑ i : Fin 2, ‖U i.succ‖ₑ :=
  eLpNorm_le_of_mem_H01_of_forall_testFn (fun h => eLpNorm_testGraph_le_two hΩm hΩb h) hU

end EllipticPdes.Embedding
