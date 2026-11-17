/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Vector.Coarea.FiberIntegral
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # The equidimensional degenerate case: almost no level is a critical value

When `n = m` the fibre dimension is `k = 0`, and `μH[0]`-nullity
of a slice means the slice is **empty**, so the statement to prove is that for almost every `t` the
level `{u = t}` contains **no** critical point at all.

**Proof.** The argument uses Mathlib's equidimensional Sard lemma
`MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` — if a map of a finite-dimensional
real space to *itself* is differentiable on a set and its differential is singular there, the image
of that set is Lebesgue-null — transported across the linear isometry
`isometryEquivOfFinrankEq` between two inner product spaces of the same dimension, plus the
linear algebra that in equal dimensions "not surjective" and "determinant zero" agree.

**Scope.** No general finite-regularity Sard theorem such as `Analysis.sard` is proved here. Sard's
theorem is a statement about the
measure of the set of critical **values** of a map `ℝⁿ → ℝᵐ`; what is proved here is only the
`n = m` case, and only that case, where the critical set maps into a null set purely because a
singular linear map contracts volume.  For `n > m` the critical values of a `C¹` map can have
positive measure (Whitney), and nothing below says otherwise.  The rank-deficient coarea conclusion
is a statement about `ℋ^k` **inside** a level and was proved independently in
`Analysis/Vector/RankDeficient/Coarea.lean`; this equidimensional theorem is a consistency check on
it, not an ingredient of its proof.

**Relation to rank-deficient coarea.**  In the equidimensional case the coarea conclusion reads
`μH[0] (C ∩ {u = t}) = 0` for almost
every `t`, and a nonempty set has `μH[0] ≥ 1`, so the two conclusions are then *equivalent*
statements.
Nothing of that equivalence is used here: this module imports neither the rank-deficient coarea
module nor any part of that route, so the two proofs are independent and the agreement is a real
cross-check.
It is recorded in `research/audits/Sard/EquidimensionalAudit.lean`, in both directions.
-/

@[expose] public section

section

open MeasureTheory Module Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace FunctionalInequalities.Analysis

/-! ### The linear algebra: in equal dimensions, non-surjective means singular -/

/-- A non-surjective endomorphism of a finite-dimensional space has vanishing determinant.  Mathlib
has the converse direction (`LinearMap.range_lt_top_of_det_eq_zero`); this one goes through
injectivity, which is equivalent to surjectivity only in finite dimension. -/
theorem det_eq_zero_of_not_surjective {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] (L : X →L[ℝ] X)
    (hL : ¬ Function.Surjective L) : L.det = 0 := by
  by_contra hdet
  refine hL ?_
  have hker : LinearMap.ker (L : X →ₗ[ℝ] X) = ⊥ := by
    by_contra hk
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)
  exact LinearMap.injective_iff_surjective.mp (LinearMap.ker_eq_bot.mp hker)

/-! ### The equidimensional Sard lemma between two spaces of the same dimension -/

section Equidimensional

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

section CriticalValues

omit [MeasurableSpace V] [BorelSpace V]
/-- **The critical values of an equidimensional `C¹` map form a null set.**  Mathlib's
self-map statement, conjugated by the linear isometry of `isometryEquivOfFinrankEq`: the image is
computed in `W` directly, by precomposing `u` with the inverse isometry rather than postcomposing
it, so no transport of the null set itself is needed. -/
theorem measure_image_critical_eq_zero {u : V → W} (hu : ContDiff ℝ 1 u)
    (h : finrank ℝ V = finrank ℝ W) :
    (volume : Measure W) (u '' {x : V | ¬ Function.Surjective (fderiv ℝ u x)}) = 0 := by
  classical
  set C : Set V := {x : V | ¬ Function.Surjective (fderiv ℝ u x)}
  set e : V ≃ₗᵢ[ℝ] W := isometryEquivOfFinrankEq h
  set E : W →L[ℝ] V := e.symm.toLinearIsometry.toContinuousLinearMap
  set g : W → W := fun y => u (e.symm y) with hg
  set g' : W → W →L[ℝ] W := fun y => (fderiv ℝ u (e.symm y)).comp E with hg'
  have hdu : Differentiable ℝ u := hu.differentiable one_ne_zero
  have himg : u '' C = g '' (e '' C) := by
    rw [Set.image_image]
    simp [hg]
  have hderiv : ∀ y ∈ e '' C, HasFDerivWithinAt g (g' y) (e '' C) y := by
    intro y _
    exact (((hdu (e.symm y)).hasFDerivAt).comp y E.hasFDerivAt).hasFDerivWithinAt
  have hdet : ∀ y ∈ e '' C, (g' y).det = 0 := by
    rintro y ⟨x, hx, rfl⟩
    have hxy : e.symm (e x) = x := e.symm_apply_apply x
    have hnot : ¬ Function.Surjective ((fderiv ℝ u x).comp E) := by
      intro hsurj
      refine hx ?_
      intro w
      obtain ⟨z, hz⟩ := hsurj w
      exact ⟨E z, hz⟩
    have : g' (e x) = (fderiv ℝ u x).comp E := by rw [hg']; simp [hxy]
    rw [this]
    exact det_eq_zero_of_not_surjective _ hnot
  rw [himg]
  exact MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
    (μ := (volume : Measure W)) hderiv hdet

/-- **In equal dimensions, almost every level avoids the critical set entirely.**  The
fibre dimension is `k = 0`, so the `ℋ^0`-null conclusion of rank-deficient coarea degenerates to
emptiness of the
slice.  See the module docstring: this is the `n = m` case only, and is not a general Sard
theorem. -/
theorem ae_critical_inter_levelSet_eq_empty {u : V → W} (hu : ContDiff ℝ 1 u)
    (h : finrank ℝ V = finrank ℝ W) :
    ∀ᵐ t ∂(volume : Measure W),
      {x : V | ¬Function.Surjective (fderiv ℝ u x)} ∩ {x : V | u x = t} = ∅ := by
  have hnull := measure_image_critical_eq_zero hu h
  have hae :
    ∀ᵐ t ∂(volume : Measure W), t ∉ u '' {x : V | ¬Function.Surjective (fderiv ℝ u x)} :=
    measure_eq_zero_iff_ae_notMem.mp hnull
  filter_upwards [hae] with t ht
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro x ⟨hx, rfl⟩
  exact ht ⟨x, hx, rfl⟩

end CriticalValues

end Equidimensional

end FunctionalInequalities.Analysis

section LipschitzNullImage

open MeasureTheory Set

/-! Lipschitz maps between spaces of equal dimension send null sets to null sets. -/

namespace FunctionalInequalities.Analysis

/-- **Lipschitz maps send null sets to null sets** (Alexandrov's second-order
differentiability theorem): for a map of a finite-dimensional real inner product space into
itself that is Lipschitz on `s`, a Lebesgue-null `s` has a Lebesgue-null image. No measurability of
`s`
is assumed. -/
theorem volume_image_eq_zero_of_lipschitzOnWith {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f : E → E} {K : NNReal} {s : Set E} (hf : LipschitzOnWith K f s)
    (hs : (volume : Measure E) s = 0) : (volume : Measure E) (f '' s) = 0 := by
  have hsH : (μH[(Module.finrank ℝ E : ℝ)] : Measure E) s = 0 := by
    rw [Measure.isAddLeftInvariant_eq_smul (μH[(Module.finrank ℝ E : ℝ)] : Measure E)
        (volume : Measure E),
      Measure.smul_apply, hs, smul_zero]
  have himageH : (μH[(Module.finrank ℝ E : ℝ)] : Measure E) (f '' s) = 0 := by
    have h := hf.hausdorffMeasure_image_le (Nat.cast_nonneg (Module.finrank ℝ E))
    rw [hsH, mul_zero] at h
    exact le_antisymm h bot_le
  rw [Measure.isAddLeftInvariant_eq_smul (volume : Measure E)
      (μH[(Module.finrank ℝ E : ℝ)] : Measure E),
    Measure.smul_apply, himageH, smul_zero]

end FunctionalInequalities.Analysis

end LipschitzNullImage
