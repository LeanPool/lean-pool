/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.TimeOUComposition
import Mathlib.Analysis.Calculus.MeanValue

/-! # Uniform time continuity from a bounded input generator -/

@[expose] public noncomputable section

open Set

namespace EhrhardGaussian.Ehrhard

/-- The derivative of the space–time family consists of unit time and the averaged generators. -/
theorem hasDerivAt_ouSpaceTimeFamily {n k : ℕ} {f : Fin k → (Fin n → ℝ) → ℝ}
    (hf : ∀ i, HasPolynomiallyBoundedSecondCoordinateDerivatives (f i))
    (y : Fin n → ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun t => ouSpaceTimeFamily f (t, y))
      (1, fun i => ouAverage (ouGenerator (f i)) y s) s := by
  have hfamily : HasDerivAt (fun t => ouFamily f (t, y))
      (fun i => ouAverage (ouGenerator (f i)) y s) s :=
    hasDerivAt_pi.mpr fun i => hasDerivAt_ouAverage_generator (hf i) y hs
  exact (hasDerivAt_id' s).prodMk hfamily

/-- A time dependent composition with an Ornstein–Uhlenbeck family satisfies the chain rule. -/
theorem hasDerivAt_time_ouComposition {n k : ℕ} {f : Fin k → (Fin n → ℝ) → ℝ}
    (hf : ∀ i, HasPolynomiallyBoundedSecondCoordinateDerivatives (f i))
    {J : ℝ × (Fin k → ℝ) → ℝ} (y : Fin n → ℝ) {s : ℝ} (hs : 0 < s)
    (hJ : DifferentiableAt ℝ J (s, ouFamily f (s, y))) :
    HasDerivAt (fun t => J (t, ouFamily f (t, y)))
      (fderiv ℝ J (s, ouFamily f (s, y))
        (1, fun i => ouAverage (ouGenerator (f i)) y s)) s :=
  hJ.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_ouSpaceTimeFamily hf y hs)

/-- A bounded generator gives uniform time continuity for dependent inputs without requiring spatial
limits at infinity. -/
theorem exists_time_ouComposition_lipschitz {n k : ℕ} {f : Fin k → (Fin n → ℝ) → ℝ}
    (hf : ∀ i, HasPolynomiallyBoundedSecondCoordinateDerivatives (f i))
    {a b c T M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hbound : ∀ i y, f i y ∈ Icc a b) (hgenerator : ∀ i y, |ouGenerator (f i) y| ≤ M)
    {J : ℝ × (Fin k → ℝ) → ℝ}
    (hJ : ∀ s ∈ Icc c T, ∀ z : Fin k → ℝ, (∀ i, z i ∈ Icc a b) → ContDiffAt ℝ 2 J (s, z)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc c T, ∀ t ∈ Icc c T, ∀ y : Fin n → ℝ,
      |J (s, ouFamily f (s, y)) - J (t, ouFamily f (t, y))| ≤ C * |s - t| := by
  have hf₁ := fun i => hasPolynomiallyBoundedCoordinateDerivatives_of_second (hf i)
  have hcompact : IsCompact (Icc c T ×ˢ {z : Fin k → ℝ | ∀ i, z i ∈ Icc a b}) :=
    isCompact_Icc.prod (isCompact_probabilitySubbox (k := k) a b)
  obtain ⟨L, hL, hLbound⟩ := exists_bound_firstDerivatives_on_compact hcompact
    (fun p hp => (hJ p.1 hp.1 p.2 hp.2).of_le (by norm_num))
  have hmax : 0 ≤ max (1 : ℝ) M := zero_le_one.trans (le_max_left _ _)
  refine ⟨L * max 1 M, mul_nonneg hL hmax, ?_⟩
  intro s hs t ht y
  have hrange (r : ℝ) := ouFamily_mem_Icc hf₁ hbound y r
  have hd (r) (hr : r ∈ Icc c T) := hasDerivAt_time_ouComposition hf y (hc.trans_le hr.1)
    ((hJ r hr _ (hrange r)).differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0))
  have hdBound (r) (hr : r ∈ Icc c T) :
      ‖fderiv ℝ J (r, ouFamily f (r, y))
        (1, fun i => ouAverage (ouGenerator (f i)) y r)‖ ≤ L * max 1 M := by
    have hv : ‖(fun i => ouAverage (ouGenerator (f i)) y r)‖ ≤ M :=
      (pi_norm_le_iff_of_nonneg hM).mpr fun i => by
        simpa only [Real.norm_eq_abs] using abs_ouAverage_le (hgenerator i) y r
    have hdir : ‖((1 : ℝ), fun i => ouAverage (ouGenerator (f i)) y r)‖ ≤ max 1 M := by
      rw [Prod.norm_mk, norm_one]
      exact max_le_max le_rfl hv
    exact ((fderiv ℝ J (r, ouFamily f (r, y))).le_opNorm _).trans
      (mul_le_mul (hLbound (r, ouFamily f (r, y)) ⟨hr, hrange r⟩).2 hdir (norm_nonneg _) hL)
  simpa only [Real.norm_eq_abs] using (convex_Icc c T).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r hr => (hd r hr).hasDerivWithinAt) hdBound ht hs

end EhrhardGaussian.Ehrhard

end
