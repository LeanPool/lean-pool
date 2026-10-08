/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.MainTheorems
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvariance

/-!
# Suitable solutions under parabolic rescaling

These fields use the translation and scaling convention of CKN's rescaling
definition.  Suitability is transported on arbitrary product domains by CKN's
scaling theorem.
-/

public section

open CKN Set
open CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Velocity after translating and parabolically scaling by `r`, as in
manuscript label `lem:thmA-rescaled`. -/
@[expose] def parabolicRescaleVelocity (x₀ : Vec3) (t₀ r : ℝ)
    (u : ParabolicPoint → Vec3) : ParabolicPoint → Vec3 :=
  fun z => r • u (parabolicTranslate x₀ t₀ (parabolicScale r z))

/-- Weak gradient after translating and parabolically scaling by `r`, as in
manuscript label `lem:thmA-rescaled`. -/
@[expose] def parabolicRescaleGradient (x₀ : Vec3) (t₀ r : ℝ)
    (Du : ParabolicPoint → Fin 3 → Vec3) : ParabolicPoint → Fin 3 → Vec3 :=
  fun z i => r ^ 2 • Du (parabolicTranslate x₀ t₀ (parabolicScale r z)) i

/-- Pressure after translating and parabolically scaling by `r`, as in
manuscript label `lem:thmA-rescaled`. -/
@[expose] def parabolicRescalePressure (x₀ : Vec3) (t₀ r : ℝ)
    (p : ParabolicPoint → ℝ) : ParabolicPoint → ℝ :=
  fun z => r ^ 2 * p (parabolicTranslate x₀ t₀ (parabolicScale r z))

/-- Suitability is preserved under translation and parabolic scaling on an
arbitrary product domain, as used in manuscript label `lem:thmA-rescaled`. -/
theorem isSuitableWeakSolution_parabolicRescale
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hSuitable : IsSuitableWeakSolution Ω I q u Du p f)
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r) :
    IsSuitableWeakSolution (CKN.rescaledSpace r x₀ Ω)
      (CKN.rescaledTime r t₀ I) q
      (parabolicRescaleVelocity x₀ t₀ r u)
      (parabolicRescaleGradient x₀ t₀ r Du)
      (parabolicRescalePressure x₀ t₀ r p)
      (fun z => r ^ 3 • f (parabolicTranslate x₀ t₀ (parabolicScale r z))) := by
  have hscaled := CKN.isSuitableWeakSolutionIntegrable_rescale
    (CKN.isSuitableWeakSolution_iff_integrable.mp hSuitable) (x₀, t₀) hr
  exact CKN.isSuitableWeakSolution_iff_integrable.mpr hscaled

/-- The positive-time interval pulls back to its translated and rescaled
half-line. -/
theorem rescaledTime_Ioi_zero (t₀ r : ℝ) (hr : 0 < r) :
    CKN.rescaledTime r t₀ (Ioi (0 : ℝ)) = Ioi (-(t₀ / r ^ 2)) := by
  ext s
  simp only [CKN.rescaledTime, CKN.scalingTime, Set.mem_preimage,
    Set.mem_Ioi]
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  constructor
  · intro hs
    have hmul : -t₀ < r ^ 2 * s := by linarith only [hs]
    have hdiv : (-t₀) / r ^ 2 < s :=
      (div_lt_iff₀ hr2).2 (by simpa [mul_comm] using hmul)
    simpa only [neg_div] using hdiv
  · intro hs
    have hdiv : (-t₀) / r ^ 2 < s := by simpa only [neg_div] using hs
    have hmul : -t₀ < r ^ 2 * s := by
      have hmul' := (div_lt_iff₀ hr2).1 hdiv
      simpa only [mul_comm] using hmul'
    linarith only [hmul]

end ESS
