/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.PotentialWeakSolution

/-!
# EllipticityWitness

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Independence from ellipticity witnesses

The canonical weak solution is independent of the quantitative ellipticity
certificate used to construct it.  These lemmas let an exhaustion use the
compactness-supplied upper constant of each domain without changing the
represented operator.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

/-- Alpha-shifted solutions built from two valid ellipticity certificates are
equal, because both solve the same weak equation. -/
theorem alphaShiftedSolution_eq_of_ellipticityWitness
    (a : CoeffField d) {alpha lam₁ Lam₁ lam₂ Lam₂ : ℝ}
    (halpha : 0 < alpha) (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂)
    (hEll₁ : IsEllipticFieldOn lam₁ Lam₁ U a)
    (hEll₂ : IsEllipticFieldOn lam₂ Lam₂ U a) (f : ScalarL2 U) :
    alphaShiftedSolution a halpha hlam₁ hEll₁ f =
      alphaShiftedSolution a halpha hlam₂ hEll₂ f := by
  apply (isAlphaShiftedWeakSolution_iff_eq a halpha hlam₂ hEll₂ f _).1
  exact alphaShiftedSolution_isAlphaShiftedWeakSolution a halpha hlam₁ hEll₁ f

/-- Potential solutions built from two valid ellipticity certificates are
equal, because both solve the same weak equation with potential. -/
theorem potentialSolution_eq_of_ellipticityWitness
    (a : CoeffField d) {alpha lam₁ Lam₁ lam₂ Lam₂ C₁ C₂ : ℝ}
    (halpha : 0 < alpha) (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂)
    (hEll₁ : IsEllipticFieldOn lam₁ Lam₁ U a)
    (hEll₂ : IsEllipticFieldOn lam₂ Lam₂ U a)
    (q : Vec d → ℝ) (hq₁ : IsBoundedNonnegativePotential U q C₁)
    (hq₂ : IsBoundedNonnegativePotential U q C₂)
    (f : ScalarL2 U) :
    potentialSolution a halpha hlam₁ hEll₁ q hq₁ f =
      potentialSolution a halpha hlam₂ hEll₂ q hq₂ f := by
  apply (isPotentialWeakSolution_iff_eq a halpha hlam₂ hEll₂ q hq₂ f _).1
  exact potentialSolution_isPotentialWeakSolution a halpha hlam₁ hEll₁ q hq₁ f

/-- Potential resolvents do not depend on the ellipticity certificate used in
their Lax–Milgram construction. -/
theorem potentialResolvent_eq_of_ellipticityWitness
    (a : CoeffField d) {alpha lam₁ Lam₁ lam₂ Lam₂ C₁ C₂ : ℝ}
    (halpha : 0 < alpha) (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂)
    (hEll₁ : IsEllipticFieldOn lam₁ Lam₁ U a)
    (hEll₂ : IsEllipticFieldOn lam₂ Lam₂ U a)
    (q : Vec d → ℝ) (hq₁ : IsBoundedNonnegativePotential U q C₁)
    (hq₂ : IsBoundedNonnegativePotential U q C₂) :
    potentialResolvent a halpha hlam₁ hEll₁ q hq₁ =
      potentialResolvent a halpha hlam₂ hEll₂ q hq₂ := by
  ext f
  simp only [potentialResolvent_apply]
  rw [potentialSolution_eq_of_ellipticityWitness a halpha hlam₁ hlam₂
    hEll₁ hEll₂ q hq₁ hq₂ f]

/-- Potential solutions depend only on the almost-everywhere value of the
potential on the domain. -/
theorem potentialSolution_eq_of_ae_eq_potential
    (a : CoeffField d) {alpha lam Lam C₁ C₂ : ℝ}
    (halpha : 0 < alpha) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (q₁ q₂ : Vec d → ℝ) (hq₁ : IsBoundedNonnegativePotential U q₁ C₁)
    (hq₂ : IsBoundedNonnegativePotential U q₂ C₂)
    (hqeq : q₁ =ᵐ[volumeMeasureOn U] q₂) (f : ScalarL2 U) :
    potentialSolution a halpha hlam hEll q₁ hq₁ f =
      potentialSolution a halpha hlam hEll q₂ hq₂ f := by
  apply (isPotentialWeakSolution_iff_eq a halpha hlam hEll q₂ hq₂ f _).1
  intro v
  have hweak := potentialSolution_isPotentialWeakSolution
    a halpha hlam hEll q₁ hq₁ f v
  unfold shiftedPotentialBilin at hweak ⊢
  rw [← hweak]
  congr 1
  apply integral_congr_ae
  filter_upwards [hqeq] with x hx
  rw [hx]

/-- Potential resolvents are unchanged when the potential is modified on a
null subset of the domain. -/
theorem potentialResolvent_eq_of_ae_eq_potential
    (a : CoeffField d) {alpha lam Lam C₁ C₂ : ℝ}
    (halpha : 0 < alpha) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (q₁ q₂ : Vec d → ℝ) (hq₁ : IsBoundedNonnegativePotential U q₁ C₁)
    (hq₂ : IsBoundedNonnegativePotential U q₂ C₂)
    (hqeq : q₁ =ᵐ[volumeMeasureOn U] q₂) :
    potentialResolvent a halpha hlam hEll q₁ hq₁ =
      potentialResolvent a halpha hlam hEll q₂ hq₂ := by
  ext f
  simp only [potentialResolvent_apply]
  rw [potentialSolution_eq_of_ae_eq_potential a halpha hlam hEll q₁ q₂
    hq₁ hq₂ hqeq f]

end

end DivergenceFormProcess.Form
