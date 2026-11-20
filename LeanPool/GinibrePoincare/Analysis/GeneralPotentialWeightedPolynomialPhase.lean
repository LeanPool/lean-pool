/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralPotentialWeightedPolynomialPhase.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialQuotientProjection
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticAlternatedMonomialPolynomial
public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialCenteredMean

/-!
# General potential weighted polynomial phase

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `volumeGlobalPhaseL2_weighted_homogeneous`, `potentialInverseGauge_phase_degree`,
`weightedPolynomialL2_eq_zero`.
-/

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section

theorem piPotentialHalfWeight_globalPhase (n d : ℕ) {V : Potential}
    (hrot : IsRotationalPotential V) (a : ℂ) (ha : ‖a‖ = 1) (z : Configuration d) :
    piPotentialHalfWeight d n V (globalPhase a z) = piPotentialHalfWeight d n V z := by
  unfold piPotentialHalfWeight planarPotentialHalfWeight
  simp only [globalPhase_apply, hrot a _ ha]

theorem volumeGlobalPhaseL2_weighted_homogeneous {n d D : ℕ} {V : Potential}
    (hrot : IsRotationalPotential V) (P : ConfigurationPolynomial d) (hP : P.IsHomogeneous D)
    (F : PlanarPiLebesgueL2 d)
    (hF : (F : Configuration d → ℂ) =ᵐ[volume]
      fun z => MvPolynomial.eval z P * piPotentialHalfWeight d n V z)
    (a : ℂ) (ha : ‖a‖ = 1) : volumeGlobalPhaseL2 a ha F = a ^ D • F := by
  apply Lp.ext
  have hp := (measurePreserving_globalPhase_configurationVolume d a
      ha).quasiMeasurePreserving.ae_eq_comp hF
  filter_upwards [Lp.coeFn_compMeasurePreserving F
    (measurePreserving_globalPhase_configurationVolume d a ha), hp, hF,
    Lp.coeFn_smul (a ^ D) F] with z hc hp hz hs
  calc
    volumeGlobalPhaseL2 a ha F z = F (globalPhase a z) := hc
    _ = MvPolynomial.eval (globalPhase a z) P * piPotentialHalfWeight d n V (globalPhase a z) := hp
    _ = a ^ D * F z := by
      rw [hz, piPotentialHalfWeight_globalPhase n d hrot a ha z,
        isHomogeneousConfigurationPolynomial_of_isHomogeneous hP a z]
      ring
    _ = (a ^ D • F) z := hs.symm

theorem potentialInverseGauge_phase_degree {n D : ℕ} (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hrot : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤)
    (hle : vandermondeDegree n ≤ D) (F : PlanarPiLebesgueL2 n)
    (hF : ∀ (a : ℂ) (ha : ‖a‖ = 1), volumeGlobalPhaseL2 a ha F = a ^ D • F)
    (a : ℂ) (ha : ‖a‖ = 1) :
    potentialGlobalPhaseL2 n hV hrot a ha ((potentialPiVandermondeL2Equiv n hn hV hfin).symm F) =
      a ^ (D - vandermondeDegree n) • (potentialPiVandermondeL2Equiv n hn hV hfin).symm F := by
  let E := potentialPiVandermondeL2Equiv n hn hV hfin
  have han : a ≠ 0 := by intro h; simp [h] at ha
  have he : volumeGlobalPhaseL2 a ha F = a ^ vandermondeDegree n •
      E (potentialGlobalPhaseL2 n hV hrot a ha (E.symm F)) := by
    have hh := volumeGlobalPhaseL2_potentialVandermonde hn hV hrot hfin a ha (E.symm F)
    change volumeGlobalPhaseL2 a ha (E (E.symm F)) = _ at hh
    rw [E.apply_symm_apply] at hh
    exact hh
  apply E.injective
  rw [E.map_smul, E.apply_symm_apply]
  have hh := congrArg (fun x : PlanarPiLebesgueL2 n => (a ^ vandermondeDegree n)⁻¹ • x) he
  rw [hF a ha] at hh
  rw [smul_smul, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ han), one_smul] at hh
  have hp : (a ^ vandermondeDegree n)⁻¹ * a ^ D = a ^ (D - vandermondeDegree n) := by
    rw [show D = vandermondeDegree n + (D - vandermondeDegree n) from (Nat.add_sub_of_le hle).symm,
      pow_add, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ han), one_mul]
    congr 1
    omega
  simpa only [hp] using hh.symm

theorem weightedPolynomialL2_eq_zero {n d : ℕ} {V : Potential}
    (F : PlanarPiLebesgueL2 d)
    (hF : (F : Configuration d → ℂ) =ᵐ[volume]
      fun z => MvPolynomial.eval z (0 : ConfigurationPolynomial d) *
        piPotentialHalfWeight d n V z) :
    F = 0 := by
  apply Lp.ext
  filter_upwards [hF, Lp.coeFn_zero ℂ 2 (volume : Measure (Configuration d))] with z hz hzero
  exact hz.trans (by simp)

end
end GinibrePoincare
