/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralPotentialProjectionPhase.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialProjectionPermutation
public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialVandermondePhase
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticBergmanPhase
public import LeanPool.GinibrePoincare.Analysis.GlobalPhaseAction
public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialLpConjugation

/-!
# General potential projection phase

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `planarPiBergmanProjection_commutes_globalPhase`,
`inner_eq_zero_of_volume_phase_degrees_ne`, `inner_eq_zero_of_potential_phase_degrees_ne`,
`potentialGlobalPhaseL2_star`.
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff BigOperators InnerProductSpace ComplexConjugate
namespace GinibrePoincare
noncomputable section

theorem planarLebesguePhase_coeFn (a : ℂ) (ha : ‖a‖ = 1) (u : PlanarLebesgueL2) :
    (planarLebesguePhase a ha u : ℂ → ℂ) =ᵐ[volume] (fun z => u (a * z)) := by
  change (Lp.compMeasurePreserving (fun z : ℂ => a * z)
    (measurePreserving_complex_mul_of_norm_one a ha) u : ℂ → ℂ) =ᵐ[volume] _
  exact Lp.coeFn_compMeasurePreserving u (measurePreserving_complex_mul_of_norm_one a ha)

/-- The actual global phase pullback rotates every scalar factor of a pure vector. -/
theorem volumeGlobalPhaseL2_pure {d : ℕ} (a : ℂ) (ha : ‖a‖ = 1)
    (u : Fin d → PlanarLebesgueL2) :
    volumeGlobalPhaseL2 a ha (l2PiProductVector (fun _ => (volume : Measure ℂ)) u) =
      l2PiProductVector (fun _ => (volume : Measure ℂ)) (fun i => planarLebesguePhase a ha (u i)) :=
          by
  have hc : ∀ᵐ z ∂configurationVolume d, ∀ i : Fin d,
      planarLebesguePhase a ha (u i) (z i) = u i (a * z i) := by
    rw [ae_all_iff]
    intro i
    exact (Measure.quasiMeasurePreserving_eval (fun _ : Fin d => (volume : Measure ℂ)) i).ae_eq_comp
      (planarLebesguePhase_coeFn a ha (u i))
  have hp := (measurePreserving_globalPhase_configurationVolume d a
      ha).quasiMeasurePreserving.ae_eq_comp
    (l2PiProductVector_coeFn (fun _ => (volume : Measure ℂ)) u)
  unfold volumeGlobalPhaseL2
  change Lp.compMeasurePreserving (globalPhase a) (measurePreserving_globalPhase_configurationVolume
      d a ha)
    (l2PiProductVector (fun _ => (volume : Measure ℂ)) u) = _
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving
    (l2PiProductVector (fun _ => (volume : Measure ℂ)) u)
    (measurePreserving_globalPhase_configurationVolume d a ha), hp,
    l2PiProductVector_coeFn (fun _ => (volume : Measure ℂ)) (fun i => planarLebesguePhase a ha (u
        i)),
    hc] with z hz hp hq hc
  have hh : (∏ i, u i (globalPhase a z i)) = ∏ i, planarLebesguePhase a ha (u i) (z i) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact (hc i).symm
  exact hz.trans (hp.trans (hh.trans hq.symm))

/-- Genuine global-phase commutation of the whole nonquadratic Bergman projection. -/
theorem planarPiBergmanProjection_commutes_globalPhase {m : ℕ} (n : ℕ) (V : Potential)
    (hV : ContDiff ℝ 2 V) (hrot : IsRotationalPotential V) (a : ℂ) (ha : ‖a‖ = 1) :
    (planarPiBergmanProjection (m := m) n V hV).comp (volumeGlobalPhaseL2 a
        ha).toContinuousLinearMap =
      (volumeGlobalPhaseL2 a ha).toContinuousLinearMap.comp (planarPiBergmanProjection (m := m) n V
          hV) := by
  apply l2PiOperators_ext_on_pure (m+1) (fun _ => (volume : Measure ℂ))
  intro u
  change planarPiBergmanProjection (m := m) n V hV
    (volumeGlobalPhaseL2 a ha (l2PiProductVector (fun _ => (volume : Measure ℂ)) u)) =
    volumeGlobalPhaseL2 a ha (planarPiBergmanProjection (m := m) n V hV
      (l2PiProductVector (fun _ => (volume : Measure ℂ)) u))
  rw [volumeGlobalPhaseL2_pure, planarPiBergmanProjection_pure,
    planarPiBergmanProjection_pure, volumeGlobalPhaseL2_pure]
  congr 1
  funext i
  exact (planarBergmanProjection_phase_intertwines n V hV
    (fun a ha z => hrot a z ha) a ha (u i)).symm

theorem inner_eq_zero_of_volume_phase_degrees_ne {n d e : ℕ}
    (hde : d ≠ e)
    (x y : Lp ℂ 2 (configurationVolume n))
    (hx : ∀ (u : ℂ) (hu : ‖u‖ = 1),
      volumeGlobalPhaseL2 u hu x = u ^ d • x)
    (hy : ∀ (u : ℂ) (hu : ‖u‖ = 1),
      volumeGlobalPhaseL2 u hu y = u ^ e • y) :
    inner ℂ x y = 0 := by
  obtain ⟨u, hu, hpow⟩ := exists_unit_phase_pow_ne d e hde
  have hchar : conj (u ^ d) * u ^ e ≠ 1 := by
    intro h
    apply hpow
    calc
      u ^ d = u ^ d * 1 := by ring
      _ = u ^ d * (conj (u ^ d) * u ^ e) := by rw [h]
      _ = (u ^ d * conj (u ^ d)) * u ^ e := by ring
      _ = u ^ e := by
        rw [Complex.mul_conj]
        have hud : ‖u ^ d‖ = 1 := by simp [norm_pow, hu]
        rw [← Complex.sq_norm, hud]
        norm_num
  exact inner_eq_zero_of_isometry_eigencharacters
    (volumeGlobalPhaseL2 u hu) x y (u ^ d) (u ^ e)
      (hx u hu) (hy u hu) hchar

theorem inner_eq_zero_of_potential_phase_degrees_ne {n d e : ℕ}
    {V : Potential} (hV : Continuous V) (hrot : IsRotationalPotential V)
    (hde : d ≠ e)
    (x y : Lp ℂ 2 (potentialMeasure n V))
    (hx : ∀ (u : ℂ) (hu : ‖u‖ = 1),
      potentialGlobalPhaseL2 n hV hrot u hu x = u ^ d • x)
    (hy : ∀ (u : ℂ) (hu : ‖u‖ = 1),
      potentialGlobalPhaseL2 n hV hrot u hu y = u ^ e • y) :
    inner ℂ x y = 0 := by
  obtain ⟨u, hu, hpow⟩ := exists_unit_phase_pow_ne d e hde
  have hchar : conj (u ^ d) * u ^ e ≠ 1 := by
    intro h
    apply hpow
    calc
      u ^ d = u ^ d * 1 := by ring
      _ = u ^ d * (conj (u ^ d) * u ^ e) := by rw [h]
      _ = (u ^ d * conj (u ^ d)) * u ^ e := by ring
      _ = u ^ e := by
        rw [Complex.mul_conj]
        have hud : ‖u ^ d‖ = 1 := by simp [norm_pow, hu]
        rw [← Complex.sq_norm, hud]
        norm_num
  exact inner_eq_zero_of_isometry_eigencharacters
    (potentialGlobalPhaseL2 n hV hrot u hu) x y (u ^ d) (u ^ e)
      (hx u hu) (hy u hu) hchar

theorem potentialGlobalPhaseL2_star {n : ℕ} {V : Potential} (hV : Continuous V)
    (hrot : IsRotationalPotential V) (a : ℂ) (ha : ‖a‖ = 1)
    (x : Lp ℂ 2 (potentialMeasure n V)) :
    potentialGlobalPhaseL2 n hV hrot a ha (star x) = star (potentialGlobalPhaseL2 n hV hrot a ha x)
        := by
  exact complexLp_compMeasurePreserving_star (potentialMeasure n V) (globalPhase a)
    (measurePreserving_globalPhase_potentialMeasure n hV hrot a ha) x

end
end GinibrePoincare
