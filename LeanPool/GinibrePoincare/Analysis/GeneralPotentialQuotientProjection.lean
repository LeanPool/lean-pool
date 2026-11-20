/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralPotentialQuotientProjection.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialProjectionOrthogonal
public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialProjectionPhase
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticPiBergmanMonomials

/-!
# General potential quotient projection

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `potentialHolomorphicQuotientProjection_adjoint`,
`potentialHolomorphicQuotientProjection_idempotent`,
`potentialHolomorphicQuotientProjection_residual_norm`,
`potentialHolomorphicQuotientProjection_phase_intertwines`.
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

theorem unitary_conjugate_projection_adjoint
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (E : H ≃ₗᵢ[ℂ] K) (P : K →L[ℂ] K) (hp : P.adjoint = P) :
    (E.symm.toLinearIsometry.toContinuousLinearMap.comp
      (P.comp E.toLinearIsometry.toContinuousLinearMap)).adjoint =
    E.symm.toLinearIsometry.toContinuousLinearMap.comp
      (P.comp E.toLinearIsometry.toContinuousLinearMap) := by
  have he : E.toLinearIsometry.toContinuousLinearMap.adjoint =
      E.symm.toLinearIsometry.toContinuousLinearMap := E.adjoint_eq_symm
  have hes : E.symm.toLinearIsometry.toContinuousLinearMap.adjoint =
      E.toLinearIsometry.toContinuousLinearMap := E.symm.adjoint_eq_symm
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, he, hes, hp]
  exact ContinuousLinearMap.comp_assoc _ _ _

/-- The genuine gauge unitary with its target written as the canonical product
Lebesgue L² space. `volume_pi` is definitional, so this is the same unitary. -/
def potentialPiVandermondeL2Equiv (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤) :
    Lp ℂ 2 (potentialMeasure n V) ≃ₗᵢ[ℂ] PlanarPiLebesgueL2 n :=
  potentialVandermondeL2Equiv n hn hV hfin

/-- The actual nonquadratic holomorphic quotient projection, transported by
the genuine normalized Vandermonde gauge unitary. -/
def potentialHolomorphicQuotientProjection {d : ℕ} (hn : 0 < d + 1)
    {V : Potential} (hV : ContDiff ℝ 2 V) (hfin : potentialPartition (d + 1) V < ⊤) :
    Lp ℂ 2 (potentialMeasure (d+1) V) →L[ℂ] Lp ℂ 2 (potentialMeasure (d+1) V) :=
  (potentialPiVandermondeL2Equiv (d+1) hn hV.continuous
      hfin).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((planarPiBergmanProjection (m := d) (d+1) V hV).comp
      (potentialPiVandermondeL2Equiv (d+1) hn hV.continuous
          hfin).toLinearIsometry.toContinuousLinearMap)

theorem potentialHolomorphicQuotientProjection_gauge {d : ℕ} (hn : 0 < d + 1)
    {V : Potential} (hV : ContDiff ℝ 2 V) (hfin : potentialPartition (d + 1) V < ⊤)
    (u : Lp ℂ 2 (potentialMeasure (d + 1) V)) :
    potentialPiVandermondeL2Equiv (d+1) hn hV.continuous hfin
      (potentialHolomorphicQuotientProjection hn hV hfin u) =
    planarPiBergmanProjection (d+1) V hV
      (potentialPiVandermondeL2Equiv (d+1) hn hV.continuous hfin u) := by
  unfold potentialHolomorphicQuotientProjection
  exact LinearIsometryEquiv.apply_symm_apply _ _

theorem potentialHolomorphicQuotientProjection_adjoint {d : ℕ} (hn : 0 < d + 1)
    {V : Potential} (hV : ContDiff ℝ 2 V) (hfin : potentialPartition (d + 1) V < ⊤) :
    (potentialHolomorphicQuotientProjection hn hV hfin).adjoint =
      potentialHolomorphicQuotientProjection hn hV hfin := by
  exact unitary_conjugate_projection_adjoint
    (potentialPiVandermondeL2Equiv (d+1) hn hV.continuous hfin)
    (planarPiBergmanProjection (m := d) (d+1) V hV)
    (planarPiBergmanProjection_adjoint (m := d) (d+1) V hV)

theorem potentialHolomorphicQuotientProjection_idempotent {d : ℕ} (hn : 0 < d + 1)
    {V : Potential} (hV : ContDiff ℝ 2 V) (hfin : potentialPartition (d + 1) V < ⊤) :
    (potentialHolomorphicQuotientProjection hn hV hfin).comp
      (potentialHolomorphicQuotientProjection hn hV hfin) =
      potentialHolomorphicQuotientProjection hn hV hfin := by
  apply ContinuousLinearMap.ext
  intro u
  apply (potentialPiVandermondeL2Equiv (d+1) hn hV.continuous hfin).injective
  change potentialPiVandermondeL2Equiv (d+1) hn hV.continuous hfin
    (potentialHolomorphicQuotientProjection hn hV hfin
      (potentialHolomorphicQuotientProjection hn hV hfin u)) = _
  rw [potentialHolomorphicQuotientProjection_gauge, potentialHolomorphicQuotientProjection_gauge]
  exact DFunLike.congr_fun (planarPiBergmanProjection_idempotent (d+1) V hV) _

theorem potentialHolomorphicQuotientProjection_residual_norm {d : ℕ} (hn : 0 < d + 1)
    {V : Potential} (hV : ContDiff ℝ 2 V) (hfin : potentialPartition (d + 1) V < ⊤)
    (u : Lp ℂ 2 (potentialMeasure (d + 1) V)) :
    ‖u - potentialHolomorphicQuotientProjection hn hV hfin u‖ =
      ‖potentialPiVandermondeL2Equiv (d+1) hn hV.continuous hfin u -
        planarPiBergmanProjection (d+1) V hV
          (potentialPiVandermondeL2Equiv (d+1) hn hV.continuous hfin u)‖ := by
  rw [← (potentialPiVandermondeL2Equiv (d+1) hn hV.continuous hfin).norm_map
    (u - potentialHolomorphicQuotientProjection hn hV hfin u), map_sub,
    potentialHolomorphicQuotientProjection_gauge]

theorem unitary_conjugate_projection_intertwines
    {H K : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (E : H ≃ₗᵢ[ℂ] K) (P : K →L[ℂ] K) (U : H →L[ℂ] H) (A : K →L[ℂ] K)
    (c : ℂ) (hc : c ≠ 0) (hE : ∀ x, A (E x) = c • E (U x))
    (hP : P.comp A = A.comp P) (x : H) :
    U (E.symm (P (E x))) = E.symm (P (E (U x))) := by
  apply E.injective
  have hh : c • E (U (E.symm (P (E x)))) = c • P (E (U x)) := by
    calc
      _ = A (E (E.symm (P (E x)))) := (hE _).symm
      _ = A (P (E x)) := by rw [E.apply_symm_apply]
      _ = P (A (E x)) := (DFunLike.congr_fun hP (E x)).symm
      _ = P (c • E (U x)) := by rw [hE]
      _ = c • P (E (U x)) := P.map_smul _ _
  have ht := congrArg (fun y => c⁻¹ • y) hh
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul, E.apply_symm_apply] using ht

theorem potentialHolomorphicQuotientProjection_phase_intertwines {d : ℕ} (hn : 0 < d + 1)
    {V : Potential} (hV : ContDiff ℝ 2 V) (hrot : IsRotationalPotential V)
    (hfin : potentialPartition (d + 1) V < ⊤) (a : ℂ) (ha : ‖a‖ = 1)
    (u : Lp ℂ 2 (potentialMeasure (d + 1) V)) :
    potentialGlobalPhaseL2 (d+1) hV.continuous hrot a ha
      (potentialHolomorphicQuotientProjection hn hV hfin u) =
    potentialHolomorphicQuotientProjection hn hV hfin
      (potentialGlobalPhaseL2 (d+1) hV.continuous hrot a ha u) := by
  have han : a ≠ 0 := by intro h; simp [h] at ha
  exact unitary_conjugate_projection_intertwines
    (potentialPiVandermondeL2Equiv (d+1) hn hV.continuous hfin)
    (planarPiBergmanProjection (m := d) (d+1) V hV)
    (potentialGlobalPhaseL2 (d+1) hV.continuous hrot a ha).toContinuousLinearMap
    (volumeGlobalPhaseL2 a ha).toContinuousLinearMap
    (a ^ vandermondeDegree (d+1)) (pow_ne_zero _ han)
    (volumeGlobalPhaseL2_potentialVandermonde hn hV.continuous hrot hfin a ha)
    (planarPiBergmanProjection_commutes_globalPhase (m := d) (d+1) V hV hrot a ha) u

end
end GinibrePoincare
