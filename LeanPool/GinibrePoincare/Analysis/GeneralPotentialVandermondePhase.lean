/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralPotentialVandermondePhase.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialVandermondeSymmetry

/-!
# General potential Vandermonde phase

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `volumeGlobalPhaseL2_potentialVandermonde`.
-/

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- Composition with the global phase rotation `z ↦ u z` (with `‖u‖ = 1`), as a linear
isometry of `L²` of Lebesgue measure on configurations. -/
def volumeGlobalPhaseL2 {n : ℕ} (u : ℂ) (hu : ‖u‖ = 1) :
    Lp ℂ 2 (configurationVolume n) →ₗᵢ[ℂ] Lp ℂ 2 (configurationVolume n) :=
  Lp.compMeasurePreservingₗᵢ ℂ (globalPhase u) (measurePreserving_globalPhase_configurationVolume n
      u hu)

/-- Composition with the global phase rotation `z ↦ u z` (with `‖u‖ = 1`), as a linear
isometry of `L²(potentialMeasure n V)` for a rotation-invariant potential `V`. -/
def potentialGlobalPhaseL2 (n : ℕ) {V : Potential} (hV : Continuous V)
    (hrot : IsRotationalPotential V) (u : ℂ) (hu : ‖u‖ = 1) :
    Lp ℂ 2 (potentialMeasure n V) →ₗᵢ[ℂ] Lp ℂ 2 (potentialMeasure n V) :=
  Lp.compMeasurePreservingₗᵢ ℂ (globalPhase u) (measurePreserving_globalPhase_potentialMeasure n hV
      hrot u hu)

theorem potentialVandermondeMultiplier_globalPhase (n : ℕ) (V : Potential)
    (hrot : IsRotationalPotential V) (u : ℂ) (hu : ‖u‖ = 1) (z : Configuration n) :
    potentialVandermondeMultiplier n V (globalPhase u z) =
      u ^ vandermondeDegree n * potentialVandermondeMultiplier n V z := by
  have hs : (∑ i : Fin n, V (globalPhase u z i)) = ∑ i : Fin n, V (z i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact hrot u (z i) hu
  unfold potentialVandermondeMultiplier
  rw [hs, vandermonde_globalPhase, ← vandermondeDegree_eq_sum_Ioi_card]
  ring

theorem volumeGlobalPhaseL2_potentialVandermonde {n : ℕ} (hn : 0 < n) {V : Potential} (hV :
    Continuous V)
    (hrot : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤)
    (u : ℂ) (hu : ‖u‖ = 1) (x : Lp ℂ 2 (potentialMeasure n V)) :
    volumeGlobalPhaseL2 u hu (potentialVandermondeL2 n hn hV hfin x) =
      u ^ vandermondeDegree n •
        potentialVandermondeL2 n hn hV hfin (potentialGlobalPhaseL2 n hV hrot u hu x) := by
  apply Lp.ext
  have hsrc := (measurePreserving_globalPhase_configurationVolume n u
      hu).quasiMeasurePreserving.ae_eq_comp (potentialVandermondeL2_coeFn_public n hn hV hfin x)
  have hcomp := (configurationVolume_absolutelyContinuous_potentialMeasure n hn hV hfin).ae_eq
      (Lp.coeFn_compMeasurePreserving x (measurePreserving_globalPhase_potentialMeasure n hV hrot u
          hu))
  filter_upwards [Lp.coeFn_compMeasurePreserving (potentialVandermondeL2 n hn hV hfin x)
      (measurePreserving_globalPhase_configurationVolume n u hu), hsrc,
    Lp.coeFn_smul (u ^ vandermondeDegree n)
      (potentialVandermondeL2 n hn hV hfin (potentialGlobalPhaseL2 n hV hrot u hu x)),
    potentialVandermondeL2_coeFn_public n hn hV hfin (potentialGlobalPhaseL2 n hV hrot u hu x),
    hcomp] with z hleft hsource hright htarget hx
  change (volumeGlobalPhaseL2 u hu (potentialVandermondeL2 n hn hV hfin x)) z =
    (potentialVandermondeL2 n hn hV hfin x) (globalPhase u z) at hleft
  rw [hleft, hright]
  change (potentialVandermondeL2 n hn hV hfin x) (globalPhase u z) =
    (u ^ vandermondeDegree n) * (potentialVandermondeL2 n hn hV hfin (potentialGlobalPhaseL2 n hV
        hrot u hu x)) z
  change (potentialVandermondeL2 n hn hV hfin x) (globalPhase u z) =
    potentialVandermondeMultiplier n V (globalPhase u z) * x (globalPhase u z) at hsource
  change (potentialGlobalPhaseL2 n hV hrot u hu x) z = x (globalPhase u z) at hx
  rw [hsource, htarget, hx]
  rw [potentialVandermondeMultiplier_globalPhase n V hrot u hu z]
  ring

end
end GinibrePoincare
