/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibrePhaseRegularSobolev.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreRadialLocalSobolev

/-! # Radial local regularity wherever independent phases can remove collisions

The phase-regular open set consists exactly of configurations with at most one
zero coordinate. The remaining exceptional sets have two zero coordinates.
-/


@[expose] public section


open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

/-- Configurations that can be moved off collisions by independent unit phases. -/
def PhaseRegular (n : ℕ) (z : Configuration n) : Prop :=
  ∃ a : Fin n → ℂ, (∀ i, ‖a i‖ = 1) ∧ CollisionFree (coordinatePhase a z)

/-- Phase regularity is an open condition. -/
theorem isOpen_phaseRegular (n : ℕ) : IsOpen {z | PhaseRegular n z} := by
  let A := {a : Fin n → ℂ // ∀ i, ‖a i‖ = 1}
  have he : {z | PhaseRegular n z} =
      ⋃ a : A, (coordinatePhaseCLE n a.val a.property) ⁻¹' {z | CollisionFree z} := by
    ext z
    constructor
    · rintro ⟨a, ha, hs⟩
      exact Set.mem_iUnion.mpr ⟨⟨a, ha⟩, hs⟩
    · intro hz
      obtain ⟨a, hs⟩ := Set.mem_iUnion.mp hz
      exact ⟨a.val, a.property, hs⟩
  rw [he]
  exact isOpen_iUnion fun a => (isOpen_collisionFree n).preimage
    (coordinatePhaseCLE n a.val a.property).continuous

/-- Unit phases can remove collisions precisely when no two coordinates are zero. -/
theorem phaseRegular_iff_zero_injective (n : ℕ) (hn : 0 < n) (z : Configuration n) :
    PhaseRegular n z ↔ ∀ i j, z i = 0 → z j = 0 → i = j := by
  constructor
  · rintro ⟨a, ha, hs⟩ i j hi hj
    apply hs
    simp [coordinatePhase, hi, hj]
  · exact exists_coordinatePhase_collisionFree_of_zero_injective n hn z

/-- In particular all configurations with nonzero coordinates are phase regular. -/
theorem phaseRegular_of_nonzero (n : ℕ) (hn : 0 < n) (z : Configuration n)
    (hz : ∀ i, z i ≠ 0) : PhaseRegular n z :=
  exists_coordinatePhase_collisionFree n hn z hz

/-- Phase invariant local integrability extends to the entire phase-regular set. -/
theorem phase_invariant_locallyIntegrable_phaseRegular (n : ℕ)
    (F : Configuration n → ℝ)
    (hF : LocallyIntegrableOn F {z | CollisionFree z} volume)
    (hp : ∀ a : Fin n → ℂ, ∀ _ha : ∀ i, ‖a i‖ = 1,
      ∀ᵐ z ∂(volume : Measure (Configuration n)), F (coordinatePhase a z) = F z) :
    LocallyIntegrableOn F {z | PhaseRegular n z} volume := by
  intro z hz
  obtain ⟨a, ha, hs⟩ := hz
  let e := coordinatePhaseCLE n a ha
  have hc := locallyIntegrableOn_comp_volume_equiv n e
    (measurePreserving_coordinatePhaseCLE_volume n a ha)
    {z | CollisionFree z} (isOpen_collisionFree n) F hF
  have he : (F ∘ e) =ᵐ[volume] F := hp a ha
  have hl : LocallyIntegrableOn F (e ⁻¹' {z | CollisionFree z}) volume :=
    hc.congr (ae_restrict_of_ae he)
  have hm : z ∈ e ⁻¹' {z | CollisionFree z} := hs
  have hi := hl z hm
  rw [nhdsWithin_eq_nhds.mpr ((isOpen_collisionFree n).preimage e.continuous |>.mem_nhds hm)] at hi
  exact hi.filter_mono nhdsWithin_le_nhds

/-- Radial weighted L² values have locally integrable ordinary squared norm
through all collisions except simultaneous zeroes of two coordinates. -/
theorem ginibre_radial_value_norm_sq_locallyIntegrable_phaseRegular (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n)) (f : Configuration n → ℝ)
    (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i))) :
    LocallyIntegrableOn (fun z => ‖u z‖ ^ 2) {z | PhaseRegular n z} volume := by
  apply phase_invariant_locallyIntegrable_phaseRegular n _
    (ginibre_memLp_norm_sq_locallyIntegrable_collisionFree hn u (Lp.memLp u))
  intro a ha
  filter_upwards [ginibre_radial_L2_phase_ae n hn u f hf hr a ha] with z hz
  rw [hz]

/-- The actual radial weak gradient has the same local squared-norm regularity. -/
theorem ginibre_radial_gradient_norm_sq_locallyIntegrable_phaseRegular (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ) (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i))) :
    LocallyIntegrableOn (fun z => ‖g z‖ ^ 2) {z | PhaseRegular n z} volume := by
  apply phase_invariant_locallyIntegrable_phaseRegular n _
    (ginibre_memLp_norm_sq_locallyIntegrable_collisionFree hn g (Lp.memLp g))
  intro a ha
  filter_upwards [ginibre_radial_weak_gradient_norm_phase_ae n hn u g hg f hf hr a ha] with z hz
  rw [hz]

/-- Radial weighted values belong to ordinary L² on every phase-regular compact set. -/
theorem ginibre_radial_value_memLp_compact_phaseRegular (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n)) (f : Configuration n → ℝ)
    (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i)))
    (K : Set (Configuration n)) (hK : IsCompact K) (hs : K ⊆ {z | PhaseRegular n z}) :
    MemLp (u : Configuration n → ℝ) 2 (volume.restrict K) := by
  have hm : AEStronglyMeasurable (u : Configuration n → ℝ) volume :=
    AEStronglyMeasurable.mono_ac (volume_absolutelyContinuous_ginibreMeasure n hn)
      (Lp.aestronglyMeasurable u)
  apply (memLp_two_iff_integrable_sq_norm hm.restrict).mpr
  exact (ginibre_radial_value_norm_sq_locallyIntegrable_phaseRegular n hn u f hf
    hr).integrableOn_compact_subset hs hK

/-- The actual gradient belongs to ordinary L² on every phase-regular compact set. -/
theorem ginibre_radial_gradient_memLp_compact_phaseRegular (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ) (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i)))
    (K : Set (Configuration n)) (hK : IsCompact K) (hs : K ⊆ {z | PhaseRegular n z}) :
    MemLp (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) 2 (volume.restrict K) := by
  have hm : AEStronglyMeasurable
      (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) volume :=
    AEStronglyMeasurable.mono_ac (volume_absolutelyContinuous_ginibreMeasure n hn)
      (Lp.aestronglyMeasurable g)
  apply (memLp_two_iff_integrable_sq_norm hm.restrict).mpr
  exact (ginibre_radial_gradient_norm_sq_locallyIntegrable_phaseRegular n hn u g hg f hf
    hr).integrableOn_compact_subset hs hK

end
end GinibrePoincare
