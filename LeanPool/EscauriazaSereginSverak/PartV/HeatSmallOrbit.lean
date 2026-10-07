/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.HeatCriticalMain

/-!
# The small heat orbit

This file proves `lem:pv-small-heat`: for `a ∈ L² ∩ L³` the norms of the heat
orbit in `L⁵(Q_τ)` and `L⁴(Q_τ)` tend to zero as `τ ↓ 0`.  By
`lem:pv-heat-critical` the orbit lies in both spaces on the slab `Q_1`, and the
slabs `Q_τ` decrease to the empty set, so the claim is the absolute continuity
of the integral.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic CKN.Foundation.Heat


noncomputable section

namespace ESS

/-- A function lying in `Lʳ` of every slab `ℝ³ × (0, τ)` has `Lʳ` norms on
these slabs tending to zero as `τ ↓ 0`. -/
theorem tendsto_eLpNorm_spaceTimeSet_zero {E : Type*} [NormedAddCommGroup E]
    {F : ParabolicPoint → E} {r : ℝ≥0∞} (hr0 : r ≠ 0) (hrtop : r ≠ ∞)
    (hF : ∀ τ : ℝ, 0 < τ →
      MemLp F r (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) :
    Tendsto (fun τ : ℝ =>
        eLpNorm F r (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  set Q : ℝ → Set ParabolicPoint := fun τ => spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)
  have hrpos : 0 < r.toReal := ENNReal.toReal_pos hr0 hrtop
  let ν : Measure ParabolicPoint := volume.withDensity (fun z => ‖F z‖ₑ ^ r.toReal)
  have hQmeas (τ : ℝ) : MeasurableSet (Q τ) := MeasurableSet.univ.prod measurableSet_Ioo
  have hν (τ : ℝ) : ν (Q τ) = ∫⁻ z in Q τ, ‖F z‖ₑ ^ r.toReal :=
    withDensity_apply _ (hQmeas τ)
  have hmono : ∀ i j : ℝ, 0 < i → i ≤ j → Q i ⊆ Q j := by
    intro i j _ hij z hz
    exact ⟨hz.1, hz.2.1, lt_of_lt_of_le hz.2.2 hij⟩
  have hnorm {τ : ℝ} (hτ : 0 < τ) :
      eLpNorm F r (volume.restrict (Q τ)) = ν (Q τ) ^ (1 / r.toReal) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 hrtop (hF τ hτ).aestronglyMeasurable, hν]
  have hfin : ∃ τ > (0 : ℝ), ν (Q τ) ≠ ⊤ := by
    refine ⟨1, one_pos, ?_⟩
    have hlt := (hF 1 one_pos).eLpNorm_lt_top
    rw [hnorm one_pos] at hlt
    exact (ENNReal.rpow_lt_top_iff_of_pos (by positivity)).1 hlt |>.ne
  have hlim := tendsto_measure_biInter_gt (μ := ν) (s := Q) (a := 0)
    (fun τ _ => (hQmeas τ).nullMeasurableSet) hmono hfin
  have hempty : (⋂ τ, ⋂ (_ : τ > (0 : ℝ)), Q τ) = ∅ := by
    ext z
    simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
    by_cases hpos : 0 < z.2
    · exact ⟨z.2, hpos, fun hz => lt_irrefl _ hz.2.2⟩
    · exact ⟨1, one_pos, fun hz => hpos hz.2.1⟩
  rw [hempty, measure_empty] at hlim
  have hpow : Tendsto (fun τ => ν (Q τ) ^ (1 / r.toReal)) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have h := ((ENNReal.continuous_rpow_const (y := 1 / r.toReal)).tendsto 0).comp hlim
    rwa [ENNReal.zero_rpow_of_pos (by positivity)] at h
  refine (tendsto_congr' ?_).2 hpow
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  exact hnorm hτ

/-- `lem:pv-small-heat`: for `a ∈ L² ∩ L³`,
`‖S(·)a‖_{L⁵(Q_τ)} + ‖S(·)a‖_{L⁴(Q_τ)} → 0` as `τ ↓ 0`. -/
theorem pvSmallHeat {a : Vec3 → Vec3} (ha2 : MemLp a 2 volume) (ha3 : MemLp a 3 volume) :
    Tendsto (fun τ : ℝ =>
        eLpNorm (heatOrbit a) 5
            (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) +
          eLpNorm (heatOrbit a) 4
            (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have h5 := tendsto_eLpNorm_spaceTimeSet_zero (F := heatOrbit a) (r := 5)
    (by norm_num) (by norm_num) fun τ hτ => heatOrbit_memLp_five ha3 hτ
  have h4 := tendsto_eLpNorm_spaceTimeSet_zero (F := heatOrbit a) (r := 4)
    (by norm_num) (by norm_num) fun τ hτ => heatOrbit_memLp_four ha2 ha3 hτ
  simpa using h5.add h4

end ESS

end
