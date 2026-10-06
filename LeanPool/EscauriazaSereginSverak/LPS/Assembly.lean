/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.EnergyEquality
public import LeanPool.EscauriazaSereginSverak.LPS.GoodTimes
public import LeanPool.EscauriazaSereginSverak.LPS.StrongSolution

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A positive-time restart may be chosen where both the good-slice
conditions and the almost-every-time energy equality hold (`lem:lps-good-times`
and `lem:lps-energy-equality`). -/
theorem lps_good_energy_time_in_interval
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du)
    (hSerrin :
      (∃ s : ℝ, 3 < s ∧
        (∫⁻ t in Ioo (0 : ℝ) T,
          (∫⁻ x : Vec3,
            ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s) ^
              ((2 * s / (s - 3)) / s)) < ⊤) ∨
      (∫⁻ t in Ioo (0 : ℝ) T,
        (essSup
          (fun x : Vec3 => ENNReal.ofReal (vec3EuclideanNorm (u (x, t))))
          (volume : Measure Vec3)) ^ (2 : ℝ)) < ⊤)
    {δ : ℝ} (hδ : 0 < δ) (hδT : δ ≤ T) :
    ∃ t, t ∈ Ioo (0 : ℝ) δ ∧ IsLpsGoodTime u Du t ∧
      (∫ x : Vec3, ∑ k : Fin 3, u (x, t) k * u (x, t) k) -
          (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) =
        -2 * ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
          ∑ k : Fin 3, ∑ j : Fin 3, Du q k j * Du q k j := by
  let μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) T)
  have hGood : ∀ᵐ t ∂μ, IsLpsGoodTime u Du t := lps_good_times_ae hLH
  have hEnergy := lps_serrin_energy_equality hLH hSerrin
  have hBoth : ∀ᵐ t ∂μ,
      IsLpsGoodTime u Du t ∧
        (∫ x : Vec3, ∑ k : Fin 3, u (x, t) k * u (x, t) k) -
            (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) =
          -2 * ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            ∑ k : Fin 3, ∑ j : Fin 3, Du q k j * Du q k j :=
    hGood.and hEnergy
  have hsub : Ioo (0 : ℝ) δ ⊆ Ioo (0 : ℝ) T := by
    intro t ht
    exact ⟨ht.1, lt_of_lt_of_le ht.2 hδT⟩
  have hμpos : μ (Ioo (0 : ℝ) δ) ≠ 0 := by
    have hpos : 0 < volume (Ioo (0 : ℝ) δ) :=
      (Measure.measure_Ioo_pos volume).2 hδ
    change (volume.restrict (Ioo (0 : ℝ) T)) (Ioo (0 : ℝ) δ) ≠ 0
    rw [Measure.restrict_apply measurableSet_Ioo]
    have hinter : Ioo (0 : ℝ) δ ∩ Ioo (0 : ℝ) T = Ioo (0 : ℝ) δ :=
      Set.inter_eq_left.mpr hsub
    rw [hinter]
    exact ne_of_gt hpos
  have hBothSmall : ∀ᵐ t ∂(μ.restrict (Ioo (0 : ℝ) δ)),
      IsLpsGoodTime u Du t ∧
        (∫ x : Vec3, ∑ k : Fin 3, u (x, t) k * u (x, t) k) -
            (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) =
          -2 * ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            ∑ k : Fin 3, ∑ j : Fin 3, Du q k j * Du q k j :=
    ae_restrict_of_ae hBoth
  obtain ⟨t, ht, hPoint⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hμpos hBothSmall
  exact ⟨t, ht, hPoint.1, hPoint.2⟩

/-- Start the local strong solution at a time where both the good-slice
conditions and the Serrin energy identity hold. The local existence theorem is
an input here so that the restart assembly is independent of its provider. -/
theorem lps_local_restart_from_good_energy_time
    (hLocal :
      ∃ c : ℝ, 0 < c ∧
        ∀ (t₀ : ℝ) (b : Vec3 → Vec3)
          (Db : Vec3 → Fin 3 → Vec3),
          IsLpsGoodTime
            (fun z : ParabolicPoint => b z.1)
            (fun z i => Db z.1 i) t₀ →
          ∃ τ : ℝ, 0 < τ ∧
            c * Real.rpow
              (1 + Real.sqrt (∫ x : Vec3,
                (∑ i : Fin 3, (b x i) ^ 2) +
                  ∑ i : Fin 3, ∑ j : Fin 3, (Db x i j) ^ 2))
              (-4 : ℝ) ≤ τ ∧
            ∃ (U : ParabolicPoint → Vec3)
              (DU : ParabolicPoint → Fin 3 → Vec3)
              (p : ParabolicPoint → ℝ),
              IsLpsStrongSolution t₀ (t₀ + τ) U DU p ∧
              (fun x : Vec3 => U (x, t₀)) =ᵐ[volume] b ∧
              Tendsto
                (fun s : ℝ => eLpNorm (fun x : Vec3 => U (x, s) - b x) 2 volume)
                (nhdsWithin t₀ (Ioi t₀)) (nhds 0) ∧
              (∀ s t : ℝ, s ∈ Icc t₀ (t₀ + τ) →
                t ∈ Icc t₀ (t₀ + τ) → s ≤ t →
                (∫ x : Vec3, ∑ i : Fin 3, (U (x, t) i) ^ 2) +
                  2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo s t),
                    ∑ i : Fin 3, ∑ j : Fin 3, (DU z i j) ^ 2 =
                ∫ x : Vec3, ∑ i : Fin 3, (U (x, s) i) ^ 2) ∧
              IsLerayHopfSolution τ b
                (fun z : ParabolicPoint => U (z.1, t₀ + z.2))
                (fun z i => DU (z.1, t₀ + z.2) i))
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du)
    (hSerrin :
      (∃ s : ℝ, 3 < s ∧
        (∫⁻ t in Ioo (0 : ℝ) T,
          (∫⁻ x : Vec3,
            ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s) ^
              ((2 * s / (s - 3)) / s)) < ⊤) ∨
      (∫⁻ t in Ioo (0 : ℝ) T,
        (essSup
          (fun x : Vec3 => ENNReal.ofReal (vec3EuclideanNorm (u (x, t))))
          (volume : Measure Vec3)) ^ (2 : ℝ)) < ⊤)
    {δ : ℝ} (hδ : 0 < δ) (hδT : δ ≤ T) :
    ∃ t₀, t₀ ∈ Ioo (0 : ℝ) δ ∧
      (∫ x : Vec3, ∑ k : Fin 3, u (x, t₀) k * u (x, t₀) k) -
          (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) =
        -2 * ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
          ∑ k : Fin 3, ∑ j : Fin 3, Du q k j * Du q k j ∧
      ∃ τ : ℝ, 0 < τ ∧
        (∃ c : ℝ, 0 < c ∧
          c * Real.rpow
            (1 + Real.sqrt (∫ x : Vec3,
              (∑ i : Fin 3, (u (x, t₀) i) ^ 2) +
                ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, t₀) i j) ^ 2))
            (-4 : ℝ) ≤ τ) ∧
        ∃ (U : ParabolicPoint → Vec3)
          (DU : ParabolicPoint → Fin 3 → Vec3)
          (p : ParabolicPoint → ℝ),
          IsLpsStrongSolution t₀ (t₀ + τ) U DU p ∧
          (fun x : Vec3 => U (x, t₀)) =ᵐ[volume]
            (fun x : Vec3 => u (x, t₀)) ∧
          Tendsto
            (fun s : ℝ =>
              eLpNorm (fun x : Vec3 => U (x, s) - u (x, t₀)) 2 volume)
            (nhdsWithin t₀ (Ioi t₀)) (nhds 0) ∧
          (∀ s t : ℝ, s ∈ Icc t₀ (t₀ + τ) →
            t ∈ Icc t₀ (t₀ + τ) → s ≤ t →
            (∫ x : Vec3, ∑ i : Fin 3, (U (x, t) i) ^ 2) +
              2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo s t),
                ∑ i : Fin 3, ∑ j : Fin 3, (DU z i j) ^ 2 =
            ∫ x : Vec3, ∑ i : Fin 3, (U (x, s) i) ^ 2) ∧
          IsLerayHopfSolution τ (fun x : Vec3 => u (x, t₀))
            (fun z : ParabolicPoint => U (z.1, t₀ + z.2))
            (fun z i => DU (z.1, t₀ + z.2) i) := by
  obtain ⟨c, hc, hLocal⟩ := hLocal
  obtain ⟨t₀, ht₀, hGood, hEnergy⟩ :=
    lps_good_energy_time_in_interval hLH hSerrin hδ hδT
  let b : Vec3 → Vec3 := fun x => u (x, t₀)
  let Db : Vec3 → Fin 3 → Vec3 := fun x i => Du (x, t₀) i
  have hGoodConst :
      IsLpsGoodTime (fun z : ParabolicPoint => b z.1)
        (fun z i => Db z.1 i) t₀ := by
    simpa [IsLpsGoodTime, b, Db] using hGood
  obtain ⟨τ, hτ, hLifetime, U, DU, p, hStrong, hTrace, hLimit, hEnergyLocal,
      hRestartLH⟩ := hLocal t₀ b Db hGoodConst
  refine ⟨t₀, ht₀, hEnergy, τ, hτ, ?_, U, DU, p, hStrong, ?_, ?_,
    hEnergyLocal, ?_⟩
  · refine ⟨c, hc, ?_⟩
    simpa [b, Db] using hLifetime
  · simpa [b] using hTrace
  · simpa [b] using hLimit
  · simpa [b] using hRestartLH

end ESS

end
