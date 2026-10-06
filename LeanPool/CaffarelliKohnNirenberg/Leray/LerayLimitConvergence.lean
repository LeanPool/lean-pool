/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitSpaceTime
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet

/-!
# Leray Limit Convergence

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- Whole-space tails and the uniform energy-space bound yield all
subcritical strong convergences, including strong convergence of the
regularized transport fields in L³. -/
theorem lerayLimit_spaceTime_outputs
    (T : ℝ) (F : ℕ → ParabolicPoint → Vec3) (u : ParabolicPoint → Vec3)
    (J : ℕ → (ParabolicPoint → Vec3) → ParabolicPoint → Vec3)
    (K : ℕ → Set ParabolicPoint)
    (hK : ∀ m, MeasurableSet (K m))
    (hlocal : ∀ m, Tendsto
      (fun n => eLpNorm (F n - u) 2
        (((volume : Measure ParabolicPoint).restrict
          (spaceTimeSet Set.univ (Ioo 0 T))).restrict (K m)))
      atTop (𝓝 0))
    (hFtail : ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ m : ℕ in atTop,
      ∀ n, eLpNorm ((K m)ᶜ.indicator (F n)) 2
        ((volume : Measure ParabolicPoint).restrict
          (spaceTimeSet Set.univ (Ioo 0 T))) ≤ ε)
    (huTail : ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ m : ℕ in atTop,
      eLpNorm ((K m)ᶜ.indicator u) 2
        ((volume : Measure ParabolicPoint).restrict
          (spaceTimeSet Set.univ (Ioo 0 T))) ≤ ε)
    (hEnergy : ∀ n, MemLp (F n) (ENNReal.ofReal 2)
      ((volume : Measure ParabolicPoint).restrict
        (spaceTimeSet Set.univ (Ioo 0 T))))
    (hTenThirds : ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ n,
      eLpNorm (F n) (ENNReal.ofReal (10 / 3 : ℝ))
        ((volume : Measure ParabolicPoint).restrict
          (spaceTimeSet Set.univ (Ioo 0 T))) ≤ B)
    (hFthree : ∀ n, MemLp (F n) (ENNReal.ofReal 3)
      ((volume : Measure ParabolicPoint).restrict
        (spaceTimeSet Set.univ (Ioo 0 T))))
    (hJthree : ∀ n, MemLp (J n (F n)) (ENNReal.ofReal 3)
      ((volume : Measure ParabolicPoint).restrict
        (spaceTimeSet Set.univ (Ioo 0 T))))
    (hJu : Tendsto
      (fun n => eLpNorm (J n u - u) 3
        ((volume : Measure ParabolicPoint).restrict
          (spaceTimeSet Set.univ (Ioo 0 T)))) atTop (𝓝 0))
    (hcontract : ∀ n,
      eLpNorm (J n (F n) - J n u) 3
        ((volume : Measure ParabolicPoint).restrict
          (spaceTimeSet Set.univ (Ioo 0 T))) ≤
      eLpNorm (F n - u) 3
        ((volume : Measure ParabolicPoint).restrict
          (spaceTimeSet Set.univ (Ioo 0 T)))) :
    (∀ q : ℝ, 2 ≤ q → q < 10 / 3 →
      Tendsto (fun n => eLpNorm (F n - u) (ENNReal.ofReal q)
        ((volume : Measure ParabolicPoint).restrict
          (spaceTimeSet Set.univ (Ioo 0 T)))) atTop (𝓝 0)) ∧
    MemLp u (ENNReal.ofReal 3)
      ((volume : Measure ParabolicPoint).restrict
        (spaceTimeSet Set.univ (Ioo 0 T))) ∧
    (∀ n, MemLp (J n (F n)) (ENNReal.ofReal 3)
      ((volume : Measure ParabolicPoint).restrict
        (spaceTimeSet Set.univ (Ioo 0 T)))) ∧
    Tendsto (fun n => eLpNorm (J n (F n) - u) 3
      ((volume : Measure ParabolicPoint).restrict
        (spaceTimeSet Set.univ (Ioo 0 T)))) atTop (𝓝 0) := by
  have hLq := lerayLimit_spaceTime_strongLp_of_local_compactness_and_tails
    T F u K hK hlocal hFtail huTail hEnergy hTenThirds
  have hLthree := hLq 3 (by norm_num) (by norm_num)
  have hLthree' : Tendsto
      (fun n => eLpNorm (F n - u) 3
        ((volume : Measure ParabolicPoint).restrict
          (spaceTimeSet Set.univ (Ioo 0 T)))) atTop (𝓝 0) := by
    simpa using hLthree
  have huThree : MemLp u (ENNReal.ofReal 3)
      ((volume : Measure ParabolicPoint).restrict
        (spaceTimeSet Set.univ (Ioo 0 T))) := by
    have hsub : ∀ᶠ n : ℕ in atTop,
        eLpNorm (F n - u) (ENNReal.ofReal 3)
          ((volume : Measure ParabolicPoint).restrict
            (spaceTimeSet Set.univ (Ioo 0 T))) < 1 := by
      have hsmall := (ENNReal.tendsto_nhds_zero.mp hLthree)
        (1 / 2 : ℝ≥0∞) (by norm_num)
      filter_upwards [hsmall] with n hn
      exact lt_of_le_of_lt hn (by norm_num)
    obtain ⟨n, hn⟩ := hsub.exists
    have hdiff : MemLp (F n - u) (ENNReal.ofReal 3)
        ((volume : Measure ParabolicPoint).restrict
          (spaceTimeSet Set.univ (Ioo 0 T))) := by
      rw [memLp_iff]
      exact hn.trans (by norm_num)
    have heq : u = F n - (F n - u) := by
      funext z
      change u z = F n z - (F n z - u z)
      abel
    rw [heq]
    exact (hFthree n).sub hdiff
  have hJthreeConv :=
    lerayLimit_strongLp_of_contraction_and_fixed_limit F u J hLthree' hJu
      hcontract
  exact ⟨hLq, huThree, hJthree, hJthreeConv⟩

end CKN.Leray

end
