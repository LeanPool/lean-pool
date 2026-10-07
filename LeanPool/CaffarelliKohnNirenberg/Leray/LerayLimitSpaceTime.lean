/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitInterpolation
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitTightness
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet

/-!
# Whole-space convergence in the Leray limit

Uniform spatial tightness upgrades the local compactness limit to a global
space-time limit, after which the energy-space bound gives the subcritical
Lebesgue convergence in `prop:leray-limit`.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- Local compactness and uniform tails yield the whole-space subcritical
convergence on a finite time slab, as in `prop:leray-limit`. -/
theorem lerayLimit_spaceTime_strongLp_of_local_compactness_and_tails
    (T : ℝ) (F : ℕ → ParabolicPoint → Vec3) (u : ParabolicPoint → Vec3)
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
          (spaceTimeSet Set.univ (Ioo 0 T))) ≤ B) :
    ∀ q : ℝ, 2 ≤ q → q < 10 / 3 →
      Tendsto
        (fun n => eLpNorm (F n - u) (ENNReal.ofReal q)
          ((volume : Measure ParabolicPoint).restrict
            (spaceTimeSet Set.univ (Ioo 0 T)))) atTop (𝓝 0) := by
  let μ : Measure ParabolicPoint :=
    (volume : Measure ParabolicPoint).restrict
      (spaceTimeSet Set.univ (Ioo 0 T))
  have hL2 : Tendsto (fun n => eLpNorm (F n - u) 2 μ) atTop (𝓝 0) :=
    lerayLimit_eLpNorm_tendsto_of_local_and_uniform_tails
      F u K hK hlocal hFtail huTail
  have hL2' : Tendsto
      (fun n => eLpNorm (F n - u) (ENNReal.ofReal 2) μ) atTop (𝓝 0) := by
    simpa using hL2
  exact lerayLimit_strongLp_of_strongL2_and_uniform_high
    (F := F) (G := u) (μ := μ) hEnergy (hbound := hTenThirds) hL2'

/-- Strong convergence of mollified fields follows from contraction and the
approximate-identity limit for the fixed field. This is the final estimate in
the `L³` assertion of `prop:leray-limit`. -/
theorem lerayLimit_strongLp_of_contraction_and_fixed_limit
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} (F : ℕ → α → E) (u : α → E)
    (J : ℕ → (α → E) → α → E)
    (hF : Tendsto (fun n => eLpNorm (F n - u) 3 μ) atTop (𝓝 0))
    (hJu : Tendsto (fun n => eLpNorm (J n u - u) 3 μ) atTop (𝓝 0))
    (hcontract : ∀ n,
      eLpNorm (J n (F n) - J n u) 3 μ ≤ eLpNorm (F n - u) 3 μ) :
    Tendsto (fun n => eLpNorm (J n (F n) - u) 3 μ) atTop (𝓝 0) := by
  have hsum : Tendsto
      (fun n => eLpNorm (F n - u) 3 μ +
        (eLpNorm (F n - u) 3 μ + eLpNorm (J n u - u) 3 μ))
      atTop (𝓝 0) := by
    have hadd := hF.add (hF.add hJu)
    simpa only [zero_add] using hadd
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hev := (ENNReal.tendsto_nhds_zero.mp hsum) ε hε
  filter_upwards [hev] with n hn
  have hsplit : J n (F n) - u =
      (J n (F n) - J n u) + (J n u - u) := by
    funext x
    change J n (F n) x - u x =
      (J n (F n) x - J n u x) + (J n u x - u x)
    abel
  calc
    eLpNorm (J n (F n) - u) 3 μ ≤
        eLpNorm (J n (F n) - J n u) 3 μ + eLpNorm (J n u - u) 3 μ := by
      calc
        _ = eLpNorm ((J n (F n) - J n u) + (J n u - u)) 3 μ := by
          rw [hsplit]
        _ ≤ eLpNorm (J n (F n) - J n u) 3 μ + eLpNorm (J n u - u) 3 μ :=
          eLpNorm_add_le (p := 3) (μ := μ)
            (by norm_num : (1 : ℝ≥0∞) ≤ 3)
    _ ≤ eLpNorm (F n - u) 3 μ + eLpNorm (J n u - u) 3 μ :=
      add_le_add (hcontract n) le_rfl
    _ ≤ eLpNorm (F n - u) 3 μ +
        (eLpNorm (F n - u) 3 μ + eLpNorm (J n u - u) 3 μ) :=
      calc
        _ ≤ _ + eLpNorm (F n - u) 3 μ :=
          le_add_of_nonneg_right (by positivity)
        _ = _ := by rw [add_comm]
    _ ≤ ε := hn

end CKN.Leray

end
