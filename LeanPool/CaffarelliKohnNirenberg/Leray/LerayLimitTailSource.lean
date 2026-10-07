/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitInitialTail
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitMain

/-!
# Leray Limit Tail Source

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

variable (ρ : RegMollifierProfile)
variable (uε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → Vec3)

variable (hregTails : ∃ C : ℝ, 0 ≤ C ∧
  ∀ (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ) (hε : 0 < ε)
    (_hεone : ε ≤ 1),
    (∀ R1 R2 t : ℝ, 0 < R1 → R1 < R2 → 0 ≤ t →
      (∫ x in {x : Vec3 | R2 < vec3EuclideanNorm x},
        (vec3EuclideanNorm (uε a ha ε (x, t))) ^ (2 : ℕ)) ≤
        (∫ x in {x : Vec3 | R1 < vec3EuclideanNorm x},
          (vec3EuclideanNorm
            (regUniformMollifiedInitial ρ ε hε a x)) ^ (2 : ℕ)) +
          C * (((eLpNorm a 2 volume).toReal) ^ (2 : ℕ) * t ^ (1 / 2 : ℝ) +
            ((eLpNorm a 2 volume).toReal) ^ (3 : ℕ) * t ^ (1 / 4 : ℝ)) /
            (R2 - R1)) ∧
    (∀ R1 : ℝ, 0 < R1 →
      (∫ x in {x : Vec3 | R1 < vec3EuclideanNorm x},
        (vec3EuclideanNorm (regUniformMollifiedInitial ρ ε hε a x)) ^
          (2 : ℕ)) ≤
        ∫ x in {x : Vec3 | R1 - 1 < vec3EuclideanNorm x},
          (vec3EuclideanNorm (a x)) ^ (2 : ℕ)))

include hregTails in
/-- The regularized exterior estimate and the initial `L²` tail give a
uniformly vanishing spatial tail on every finite positive time interval, as
in `prop:leray-limit`. -/
theorem lerayLimit_regularised_tail_tendsto
    (a : Vec3 → Vec3) (ha : IsInJ a)
    (εseq : ℕ → ℝ) (hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1)
    (T : ℝ) :
    ∃ b : ℕ → ℝ, Tendsto b atTop (𝓝 0) ∧
      ∀ (k n : ℕ) (t : ℝ), t ∈ Icc 0 T →
        (∫ x in {x : Vec3 | 2 * ((n : ℝ) + 1) < vec3EuclideanNorm x},
          (vec3EuclideanNorm (uε a ha (εseq k) (x, t))) ^ (2 : ℕ)) ≤ b n := by
  obtain ⟨C, hC, htailAll⟩ := hregTails
  have hinitialTail := lerayLimit_initialEnergyTail_tendsto_zero a ha.1
  let E : ℝ := (eLpNorm a 2 volume).toReal
  let K : ℝ := E ^ (2 : ℕ) * T ^ (1 / 2 : ℝ) +
    E ^ (3 : ℕ) * T ^ (1 / 4 : ℝ)
  let b : ℕ → ℝ := fun n =>
    (∫ x in {x : Vec3 | (n : ℝ) < vec3EuclideanNorm x},
      (vec3EuclideanNorm (a x)) ^ (2 : ℕ)) +
      C * K / ((n : ℝ) + 1)
  have hdiv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹)
      atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hresidual : Tendsto (fun n : ℕ => C * K * ((n : ℝ) + 1)⁻¹)
      atTop (𝓝 0) := by
    simpa [mul_comm] using hdiv.const_mul (C * K)
  have hb : Tendsto b atTop (𝓝 0) := by
    dsimp [b]
    have hsum := hinitialTail.add hresidual
    simpa [K, E, div_eq_mul_inv, add_zero] using hsum
  refine ⟨b, hb, ?_⟩
  intro k n t ht
  have ht0 : 0 ≤ t := ht.1
  have htT : t ≤ T := ht.2
  let R1 : ℝ := (n : ℝ) + 1
  let R2 : ℝ := 2 * ((n : ℝ) + 1)
  have hR1 : 0 < R1 := by dsimp [R1]; positivity
  have hR12 : R1 < R2 := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    dsimp [R1, R2]
    nlinarith only [hn]
  obtain ⟨htail, hinitial⟩ := htailAll a ha (εseq k) (hseq k).1 (hseq k).2
  have htailn := htail R1 R2 t hR1 hR12 ht0
  have hinitialn := hinitial R1 hR1
  have hpowHalf : t ^ (1 / 2 : ℝ) ≤ T ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow ht0 htT (by norm_num)
  have hpowQuarter : t ^ (1 / 4 : ℝ) ≤ T ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow ht0 htT (by norm_num)
  have htime :
      E ^ (2 : ℕ) * t ^ (1 / 2 : ℝ) + E ^ (3 : ℕ) * t ^ (1 / 4 : ℝ) ≤ K := by
    dsimp [K]
    gcongr
  have hden : R2 - R1 = (n : ℝ) + 1 := by
    dsimp [R1, R2]
    ring
  have hR1sub : R1 - 1 = (n : ℝ) := by
    dsimp [R1]
    ring
  have hinitRewrite :
      (∫ x in {x : Vec3 | R1 < vec3EuclideanNorm x},
        (vec3EuclideanNorm (regUniformMollifiedInitial ρ (εseq k)
          (hseq k).1 a x)) ^ (2 : ℕ)) ≤
      ∫ x in {x : Vec3 | (n : ℝ) < vec3EuclideanNorm x},
        (vec3EuclideanNorm (a x)) ^ (2 : ℕ) := by
    simpa only [hR1sub] using hinitialn
  calc
    _ ≤ (∫ x in {x : Vec3 | R1 < vec3EuclideanNorm x},
          (vec3EuclideanNorm (regUniformMollifiedInitial ρ (εseq k)
            (hseq k).1 a x)) ^ (2 : ℕ)) +
        C * (((eLpNorm a 2 volume).toReal) ^ (2 : ℕ) *
          t ^ (1 / 2 : ℝ) +
          ((eLpNorm a 2 volume).toReal) ^ (3 : ℕ) *
          t ^ (1 / 4 : ℝ)) / (R2 - R1) := by
      simpa [R1, R2] using htailn
    _ ≤ (∫ x in {x : Vec3 | (n : ℝ) < vec3EuclideanNorm x},
          (vec3EuclideanNorm (a x)) ^ (2 : ℕ)) + C * K / ((n : ℝ) + 1) := by
      rw [hden]
      have hnumerator := mul_le_mul_of_nonneg_left htime hC
      exact add_le_add hinitRewrite
        (div_le_div_of_nonneg_right hnumerator (by positivity))
    _ = b n := by rfl

end CKN.Leray

end
