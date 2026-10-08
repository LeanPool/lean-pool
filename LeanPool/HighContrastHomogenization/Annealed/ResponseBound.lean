/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Frozen.CoarseEllipticityDagger

/-!
# High-contrast homogenization: Annealed.ResponseBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The almost sure entrywise bound on the coarse response

Under `e.coarse.ellipticity` the response on a centered cube is dominated by
the reference block with a discount factor that the sample itself controls: run
the assumption at the sample's own burn scale `m' ≥ m`, where `3^{m'} ≥ S`, and
pay the lost discount `3^{g(m'-m)}`.  Because the burn scale overshoots by at
most one triadic step, that factor is affine in the source scale, and the
entries of the response are bounded almost surely by an affine function of the
source.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- For every real `s` and every scale `m` there is a scale `m' ≥ m` at which the
source has burned, `s ≤ 3^{m'}`, and which overshoots by at most one triadic
step. -/
theorem exists_burn_scale (m : ℤ) (s : ℝ) :
    ∃ m' : ℤ, m ≤ m' ∧ s ≤ (3 : ℝ) ^ m' ∧
      (3 : ℝ) ^ m' ≤ 3 * max ((3 : ℝ) ^ m) s := by
  classical
  set T : ℝ := max ((3 : ℝ) ^ m) s with hT
  have h3m : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hTpos : 0 < T := lt_of_lt_of_le h3m (le_max_left _ _)
  have hex : ∃ n : ℕ, T ≤ (3 : ℝ) ^ m * (3 : ℝ) ^ n := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (T / (3 : ℝ) ^ m) (by norm_num : (1 : ℝ) < 3)
    exact ⟨n, by rw [mul_comm]; exact (div_le_iff₀ h3m).1 hn.le⟩
  set n₀ : ℕ := Nat.find hex with hn₀
  have hfind : T ≤ (3 : ℝ) ^ m * (3 : ℝ) ^ n₀ := Nat.find_spec hex
  have hpow : (3 : ℝ) ^ (m + (n₀ : ℤ)) = (3 : ℝ) ^ m * (3 : ℝ) ^ n₀ := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
  refine ⟨m + (n₀ : ℤ), by omega, ?_, ?_⟩
  · rw [hpow]
    exact le_trans (le_max_right _ _) hfind
  · rw [hpow]
    rcases Nat.eq_zero_or_pos n₀ with h0 | hpos
    · rw [h0]
      have hle : (3 : ℝ) ^ m ≤ T := le_max_left _ _
      simp only [pow_zero, mul_one]
      linarith only [hle, hTpos]
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, n₀ = k + 1 := ⟨n₀ - 1, by omega⟩
      have hmin : ¬ (T ≤ (3 : ℝ) ^ m * (3 : ℝ) ^ k) := by
        rw [hn₀] at hk
        exact Nat.find_min hex (by omega)
      have hlt : (3 : ℝ) ^ m * (3 : ℝ) ^ k < T := not_le.1 hmin
      rw [hk, pow_succ]
      linarith only [hlt]

/-- **The almost sure entrywise bound.**  Under `e.coarse.ellipticity` the
entries of the coarse response on a centered cube are bounded, almost surely, by
an affine function of the source scale. -/
theorem ae_abs_blockMatEntry_coarseBlock_le
    {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) (m : ℤ) :
    ∀ᵐ a ∂P, ∀ α β : BlockCoord d,
      |blockMatEntry (coarseBlock (centeredCube d m) a) α β| ≤
        6 * blockEntrySum E * (1 + (3 : ℝ) ^ (-m) * S a) := by
  have hg1 : g ≤ 1 := le_of_lt hdag.g_mem.2
  have hCE : 0 ≤ blockEntrySum E := blockEntrySum_nonneg E
  filter_upwards [hdag.coarse_bound] with a hbound α β
  obtain ⟨m', hmm', hburn, hover⟩ := exists_burn_scale m (S a)
  have hloew := hbound m' hburn m hmm' 0 (standardCellCenter_zero_mem_centeredCube m m')
  rw [standardCell_zero] at hloew
  set c : ℝ := (3 : ℝ) ^ (g * ((m' : ℝ) - (m : ℝ))) with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg (by norm_num) _
  have hexp : (0 : ℝ) ≤ (m' : ℝ) - (m : ℝ) := by
    have hcast : (m : ℝ) ≤ (m' : ℝ) := by exact_mod_cast hmm'
    linarith only [hcast]
  have hcle : c ≤ (3 : ℝ) ^ (m' - m) := by
    have h1 : c ≤ (3 : ℝ) ^ ((m' : ℝ) - (m : ℝ)) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hmul := mul_le_mul_of_nonneg_right hg1 hexp
      linarith only [hmul]
    have h2 : ((m' - m : ℤ) : ℝ) = (m' : ℝ) - (m : ℝ) := by push_cast; ring
    rwa [← h2, Real.rpow_intCast] at h1
  have h3m : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have haffine : (3 : ℝ) ^ (m' - m) ≤ 3 * (1 + (3 : ℝ) ^ (-m) * S a) := by
    have hsplit : (3 : ℝ) ^ (m' - m) = (3 : ℝ) ^ m' * (3 : ℝ) ^ (-m) := by
      rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      ring_nf
    have hinv : (0 : ℝ) < (3 : ℝ) ^ (-m) := by positivity
    have hmul : (3 : ℝ) ^ m' * (3 : ℝ) ^ (-m) ≤
        3 * max ((3 : ℝ) ^ m) (S a) * (3 : ℝ) ^ (-m) :=
      mul_le_mul_of_nonneg_right hover hinv.le
    have hmax : max ((3 : ℝ) ^ m) (S a) * (3 : ℝ) ^ (-m) ≤ 1 + (3 : ℝ) ^ (-m) * S a := by
      rcases max_cases ((3 : ℝ) ^ m) (S a) with ⟨he, _⟩ | ⟨he, _⟩
      · rw [he, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
        have hz : m + -m = 0 := by omega
        rw [hz, zpow_zero]
        have hnn : (0 : ℝ) ≤ (3 : ℝ) ^ (-m) * S a :=
          mul_nonneg hinv.le (hdag.source_nonneg a)
        linarith only [hnn]
      · rw [he, mul_comm]
        linarith only []
    rw [hsplit]
    calc (3 : ℝ) ^ m' * (3 : ℝ) ^ (-m)
        ≤ 3 * max ((3 : ℝ) ^ m) (S a) * (3 : ℝ) ^ (-m) := hmul
      _ = 3 * (max ((3 : ℝ) ^ m) (S a) * (3 : ℝ) ^ (-m)) := by ring
      _ ≤ 3 * (1 + (3 : ℝ) ^ (-m) * S a) := by linarith only [hmax]
  have hsymmA : IsSymmetricBlockMat (coarseBlock (centeredCube d m) a) := by
    rw [coarseBlock]
    exact isSymmetricBlockMat_coarseBlockMatrix _ _
  have hentry : |blockMatEntry (coarseBlock (centeredCube d m) a) α β| ≤
      2 * blockEntrySum (blockScale c E) := by
    refine abs_blockMatEntry_le_of_bounds hsymmA
      (zero_le_blockMatEntry_coarseBlock_diag _ a)
      (fun γ => ?_)
      (zero_le_blockVecDot_coarseBlock_blockBasis_add _ a α β)
      (by linarith only [hloew (blockBasis α + blockBasis β)])
    have h := hloew (blockBasis γ)
    rw [blockBasis_pairing, blockBasis_pairing] at h
    linarith only [h]
  have hscale : blockEntrySum (blockScale c E) = c * blockEntrySum E :=
    blockEntrySum_blockScale hc0 E
  rw [hscale] at hentry
  refine hentry.trans ?_
  have hstep : c ≤ 3 * (1 + (3 : ℝ) ^ (-m) * S a) := le_trans hcle haffine
  have hmul := mul_le_mul_of_nonneg_left hstep hCE
  linarith only [hmul]

end

end HighContrast
end HCPolySupport
