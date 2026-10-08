/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Transport.WindowTerminalNormalization
public import LeanPool.HighContrastHomogenization.Provider.Transport.TransportCoefficients
public import LeanPool.HighContrastHomogenization.Geometry.SizeAlignment
public import LeanPool.HighContrastHomogenization.Setup.SelectionObjects

/-!
# High-contrast homogenization: Provider.Persistence.TransferGauge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The transfer gauge, the comparison sizes, and the two decay gaps

The comparison between adapted and Euclidean cubes measures its error in units
of the reference block, with the source gauge
`Γ_{g,S}(j) = (1-g)^{-1}(1 + K_{Ψ_S}^2 3^{-j})^g` as the coefficient.  This file
collects the scalar account that turns such an error into a tolerance on the
entry mean.

Three facts about the gauge come first.  Above the alignment scale the burn
`e.source.lower.scale` has already paid for the growth witness:
its second term puts `3^{j_*}` above `K_bar_S^2 ≥ K_{Ψ_S}^2`, so `K_{Ψ_S}^23^{-j}`
never exceeds one there.  The gauge is therefore below `2^g/(1-g)` from the
alignment on, and it is antitone in the scale on every branch.

The two transfer sizes come next.  The actual size
`𝒯_{q,S}(j) = C_AE 𝔢_q Γ_{g,S}(j) Λ_t` carries the random normalization
`Λ_t = |(E_t^q)^{-1/2}𝐄(E_t^q)^{-1/2}|`; the deterministic size
`𝒯_bar_{q,S}(j)` replaces it by `U κ_𝐄 B_q`.  The terminal normalization
`e.two.grid.source.normalization` bounds the first by the second, which is the
envelope for the transfer size: only the constant `U`, never the multiplier,
survives.

Last is the gap arithmetic.  Each gap is the ceiling of a truncated logarithm,
so it is at least one — which makes both adapter chains strict — and it always
dominates the untruncated logarithm, which is what the forward and the reverse
comparison error need.  The degenerate branch where the comparison size is
nonpositive is trivial, so no positivity of the size is assumed anywhere.
-/

namespace HCPolySupport
namespace HighContrast
namespace Persistence

open MeasureTheory

noncomputable section

/-! ## The source gauge -/

/-- The source gauge is positive below the critical exponent: its base exceeds
one and its prefactor is the reciprocal of a positive number. -/
theorem zero_lt_transferGauge {g : ℝ} (hg : g < 1) (K : ℝ) (j : ℤ) :
    0 < transferGauge g K j := by
  have hbase : (0 : ℝ) < 1 + K ^ 2 * (3 : ℝ) ^ (-j) := by positivity
  rw [transferGauge]
  exact mul_pos (inv_pos.mpr (by linarith only [hg])) (Real.rpow_pos_of_pos hbase g)

/-- **The growth witness is burned above the alignment scale**.  The second term
of the maximum defining the source burn `e.source.lower.scale` puts `3^{j_*}`
above
`K_bar_S^2`, the enlarged witness dominates the witness, and `3^{-j}` decreases. -/
theorem sq_mul_zpow_le_one {d : ℕ} {Q K : ℝ} {jStar M j : ℤ} (hK : 1 < K)
    (hw : IsCoupledWindow d Q K jStar M) (hj : jStar ≤ j) :
    K ^ 2 * (3 : ℝ) ^ (-j) ≤ 1 := by
  have hgb2 : (2 : ℝ) ≤ growthBar K := le_max_left _ _
  have hKgb : K ≤ growthBar K := le_max_right _ _
  -- the burn dominates twice the logarithm of the enlarged witness
  have hceil : (⌈2 * Real.logb 3 (growthBar K)⌉ : ℤ) ≤ j := by
    refine le_trans (le_trans ?_ hw.1) hj
    rw [sourceBurn]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hlog : 2 * Real.logb 3 (growthBar K) ≤ (j : ℝ) := Int.ceil_le.mp hceil
  have hlogsq : Real.logb 3 (growthBar K ^ 2) ≤ (j : ℝ) := by
    rw [Real.logb_pow]
    push_cast
    linarith only [hlog]
  have hsq : growthBar K ^ 2 ≤ (3 : ℝ) ^ j := by
    have h := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 3)
      (by positivity : (0 : ℝ) < growthBar K ^ 2)).mp hlogsq
    rwa [Real.rpow_intCast] at h
  have hKsq : K ^ 2 ≤ (3 : ℝ) ^ j :=
    le_trans (pow_le_pow_left₀ (by linarith only [hK]) hKgb 2) hsq
  calc K ^ 2 * (3 : ℝ) ^ (-j) ≤ (3 : ℝ) ^ j * (3 : ℝ) ^ (-j) :=
        mul_le_mul_of_nonneg_right hKsq (by positivity)
    _ = 1 := by
        rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
        simp

/-- **The gauge is bounded above the alignment scale**, from the source burn
`e.source.lower.scale`. -/
theorem transferGauge_le {d : ℕ} {Q K g : ℝ} {jStar M j : ℤ} (hg0 : 0 ≤ g)
    (hg1 : g < 1) (hK : 1 < K) (hw : IsCoupledWindow d Q K jStar M) (hj : jStar ≤ j) :
    transferGauge g K j ≤ (2 : ℝ) ^ g / (1 - g) := by
  have hburn := sq_mul_zpow_le_one hK hw hj
  have hbase : (0 : ℝ) ≤ 1 + K ^ 2 * (3 : ℝ) ^ (-j) := by positivity
  have hrp : (1 + K ^ 2 * (3 : ℝ) ^ (-j)) ^ g ≤ (2 : ℝ) ^ g :=
    Real.rpow_le_rpow hbase (by linarith only [hburn]) hg0
  rw [transferGauge, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hrp (inv_nonneg.mpr (by linarith only [hg1]))

/-! ## The size envelope -/

/-! ## The two decay gaps -/

/-- Each gap is at least one, on every branch of its truncated logarithm; this is
what makes both adapter chains strict. -/
theorem one_le_gapCeil (x : ℝ) : (1 : ℤ) ≤ ⌈max 1 (max 0 x)⌉ := by
  rw [Int.le_ceil_iff]
  have hx : (1 : ℝ) ≤ max 1 (max 0 x) := le_max_left _ _
  push_cast
  linarith only [hx]

/-- Each gap dominates the untruncated logarithm it is built from. -/
theorem logb_le_gapCeil (x : ℝ) :
    Real.logb 3 x ≤ ((⌈max 1 (max 0 (Real.logb 3 x))⌉ : ℤ) : ℝ) :=
  le_trans (le_trans (le_max_right 0 _) (le_max_right 1 _)) (Int.le_ceil _)

/-- **The decay gap defeats the comparison size.**  If the gap exponent dominates
`log_3(T/η)`, then `T·3^{-gap} ≤ η`.  The degenerate branch `T ≤ 0`, where the
logarithm is at its junk value, is trivial, so no positivity of `T` is needed. -/
theorem mul_zpow_neg_le_of_logb_le {T eta : ℝ} (heta : 0 < eta) {l : ℤ}
    (hl : Real.logb 3 (T / eta) ≤ (l : ℝ)) : T * (3 : ℝ) ^ (-l) ≤ eta := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (-l) := by positivity
  rcases le_or_gt T 0 with hT | hT
  · have hle : T * (3 : ℝ) ^ (-l) ≤ 0 := by
      have h := mul_le_mul_of_nonneg_right hT h3.le
      rwa [zero_mul] at h
    linarith only [hle, heta]
  · have hdiv : (0 : ℝ) < T / eta := div_pos hT heta
    have h := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 3) hdiv).mp hl
    rw [Real.rpow_intCast, div_le_iff₀ heta] at h
    calc T * (3 : ℝ) ^ (-l) ≤ (3 : ℝ) ^ l * eta * (3 : ℝ) ^ (-l) :=
          mul_le_mul_of_nonneg_right h h3.le
      _ = eta * ((3 : ℝ) ^ l * (3 : ℝ) ^ (-l)) := by ring
      _ = eta := by
          rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
          simp

/-- **The gap inequality at the printed gap** of `e.response.transfer.gaps`, for
the forward and for the reverse gap: the deterministic comparison size,
discounted by the gap it defines, is below the tolerance that defines
it. -/
theorem transferSizeBar_mul_zpow_le {d : ℕ} {U CAE Cd g K eta : ℝ} {E : BlockMat d}
    {m0 : Mat d} {j l : ℤ} (heta : 0 < eta)
    (hl : l = ⌈max 1 (max 0
      (Real.logb 3 (transferSizeBar U CAE Cd g K E m0 j / eta)))⌉) :
    transferSizeBar U CAE Cd g K E m0 j * (3 : ℝ) ^ (-l) ≤ eta := by
  refine mul_zpow_neg_le_of_logb_le heta ?_
  rw [hl]
  exact logb_le_gapCeil _

/-- The adapter's error exponent, read on a chain whose two ends differ by the
gap, is the gap discount. -/
theorem rpow_neg_sub_eq_zpow {t m l : ℤ} (h : m = t + l) :
    (3 : ℝ) ^ (-((m : ℝ) - (t : ℝ))) = (3 : ℝ) ^ (-l) := by
  have hexp : -((m : ℝ) - (t : ℝ)) = ((-l : ℤ) : ℝ) := by
    subst h; push_cast; ring
  rw [hexp, Real.rpow_intCast]

end

end Persistence
end HighContrast
end HCPolySupport
