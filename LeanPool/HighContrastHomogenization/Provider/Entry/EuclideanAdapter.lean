/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Entry.SourceMoment
public import LeanPool.HighContrastHomogenization.Provider.Persistence.EuclideanTransfer
public import LeanPool.HighContrastHomogenization.Provider.Initialization.IdentityGrid
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.MeanOrder
public import LeanPool.HighContrastHomogenization.Annealed.Integrability
public import LeanPool.HighContrastHomogenization.Geometry.IntegralOrder
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# High-contrast homogenization: Provider.Entry.EuclideanAdapter

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The Euclidean inputs of the adapted-to-Euclidean comparison

The proof of the comparison between adapted and Euclidean cubes decomposes each
cell of one grid into cells of the other and reads the resulting
boundary layers in two regimes: the layers at generations at or above the
comparison scale are handled by integer stationarity, the layers below it by the
random-source ellipticity together with the source moment.  This file proves the
Euclidean-side input of each regime, both unconditionally in the generation.

*Below the comparison scale.*  The ellipticity of `e.coarse.ellipticity`
bounds the response of a centered cube of generation `i` by `3^{g(m-i)}𝐄` at
every macroscopic generation `m ≥ i` that has burned the source.  Taking `m` to
be the smallest such triadic generation gives the pathwise bound
`𝐀(□_i) ≤ (1 + 3·3^{-i}S)^g𝐄`, and Jensen's inequality for the concave
`x ↦ x^g` — the step the printed proof performs with Hölder — turns its mean
into `(1 + 6K_{Ψ_S}^23^{-i})^g𝐄`.  The cube being centered at the origin, the
macroscopic containment costs nothing, so no factor of the generation survives.

*At or above the comparison scale.*  Centered cubes are the adapted cells of the
identity grid, which the rounded adapted grid of `s.scale.selection` fixes at
every nonnegative alignment, so the annealed mean order of
`p.fixed.geometry.parent.child.recurrence` reads on them directly: `F_p ≤ F_j` whenever
`k_0(d) ≤ j ≤ p`.  Finiteness at every generation is itself a consequence of
`e.coarse.ellipticity`, so no window enters.

There are no definitions in this file.
-/

namespace HCPolySupport
namespace HighContrast
namespace Entry

open MeasureTheory Set

open scoped MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The Euclidean generation bound -/

/-- A natural power of three that dominates a nonnegative real and is itself
dominated by `1 + 3x`. -/
theorem exists_pow_three_bracket {x : ℝ} (hx : 0 ≤ x) :
    ∃ l : ℕ, x ≤ (3 : ℝ) ^ (l : ℤ) ∧ (3 : ℝ) ^ (l : ℤ) ≤ 1 + 3 * x := by
  have hcast : (3 : ℝ) ^ ((⌈Real.logb 3 x⌉₊ : ℕ) : ℤ) =
      (3 : ℝ) ^ ((⌈Real.logb 3 x⌉₊ : ℝ)) := by
    rw [← Real.rpow_intCast]
    norm_num
  refine ⟨⌈Real.logb 3 x⌉₊, ?_, ?_⟩
  · rcases eq_or_lt_of_le hx with hx0 | hx0
    · rw [← hx0]; positivity
    · have hle : Real.logb 3 x ≤ (⌈Real.logb 3 x⌉₊ : ℝ) := Nat.le_ceil _
      calc x = (3 : ℝ) ^ Real.logb 3 x :=
            (Real.rpow_logb (by norm_num : (0 : ℝ) < 3) (by norm_num) hx0).symm
        _ ≤ (3 : ℝ) ^ ((⌈Real.logb 3 x⌉₊ : ℝ)) :=
            (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 3)).mpr hle
        _ = (3 : ℝ) ^ ((⌈Real.logb 3 x⌉₊ : ℕ) : ℤ) := hcast.symm
  · rcases Nat.eq_zero_or_pos ⌈Real.logb 3 x⌉₊ with hl | hl
    · rw [hl]
      have h1 : (3 : ℝ) ^ ((0 : ℕ) : ℤ) = 1 := by norm_num
      rw [h1]
      linarith only [hx]
    · have hnl : 0 < Real.logb 3 x := by
        by_contra hc
        push Not at hc
        exact hl.ne' (Nat.ceil_eq_zero.mpr hc)
      have hx0 : 0 < x := by
        rcases eq_or_lt_of_le hx with h | h
        · exact absurd hnl (by rw [← h, Real.logb_zero]; exact lt_irrefl 0)
        · exact h
      have hlt : (⌈Real.logb 3 x⌉₊ : ℝ) < Real.logb 3 x + 1 :=
        Nat.ceil_lt_add_one hnl.le
      have hmono : (3 : ℝ) ^ ((⌈Real.logb 3 x⌉₊ : ℝ)) ≤
          (3 : ℝ) ^ (Real.logb 3 x + 1) :=
        (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 3)).mpr hlt.le
      have hval : (3 : ℝ) ^ (Real.logb 3 x + 1) = 3 * x := by
        rw [Real.rpow_add (by norm_num),
          Real.rpow_logb (by norm_num : (0 : ℝ) < 3) (by norm_num) hx0,
          Real.rpow_one]
        ring
      rw [hval] at hmono
      rw [hcast]
      linarith only [hmono]

/-- **The pathwise Euclidean generation bound.**  The random-source ellipticity
of `e.coarse.ellipticity`, read at the smallest triadic macroscopic scale
above both the generation and the source scale; the argument being centered at
the origin, the macroscopic containment costs nothing. -/
theorem ae_coarseBlock_centeredCube_le {P : Measure (CoeffSpace d)}
    {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) (i : ℤ) :
    ∀ᵐ a ∂P, BlockMatLoewnerLE (coarseBlock (centeredCube d i) a)
      (blockScale ((1 + 3 * ((3 : ℝ) ^ (-i) * S a)) ^ g) E) := by
  filter_upwards [hdag.coarse_bound] with a ha
  have hu0 : 0 ≤ (3 : ℝ) ^ (-i) * S a := by
    have hS := hdag.source_nonneg a
    positivity
  obtain ⟨l, hl1, hl2⟩ := exists_pow_three_bracket hu0
  have h3i : (0 : ℝ) < (3 : ℝ) ^ i := by positivity
  have hSle : S a ≤ (3 : ℝ) ^ (i + (l : ℤ)) := by
    have hmul := mul_le_mul_of_nonneg_left hl1 h3i.le
    rw [← mul_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), add_neg_cancel,
      zpow_zero, one_mul] at hmul
    rwa [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  have him : i ≤ i + (l : ℤ) := le_add_of_nonneg_right (Int.natCast_nonneg l)
  have hb := ha (i + (l : ℤ)) hSle i him 0
    (standardCellCenter_zero_mem_centeredCube i (i + (l : ℤ)))
  rw [standardCell_zero] at hb
  refine Persistence.blockMatLoewnerLE_blockScale_mono (isSymmetricBlockMat_coarseBlock _ a)
    hdag.refBlock_isSymm hdag.refBlock_posDef ?_ hb
  have hexp : g * (((i + (l : ℤ) : ℤ) : ℝ) - (i : ℝ)) = (l : ℝ) * g := by
    push_cast
    ring
  have hcast2 : (3 : ℝ) ^ ((l : ℕ) : ℤ) = (3 : ℝ) ^ ((l : ℕ) : ℝ) := by
    rw [← Real.rpow_intCast]
    norm_num
  rw [hexp, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), ← hcast2]
  exact Real.rpow_le_rpow (by positivity) hl2 hdag.g_mem.1

/-- **Jensen's inequality at the source gauge.**  The concavity of `x ↦ x^g` on
the nonnegative reals moves the mean of the source scale inside the power: this
is the step the printed proof performs with Hölder. -/
theorem integral_rpow_le {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) {c : ℝ} (hc : 0 ≤ c) :
    ∫ a, (1 + c * S a) ^ g ∂P ≤ (1 + c * ∫ a, S a ∂P) ^ g := by
  have hg0 : 0 ≤ g := hdag.g_mem.1
  have hg1 : g ≤ 1 := le_of_lt hdag.g_mem.2
  have hS0 : ∀ a, 0 ≤ S a := hdag.source_nonneg
  have hfi : Integrable (fun a => 1 + c * S a) P :=
    (integrable_const (1 : ℝ)).add ((integrable_source hdag).const_mul c)
  have hone : ∀ a, (1 : ℝ) ≤ 1 + c * S a := fun a => by nlinarith only [hc, hS0 a]
  have hmeas : AEStronglyMeasurable (fun a => (1 + c * S a) ^ g) P :=
    ((measurable_const.add
      (hdag.source_measurable.const_mul c)).pow_const g).aestronglyMeasurable
  have hgi : Integrable (fun a => (1 + c * S a) ^ g) P := by
    refine hfi.mono' hmeas (_root_.Filter.Eventually.of_forall fun a => ?_)
    have hpow : (1 + c * S a) ^ g ≤ (1 + c * S a) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (hone a) hg1
    rw [Real.rpow_one] at hpow
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith only [hone a]) g)]
    exact hpow
  have hjensen := (Real.concaveOn_rpow hg0 hg1).le_map_integral
    (f := fun a => 1 + c * S a)
    (fun x _ => (Real.continuousAt_rpow_const x g (Or.inr hg0)).continuousWithinAt)
    isClosed_Ici
    (_root_.Filter.Eventually.of_forall fun a => by
      have := hone a
      simp only [Set.mem_Ici]
      linarith only [this])
    hfi hgi
  have hsum : ∫ a, (1 + c * S a) ∂P = 1 + c * ∫ a, S a ∂P := by
    rw [integral_add (integrable_const (1 : ℝ)) ((integrable_source hdag).const_mul c),
      integral_const, integral_const_mul, probReal_univ, smul_eq_mul, mul_one]
  rw [hsum] at hjensen
  exact hjensen

/-- **The Euclidean generation bound.**  The annealed block of the centered cube
of generation `i` is below `(1 + 6K_{Ψ_S}^23^{-i})^g` times the reference block,
at every generation. -/
theorem annealedBlock_centeredCube_le_blockScale {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) (i : ℤ) :
    BlockMatLoewnerLE (annealedBlock P (centeredCube d i))
      (blockScale ((1 + 6 * K ^ 2 * (3 : ℝ) ^ (-i)) ^ g) E) := by
  have hg0 : 0 ≤ g := hdag.g_mem.1
  have hS0 : ∀ a, 0 ≤ S a := hdag.source_nonneg
  have hint : HasIntegrableCoarseBlock P (centeredCube d i) :=
    hasIntegrableCoarseBlock_of_coarseEllipticityDagger hdag i
  set c : ℝ := 3 * (3 : ℝ) ^ (-i) with hcdef
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  have hone : ∀ a, (1 : ℝ) ≤ 1 + c * S a := fun a => by nlinarith only [hc0, hS0 a]
  have hgi : Integrable (fun a => (1 + c * S a) ^ g) P := by
    have hfi : Integrable (fun a => 1 + c * S a) P :=
      (integrable_const (1 : ℝ)).add ((integrable_source hdag).const_mul c)
    refine hfi.mono' ((measurable_const.add
      (hdag.source_measurable.const_mul c)).pow_const g).aestronglyMeasurable
      (_root_.Filter.Eventually.of_forall fun a => ?_)
    have hpow : (1 + c * S a) ^ g ≤ (1 + c * S a) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (hone a) (le_of_lt hdag.g_mem.2)
    rw [Real.rpow_one] at hpow
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith only [hone a]) g)]
    exact hpow
  -- the mean of the pathwise bound
  have haver : BlockMatLoewnerLE (annealedBlock P (centeredCube d i))
      (blockScale (∫ a, (1 + c * S a) ^ g ∂P) E) := by
    refine blockMatLoewnerLE_of_le ?_
    rw [toFullBlockMat_annealedBlock hint, toFullBlockMat_blockScale,
      show (∫ a, (1 + c * S a) ^ g ∂P) • toFullBlockMat E =
          ∫ a, ((1 + c * S a) ^ g) • toFullBlockMat E ∂P by
        rw [integral_smul_const]]
    have hgiC : Integrable (fun a => (1 + c * S a) ^ g • toFullBlockMat E) P := by
      have hgiC' : Integrable (fun a : CoeffSpace d => fun p q : BlockCoord d =>
          (1 + c * S a) ^ g * toFullBlockMat E p q) P := by
        rw [integrable_pi_iff]
        intro p
        rw [integrable_pi_iff]
        intro q
        exact hgi.mul_const _
      exact hgiC'
    refine integral_mono' (integrable_toFullBlockMat hint) hgiC ?_
    filter_upwards [ae_coarseBlock_centeredCube_le hdag i] with a ha
    have hrw : 1 + c * S a = 1 + 3 * ((3 : ℝ) ^ (-i) * S a) := by rw [hcdef]; ring
    rw [← hrw] at ha
    have h := le_of_blockMatLoewnerLE (isSymmetricBlockMat_coarseBlock _ a)
      (isSymmetricBlockMat_blockScale _ hdag.refBlock_isSymm) ha
    rwa [toFullBlockMat_blockScale] at h
  refine Persistence.blockMatLoewnerLE_blockScale_mono
    (isSymmetricBlockMat_annealedBlock P _) hdag.refBlock_isSymm
    hdag.refBlock_posDef ?_ haver
  refine le_trans (integral_rpow_le hdag hc0) ?_
  have hmean0 : (0 : ℝ) ≤ ∫ a, S a ∂P :=
    integral_nonneg fun a => hS0 a
  refine Real.rpow_le_rpow (by nlinarith only [hc0, hmean0]) ?_ hg0
  have hmean := integral_source_le hdag
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (-i) := by positivity
  have hstep : c * ∫ a, S a ∂P ≤ c * (2 * K ^ 2) :=
    mul_le_mul_of_nonneg_left hmean hc0
  have hval : c * (2 * K ^ 2) = 6 * K ^ 2 * (3 : ℝ) ^ (-i) := by rw [hcdef]; ring
  rw [hval] at hstep
  linarith only [hstep]

/-! ## The Euclidean mean order -/

/-- The identity witness is fixed by the rounding of `s.scale.selection` at
every nonnegative alignment. -/
theorem roundedGrid_one_of_nonneg [Nonempty (Fin d)] {j : ℤ} (hj : 0 ≤ j) :
    roundedGrid j (1 : Mat d) = (1 : Mat d) := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hj
  have hspec : specBound ((1 : Mat d)⁻¹) = 1 := by
    rw [inv_one, specBound_eq_norm Matrix.PosSemidef.one, norm_one]
  ext i k
  rw [Recurrence.roundedGrid_apply, hspec, Real.sqrt_one, Recurrence.matSqrt_one]
  by_cases hik : i = k
  · subst k
    simp only [Matrix.one_apply_eq, mul_one, zpow_natCast]
    have hceil : ⌈(3 : ℝ) ^ n⌉ = (((3 ^ n : ℕ) : ℤ)) := by
      simpa only [Nat.cast_ofNat, Nat.cast_pow] using
        (Int.ceil_natCast (R := ℝ) (3 ^ n))
    rw [hceil, Int.cast_natCast, zpow_neg, zpow_natCast, Nat.cast_pow]
    exact inv_mul_cancel₀ (by positivity)
  · simp [hik, zpow_natCast]

/-- The identity grid is a rounded adapted grid at the rounding scale. -/
theorem isRoundedGrid_one [Nonempty (Fin d)] :
    IsRoundedGrid (kZero d : ℤ) (1 : Mat d) :=
  ⟨le_rfl, 1, Matrix.PosDef.one,
    (roundedGrid_one_of_nonneg (Int.natCast_nonneg _)).symm⟩

end

end Entry
end HighContrast
end HCPolySupport
