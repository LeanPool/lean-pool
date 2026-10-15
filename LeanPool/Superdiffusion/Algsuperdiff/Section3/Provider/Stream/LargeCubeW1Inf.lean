/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.LargeCubeLinfty
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.GeometricSums
import LeanPool.Superdiffusion.Algsuperdiff.Section3.Probability.OneSidedOrlicz

/-!
# LargeCubeW1Inf

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The summed derivative-stream bound: ABK26's `e.W.1.inf.bound`

ABK26 states, for `l, m, n ∈ ℤ` with `n ≤ min{m, l}`,

`∑_{k = n+1}^m (3^k ‖∇j_k‖_{L∞(cu_l)} + 3^{2k} ‖∇²j_k‖_{L∞(cu_l)})
   ≤ O_{Γ₂}(C (l-n)^{1/2} min{γ^{-1}, m-n} 3^{γm})`.

The source proof has two regimes.  For `k < l` the display
`e.W1inf.jL.bound.smaller` covers `cu_l` by translates of `cu_k` and applies the
maximum lemma `l.maximums.Gamma.s` to the single-shell derivative display
`e.nabla.jk.O`, which costs the amplitude factor `(log N)^{1/2} ≃ (l-k)^{1/2}`.
For `k ≥ l` the cube `cu_l` is *contained* in the own scale cube `cu_k`, so
`e.nabla.jk.O` applies with no covering loss.  The two regimes are then summed
with the `Γ₂` triangle inequality against the geometric series `∑_{k ∈ (n,m]}
3^{γk} ≤ C min{γ^{-1}, m-n} 3^{γm}` (`e.geo.part.sum`).

## Deviations from the source, all absorbed by its `C(d)`

* The covering family is the one proved for `e.km.kn.Linfty` (`subcubeShifts`),
  whose lattice spacing is `3^{k-1}` rather than `3^k`; this makes the open
  cover exact and multiplies the count by `3^d`.
* The amplitude factor of the proved maximum lemma is `(3 max{1, log N})^{1/2}`
  rather than `(log N)^{1/2}`.
* Since the maximizing translate of the first-derivative norm need not be the
  maximizing translate of the second-derivative norm, the covering step is
  applied to each of the two gauges separately, costing a factor `2`.
* The source hypothesis `n ≤ l` is **not** needed and is dropped: for `l < n`
  every shell in `(n, m]` is estimated in the own-scale regime and the
  corrected factor `(1 ∨ (l-n))^{1/2}` equals `1`.  The local proof is
  therefore strictly stronger than the (corrected) source statement on that
  side.

## Main definitions

* `Algsuperdiff.Section3.Provider.Stream.largeCubeDerivGauge`: the source
  summand `3^k ‖∇j_k‖_{L∞(cu_l)} + 3^{2k} ‖∇²j_k‖_{L∞(cu_l)}`.
* `Algsuperdiff.Section3.Provider.Stream.shellDerivGaugeCover`: the maximum of
  the translated own-scale derivative gauges over the covering family.

## Main results

* `Algsuperdiff.Section3.Provider.Stream.isBigOWith_gammaSigma_largeCubeDerivGauge_lt`:
  ABK26's `e.W1inf.jL.bound.smaller`.
* `Algsuperdiff.Section3.Provider.Stream.isBigOWith_gammaSigma_largeCubeDerivGaugeSum`:
  ABK26's `e.W.1.inf.bound`, in its corrected form.

## References

* ABK26, `e.W.1.inf.bound`.
* ABK26, `e.W1inf.jL.bound.smaller`.
* ABK26, `e.nabla.jk.O`.
* ABK26, `l.maximums.Gamma.s`.
* ABK26, `e.geo.part.sum`.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory
open HCPolySupport
open HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## Elementary rewrites -/

private theorem three_zpow_pos' (k : ℤ) : (0 : ℝ) < (3 : ℝ) ^ k :=
  zpow_pos (by norm_num) k

private theorem three_zpow_two_mul (k : ℤ) :
    (3 : ℝ) ^ (2 * k) = (3 : ℝ) ^ k * (3 : ℝ) ^ k := by
  rw [two_mul, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]

private theorem three_zpow_mul_rpow_gamma_sub_one (gamma : ℝ) (k : ℤ) :
    (3 : ℝ) ^ k * Real.rpow 3 ((gamma - 1) * (k : ℝ)) =
      (3 : ℝ) ^ (gamma * (k : ℝ)) := by
  change (3 : ℝ) ^ k * (3 : ℝ) ^ ((gamma - 1) * (k : ℝ)) =
    (3 : ℝ) ^ (gamma * (k : ℝ))
  rw [← Real.rpow_intCast (3 : ℝ) k, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

private theorem rpow_inv_two (x : ℝ) : x ^ ((2 : ℝ)⁻¹) = Real.sqrt x := by
  rw [Real.sqrt_eq_rpow, one_div]

/-- The identically zero random variable satisfies every nonnegative
weak-Orlicz upper bound.  Used for the empty shell range `m = n`. -/
private theorem isBigOWith_gammaSigma_of_eq_zero {Omega : Type*}
    [MeasurableSpace Omega] {mu : Measure Omega} {X : Omega → ℝ} {sigma A : ℝ}
    (hA : 0 ≤ A) (hX : ∀ omega, X omega = 0) :
    IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma sigma) X A :=
  Algsuperdiff.Section3.Probability.isBigOWith_gammaSigma_of_eq_zero hA hX

/-! ## The source summand -/

/-- The summand of ABK26's `e.W.1.inf.bound`:
`3^k ‖∇j_k‖_{L∞(cu_l)} + 3^{2k} ‖∇²j_k‖_{L∞(cu_l)}`, read on the *observation*
cube `cu_l` and at the shell index `k`. -/
def largeCubeDerivGauge (l k : ℤ) (j : ShellField d) : ℝ :=
  (3 : ℝ) ^ k * localCubeDerivNorm l j +
    (3 : ℝ) ^ (2 * k) * localCubeSecondDerivNorm l j

theorem largeCubeDerivGauge_nonneg (l k : ℤ) (j : ShellField d) :
    0 ≤ largeCubeDerivGauge l k j :=
  add_nonneg
    (mul_nonneg (three_zpow_pos' k).le (localCubeDerivNorm_nonneg l j))
    (mul_nonneg (three_zpow_pos' (2 * k)).le (localCubeSecondDerivNorm_nonneg l j))

theorem measurable_largeCubeDerivGauge (l k : ℤ) :
    Measurable (largeCubeDerivGauge (d := d) l k) :=
  (measurable_const.mul (measurable_localCubeDerivNorm l)).add
    (measurable_const.mul (measurable_localCubeSecondDerivNorm l))

/-- The exact factorization of the summand through the own-scale gauge weight. -/
theorem largeCubeDerivGauge_eq (l k : ℤ) (j : ShellField d) :
    largeCubeDerivGauge l k j =
      (3 : ℝ) ^ k *
        (localCubeDerivNorm l j + (3 : ℝ) ^ k * localCubeSecondDerivNorm l j) := by
  rw [largeCubeDerivGauge, three_zpow_two_mul]
  ring

/-! ## The covering maximum -/

/-- The maximum, over the proved covering family of `cu_l` by translates of `cu_k`,
of the translated own-scale derivative gauge `‖∇j‖_{L∞(z + cu_k)} + 3^k
‖∇²j‖_{L∞(z + cu_k)}`. -/
def shellDerivGaugeCover (l k : ℤ) (j : ShellField d) : ℝ :=
  (subcubeShifts d k l).sup' (subcubeShifts_nonempty d k l) fun p =>
    localCubeDerivNorm k (ShellField.translate (subcubeCenter k p) j) +
      (3 : ℝ) ^ k *
        localCubeSecondDerivNorm k (ShellField.translate (subcubeCenter k p) j)

theorem le_shellDerivGaugeCover (l k : ℤ) (j : ShellField d) {p : Fin d → ℤ}
    (hp : p ∈ subcubeShifts d k l) :
    localCubeDerivNorm k (ShellField.translate (subcubeCenter k p) j) +
        (3 : ℝ) ^ k *
          localCubeSecondDerivNorm k (ShellField.translate (subcubeCenter k p) j) ≤
      shellDerivGaugeCover l k j := by
  rw [shellDerivGaugeCover]
  exact Finset.le_sup' (fun q : Fin d → ℤ =>
    localCubeDerivNorm k (ShellField.translate (subcubeCenter k q) j) +
      (3 : ℝ) ^ k *
        localCubeSecondDerivNorm k (ShellField.translate (subcubeCenter k q) j)) hp

theorem shellDerivGaugeCover_nonneg (l k : ℤ) (j : ShellField d) :
    0 ≤ shellDerivGaugeCover l k j := by
  obtain ⟨p, hp⟩ := subcubeShifts_nonempty d k l
  exact le_trans
    (shellDerivGauge_nonneg k (ShellField.translate (subcubeCenter k p) j))
    (le_shellDerivGaugeCover l k j hp)

/-- The covering bound for the first-derivative norm: every point of `cu_l`
lies in one of the translated cubes `z + cu_k`, and the translated shell has
the same derivative there. -/
theorem localCubeDerivNorm_le_shellDerivGaugeCover (l k : ℤ) (j : ShellField d) :
    localCubeDerivNorm l j ≤ shellDerivGaugeCover l k j := by
  refine localCubeDerivNorm_le_of_forall l j (shellDerivGaugeCover_nonneg l k j) ?_
  intro x hx
  obtain ⟨p, hp, hmem⟩ := exists_subcubeShift_mem (d := d) k l hx
  rw [mem_translateSet_iff_sub_mem] at hmem
  have hderiv : ShellField.deriv (ShellField.translate (subcubeCenter k p) j)
      (x - subcubeCenter k p) = ShellField.deriv j x := by
    rw [ShellField.translate_deriv, sub_add_cancel]
  have h1 : ShellField.matrixDerivativeNorm (ShellField.deriv j x) ≤
      localCubeDerivNorm k (ShellField.translate (subcubeCenter k p) j) := by
    rw [← hderiv]
    exact matrixDerivativeNorm_deriv_le_localCubeDerivNorm k _ hmem
  refine h1.trans (le_trans ?_ (le_shellDerivGaugeCover l k j hp))
  have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ k *
      localCubeSecondDerivNorm k (ShellField.translate (subcubeCenter k p) j) :=
    mul_nonneg (three_zpow_pos' k).le
      (localCubeSecondDerivNorm_nonneg k _)
  linarith

/-- The covering bound for the weighted second-derivative norm. -/
theorem three_zpow_mul_localCubeSecondDerivNorm_le_shellDerivGaugeCover
    (l k : ℤ) (j : ShellField d) :
    (3 : ℝ) ^ k * localCubeSecondDerivNorm l j ≤ shellDerivGaugeCover l k j := by
  have hpos : (0 : ℝ) < (3 : ℝ) ^ k := three_zpow_pos' k
  have hkey : localCubeSecondDerivNorm l j ≤
      ((3 : ℝ) ^ k)⁻¹ * shellDerivGaugeCover l k j := by
    refine localCubeSecondDerivNorm_le_of_forall l j
      (mul_nonneg (inv_nonneg.2 hpos.le) (shellDerivGaugeCover_nonneg l k j)) ?_
    intro x hx
    obtain ⟨p, hp, hmem⟩ := exists_subcubeShift_mem (d := d) k l hx
    rw [mem_translateSet_iff_sub_mem] at hmem
    have hsecond :
        ShellField.secondDeriv (ShellField.translate (subcubeCenter k p) j)
          (x - subcubeCenter k p) = ShellField.secondDeriv j x := by
      rw [ShellField.translate_secondDeriv, sub_add_cancel]
    have h1 : ShellField.matrixSecondDerivativeNorm
        (ShellField.secondDeriv j x) ≤
        localCubeSecondDerivNorm k
          (ShellField.translate (subcubeCenter k p) j) := by
      rw [← hsecond]
      exact matrixSecondDerivativeNorm_secondDeriv_le_localCubeSecondDerivNorm
        k _ hmem
    refine h1.trans ?_
    rw [le_inv_mul_iff₀ hpos]
    refine le_trans ?_ (le_shellDerivGaugeCover l k j hp)
    have h2 : (0 : ℝ) ≤
        localCubeDerivNorm k (ShellField.translate (subcubeCenter k p) j) :=
      localCubeDerivNorm_nonneg k _
    linarith
  calc (3 : ℝ) ^ k * localCubeSecondDerivNorm l j
      ≤ (3 : ℝ) ^ k * (((3 : ℝ) ^ k)⁻¹ * shellDerivGaugeCover l k j) :=
        mul_le_mul_of_nonneg_left hkey hpos.le
    _ = shellDerivGaugeCover l k j := by
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), one_mul]

/-- The deterministic half of `e.W1inf.jL.bound.smaller`: the source summand on
`cu_l` is dominated by twice the weighted covering maximum. -/
theorem largeCubeDerivGauge_le_two_mul_shellDerivGaugeCover (l k : ℤ)
    (j : ShellField d) :
    largeCubeDerivGauge l k j ≤
      2 * (3 : ℝ) ^ k * shellDerivGaugeCover l k j := by
  have hpos : (0 : ℝ) < (3 : ℝ) ^ k := three_zpow_pos' k
  have h1 := localCubeDerivNorm_le_shellDerivGaugeCover l k j
  have h2 := three_zpow_mul_localCubeSecondDerivNorm_le_shellDerivGaugeCover l k j
  rw [largeCubeDerivGauge_eq]
  nlinarith [hpos]

/-- The probabilistic half of `e.W1inf.jL.bound.smaller`: the covering maximum
obeys the single-shell `Γ₂` estimate `e.nabla.jk.O` with the amplitude factor
supplied by the proved cardinality-free maximum lemma. -/
theorem isBigOWith_gammaSigma_shellDerivGaugeCover (M : ABKModel d) (l k : ℤ) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d => shellDerivGaugeCover l k (omega k))
      ((3 * max 1 (Real.log (((subcubeShifts d k l).card : ℕ) : ℝ))) ^ (2 : ℝ)⁻¹ *
        Real.rpow 3 ((M.gamma - 1) * (k : ℝ))) := by
  simp only [shellDerivGaugeCover]
  refine Orlicz.isBigOWith_gammaSigma_finset_sup'_of_nonempty
    (subcubeShifts d k l) (subcubeShifts_nonempty d k l) (by norm_num)
    (Real.rpow_nonneg (by norm_num) _) ?_
  intro p _
  exact isBigOWith_gammaSigma_shellDerivGauge_cube_translate M (le_refl k)
    (subcubeCenter k p)

/-! ## `e.W1inf.jL.bound.smaller` -/

/-- The dimensional constant of ABK26's `e.W1inf.jL.bound.smaller`. -/
def shellW1InfSmallerConst (d : ℕ) : ℝ :=
  2 * Real.sqrt (largeCubeLogConst * (d : ℝ))

theorem shellW1InfSmallerConst_nonneg (d : ℕ) : 0 ≤ shellW1InfSmallerConst d :=
  mul_nonneg (by norm_num) (Real.sqrt_nonneg _)

/-- **ABK26's `e.W1inf.jL.bound.smaller`**: for `k < l`,

`3^k ‖∇j_k‖_{L∞(cu_l)} + 3^{2k} ‖∇²j_k‖_{L∞(cu_l)}
   ≤ O_{Γ₂}(C (l-k)^{1/2} 3^{γk})`,

with the explicit dimensional constant `2 √(largeCubeLogConst · d)`. -/
theorem isBigOWith_gammaSigma_largeCubeDerivGauge_lt (M : ABKModel d) {l k : ℤ}
    (hkl : k < l) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d => largeCubeDerivGauge l k (omega k))
      (shellW1InfSmallerConst d * Real.sqrt ((l : ℝ) - (k : ℝ)) *
        (3 : ℝ) ^ (M.gamma * (k : ℝ))) := by
  have hd : (1 : ℕ) ≤ d := le_trans (by norm_num) M.shellPrefix.dimension
  have hpos : (0 : ℝ) < (3 : ℝ) ^ k := three_zpow_pos' k
  have hc : (0 : ℝ) ≤ 2 * (3 : ℝ) ^ k := by positivity
  have hcov := (isBigOWith_gammaSigma_shellDerivGaugeCover M l k).const_mul hc
  refine (hcov.of_le
    (fun omega => largeCubeDerivGauge_le_two_mul_shellDerivGaugeCover l k
      (omega k))).mono_scale ?_
  -- the amplitude arithmetic
  have hlogpos : (0 : ℝ) ≤
      3 * max 1 (Real.log (((subcubeShifts d k l).card : ℕ) : ℝ)) := by
    have h1 : (1 : ℝ) ≤ max 1 (Real.log (((subcubeShifts d k l).card : ℕ) : ℝ)) :=
      le_max_left _ _
    linarith
  have hlogbound := three_mul_max_one_log_card_subcubeShifts_le d
    (n := k) (l := l) hd hkl
  have hLnonneg : (0 : ℝ) ≤ largeCubeLogConst * (d : ℝ) := by
    have h1 : (0 : ℝ) ≤ largeCubeLogConst := largeCubeLogConst_pos.le
    have h2 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    exact mul_nonneg h1 h2
  have hsqrt : (3 * max 1 (Real.log (((subcubeShifts d k l).card : ℕ) : ℝ)))
      ^ (2 : ℝ)⁻¹ ≤
      Real.sqrt (largeCubeLogConst * (d : ℝ)) * Real.sqrt ((l : ℝ) - (k : ℝ)) := by
    rw [rpow_inv_two, ← Real.sqrt_mul hLnonneg]
    refine Real.sqrt_le_sqrt ?_
    calc 3 * max 1 (Real.log (((subcubeShifts d k l).card : ℕ) : ℝ))
        ≤ largeCubeLogConst * (d : ℝ) * ((l : ℝ) - (k : ℝ)) := hlogbound
      _ = largeCubeLogConst * (d : ℝ) * ((l : ℝ) - (k : ℝ)) := rfl
  have hrpow : (0 : ℝ) < (3 : ℝ) ^ (M.gamma * (k : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  calc 2 * (3 : ℝ) ^ k *
        ((3 * max 1 (Real.log (((subcubeShifts d k l).card : ℕ) : ℝ)))
            ^ (2 : ℝ)⁻¹ * Real.rpow 3 ((M.gamma - 1) * (k : ℝ)))
      = 2 * (3 * max 1 (Real.log (((subcubeShifts d k l).card : ℕ) : ℝ)))
            ^ (2 : ℝ)⁻¹ *
          ((3 : ℝ) ^ k * Real.rpow 3 ((M.gamma - 1) * (k : ℝ))) := by ring
    _ = 2 * (3 * max 1 (Real.log (((subcubeShifts d k l).card : ℕ) : ℝ)))
            ^ (2 : ℝ)⁻¹ * (3 : ℝ) ^ (M.gamma * (k : ℝ)) := by
          rw [three_zpow_mul_rpow_gamma_sub_one]
    _ ≤ 2 * (Real.sqrt (largeCubeLogConst * (d : ℝ)) *
            Real.sqrt ((l : ℝ) - (k : ℝ))) * (3 : ℝ) ^ (M.gamma * (k : ℝ)) := by
          refine mul_le_mul_of_nonneg_right ?_ hrpow.le
          exact mul_le_mul_of_nonneg_left hsqrt (by norm_num)
    _ = shellW1InfSmallerConst d * Real.sqrt ((l : ℝ) - (k : ℝ)) *
          (3 : ℝ) ^ (M.gamma * (k : ℝ)) := by
          rw [shellW1InfSmallerConst]
          ring

/-! ## The uniform per-shell estimate -/

/-- The dimensional constant covering both regimes of the source proof. -/
def shellW1InfConst (d : ℕ) : ℝ := shellW1InfSmallerConst d + 1

theorem shellW1InfConst_pos (d : ℕ) : 0 < shellW1InfConst d := by
  have := shellW1InfSmallerConst_nonneg d
  rw [shellW1InfConst]
  linarith

private theorem one_le_sqrt_max_one (a : ℝ) : (1 : ℝ) ≤ Real.sqrt (max 1 a) := by
  have h := Real.sqrt_le_sqrt (le_max_left (1 : ℝ) a)
  rwa [Real.sqrt_one] at h

/-- The per-shell estimate uniform in the two regimes of the source proof: for
`n < k` the source summand on `cu_l` is `O_{Γ₂}(C (1 ∨ (l-n))^{1/2} 3^{γk})`.

For `k < l` this is `e.W1inf.jL.bound.smaller` together with `l - k ≤ l - n`;
for `l ≤ k` it is `e.nabla.jk.O` on the smaller cube `cu_l ⊆ cu_k`, whose
amplitude carries no covering factor at all. -/
theorem isBigOWith_gammaSigma_largeCubeDerivGauge (M : ABKModel d) {l n k : ℤ}
    (hnk : n < k) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d => largeCubeDerivGauge l k (omega k))
      (shellW1InfConst d * Real.sqrt (max 1 ((l : ℝ) - (n : ℝ))) *
        (3 : ℝ) ^ (M.gamma * (k : ℝ))) := by
  have hnkR : (n : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hnk
  have hsq1 : (1 : ℝ) ≤ Real.sqrt (max 1 ((l : ℝ) - (n : ℝ))) :=
    one_le_sqrt_max_one _
  have hrpow : (0 : ℝ) < (3 : ℝ) ^ (M.gamma * (k : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hCsm := shellW1InfSmallerConst_nonneg d
  rcases lt_or_ge k l with hkl | hlk
  · refine (isBigOWith_gammaSigma_largeCubeDerivGauge_lt M hkl).mono_scale ?_
    have hle : Real.sqrt ((l : ℝ) - (k : ℝ)) ≤
        Real.sqrt (max 1 ((l : ℝ) - (n : ℝ))) := by
      refine Real.sqrt_le_sqrt (le_trans ?_ (le_max_right (1 : ℝ) _))
      linarith
    have hsq0 : (0 : ℝ) ≤ Real.sqrt ((l : ℝ) - (k : ℝ)) := Real.sqrt_nonneg _
    have hstep : shellW1InfSmallerConst d * Real.sqrt ((l : ℝ) - (k : ℝ)) ≤
        shellW1InfConst d * Real.sqrt (max 1 ((l : ℝ) - (n : ℝ))) := by
      rw [shellW1InfConst]
      nlinarith [hsq1, hle, hsq0, hCsm]
    exact mul_le_mul_of_nonneg_right hstep hrpow.le
  · have hpos : (0 : ℝ) < (3 : ℝ) ^ k := three_zpow_pos' k
    have hdom : ∀ omega : ShellSeq d,
        largeCubeDerivGauge l k (omega k) ≤
          (3 : ℝ) ^ k * (localCubeDerivNorm k (omega k) +
            (3 : ℝ) ^ k * localCubeSecondDerivNorm k (omega k)) := by
      intro omega
      rw [largeCubeDerivGauge_eq]
      refine mul_le_mul_of_nonneg_left ?_ hpos.le
      exact add_le_add (localCubeDerivNorm_mono hlk (omega k))
        (mul_le_mul_of_nonneg_left (localCubeSecondDerivNorm_mono hlk (omega k))
          hpos.le)
    refine (((isBigOWith_gammaSigma_shellDerivGauge M k).const_mul
      hpos.le).of_le hdom).mono_scale ?_
    rw [three_zpow_mul_rpow_gamma_sub_one]
    have hC1 : (1 : ℝ) ≤ shellW1InfConst d := by
      rw [shellW1InfConst]; linarith
    have hone : (1 : ℝ) ≤
        shellW1InfConst d * Real.sqrt (max 1 ((l : ℝ) - (n : ℝ))) := by
      nlinarith [hsq1, hC1]
    calc (3 : ℝ) ^ (M.gamma * (k : ℝ))
        = 1 * (3 : ℝ) ^ (M.gamma * (k : ℝ)) := (one_mul _).symm
      _ ≤ shellW1InfConst d * Real.sqrt (max 1 ((l : ℝ) - (n : ℝ))) *
            (3 : ℝ) ^ (M.gamma * (k : ℝ)) :=
          mul_le_mul_of_nonneg_right hone hrpow.le

/-! ## `e.W.1.inf.bound` -/

/-- The dimensional constant of ABK26's `e.W.1.inf.bound`. -/
def streamW1InfSumConst (d : ℕ) : ℝ :=
  IndependentSums.gammaTriangleConst 2 * shellW1InfConst d * (7 / Real.log 3)

theorem streamW1InfSumConst_pos (d : ℕ) : 0 < streamW1InfSumConst d := by
  have h1 : (0 : ℝ) < IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have h2 : (0 : ℝ) < shellW1InfConst d := shellW1InfConst_pos d
  have h3 : (0 : ℝ) < 7 / Real.log 3 := by
    have hlog : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    positivity
  rw [streamW1InfSumConst]
  exact mul_pos (mul_pos h1 h2) h3

/-- The geometric series of the source amplitudes:
`∑_{k ∈ (n,m]} 3^{γk} ≤ (7 / log 3) min{γ^{-1}, m-n} 3^{γm}`.  This is
`e.geo.part.sum` at the halved exponent. -/
theorem sum_Ioc_rpow_gamma_le (M : ABKModel d) {n m : ℤ} (hnm : n ≤ m) :
    ∑ k ∈ Finset.Ioc n m, (3 : ℝ) ^ (M.gamma * (k : ℝ)) ≤
      7 / Real.log 3 * min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
        (3 : ℝ) ^ (M.gamma * (m : ℝ)) := by
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hhalf : 0 < M.gamma / 2 := by linarith
  have hquarter : M.gamma / 2 ≤ 1 / 4 := by
    have := M.shellPrefix.gamma_le_quarter
    linarith
  have hbase := geo_part_sum_le_min_inv hhalf hquarter hnm
  have hexp : ∀ j : ℤ,
      (3 : ℝ) ^ (2 * (M.gamma / 2) * (j : ℝ)) =
        (3 : ℝ) ^ (M.gamma * (j : ℝ)) := by
    intro j
    congr 1
    ring
  simp only [hexp] at hbase
  have hmnR : (0 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by
    have : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    linarith
  have hinv : (M.gamma / 2)⁻¹ = 2 * M.gamma⁻¹ := by
    field_simp
  have hminle : min ((M.gamma / 2)⁻¹) ((m : ℝ) - (n : ℝ)) ≤
      2 * min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) := by
    rw [hinv]
    rcases le_total M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) with h | h
    · rw [min_eq_left h]
      exact min_le_left _ _
    · rw [min_eq_right h]
      have : min (2 * M.gamma⁻¹) ((m : ℝ) - (n : ℝ)) ≤ (m : ℝ) - (n : ℝ) :=
        min_le_right _ _
      linarith
  have hlog : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hmpow : (0 : ℝ) < (3 : ℝ) ^ (M.gamma * (m : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hchain : 2 * Real.log 3 *
      ∑ k ∈ Finset.Ioc n m, (3 : ℝ) ^ (M.gamma * (k : ℝ)) ≤
      14 * min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
        (3 : ℝ) ^ (M.gamma * (m : ℝ)) := by
    refine hbase.trans ?_
    have h7 : (0 : ℝ) ≤ 7 := by norm_num
    nlinarith [hminle, hmpow]
  have hsumnonneg : (0 : ℝ) ≤
      ∑ k ∈ Finset.Ioc n m, (3 : ℝ) ^ (M.gamma * (k : ℝ)) :=
    Finset.sum_nonneg fun k _ => (Real.rpow_pos_of_pos (by norm_num) _).le
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hlog]
  nlinarith [hchain]

/-- **ABK26's `e.W.1.inf.bound`**, in its corrected form: for every `n ≤ m`,

`∑_{k ∈ (n,m]} (3^k ‖∇j_k‖_{L∞(cu_l)} + 3^{2k} ‖∇²j_k‖_{L∞(cu_l)})
   ≤ O_{Γ₂}(C (1 ∨ (l-n))^{1/2} min{γ^{-1}, m-n} 3^{γm})`.

The source hypothesis `n ≤ l` is dropped: it is not needed, since for `l < n`
every shell of the range is estimated on the cube `cu_l ⊆ cu_k` at its own
scale. -/
theorem isBigOWith_gammaSigma_largeCubeDerivGaugeSum (M : ABKModel d) {l n m : ℤ}
    (hnm : n ≤ m) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d =>
        ∑ k ∈ Finset.Ioc n m, largeCubeDerivGauge l k (omega k))
      (streamW1InfSumConst d * Real.sqrt (max 1 ((l : ℝ) - (n : ℝ))) *
        min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
        (3 : ℝ) ^ (M.gamma * (m : ℝ))) := by
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hginv : (0 : ℝ) < M.gamma⁻¹ := inv_pos.2 hgamma
  have hsq1 : (1 : ℝ) ≤ Real.sqrt (max 1 ((l : ℝ) - (n : ℝ))) :=
    one_le_sqrt_max_one _
  have hmpow : (0 : ℝ) < (3 : ℝ) ^ (M.gamma * (m : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  rcases eq_or_lt_of_le hnm with rfl | hlt
  · refine isBigOWith_gammaSigma_of_eq_zero ?_ ?_
    · have hmin : min M.gamma⁻¹ ((n : ℝ) - (n : ℝ)) = 0 := by
        rw [sub_self]
        exact min_eq_right hginv.le
      rw [hmin]
      simp
    · intro omega
      simp
  · have hs : (Finset.Ioc n m).Nonempty := ⟨m, by simp only [Finset.mem_Ioc]; omega⟩
    have hnonneg : ∀ (k : ℤ) (omega : ShellSeq d),
        0 ≤ largeCubeDerivGauge l k (omega k) :=
      fun k omega => largeCubeDerivGauge_nonneg l k (omega k)
    have hapos : ∀ k ∈ Finset.Ioc n m,
        (0 : ℝ) < shellW1InfConst d * Real.sqrt (max 1 ((l : ℝ) - (n : ℝ))) *
          (3 : ℝ) ^ (M.gamma * (k : ℝ)) := by
      intro k _
      have h1 : (0 : ℝ) < shellW1InfConst d := shellW1InfConst_pos d
      have h2 : (0 : ℝ) < (3 : ℝ) ^ (M.gamma * (k : ℝ)) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have h3 : (0 : ℝ) < Real.sqrt (max 1 ((l : ℝ) - (n : ℝ))) := by linarith
      positivity
    have hbigO : ∀ k ∈ Finset.Ioc n m,
        IndependentSums.IsBigO M.P.toMeasure (IndependentSums.gammaSigma 2)
          (fun omega : ShellSeq d => largeCubeDerivGauge l k (omega k))
          (shellW1InfConst d * Real.sqrt (max 1 ((l : ℝ) - (n : ℝ))) *
            (3 : ℝ) ^ (M.gamma * (k : ℝ))) := by
      intro k hk
      have hnk : n < k := (Finset.mem_Ioc.mp hk).1
      exact (Orlicz.isBigOWith_iff_isBigO_of_nonneg (hnonneg k)).1
        (isBigOWith_gammaSigma_largeCubeDerivGauge M (n := n) hnk)
    have hmeas : ∀ k ∈ Finset.Ioc n m,
        Measurable (fun omega : ShellSeq d => largeCubeDerivGauge l k (omega k)) :=
      fun k _ => (measurable_largeCubeDerivGauge l k).comp (measurable_pi_apply k)
    have hfinite := IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma
      (μ := M.P.toMeasure) (Finset.Ioc n m)
      (X := fun k omega => largeCubeDerivGauge l k (omega k))
      (a := fun k : ℤ => shellW1InfConst d *
        Real.sqrt (max 1 ((l : ℝ) - (n : ℝ))) * (3 : ℝ) ^ (M.gamma * (k : ℝ)))
      (σ := 2) (by norm_num) hs hapos hbigO hmeas
    have hwith : IndependentSums.IsBigOWith M.P.toMeasure
        (IndependentSums.gammaSigma 2)
        (fun omega : ShellSeq d =>
          ∑ k ∈ Finset.Ioc n m, largeCubeDerivGauge l k (omega k))
        (IndependentSums.gammaTriangleConst 2 *
          ∑ k ∈ Finset.Ioc n m, shellW1InfConst d *
            Real.sqrt (max 1 ((l : ℝ) - (n : ℝ))) *
            (3 : ℝ) ^ (M.gamma * (k : ℝ))) :=
      (Orlicz.isBigOWith_iff_isBigO_of_nonneg
        (fun omega => Finset.sum_nonneg fun k _ => hnonneg k omega)).2 hfinite
    refine hwith.mono_scale ?_
    have hsumfac : ∑ k ∈ Finset.Ioc n m, shellW1InfConst d *
        Real.sqrt (max 1 ((l : ℝ) - (n : ℝ))) * (3 : ℝ) ^ (M.gamma * (k : ℝ)) =
        shellW1InfConst d * Real.sqrt (max 1 ((l : ℝ) - (n : ℝ))) *
          ∑ k ∈ Finset.Ioc n m, (3 : ℝ) ^ (M.gamma * (k : ℝ)) := by
      rw [Finset.mul_sum]
    rw [hsumfac]
    have hgeo := sum_Ioc_rpow_gamma_le M hnm
    have hCnn : (0 : ℝ) ≤ shellW1InfConst d * Real.sqrt (max 1 ((l : ℝ) - (n : ℝ))) := by
      have h1 : (0 : ℝ) < shellW1InfConst d := shellW1InfConst_pos d
      nlinarith [hsq1]
    have hTri : (0 : ℝ) < IndependentSums.gammaTriangleConst 2 :=
      IndependentSums.gammaTriangleConst_pos
    have hstep : IndependentSums.gammaTriangleConst 2 *
        (shellW1InfConst d * Real.sqrt (max 1 ((l : ℝ) - (n : ℝ))) *
          ∑ k ∈ Finset.Ioc n m, (3 : ℝ) ^ (M.gamma * (k : ℝ))) ≤
        IndependentSums.gammaTriangleConst 2 *
          (shellW1InfConst d * Real.sqrt (max 1 ((l : ℝ) - (n : ℝ))) *
            (7 / Real.log 3 * min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
              (3 : ℝ) ^ (M.gamma * (m : ℝ)))) := by
      refine mul_le_mul_of_nonneg_left ?_ hTri.le
      exact mul_le_mul_of_nonneg_left hgeo hCnn
    refine hstep.trans (le_of_eq ?_)
    rw [streamW1InfSumConst]
    ring

end

end Algsuperdiff.Section3.Provider.Stream
