/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.TranslatedTransport
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementLinfty
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.Maximum

/-!
# LargeCubeLinfty

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The large-cube `L∞` bound: ABK26's `e.km.kn.Linfty`

ABK26 upgrades the small-cube estimate `e.km.kn.Linfty.smallcube` to the large
cube `cu_l`: for `n < m ≤ l`,

`‖k_m - k_n‖²_{L∞(cu_l)} ≤ O_{Γ₁}(C (l-n) min{γ^{-1}, m-n} 3^{2γm})`,

by covering `cu_l` with translated copies of the small cube and applying the
maximum lemma `l.maximums.Gamma.s`, which costs the amplitude factor
`(log N)^{1/2}` with `N` the number of copies.

As in the small-cube layer, the statement is split into a deterministic part
and a probabilistic part, because the finite increment `k_m - k_n = ∑_{k ∈
(n,m]} j_k` is not itself a shell and so carries no `localCubeControl` gauge.

* `matrixOperatorNorm_finiteShellIncrement_le_largeCubeSupBound` is the
  deterministic part: at *every* point of `cu_l` the increment is dominated by
  the single random variable `largeCubeSupBound l n m`, the maximum of the
  translated small-cube bounds over the covering family.
* `isBigOWith_gammaSigma_one_largeCubeSupBound_sq` is the source display for the
  square of that random variable.

Composing the two gives the source display for every realization: the left-hand
side of `e.km.kn.Linfty` is the essential supremum over `cu_l` of the squared
matrix norm of the increment, which is at most `largeCubeSupBound l n m ^ 2`
pointwise on `cu_l`.

The covering family is explicit: the shifts are the lattice points of
`3^{n-1} ℤ^d` with coordinates bounded by `3^{(l-n+1)^+}`, and each translated
open cube has scale `n`.  Rounding each coordinate to the nearest lattice point
moves it by at most `3^{n-1}/2 < 3^n/2`, so the translated *open* cubes really
do cover the whole of `cu_l`, with no boundary exception.  The count is
`N = (2·3^{l-n+1} + 1)^d`, so `log N ≤ 3 d (l-n) log 3`, which is the source's
`(l-n)` factor with an explicit dimensional constant.

Deviations from the source, all absorbed by its `C(d)`:

* the covering lattice has spacing `3^{n-1}` rather than `3^n`, which is what
  makes the open cover exact; this multiplies `N` by `3^d` and is absorbed by
  the constant;
* the amplitude factor is `(3 max{1, log N})^{1/2}` rather than `(log
  N)^{1/2}`, from the proved cardinality-free maximum lemma.

## Main definitions

* `Algsuperdiff.Section3.Provider.Stream.translatedIncrementSupBound`
* `Algsuperdiff.Section3.Provider.Stream.subcubeShifts`
* `Algsuperdiff.Section3.Provider.Stream.largeCubeSupBound`
* `Algsuperdiff.Section3.Provider.Stream.largeCubeLinftyConst`

## Main results

* `Algsuperdiff.Section3.Provider.Stream.matrixOperatorNorm_finiteShellIncrement_le_largeCubeSupBound`
* `Algsuperdiff.Section3.Provider.Stream.isBigOWith_gammaSigma_largeCubeSupBound`
* `Algsuperdiff.Section3.Provider.Stream.isBigOWith_gammaSigma_one_largeCubeSupBound_sq`

## References

* ABK26, `e.km.kn.Linfty`.
* ABK26, `e.km.kn.Linfty.smallcube`.
* ABK26, Lemma `l.maximums.Gamma.s`.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory
open HCPolySupport
open HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## The stream increment at an arbitrary base point -/

/-- ABK26's `e.k.ell.upscales`, entrywise at an arbitrary base point `z`: for
`n < m` and every matrix entry,

`∑_{k = n+1}^m j_k(z)_{il} = O_{Γ₂}(C min{γ^{-1/2}, (m-n)^{1/2}} 3^{γm})`,

with an amplitude that does not depend on `z`. -/
theorem isBigO_gammaSigma_incrementAt_entry (M : ABKModel d) {n m : ℤ} (hnm : n < m)
    (z : Vec d) (i l : Fin d) :
    IndependentSums.IsBigO M.P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d => ∑ k ∈ Finset.Ioc n m, (omega k) z i l)
      (geometricConcentrationConst *
        min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
        (3 : ℝ) ^ (M.gamma * (m : ℝ))) :=
  isBigO_gammaSigma_two_sum_Ioc_geometric M.shellPrefix.gamma_pos
    M.shellPrefix.gamma_le_quarter hnm
    (iIndepFun_shell_entry M z i l)
    (fun k => (ShellField.measurable_eval_entry z i l).comp (measurable_pi_apply k))
    (fun k => isBigO_gammaSigma_shell_entry M k z i l)
    (fun k => integral_shell_entry_eq_zero M k z i l)

/-- ABK26's `e.k.ell.upscales` at an arbitrary base point `z`:

`|(k_m - k_n)(z)| ≤ O_{Γ₂}(C min{γ^{-1/2}, (m-n)^{1/2}} 3^{γm})`,

with `|·|` the exact Euclidean matrix operator norm.  This is the translated
form of `isBigOWith_gammaSigma_originIncrement`; the amplitude is the same,
which is where the stationarity half of (J1) enters through
`isBigO_gammaSigma_shell_entry`. -/
theorem isBigOWith_gammaSigma_incrementAt (M : ABKModel d) {n m : ℤ} (hnm : n < m)
    (z : Vec d) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d =>
        matrixOperatorNorm (finiteShellIncrement omega n m z))
      (IndependentSums.gammaTriangleConst 2 * ((d : ℝ) ^ 2 *
        (geometricConcentrationConst *
          min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
          (3 : ℝ) ^ (M.gamma * (m : ℝ))))) := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  have hAmp : (0 : ℝ) < geometricConcentrationConst *
      min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
      (3 : ℝ) ^ (M.gamma * (m : ℝ)) := by
    have hmin : 0 < min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) := by
      refine lt_min (Real.sqrt_pos.2 (inv_pos.2 M.shellPrefix.gamma_pos))
        (Real.sqrt_pos.2 ?_)
      have hlt : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
      linarith
    exact mul_pos (mul_pos geometricConcentrationConst_pos hmin)
      (Real.rpow_pos_of_pos (by norm_num) _)
  have hne : (Finset.univ : Finset (Fin d × Fin d)).Nonempty :=
    ⟨(⟨0, hd⟩, ⟨0, hd⟩), Finset.mem_univ _⟩
  have hentry : ∀ p : Fin d × Fin d,
      IndependentSums.IsBigO M.P.toMeasure (IndependentSums.gammaSigma 2)
        (fun omega : ShellSeq d => |∑ k ∈ Finset.Ioc n m, (omega k) z p.1 p.2|)
        (geometricConcentrationConst *
          min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
          (3 : ℝ) ^ (M.gamma * (m : ℝ))) := by
    intro p
    have h := isBigO_gammaSigma_incrementAt_entry M hnm z p.1 p.2
    have habs : (fun omega : ShellSeq d =>
        |(fun omega : ShellSeq d => |∑ k ∈ Finset.Ioc n m, (omega k) z p.1 p.2|)
          omega|) =
        fun omega : ShellSeq d => |∑ k ∈ Finset.Ioc n m, (omega k) z p.1 p.2| := by
      funext omega
      exact abs_abs _
    show IndependentSums.IsBigOWith _ _ _ _
    rw [habs]
    exact h
  have hmeas : ∀ p : Fin d × Fin d, Measurable (fun omega : ShellSeq d =>
      |∑ k ∈ Finset.Ioc n m, (omega k) z p.1 p.2|) := by
    intro p
    have hsummeas : Measurable (fun omega : ShellSeq d =>
        ∑ k ∈ Finset.Ioc n m, (omega k) z p.1 p.2) :=
      Finset.measurable_sum (Finset.Ioc n m) fun k _ =>
        (ShellField.measurable_eval_entry z p.1 p.2).comp (measurable_pi_apply k)
    have habs : (fun omega : ShellSeq d =>
        |∑ k ∈ Finset.Ioc n m, (omega k) z p.1 p.2|) =
        fun omega : ShellSeq d => ‖∑ k ∈ Finset.Ioc n m, (omega k) z p.1 p.2‖ := by
      funext omega
      exact (Real.norm_eq_abs _).symm
    rw [habs]
    exact Measurable.norm hsummeas
  have htriangle := IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := M.P.toMeasure) (Finset.univ : Finset (Fin d × Fin d))
    (X := fun p omega => |∑ k ∈ Finset.Ioc n m, (omega k) z p.1 p.2|)
    (a := fun _ : Fin d × Fin d => geometricConcentrationConst *
      min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
      (3 : ℝ) ^ (M.gamma * (m : ℝ)))
    (σ := 2) (by norm_num) hne (fun _ _ => hAmp) (fun p _ => hentry p)
    (fun p _ => hmeas p)
  have hcard : ∑ _p : Fin d × Fin d, (geometricConcentrationConst *
      min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
      (3 : ℝ) ^ (M.gamma * (m : ℝ))) =
      (d : ℝ) ^ 2 * (geometricConcentrationConst *
        min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
        (3 : ℝ) ^ (M.gamma * (m : ℝ))) := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin]
    push_cast
    ring
  rw [hcard] at htriangle
  refine htriangle.of_le fun omega => ?_
  refine (matrixOperatorNorm_le_sum_univ_abs_entry _).trans ?_
  refine le_trans (le_of_eq ?_) (le_abs_self _)
  exact Finset.sum_congr rfl fun p _ => by rw [finiteShellIncrement_apply_entry]

/-! ## The small-cube bound on a translated cube -/

/-- The shell sequence translated by a fixed vector. -/
def translateShellSeq (z : Vec d) (omega : ShellSeq d) : ShellSeq d :=
  fun k => ShellField.translate z (omega k)

/-- The random variable dominating `‖k_m - k_n‖_{L∞(z + cu_n)}`: the small-cube
bound `incrementSupBound` of the translated shell sequence. -/
def translatedIncrementSupBound (z : Vec d) (n m : ℤ) (omega : ShellSeq d) : ℝ :=
  incrementSupBound n m (translateShellSeq z omega)

/-- Translating the shell sequence translates the finite stream increment. -/
theorem finiteShellIncrement_translateShellSeq (z : Vec d) (omega : ShellSeq d)
    (n m : ℤ) (x : Vec d) :
    finiteShellIncrement (translateShellSeq z omega) n m x =
      finiteShellIncrement omega n m (x + z) := by
  rw [finiteShellIncrement_eq_sum, finiteShellIncrement_eq_sum]
  rfl

/-- The explicit form of the translated small-cube bound: the increment value at
the base point `z` plus the geometric factor times the summed first-derivative
gauges on the translated cube. -/
theorem translatedIncrementSupBound_eq (z : Vec d) (n m : ℤ) (omega : ShellSeq d) :
    translatedIncrementSupBound z n m omega =
      matrixOperatorNorm (finiteShellIncrement omega n m z) +
        (d : ℝ) ^ 2 * Real.sqrt d * ((3 : ℝ) ^ n / 2) *
          ∑ k ∈ Finset.Ioc n m,
            localCubeDerivNorm n (ShellField.translate z (omega k)) := by
  rw [translatedIncrementSupBound, incrementSupBound,
    finiteShellIncrement_translateShellSeq, zero_add]
  rfl

/-- The small-cube bound is nonnegative. -/
theorem incrementSupBound_nonneg (n m : ℤ) (omega : ShellSeq d) :
    0 ≤ incrementSupBound n m omega := by
  have h3n : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hgeo : (0 : ℝ) ≤ (d : ℝ) ^ 2 * Real.sqrt d * ((3 : ℝ) ^ n / 2) := by positivity
  exact add_nonneg (matrixOperatorNorm_nonneg _)
    (mul_nonneg hgeo
      (Finset.sum_nonneg fun k _ => localCubeDerivNorm_nonneg n (omega k)))

theorem translatedIncrementSupBound_nonneg (z : Vec d) (n m : ℤ)
    (omega : ShellSeq d) :
    0 ≤ translatedIncrementSupBound z n m omega :=
  incrementSupBound_nonneg n m (translateShellSeq z omega)

/-- The deterministic half of ABK26's `e.k.ell.upscales.infty` on a translated
cube: at every point of `z + cu_n` the finite stream increment is dominated by
`translatedIncrementSupBound z n m`. -/
theorem matrixOperatorNorm_finiteShellIncrement_le_translatedIncrementSupBound
    (z : Vec d) (omega : ShellSeq d) (n m : ℤ) {x : Vec d}
    (hx : x ∈ translateSet z (openCubeSet (originCube d n))) :
    matrixOperatorNorm (finiteShellIncrement omega n m x) ≤
      translatedIncrementSupBound z n m omega := by
  rw [mem_translateSet_iff_sub_mem] at hx
  have h := matrixOperatorNorm_finiteShellIncrement_le_incrementSupBound
    (translateShellSeq z omega) n m hx
  rwa [finiteShellIncrement_translateShellSeq, sub_add_cancel] at h

/-- The value of the finite stream increment at a fixed point is a measurable
random variable. -/
theorem measurable_matrixOperatorNorm_finiteShellIncrement (n m : ℤ) (z : Vec d) :
    Measurable (fun omega : ShellSeq d =>
      matrixOperatorNorm (finiteShellIncrement omega n m z)) := by
  have hvec : Measurable (fun omega : ShellSeq d =>
      finiteShellIncrement omega n m z) := by
    have hMAdd : MeasurableAdd₂ (Mat d) := by
      show MeasurableAdd₂ (Fin d → Fin d → ℝ)
      infer_instance
    have hrw : (fun omega : ShellSeq d => finiteShellIncrement omega n m z) =
        fun omega : ShellSeq d => ∑ k ∈ Finset.Ioc n m, (omega k) z := by
      funext omega
      exact finiteShellIncrement_eq_sum omega n m z
    rw [hrw]
    exact Finset.measurable_sum (Finset.Ioc n m) fun k _ =>
      (ShellField.measurable_eval z).comp (measurable_pi_apply k)
  exact (ShellField.continuous_matrixOperatorNorm).measurable.comp hvec

/-- The probabilistic half of ABK26's `e.k.ell.upscales.infty` on a translated
cube, at the same amplitude as at the origin. -/
theorem isBigOWith_gammaSigma_translatedIncrementSupBound (M : ABKModel d)
    {n m : ℤ} (hnm : n < m) (z : Vec d) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
      (translatedIncrementSupBound z n m)
      (streamLinftyConst d *
        min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
        (3 : ℝ) ^ (M.gamma * (m : ℝ))) := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hCT : (0 : ℝ) < IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have hKm : (0 : ℝ) < (3 : ℝ) ^ (M.gamma * (m : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have h3n : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hmn_real : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
  have hmin_pos : 0 < min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) :=
    lt_min (Real.sqrt_pos.2 (inv_pos.2 M.shellPrefix.gamma_pos))
      (Real.sqrt_pos.2 (by linarith))
  have hsd : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 hdR
  have hr : (0 : ℝ) < (3 : ℝ) ^ ((M.gamma - 1) * (n : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hgeo : (0 : ℝ) ≤ (d : ℝ) ^ 2 * Real.sqrt d * ((3 : ℝ) ^ n / 2) := by positivity
  have hA : (0 : ℝ) < geometricConcentrationConst *
      min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
      (3 : ℝ) ^ (M.gamma * (m : ℝ)) :=
    mul_pos (mul_pos geometricConcentrationConst_pos hmin_pos) hKm
  have ha0 : (0 : ℝ) < IndependentSums.gammaTriangleConst 2 *
      ((d : ℝ) ^ 2 * (geometricConcentrationConst *
        min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
        (3 : ℝ) ^ (M.gamma * (m : ℝ)))) :=
    mul_pos hCT (mul_pos (by positivity) hA)
  have ha1 : (0 : ℝ) < (d : ℝ) ^ 2 * Real.sqrt d * ((3 : ℝ) ^ n / 2) *
      (IndependentSums.gammaTriangleConst 2 *
        (3 : ℝ) ^ ((M.gamma - 1) * (n : ℝ))) := by positivity
  have hY0 : IndependentSums.IsBigO M.P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d =>
        matrixOperatorNorm (finiteShellIncrement omega n m z))
      (IndependentSums.gammaTriangleConst 2 *
        ((d : ℝ) ^ 2 * (geometricConcentrationConst *
          min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
          (3 : ℝ) ^ (M.gamma * (m : ℝ))))) :=
    (Orlicz.isBigOWith_iff_isBigO_of_nonneg
      (fun omega => matrixOperatorNorm_nonneg (finiteShellIncrement omega n m z))).1
      (isBigOWith_gammaSigma_incrementAt M hnm z)
  have hY1 : IndependentSums.IsBigO M.P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d => (d : ℝ) ^ 2 * Real.sqrt d * ((3 : ℝ) ^ n / 2) *
        ∑ k ∈ Finset.Ioc n m,
          localCubeDerivNorm n (ShellField.translate z (omega k)))
      ((d : ℝ) ^ 2 * Real.sqrt d * ((3 : ℝ) ^ n / 2) *
        (IndependentSums.gammaTriangleConst 2 *
          (3 : ℝ) ^ ((M.gamma - 1) * (n : ℝ)))) := by
    refine (Orlicz.isBigOWith_iff_isBigO_of_nonneg (fun omega => ?_)).1
      ((isBigOWith_gammaSigma_shellDerivNormSum_Ioc_translate M hnm z).const_mul hgeo)
    exact mul_nonneg hgeo (Finset.sum_nonneg fun k _ =>
      localCubeDerivNorm_nonneg n (ShellField.translate z (omega k)))
  have hcomb := isBigO_gammaSigma_add_of_isBigO (by norm_num : (0 : ℝ) < 2)
    ha0 ha1 hY0 hY1
    (measurable_matrixOperatorNorm_finiteShellIncrement n m z)
    (Measurable.const_mul
      (Finset.measurable_sum (Finset.Ioc n m) fun k _ =>
        ((measurable_localCubeDerivNorm n).comp
          (ShellField.measurable_translate z)).comp (measurable_pi_apply k)) _)
  have hnonneg : ∀ omega : ShellSeq d,
      0 ≤ translatedIncrementSupBound z n m omega :=
    fun omega => translatedIncrementSupBound_nonneg z n m omega
  have hrw : translatedIncrementSupBound z n m =
      fun omega : ShellSeq d =>
        matrixOperatorNorm (finiteShellIncrement omega n m z) +
          (d : ℝ) ^ 2 * Real.sqrt d * ((3 : ℝ) ^ n / 2) *
            ∑ k ∈ Finset.Ioc n m,
              localCubeDerivNorm n (ShellField.translate z (omega k)) :=
    funext fun omega => translatedIncrementSupBound_eq z n m omega
  refine (Orlicz.isBigOWith_iff_isBigO_of_nonneg hnonneg).2 ?_
  rw [hrw]
  refine hcomb.mono_scale ?_
  have hpow := zpow_mul_rpow_gamma_sub_one M.gamma n
  have hbound := rpow_gamma_mul_le_min_mul M hnm
  have hc : (0 : ℝ) ≤ IndependentSums.gammaTriangleConst 2 ^ 2 *
      ((d : ℝ) ^ 2 * (Real.sqrt d / 2)) := by positivity
  rw [streamLinftyConst]
  calc IndependentSums.gammaTriangleConst 2 *
        (IndependentSums.gammaTriangleConst 2 *
          ((d : ℝ) ^ 2 * (geometricConcentrationConst *
            min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
            (3 : ℝ) ^ (M.gamma * (m : ℝ)))) +
          (d : ℝ) ^ 2 * Real.sqrt d * ((3 : ℝ) ^ n / 2) *
            (IndependentSums.gammaTriangleConst 2 *
              (3 : ℝ) ^ ((M.gamma - 1) * (n : ℝ))))
      = IndependentSums.gammaTriangleConst 2 ^ 2 * (d : ℝ) ^ 2 *
            geometricConcentrationConst *
            min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
            (3 : ℝ) ^ (M.gamma * (m : ℝ)) +
          IndependentSums.gammaTriangleConst 2 ^ 2 *
            ((d : ℝ) ^ 2 * (Real.sqrt d / 2)) *
            ((3 : ℝ) ^ n * (3 : ℝ) ^ ((M.gamma - 1) * (n : ℝ))) := by ring
    _ = IndependentSums.gammaTriangleConst 2 ^ 2 * (d : ℝ) ^ 2 *
            geometricConcentrationConst *
            min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
            (3 : ℝ) ^ (M.gamma * (m : ℝ)) +
          IndependentSums.gammaTriangleConst 2 ^ 2 *
            ((d : ℝ) ^ 2 * (Real.sqrt d / 2)) *
            (3 : ℝ) ^ (M.gamma * (n : ℝ)) := by rw [hpow]
    _ ≤ IndependentSums.gammaTriangleConst 2 ^ 2 * (d : ℝ) ^ 2 *
            geometricConcentrationConst *
            min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
            (3 : ℝ) ^ (M.gamma * (m : ℝ)) +
          IndependentSums.gammaTriangleConst 2 ^ 2 *
            ((d : ℝ) ^ 2 * (Real.sqrt d / 2)) *
            (min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
              (3 : ℝ) ^ (M.gamma * (m : ℝ))) :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hbound hc)
    _ = IndependentSums.gammaTriangleConst 2 ^ 2 * (d : ℝ) ^ 2 *
          (geometricConcentrationConst + Real.sqrt d / 2) *
          min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
          (3 : ℝ) ^ (M.gamma * (m : ℝ)) := by ring

/-! ## A finite cover of the large cube by translated small cubes -/

/-- The per-coordinate lattice radius of the covering family: the shifts range
over the lattice `3^{n-1} ℤ^d` with integer coordinates bounded by
`3^{(l-n+1)^+}`. -/
def subcubeRadius (n l : ℤ) : ℕ := 3 ^ (l - n + 1).toNat

/-- The finite index set of lattice shifts covering `cu_l` by translates of
`cu_n`. -/
def subcubeShifts (d : ℕ) (n l : ℤ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ =>
    Finset.Icc (-(subcubeRadius n l : ℤ)) (subcubeRadius n l : ℤ)

/-- The lattice point of `3^{n-1} ℤ^d` attached to an index. -/
def subcubeCenter (n : ℤ) (p : Fin d → ℤ) : Vec d :=
  fun i => (3 : ℝ) ^ (n - 1) * (p i : ℝ)

theorem subcubeShifts_nonempty (d : ℕ) (n l : ℤ) :
    (subcubeShifts d n l).Nonempty := by
  refine ⟨fun _ => 0, ?_⟩
  rw [subcubeShifts, Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  exact ⟨neg_nonpos.2 (Int.natCast_nonneg _), Int.natCast_nonneg _⟩

theorem card_subcubeShifts (d : ℕ) (n l : ℤ) :
    (subcubeShifts d n l).card = (2 * subcubeRadius n l + 1) ^ d := by
  have hcard : (subcubeShifts d n l).card =
      ∏ _i : Fin d,
        ((subcubeRadius n l : ℤ) + 1 - -(subcubeRadius n l : ℤ)).toNat := by
    simp only [subcubeShifts, Fintype.card_piFinset, Int.card_Icc]
  rw [hcard, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

/-- The covering property: every point of the open cube `cu_l` lies in one of
the translated open cubes `z + cu_n` of the family.  Rounding each coordinate
to the nearest point of the lattice `3^{n-1} ℤ^d` moves it by at most
`3^{n-1}/2`, which is strictly less than the half-side `3^n/2`, so the *open*
cubes already cover `cu_l`. -/
theorem exists_subcubeShift_mem (n l : ℤ) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d l)) :
    ∃ p ∈ subcubeShifts d n l,
      x ∈ translateSet (subcubeCenter n p) (openCubeSet (originCube d n)) := by
  have hr : (0 : ℝ) < (3 : ℝ) ^ (n - 1) := zpow_pos (by norm_num) (n - 1)
  have hstep : (3 : ℝ) ^ (n - 1) * 3 = (3 : ℝ) ^ n := by
    rw [← zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0) (n - 1), sub_add_cancel]
  have hR1 : (1 : ℝ) ≤ (subcubeRadius n l : ℝ) := by
    have h1 : 1 ≤ subcubeRadius n l := Nat.one_le_pow _ _ (by norm_num)
    exact_mod_cast h1
  have hRpow : (3 : ℝ) ^ (l - n + 1) ≤ (subcubeRadius n l : ℝ) := by
    have hcast : ((subcubeRadius n l : ℕ) : ℝ) =
        (3 : ℝ) ^ (((l - n + 1).toNat : ℕ) : ℤ) := by
      rw [zpow_natCast, subcubeRadius]
      norm_cast
    rw [hcast]
    exact zpow_le_zpow_right₀ (by norm_num) (Int.self_le_toNat _)
  have hquot : ∀ i : Fin d,
      |x i / (3 : ℝ) ^ (n - 1)| < (1 / 2 : ℝ) * (3 : ℝ) ^ (l - n + 1) := by
    intro i
    have hxi := (mem_openCubeSet_originCube_iff.mp hx) i
    have habs : |x i| < (1 / 2 : ℝ) * (3 : ℝ) ^ l :=
      abs_lt.mpr ⟨by linarith [hxi.1], hxi.2⟩
    rw [abs_div, abs_of_pos hr, div_lt_iff₀ hr]
    have hmul : (1 / 2 : ℝ) * (3 : ℝ) ^ (l - n + 1) * (3 : ℝ) ^ (n - 1) =
        (1 / 2 : ℝ) * (3 : ℝ) ^ l := by
      rw [mul_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      congr 2
      ring
    rw [hmul]
    exact habs
  refine ⟨fun i => round (x i / (3 : ℝ) ^ (n - 1)), ?_, ?_⟩
  · rw [subcubeShifts, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have ht := abs_lt.mp (hquot i)
    have hd := abs_le.mp (abs_sub_round (x i / (3 : ℝ) ^ (n - 1)))
    constructor
    · have hlow : -(subcubeRadius n l : ℝ) ≤
          ((round (x i / (3 : ℝ) ^ (n - 1)) : ℤ) : ℝ) := by linarith
      exact_mod_cast hlow
    · have hhigh : ((round (x i / (3 : ℝ) ^ (n - 1)) : ℤ) : ℝ) ≤
          (subcubeRadius n l : ℝ) := by linarith
      exact_mod_cast hhigh
  · rw [mem_translateSet_iff_sub_mem, mem_openCubeSet_originCube_iff]
    intro i
    have hd := abs_le.mp (abs_sub_round (x i / (3 : ℝ) ^ (n - 1)))
    have hcoord : (x - subcubeCenter n (fun i => round (x i / (3 : ℝ) ^ (n - 1)))) i =
        x i - (3 : ℝ) ^ (n - 1) *
          ((round (x i / (3 : ℝ) ^ (n - 1)) : ℤ) : ℝ) := rfl
    have hmul : x i - (3 : ℝ) ^ (n - 1) *
        ((round (x i / (3 : ℝ) ^ (n - 1)) : ℤ) : ℝ) =
        (3 : ℝ) ^ (n - 1) *
          (x i / (3 : ℝ) ^ (n - 1) -
            ((round (x i / (3 : ℝ) ^ (n - 1)) : ℤ) : ℝ)) := by
      field_simp
    have hub : (3 : ℝ) ^ (n - 1) *
        (x i / (3 : ℝ) ^ (n - 1) -
          ((round (x i / (3 : ℝ) ^ (n - 1)) : ℤ) : ℝ)) ≤
        (3 : ℝ) ^ (n - 1) * (1 / 2) :=
      mul_le_mul_of_nonneg_left hd.2 hr.le
    have hlb : (3 : ℝ) ^ (n - 1) * (-(1 / 2)) ≤
        (3 : ℝ) ^ (n - 1) *
          (x i / (3 : ℝ) ^ (n - 1) -
            ((round (x i / (3 : ℝ) ^ (n - 1)) : ℤ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hd.1 hr.le
    rw [hcoord, hmul]
    constructor <;> linarith

/-! ## The maximum over the cover -/

/-- The single random variable dominating `‖k_m - k_n‖_{L∞(cu_l)}`: the maximum
of the translated small-cube bounds over the covering family. -/
def largeCubeSupBound (l n m : ℤ) (omega : ShellSeq d) : ℝ :=
  (subcubeShifts d n l).sup' (subcubeShifts_nonempty d n l)
    fun p => translatedIncrementSupBound (subcubeCenter n p) n m omega

theorem largeCubeSupBound_nonneg (l n m : ℤ) (omega : ShellSeq d) :
    0 ≤ largeCubeSupBound l n m omega := by
  obtain ⟨p, hp⟩ := subcubeShifts_nonempty d n l
  refine le_trans (translatedIncrementSupBound_nonneg (subcubeCenter n p) n m omega) ?_
  exact Finset.le_sup'
    (fun q : Fin d → ℤ => translatedIncrementSupBound (subcubeCenter n q) n m omega) hp

/-- The deterministic half of ABK26's `e.km.kn.Linfty`: at every point of `cu_l`
the finite stream increment is dominated by `largeCubeSupBound l n m`. -/
theorem matrixOperatorNorm_finiteShellIncrement_le_largeCubeSupBound
    (omega : ShellSeq d) (l n m : ℤ) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d l)) :
    matrixOperatorNorm (finiteShellIncrement omega n m x) ≤
      largeCubeSupBound l n m omega := by
  obtain ⟨p, hp, hmem⟩ := exists_subcubeShift_mem (d := d) n l hx
  refine le_trans
    (matrixOperatorNorm_finiteShellIncrement_le_translatedIncrementSupBound
      (subcubeCenter n p) omega n m hmem) ?_
  exact Finset.le_sup'
    (fun q : Fin d → ℤ => translatedIncrementSupBound (subcubeCenter n q) n m omega) hp

/-- The maximum over the cover, with the amplitude factor supplied by the proved
cardinality-free maximum lemma. -/
theorem isBigOWith_gammaSigma_largeCubeSupBound (M : ABKModel d) {l n m : ℤ}
    (hnm : n < m) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
      (largeCubeSupBound l n m)
      ((3 * max 1 (Real.log (((subcubeShifts d n l).card : ℕ) : ℝ))) ^ (2 : ℝ)⁻¹ *
        (streamLinftyConst d *
          min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
          (3 : ℝ) ^ (M.gamma * (m : ℝ)))) := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  have hmin_nonneg : (0 : ℝ) ≤
      min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) :=
    le_min (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hA : (0 : ℝ) ≤ streamLinftyConst d *
      min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
      (3 : ℝ) ^ (M.gamma * (m : ℝ)) :=
    mul_nonneg (mul_nonneg (streamLinftyConst_pos hd).le hmin_nonneg)
      (Real.rpow_pos_of_pos (by norm_num) _).le
  exact Orlicz.isBigOWith_gammaSigma_finset_sup'_of_nonempty
    (subcubeShifts d n l) (subcubeShifts_nonempty d n l) (by norm_num) hA
    fun p _ => isBigOWith_gammaSigma_translatedIncrementSupBound M hnm
      (subcubeCenter n p)

/-! ## The source display -/

/-- The universal factor produced by the maximum over the cover. -/
def largeCubeLogConst : ℝ := 3 * (1 + 3 * Real.log 3)

/-- The explicit dimensional constant of ABK26's `e.km.kn.Linfty`. -/
def largeCubeLinftyConst (d : ℕ) : ℝ :=
  largeCubeLogConst * (d : ℝ) * streamLinftyConst d ^ 2

theorem largeCubeLogConst_pos : 0 < largeCubeLogConst := by
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [largeCubeLogConst]
  linarith

theorem largeCubeLinftyConst_pos (hd : 0 < d) : 0 < largeCubeLinftyConst d := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hC : 0 < streamLinftyConst d := streamLinftyConst_pos hd
  rw [largeCubeLinftyConst]
  exact mul_pos (mul_pos largeCubeLogConst_pos hdR) (pow_pos hC 2)

/-- The count of the covering family is `(2·3^{l-n+1} + 1)^d`, so the amplitude
factor of the maximum lemma is at most `C(d) (l-n)`.  This is the source's
`(l-n)` factor, with an explicit dimensional constant. -/
theorem three_mul_max_one_log_card_subcubeShifts_le (d : ℕ) {n l : ℤ}
    (hd : 1 ≤ d) (hnl : n < l) :
    3 * max 1 (Real.log (((subcubeShifts d n l).card : ℕ) : ℝ)) ≤
      largeCubeLogConst * (d : ℝ) * ((l : ℝ) - (n : ℝ)) := by
  have hlog3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hlnZ : (1 : ℤ) ≤ l - n := by omega
  have hln : (1 : ℝ) ≤ (l : ℝ) - (n : ℝ) := by exact_mod_cast hlnZ
  have hD : (1 : ℝ) ≤ (d : ℝ) * ((l : ℝ) - (n : ℝ)) := by nlinarith
  have hRpos : 1 ≤ 3 ^ (l - n + 1).toNat := Nat.one_le_pow _ _ (by norm_num)
  have hle : 2 * 3 ^ (l - n + 1).toNat + 1 ≤ 3 ^ ((l - n + 1).toNat + 1) := by
    rw [pow_succ]
    omega
  have heZ : (((l - n + 1).toNat : ℕ) : ℤ) = l - n + 1 :=
    Int.toNat_of_nonneg (by omega)
  have heR : (((l - n + 1).toNat : ℕ) : ℝ) = (l : ℝ) - (n : ℝ) + 1 := by
    exact_mod_cast heZ
  have hlogN : Real.log (((subcubeShifts d n l).card : ℕ) : ℝ) ≤
      (d : ℝ) * ((l : ℝ) - (n : ℝ)) * (3 * Real.log 3) := by
    have hcard : ((subcubeShifts d n l).card : ℝ) =
        ((2 * 3 ^ (l - n + 1).toNat + 1 : ℕ) : ℝ) ^ d := by
      rw [card_subcubeShifts, subcubeRadius, Nat.cast_pow]
    have hposbase : (0 : ℝ) < ((2 * 3 ^ (l - n + 1).toNat + 1 : ℕ) : ℝ) := by
      have h0 : 0 < 2 * 3 ^ (l - n + 1).toNat + 1 := by omega
      exact_mod_cast h0
    have hmono : Real.log ((2 * 3 ^ (l - n + 1).toNat + 1 : ℕ) : ℝ) ≤
        Real.log (((3 : ℕ) ^ ((l - n + 1).toNat + 1) : ℕ) : ℝ) :=
      Real.log_le_log hposbase (by exact_mod_cast hle)
    have hpow : Real.log (((3 : ℕ) ^ ((l - n + 1).toNat + 1) : ℕ) : ℝ) =
        ((((l - n + 1).toNat : ℕ) : ℝ) + 1) * Real.log 3 := by
      have hc : ((((3 : ℕ) ^ ((l - n + 1).toNat + 1) : ℕ)) : ℝ) =
          (3 : ℝ) ^ ((l - n + 1).toNat + 1) := by
        norm_cast
      rw [hc, Real.log_pow]
      push_cast
      ring
    rw [hcard, Real.log_pow]
    have hstep : Real.log ((2 * 3 ^ (l - n + 1).toNat + 1 : ℕ) : ℝ) ≤
        ((l : ℝ) - (n : ℝ) + 2) * Real.log 3 := by
      rw [hpow, heR] at hmono
      calc Real.log ((2 * 3 ^ (l - n + 1).toNat + 1 : ℕ) : ℝ)
          ≤ ((l : ℝ) - (n : ℝ) + 1 + 1) * Real.log 3 := hmono
        _ = ((l : ℝ) - (n : ℝ) + 2) * Real.log 3 := by ring
    have hthree : ((l : ℝ) - (n : ℝ) + 2) * Real.log 3 ≤
        ((l : ℝ) - (n : ℝ)) * (3 * Real.log 3) := by nlinarith
    have hdpos : (0 : ℝ) ≤ (d : ℝ) := by linarith
    calc (d : ℝ) * Real.log ((2 * 3 ^ (l - n + 1).toNat + 1 : ℕ) : ℝ)
        ≤ (d : ℝ) * (((l : ℝ) - (n : ℝ)) * (3 * Real.log 3)) :=
          mul_le_mul_of_nonneg_left (hstep.trans hthree) hdpos
      _ = (d : ℝ) * ((l : ℝ) - (n : ℝ)) * (3 * Real.log 3) := by ring
  have hlogN0 : 0 ≤ Real.log (((subcubeShifts d n l).card : ℕ) : ℝ) := by
    refine Real.log_nonneg ?_
    have h1 : 1 ≤ (subcubeShifts d n l).card :=
      Finset.card_pos.mpr (subcubeShifts_nonempty d n l)
    exact_mod_cast h1
  have hmax : max 1 (Real.log (((subcubeShifts d n l).card : ℕ) : ℝ)) ≤
      1 + Real.log (((subcubeShifts d n l).card : ℕ) : ℝ) :=
    max_le (by linarith) (by linarith)
  rw [largeCubeLogConst]
  nlinarith

/-- ABK26's `e.km.kn.Linfty`:

`‖k_m - k_n‖²_{L∞(cu_l)} ≤ O_{Γ₁}(C (l-n) min{γ^{-1}, m-n} 3^{2γm})`.

The left-hand side is represented, as in the proved small-cube layer, by the
random variable `largeCubeSupBound l n m`, which dominates the matrix operator
norm of `k_m - k_n` at *every* point of `cu_l` by
`matrixOperatorNorm_finiteShellIncrement_le_largeCubeSupBound`.  The tail
exponent moves from `σ = 2` to `σ = 1` through the proved power rule
`e.powerofGammasigma` at `p = 2`, exactly as in the small-cube display. -/
theorem isBigOWith_gammaSigma_one_largeCubeSupBound_sq (M : ABKModel d) {l n m : ℤ}
    (hnm : n < m) (hml : m ≤ l) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 1)
      (fun omega : ShellSeq d => largeCubeSupBound l n m omega ^ 2)
      (largeCubeLinftyConst d * ((l : ℝ) - (n : ℝ)) *
        min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
        (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  have hginv : 0 < M.gamma⁻¹ := inv_pos.2 M.shellPrefix.gamma_pos
  have hmn_real : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
  have hnl : n < l := lt_of_lt_of_le hnm hml
  have hmin_nonneg : (0 : ℝ) ≤
      min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) :=
    le_min (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hKm : (0 : ℝ) < (3 : ℝ) ^ (M.gamma * (m : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hA : (0 : ℝ) ≤ streamLinftyConst d *
      min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
      (3 : ℝ) ^ (M.gamma * (m : ℝ)) :=
    mul_nonneg (mul_nonneg (streamLinftyConst_pos hd).le hmin_nonneg) hKm.le
  have hlogpos : (0 : ℝ) ≤
      3 * max 1 (Real.log (((subcubeShifts d n l).card : ℕ) : ℝ)) := by
    have h1 : (1 : ℝ) ≤ max 1 (Real.log (((subcubeShifts d n l).card : ℕ) : ℝ)) :=
      le_max_left _ _
    linarith
  have hK : (0 : ℝ) ≤
      (3 * max 1 (Real.log (((subcubeShifts d n l).card : ℕ) : ℝ))) ^ (2 : ℝ)⁻¹ *
        (streamLinftyConst d *
          min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
          (3 : ℝ) ^ (M.gamma * (m : ℝ))) :=
    mul_nonneg (Real.rpow_nonneg hlogpos _) hA
  have h := (Orlicz.isBigOWith_gammaSigma_sq_iff_of_nonneg (μ := M.P.toMeasure)
    (X := largeCubeSupBound l n m) (σ := 2) hK
    (largeCubeSupBound_nonneg l n m)).1
      (isBigOWith_gammaSigma_largeCubeSupBound M hnm)
  rw [show (2 : ℝ) / 2 = 1 by norm_num] at h
  refine h.mono_scale ?_
  have hrpow : ((3 * max 1 (Real.log (((subcubeShifts d n l).card : ℕ) : ℝ)))
      ^ (2 : ℝ)⁻¹) ^ 2 =
      3 * max 1 (Real.log (((subcubeShifts d n l).card : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast ((3 * max 1
      (Real.log (((subcubeShifts d n l).card : ℕ) : ℝ))) ^ (2 : ℝ)⁻¹) 2,
      ← Real.rpow_mul hlogpos,
      show (2 : ℝ)⁻¹ * ((2 : ℕ) : ℝ) = 1 by push_cast; ring, Real.rpow_one]
  have hs : (min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ)))) ^ 2 =
      min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) := by
    rcases le_total M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) with hle | hle
    · rw [min_eq_left (Real.sqrt_le_sqrt hle), min_eq_left hle,
        Real.sq_sqrt hginv.le]
    · rw [min_eq_right (Real.sqrt_le_sqrt hle), min_eq_right hle,
        Real.sq_sqrt (by linarith)]
  have hK2 : ((3 : ℝ) ^ (M.gamma * (m : ℝ))) ^ 2 =
      (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (M.gamma * (m : ℝ))) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    push_cast
    ring
  have hlogbound := three_mul_max_one_log_card_subcubeShifts_le d
    (n := n) (l := l) hd hnl
  have hrest : (0 : ℝ) ≤ streamLinftyConst d ^ 2 *
      min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by
    have h1 : (0 : ℝ) ≤ min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) :=
      le_min hginv.le (by linarith)
    have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) :=
      (Real.rpow_pos_of_pos (by norm_num) _).le
    exact mul_nonneg (mul_nonneg (sq_nonneg _) h1) h2
  calc ((3 * max 1 (Real.log (((subcubeShifts d n l).card : ℕ) : ℝ))) ^ (2 : ℝ)⁻¹ *
        (streamLinftyConst d *
          min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
          (3 : ℝ) ^ (M.gamma * (m : ℝ)))) ^ 2
      = (((3 * max 1 (Real.log (((subcubeShifts d n l).card : ℕ) : ℝ)))
            ^ (2 : ℝ)⁻¹) ^ 2) *
          (streamLinftyConst d ^ 2 *
            (min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ)))) ^ 2 *
            ((3 : ℝ) ^ (M.gamma * (m : ℝ))) ^ 2) := by ring
    _ = (3 * max 1 (Real.log (((subcubeShifts d n l).card : ℕ) : ℝ))) *
          (streamLinftyConst d ^ 2 * min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
            (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) := by rw [hrpow, hs, hK2]
    _ ≤ (largeCubeLogConst * (d : ℝ) * ((l : ℝ) - (n : ℝ))) *
          (streamLinftyConst d ^ 2 * min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
            (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) :=
        mul_le_mul_of_nonneg_right hlogbound hrest
    _ = largeCubeLinftyConst d * ((l : ℝ) - (n : ℝ)) *
          min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by
        rw [largeCubeLinftyConst]
        ring

end

end Algsuperdiff.Section3.Provider.Stream
