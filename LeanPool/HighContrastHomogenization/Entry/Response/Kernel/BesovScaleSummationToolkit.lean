/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.AdaptedCellFoundations
public import LeanPool.HighContrastHomogenization.Entry.CG.Proofs.AdaptedDomainRecovery
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.RecenteredResponseIntegrability
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.ResponseBlockObjects
public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.CanonicalCutoffPairingMeasurability
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.HeadCellDeficitInputs
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.RecentCellDefectBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.ScaleAverageSeminorm
public import LeanPool.HighContrastHomogenization.Entry.Setup.AdaptedGridCells
public import LeanPool.HighContrastHomogenization.Entry.Setup.ProjectiveDistance
public import LeanPool.HighContrastHomogenization.Support.Ambient.BlockMatrix
public import LeanPool.HighContrastHomogenization.Support.Ambient.CoefficientField
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.BasicVariationalIdentities
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.ResponseIdentities.Foundations.Algebra
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.ResponseIdentities.Foundations.Ellipticity
public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.Adapters
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Basic.Real.ConjExponents
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# High-contrast homogenization: Entry.Response.Kernel.BesovScaleSummationToolkit

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The Besov seminorm's scale toolkit and the cell-average energy bound

The all-scale maximum `ℳ = sup_{k ≤ t} 3^{-ρ(t-k)} max_z |(·)_+|` of `p.response.transfer`
dominates the normalized spectral defect of every triadic cell at every depth, and this file
records that a pathwise response dominated by `1 + ℳ` is integrable whenever `ℳ`'s `Q`-th moment
is, and that the pathwise response `J` is measurable in the sample for both recentred
coefficients. It bounds the scale-average (Besov) seminorm `[·]` of AK.HC (2.130), and its
square, by any geometrically growing per-scale majorant `A · 3^{ρ n}` with `ρ < 1`, and shows the
corresponding series is summable. It proves the exact partition-averaging identity - the
normalized sum of the averages of an integrable function over the depth-`n` triadic subcells of
an adapted cell equals the average over the parent cell - and the cell-average half of AK.HC
(2.15): the doubled cell average of a `b`-harmonic field on a cell `V` is controlled by the
pathwise symmetric energy of the field, via the variational (Fenchel) inequality together with
the canonical Cauchy-Schwarz bound.
-/

section
/-!
## Integrability of the all-scale envelope times the response

The all-scale maximum `ℳ = sup_{k <= t} 3^{-ρ(t-k)} max_z |(...)_+|` of
`p.response.transfer` dominates the normalized spectral defect of every
triadic cell at every depth, and the response estimate `e.response.weak.estimate` controls
its `Q`-th moment.  This file records the elementary consequence used when the envelope
multiplies a pathwise response: if `ℳ ^ Q` is `P`-integrable with `2 ≤ Q` and the response
`J` is square integrable, then `(1 + ℳ) J` is `P`-integrable.

Because `P` is a probability measure and `ℳ ≥ 0`, the pointwise bound
`ℳ ^ 2 ≤ 1 + ℳ ^ Q` (split at `ℳ = 1`) makes `ℳ` square integrable.  The product
`(1 + ℳ) J = J + ℳ J` is then a sum of integrable functions: `J` is integrable as an
`L²` function on a finite measure, and `ℳ J` is the product of two `L²` functions
(Hölder with conjugate exponents `2` and `2`).  The pathwise response is that of AK.HC (2.15).
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Integrability of `(1 + ℳ) J` from the envelope moment and square integrability of `J`.**
Let `ℳ = respAllScaleMax` be the all-scale maximum of `p.response.transfer`, let
`J` be measurable, and suppose `ℳ` is measurable, `ℳ ^ Q` is `P`-integrable with `2 ≤ Q`, and
`J ^ 2` is `P`-integrable.  Since `P` is a probability measure and `ℳ ≥ 0`, the bound
`ℳ ^ 2 ≤ 1 + ℳ ^ Q` gives `ℳ ∈ L²`; with `J ∈ L²` the product `ℳ J` is integrable by Hölder,
and `(1 + ℳ) J = J + ℳ J` is a sum of integrable functions. -/
private theorem integrable_one_add_respAllScaleMax_mul_of {d : ℕ} (γ : ℝ)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hMmeas : AEStronglyMeasurable (respAllScaleMax P γ jStar F t) P)
    (hMint : Integrable (fun a => respAllScaleMax P γ jStar F t a ^ bigQ d γ) P)
    (hQ : 2 ≤ bigQ d γ)
    (J : CoeffSpace d → ℝ)
    (hJsq : Integrable (fun a => J a ^ 2) P)
    (hJmeas : AEStronglyMeasurable J P) :
    Integrable (fun a => (1 + respAllScaleMax P γ jStar F t a) * J a) P := by
  have hM2int : Integrable (fun a => respAllScaleMax P γ jStar F t a ^ 2) P := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hMint) (hMmeas.pow 2) ?_
    filter_upwards with a
    have h0 : 0 ≤ respAllScaleMax P γ jStar F t a := respAllScaleMax_nonneg P γ jStar F t a
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 2)]
    simp only [Pi.add_apply]
    rcases le_or_gt (respAllScaleMax P γ jStar F t a) 1 with h1 | h1
    · have hsq : respAllScaleMax P γ jStar F t a ^ 2 ≤ 1 := pow_le_one₀ h0 h1
      have hQnn : (0 : ℝ) ≤ respAllScaleMax P γ jStar F t a ^ bigQ d γ := pow_nonneg h0 _
      linarith only [hsq, hQnn]
    · have hsq : respAllScaleMax P γ jStar F t a ^ 2 ≤
          respAllScaleMax P γ jStar F t a ^ bigQ d γ := pow_le_pow_right₀ h1.le hQ
      have hQnn : (0 : ℝ) ≤ respAllScaleMax P γ jStar F t a ^ bigQ d γ := pow_nonneg h0 _
      linarith only [hsq, hQnn]
  have hMmemLp : MemLp (respAllScaleMax P γ jStar F t) 2 P :=
    (memLp_two_iff_integrable_sq hMmeas).2 hM2int
  have hJmemLp : MemLp J 2 P := (memLp_two_iff_integrable_sq hJmeas).2 hJsq
  have hJint : Integrable J P := hJmemLp.integrable (by norm_num)
  have : ENNReal.HolderTriple 2 2 1 := by
    simpa only [ENNReal.ofReal_ofNat] using Real.HolderConjugate.two_two.ennrealOfReal
  have hMJint : Integrable (respAllScaleMax P γ jStar F t * J) P :=
    hMmemLp.integrable_mul hJmemLp
  have hsum : Integrable (J + respAllScaleMax P γ jStar F t * J) P := hJint.add hMJint
  exact hsum.congr (Filter.Eventually.of_forall fun a => by
    simp only [Pi.add_apply, Pi.mul_apply]
    ring)

/-- **Integrability of the all-scale envelope times the recentred response.**  For a probability
law `P`, the all-scale maximum `ℳ` of `p.response.transfer` with `Q`-th moment
integrable, `2 ≤ Q`, multiplies the pathwise recentred response `J(U_t; a_-, p, q')` of
AK.HC (2.15) into a `P`-integrable function: `(1 + ℳ) J` is integrable whenever `ℳ` is
measurable and `J ^ 2` is integrable and measurable. -/
theorem integrable_one_add_respAllScaleMax_mul_respJ {d : ℕ} (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (jStar : ℕ) (F : BlockMat d) (t : ℤ) (p q' : Vec d)
    (hMmeas : AEStronglyMeasurable (respAllScaleMax P γ jStar F t) P)
    (hMint : Integrable (fun a => respAllScaleMax P γ jStar F t a ^ bigQ d γ) P)
    (hQ : 2 ≤ bigQ d γ)
    (hJsq : Integrable (fun a => respJ (respGrid jStar F) t p q' (respCoeffMinus F a) ^ 2) P)
    (hJmeas : AEStronglyMeasurable
      (fun a => respJ (respGrid jStar F) t p q' (respCoeffMinus F a)) P) :
    Integrable (fun a =>
      (1 + respAllScaleMax P γ jStar F t a) *
        respJ (respGrid jStar F) t p q' (respCoeffMinus F a)) P := by
  have _ := hd
  have _ := hγ
  exact integrable_one_add_respAllScaleMax_mul_of γ P jStar F t hMmeas hMint hQ
    (fun a => respJ (respGrid jStar F) t p q' (respCoeffMinus F a)) hJsq hJmeas

/-- **Integrability of the all-scale envelope times the adjoint recentred response.**  The
adjoint twin of `integrable_one_add_respAllScaleMax_mul_respJ`: the same probability-law
argument applies with the pathwise adjoint recentred response `J(U_t; a_+, p, q')` of
AK.HC (2.15) in place of `J(U_t; a_-, p, q')`, so `(1 + ℳ) J` is `P`-integrable under the
same envelope-moment, measurability and square-integrability hypotheses. -/
theorem integrable_one_add_respAllScaleMax_mul_respJPlus {d : ℕ} (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (jStar : ℕ) (F : BlockMat d) (t : ℤ) (p q' : Vec d)
    (hMmeas : AEStronglyMeasurable (respAllScaleMax P γ jStar F t) P)
    (hMint : Integrable (fun a => respAllScaleMax P γ jStar F t a ^ bigQ d γ) P)
    (hQ : 2 ≤ bigQ d γ)
    (hJsq : Integrable (fun a => respJ (respGrid jStar F) t p q' (respCoeffPlus F a) ^ 2) P)
    (hJmeas : AEStronglyMeasurable
      (fun a => respJ (respGrid jStar F) t p q' (respCoeffPlus F a)) P) :
    Integrable (fun a =>
      (1 + respAllScaleMax P γ jStar F t a) *
        respJ (respGrid jStar F) t p q' (respCoeffPlus F a)) P := by
  have _ := hd
  have _ := hγ
  exact integrable_one_add_respAllScaleMax_mul_of γ P jStar F t hMmeas hMint hQ
    (fun a => respJ (respGrid jStar F) t p q' (respCoeffPlus F a)) hJsq hJmeas

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The unweighted quadratic readout of the canonical cutoff pairing

The cutoff pairing of `e.response.cutoff.estimate` expands into one quadratic term and three
linear terms (AK.HC Lemma A.1, (A.4)).  `CanonicalCutoffPairingMeasurability` treats the three
linear
terms, and the quadratic term reduces to the cutoff-weighted block self-pairing of the canonical
optimizer state.

This file treats the unweighted quadratic readout, the full-cell energy of the canonical
optimizer,

`a ↦ volumeAverage (adaptedCell q t) (fun x => vecDot Z(a,x).1 Z(a,x).2)`,

where `Z(a,·)` is the canonical optimizer state.  The flux slot of that state is the recentred
coefficient applied to its gradient slot, so the integrand is the `a`-energy density
`⟨∇v, a ∇v⟩` of the canonical maximizer.  The full-cell average of that density is the doubled
maximizer energy, which is twice the pathwise response `J(adaptedCell q t, p, r)` of the
recentred coefficient.  The pathwise response is an explicit block quadratic of the coarse
block, hence a measurable function of the sample, so the unweighted quadratic readout is
measurable in the sample with no hypothesis beyond the cutoff class data.  This is the `φ = 1`
case of the quadratic term of the expansion.

The genuinely cutoff-weighted readout is local and is not the full-cell energy; its
measurability is the block self-pairing statement of the canonical optimizer state.
-/

open HCPolySupport.HighContrast (CoeffSpace blockVecDot_blockMatVecMul_eq_sum
  toFullBlockMat_eq_blockMatEntry)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Measurability of the recentred pathwise responses -/

/-- The recentred minus pathwise response on an adapted cell is measurable in the sample.  It is
the explicit block quadratic of the recentred coarse block (AK.HC (2.15)), whose flattened
entries are measurable. -/
theorem measurable_respJ_respCoeffMinus [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (p r : Vec d) :
    Measurable fun a : CoeffSpace d => respJ q t p r (respCoeffMinus F a) := by
  have hpath : (fun a : CoeffSpace d => respJ q t p r (respCoeffMinus F a))
      = fun a : CoeffSpace d =>
        (1 / 2 : ℝ) * blockVecDot (-p, r)
            (blockMatVecMul
              (coarseBlockMatrix (HighContrast.adaptedCell q t) (respCoeffMinus F a)) (-p, r))
          - vecDot p r := by
    funext a
    exact respJ_respCoeffMinus_eq q hq t F a p r
  rw [hpath]
  have hentry : ∀ α β : BlockCoord d, Measurable fun a : CoeffSpace d =>
      blockMatEntry (coarseBlockMatrix (HighContrast.adaptedCell q t)
        (respCoeffMinus F a)) α β := by
    intro α β
    have h := measurable_coarseBlockMatrix_minus (q := q) hq t 0 F α β
    simpa only [adaptedCellAtCenter_zero, toFullBlockMat_eq_blockMatEntry] using h
  have hquad : Measurable fun a : CoeffSpace d =>
      blockVecDot (-p, r)
        (blockMatVecMul
          (coarseBlockMatrix (HighContrast.adaptedCell q t) (respCoeffMinus F a)) (-p, r)) := by
    have hsum : (fun a : CoeffSpace d => blockVecDot (-p, r)
        (blockMatVecMul
          (coarseBlockMatrix (HighContrast.adaptedCell q t) (respCoeffMinus F a)) (-p, r)))
        = fun a : CoeffSpace d => ∑ α : BlockCoord d, ∑ β : BlockCoord d,
            toFullBlockVec (-p, r) α *
              (blockMatEntry
                  (coarseBlockMatrix (HighContrast.adaptedCell q t) (respCoeffMinus F a)) α β *
                toFullBlockVec (-p, r) β) := by
      funext a
      rw [blockVecDot_blockMatVecMul_eq_sum]
    rw [hsum]
    exact Finset.measurable_sum Finset.univ fun α _ =>
      Finset.measurable_sum Finset.univ fun β _ =>
        ((hentry α β).mul_const _).const_mul _
  exact (hquad.const_mul (1 / 2 : ℝ)).sub measurable_const

/-- The recentred plus pathwise response on an adapted cell is measurable in the sample.  It is
the explicit block quadratic of the adjoint recentred coarse block, whose flattened entries are
measurable. -/
theorem measurable_respJ_respCoeffPlus [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (p r : Vec d) :
    Measurable fun a : CoeffSpace d => respJ q t p r (respCoeffPlus F a) := by
  have hpath : (fun a : CoeffSpace d => respJ q t p r (respCoeffPlus F a))
      = fun a : CoeffSpace d =>
        (1 / 2 : ℝ) * blockVecDot (-p, r)
            (blockMatVecMul
              (coarseBlockMatrix (HighContrast.adaptedCell q t) (respCoeffPlus F a)) (-p, r))
          - vecDot p r := by
    funext a
    exact respJ_respCoeffPlus_eq q hq t F a p r
  rw [hpath]
  have hentry : ∀ α β : BlockCoord d, Measurable fun a : CoeffSpace d =>
      blockMatEntry (coarseBlockMatrix (HighContrast.adaptedCell q t)
        (respCoeffPlus F a)) α β := by
    intro α β
    have h := measurable_coarseBlockMatrix_plus (q := q) hq t 0 F α β
    simpa only [adaptedCellAtCenter_zero, toFullBlockMat_eq_blockMatEntry] using h
  have hquad : Measurable fun a : CoeffSpace d =>
      blockVecDot (-p, r)
        (blockMatVecMul
          (coarseBlockMatrix (HighContrast.adaptedCell q t) (respCoeffPlus F a)) (-p, r)) := by
    have hsum : (fun a : CoeffSpace d => blockVecDot (-p, r)
        (blockMatVecMul
          (coarseBlockMatrix (HighContrast.adaptedCell q t) (respCoeffPlus F a)) (-p, r)))
        = fun a : CoeffSpace d => ∑ α : BlockCoord d, ∑ β : BlockCoord d,
            toFullBlockVec (-p, r) α *
              (blockMatEntry
                  (coarseBlockMatrix (HighContrast.adaptedCell q t) (respCoeffPlus F a)) α β *
                toFullBlockVec (-p, r) β) := by
      funext a
      rw [blockVecDot_blockMatVecMul_eq_sum]
    rw [hsum]
    exact Finset.measurable_sum Finset.univ fun α _ =>
      Finset.measurable_sum Finset.univ fun β _ =>
        ((hentry α β).mul_const _).const_mul _
  exact (hquad.const_mul (1 / 2 : ℝ)).sub measurable_const

/-! ## The full-cell quadratic readout as twice the pathwise response -/

/-! ## The unweighted quadratic readouts as pathwise responses -/

/-! ## Measurability of the unweighted quadratic readouts -/

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## HC bridge III: the scale-weighted summation of the seminorm (AK.HC (2.130))

The scale-average seminorm of AK.HC (2.130) is a series of per-scale averages.  The preceding
bridge `ScaleAverageSeminorm` bounds it against the constant per-scale majorant `cellMeanSq`.
Here the
per-scale majorant is allowed to grow geometrically, `A * 3 ^ (ρ * n)` with `ρ < 1`, which is the
shape produced by the multiscale coarse-block envelope.  The chain is the same three steps: a
termwise bound against the scale majorant, summability by comparison with a geometric series, and
the resulting bound on `besovSeminorm`.
-/

namespace HCPolySupport.HighContrast.Multiscale

noncomputable section

variable {d : ℕ}

/-- Termwise bound for the scale-average seminorm against a geometrically growing per-scale
majorant.  If the squared average at depth `n` is at most `A * 3 ^ (ρ * n)` with `ρ < 1`, then the
weighted `n`-th summand of the seminorm of AK.HC (2.130) is at most
`3 ^ (t / 2) * sqrt A * (3 ^ ((ρ - 1) / 2)) ^ n`, i.e. the scale weight and the growing majorant
combine into the geometric ratio `3 ^ ((ρ - 1) / 2) < 1`. -/
theorem besov_term_le_of_scale_bound {d : ℕ} (t : ℤ) (ρ A : ℝ)
    (hρ : ρ < 1) (hρ0 : 0 ≤ ρ) (hA : 0 ≤ A)
    (avg : ℕ → (Fin d → ℤ) → BlockVec d)
    (h : ∀ n : ℕ, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w) ≤
          A * (3 : ℝ) ^ (ρ * (n : ℝ)))
    (n : ℕ) :
    (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) *
        Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w))
      ≤ (3 : ℝ) ^ ((t : ℝ) / 2) * Real.sqrt A * ((3 : ℝ) ^ ((ρ - 1) / 2)) ^ n := by
  have _ := hρ
  have _ := hρ0
  have hle := h n
  have hsqrt := Real.sqrt_le_sqrt hle
  have hbase : 0 ≤ (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
  have hsqrt3 : Real.sqrt ((3 : ℝ) ^ (ρ * (n : ℝ))) =
      (3 : ℝ) ^ (ρ * (n : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  have hpow : ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n * (3 : ℝ) ^ (ρ * (n : ℝ) / 2) =
      ((3 : ℝ) ^ ((ρ - 1) / 2)) ^ n := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(1 / 2 : ℝ))) n,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      ← Real.rpow_natCast ((3 : ℝ) ^ ((ρ - 1) / 2)) n,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hEq : (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) *
        Real.sqrt (A * (3 : ℝ) ^ (ρ * (n : ℝ))) =
      (3 : ℝ) ^ ((t : ℝ) / 2) * Real.sqrt A * ((3 : ℝ) ^ ((ρ - 1) / 2)) ^ n := by
    rw [Real.sqrt_mul hA, hsqrt3, three_rpow_scale_split t n]
    calc ((3 : ℝ) ^ ((t : ℝ) / 2) * ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n) *
          (Real.sqrt A * (3 : ℝ) ^ (ρ * (n : ℝ) / 2))
        = (3 : ℝ) ^ ((t : ℝ) / 2) * Real.sqrt A *
            (((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n * (3 : ℝ) ^ (ρ * (n : ℝ) / 2)) := by
          ring
      _ = (3 : ℝ) ^ ((t : ℝ) / 2) * Real.sqrt A *
            ((3 : ℝ) ^ ((ρ - 1) / 2)) ^ n := by rw [hpow]
  exact (mul_le_mul_of_nonneg_left hsqrt hbase).trans (le_of_eq hEq)

/-- The series defining the scale-average seminorm of AK.HC (2.130) is summable when the squared
per-scale averages grow at most like `A * 3 ^ (ρ * n)` with `ρ < 1`, since each summand is then
dominated by a geometric multiple of `3 ^ ((ρ - 1) / 2) < 1`. -/
theorem summable_besov_of_scale_bound {d : ℕ} (t : ℤ) (ρ A : ℝ)
    (hρ : ρ < 1) (hρ0 : 0 ≤ ρ) (hA : 0 ≤ A)
    (avg : ℕ → (Fin d → ℤ) → BlockVec d)
    (h : ∀ n : ℕ, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w) ≤
          A * (3 : ℝ) ^ (ρ * (n : ℝ))) :
    Summable fun n : ℕ => (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) *
      Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w)) := by
  have hr0 : 0 ≤ (3 : ℝ) ^ ((ρ - 1) / 2) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
  have hr1 : (3 : ℝ) ^ ((ρ - 1) / 2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3) (by linarith only [hρ])
  refine Summable.of_nonneg_of_le (fun n => ?_)
    (fun n => besov_term_le_of_scale_bound t ρ A hρ hρ0 hA avg h n)
    ((summable_geometric_of_lt_one hr0 hr1).mul_left
      ((3 : ℝ) ^ ((t : ℝ) / 2) * Real.sqrt A))
  exact mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _) (Real.sqrt_nonneg _)

/-- The scale-average seminorm of AK.HC (2.130) is bounded by the geometric series of its
per-scale majorant: for a squared per-scale average at most `A * 3 ^ (ρ * n)` with `ρ < 1`,
`besovSeminorm t avg ≤ 3 ^ (t / 2) * sqrt A * (1 - 3 ^ ((ρ - 1) / 2))⁻¹`. -/
theorem besovSeminorm_le_of_scale_bound {d : ℕ} (t : ℤ) (ρ A : ℝ)
    (hρ : ρ < 1) (hρ0 : 0 ≤ ρ) (hA : 0 ≤ A)
    (avg : ℕ → (Fin d → ℤ) → BlockVec d)
    (h : ∀ n : ℕ, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w) ≤
          A * (3 : ℝ) ^ (ρ * (n : ℝ))) :
    besovSeminorm t avg ≤
      (3 : ℝ) ^ ((t : ℝ) / 2) * Real.sqrt A * (1 - (3 : ℝ) ^ ((ρ - 1) / 2))⁻¹ := by
  have hr0 : 0 ≤ (3 : ℝ) ^ ((ρ - 1) / 2) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
  have hr1 : (3 : ℝ) ^ ((ρ - 1) / 2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3) (by linarith only [hρ])
  have hsum := summable_besov_of_scale_bound t ρ A hρ hρ0 hA avg h
  have hmaj : Summable fun n : ℕ =>
      (3 : ℝ) ^ ((t : ℝ) / 2) * Real.sqrt A * ((3 : ℝ) ^ ((ρ - 1) / 2)) ^ n :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hb : besovSeminorm t avg ≤
      ∑' n : ℕ, (3 : ℝ) ^ ((t : ℝ) / 2) * Real.sqrt A * ((3 : ℝ) ^ ((ρ - 1) / 2)) ^ n := by
    unfold besovSeminorm
    exact Summable.tsum_le_tsum
      (fun n => besov_term_le_of_scale_bound t ρ A hρ hρ0 hA avg h n) hsum hmaj
  have htsum : (∑' n : ℕ,
        (3 : ℝ) ^ ((t : ℝ) / 2) * Real.sqrt A * ((3 : ℝ) ^ ((ρ - 1) / 2)) ^ n) =
      (3 : ℝ) ^ ((t : ℝ) / 2) * Real.sqrt A * (1 - (3 : ℝ) ^ ((ρ - 1) / 2))⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  rwa [htsum] at hb

/-- Squared form of the preceding bound.  For a squared per-scale average at most
`A * 3 ^ (ρ * n)` with `ρ < 1`,
`besovSeminorm t avg ^ 2 ≤ ((1 - 3 ^ ((ρ - 1) / 2))⁻¹) ^ 2 * (3 ^ t * A)`. -/
theorem besovSeminorm_sq_le_of_scale_bound {d : ℕ} (t : ℤ) (ρ A : ℝ)
    (hρ : ρ < 1) (hρ0 : 0 ≤ ρ) (hA : 0 ≤ A)
    (avg : ℕ → (Fin d → ℤ) → BlockVec d)
    (h : ∀ n : ℕ, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w) ≤
          A * (3 : ℝ) ^ (ρ * (n : ℝ))) :
    besovSeminorm t avg ^ 2 ≤
      ((1 - (3 : ℝ) ^ ((ρ - 1) / 2))⁻¹) ^ 2 * ((3 : ℝ) ^ (t : ℝ) * A) := by
  have hle := besovSeminorm_le_of_scale_bound t ρ A hρ hρ0 hA avg h
  have hb0 : 0 ≤ besovSeminorm t avg := by
    unfold besovSeminorm
    exact tsum_nonneg fun n =>
      mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _) (Real.sqrt_nonneg _)
  have hsq := pow_le_pow_left₀ hb0 hle 2
  have h3sq : ((3 : ℝ) ^ ((t : ℝ) / 2)) ^ (2 : ℕ) = (3 : ℝ) ^ (t : ℝ) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ ((t : ℝ) / 2)) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  calc besovSeminorm t avg ^ 2
      ≤ ((3 : ℝ) ^ ((t : ℝ) / 2) * Real.sqrt A *
          (1 - (3 : ℝ) ^ ((ρ - 1) / 2))⁻¹) ^ 2 := hsq
    _ = ((1 - (3 : ℝ) ^ ((ρ - 1) / 2))⁻¹) ^ 2 * ((3 : ℝ) ^ (t : ℝ) * A) := by
        rw [mul_pow, mul_pow, h3sq, Real.sq_sqrt hA]
        ring

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Exact partition averaging for a cell average

The `3 ^ (n * d)` depth-`n` triadic subcells `adaptedCellAtCenter q (t - n) w`, indexed by
`w ∈ triadicIndexBox d n`, partition the adapted cell `HighContrast.adaptedCell q t` up to a null
set,
and all have the same volume.  Hence the normalized sum of their averages of an integrable
function is the average over the parent cell.  This isolates the partition step used in the proof
of the response weak estimate `e.response.weak.estimate`.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The triadic index box `triadicIndexBox d n` is exactly the set of depth-`n` index labels
whose standard-cell center lies in the generation-`t` centered cube. -/
theorem triadicIndexBox_eq_centerSet (t : ℤ) (n : ℕ) :
    (triadicIndexBox d n : Set (Fin d → ℤ)) =
      {w : Fin d → ℤ |
        HighContrast.standardCellCenter (t - (n : ℤ)) w ∈ HighContrast.centeredCube d t} := by
  obtain ⟨b, hb⟩ : Odd ((3 : ℕ) ^ n) := Odd.pow (by decide)
  have hm : (((3 ^ n - 1) / 2 : ℕ) : ℤ) = (b : ℤ) := by
    have hone : 1 ≤ (3 : ℕ) ^ n := Nat.one_le_pow _ _ (by norm_num)
    omega
  ext w
  change w ∈ triadicIndexBox d n ↔
    HighContrast.standardCellCenter (t - (n : ℤ)) w ∈ HighContrast.centeredCube d t
  rw [triadicIndexBox, Fintype.mem_piFinset]
  have hmem : HighContrast.standardCellCenter (t - (n : ℤ)) w ∈
      HighContrast.centeredCube d (t - (n : ℤ) + (n : ℤ)) ↔
        ∀ i, -(b : ℤ) ≤ w i ∧ w i ≤ (b : ℤ) :=
    HCPolySupport.HighContrast.Annealed.alignedCenter_mem_iff d (t - (n : ℤ)) n w b hb
  rw [show t - (n : ℤ) + (n : ℤ) = t by ring] at hmem
  rw [hmem]
  constructor
  · intro h i
    have hi := h i
    rw [Finset.mem_Icc, hm] at hi
    exact hi
  · intro h i
    rw [Finset.mem_Icc, hm]
    exact h i

/-- Exact partition averaging: the normalized sum of the averages of an integrable function over
the `3 ^ (n * d)` depth-`n` triadic subcells equals the average over the adapted parent cell.
This is the partition step in the proof of the response weak estimate
`e.response.weak.estimate`. -/
theorem avsum_volumeAverage_eq (q : Mat d) (hq : IsUnit q) (t : ℤ) (n : ℕ)
    {f : Vec d → ℝ} (hf : IntegrableOn f (HighContrast.adaptedCell q t)) :
    (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) f
      = volumeAverage (HighContrast.adaptedCell q t) f := by
  classical
  have _ : NeZero d := inferInstance
  set U : Set (Vec d) := HighContrast.adaptedCell q t with hU
  set V : (Fin d → ℤ) → Set (Vec d) := fun w => adaptedCellAtCenter q (t - (n : ℤ)) w with hV
  have hUreal : (volume U).toReal = |q.det| * ((3 : ℝ) ^ t) ^ d :=
    Geometry.volume_adaptedCell_toReal q t
  have hVmeas : ∀ w, MeasurableSet (V w) :=
    fun w => (isOpen_adaptedCellAtCenter_of_isUnit hq _ w).measurableSet
  have hVreal : ∀ w, (volume (V w)).toReal = |q.det| * ((3 : ℝ) ^ (t - (n : ℤ))) ^ d := by
    intro w
    rw [hV, Geometry.volume_adaptedCellAtCenter]
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (abs_nonneg _),
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ (t - (n : ℤ)))]
  have hVconst : ∀ w, (volume (V w)).toReal = (volume (V 0)).toReal := by
    intro w; rw [hVreal w, hVreal 0]
  have hsub : ∀ w ∈ triadicIndexBox d n, V w ⊆ U := by
    intro w hw
    rw [hU, hV]
    exact adaptedCellAtCenter_subset_adaptedCell q t n hw
  have hVint : ∀ w ∈ triadicIndexBox d n, IntegrableOn f (V w) :=
    fun w hw => hf.mono_set (hsub w hw)
  have hdisj : Set.Pairwise (↑(triadicIndexBox d n) : Set (Fin d → ℤ))
      (Function.onFun Disjoint V) := by
    intro a _ b _ hab
    exact Geometry.adaptedCellAtCenter_disjoint_of_ne hq (t - (n : ℤ)) hab
  have hunion : ∫ x in (⋃ w ∈ triadicIndexBox d n, V w), f x
      = ∑ w ∈ triadicIndexBox d n, ∫ x in V w, f x :=
    integral_biUnion_finset _ (fun w _ => hVmeas w) hdisj hVint
  have hcover : volume (U \ ⋃ w ∈ triadicIndexBox d n, V w) = 0 := by
    rw [hU, hV]
    exact adaptedCell_diff_biUnion_null q hq t n
  have hae : U =ᵐ[volume] (⋃ w ∈ triadicIndexBox d n, V w) := by
    rw [ae_eq_set]
    refine ⟨hcover, ?_⟩
    have hsubU : (⋃ w ∈ triadicIndexBox d n, V w) ⊆ U :=
      Set.iUnion₂_subset (fun w hw => hsub w hw)
    rw [Set.sdiff_eq_empty.mpr hsubU, measure_empty]
  have hInt : ∫ x in U, f x = ∫ x in (⋃ w ∈ triadicIndexBox d n, V w), f x :=
    setIntegral_congr_set hae
  have hNcard : ((triadicIndexBox d n).card : ℝ) = ((3 : ℝ) ^ n) ^ d := card_triadicIndexBox n
  have hprod : ((triadicIndexBox d n).card : ℝ) * (volume (V 0)).toReal = (volume U).toReal := by
    rw [hNcard, hVreal 0, hUreal]
    have h3 : (3 : ℝ) ^ n * (3 : ℝ) ^ (t - (n : ℤ)) = (3 : ℝ) ^ t := by
      rw [show ((3 : ℝ) ^ n) = (3 : ℝ) ^ ((n : ℤ)) from (zpow_natCast (3 : ℝ) n).symm,
        ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      ring_nf
    calc ((3 : ℝ) ^ n) ^ d * (|q.det| * ((3 : ℝ) ^ (t - (n : ℤ))) ^ d)
        = |q.det| * ((3 : ℝ) ^ n * (3 : ℝ) ^ (t - (n : ℤ))) ^ d := by rw [mul_pow]; ring
      _ = |q.det| * ((3 : ℝ) ^ t) ^ d := by rw [h3]
  have hcoef : ((triadicIndexBox d n).card : ℝ)⁻¹ * ((volume (V 0)).toReal)⁻¹
      = (((triadicIndexBox d n).card : ℝ) * (volume (V 0)).toReal)⁻¹ := by
    rw [mul_inv]
  calc (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, volumeAverage (V w) f
      = (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, (volume (V 0)).toReal⁻¹ * ∫ x in V w, f x := by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro w _
        rw [volumeAverage, hVconst w]
    _ = (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ((volume (V 0)).toReal⁻¹ * ∑ w ∈ triadicIndexBox d n, ∫ x in V w, f x) := by
        rw [← Finset.mul_sum]
    _ = (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ((volume (V 0)).toReal⁻¹ * ∫ x in U, f x) := by
        rw [← hunion, hInt]
    _ = (((triadicIndexBox d n).card : ℝ) * (volume (V 0)).toReal)⁻¹ * ∫ x in U, f x := by
        rw [← mul_assoc, hcoef]
    _ = volumeAverage U f := by
        rw [hprod, volumeAverage]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The cell-average energy bound

The cell-average half of AK.HC (2.15): the doubled cell average of a `b`-harmonic field on a cell
`V` is controlled by the pathwise symmetric energy of the field, with the constant supplied by the
quadratic form of the coarse block of `b` on `V` augmented by the swap block `𝐑`.  The proof
combines the variational (Fenchel) inequality satisfied by every admissible field with the
canonical response--coarse-block identity on a bounded open convex domain.
-/

open HCPolySupport.HighContrast.CG

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Fenchel's algebraic core of the cell-average energy bound.  A vector `W` that satisfies the
variational inequality for the quadratic form of `B` is controlled by `E` as soon as `B` is
bounded above by `K` times the identity form.  This is the algebraic step of the cell-average half
of AK.HC (2.15). -/
theorem blockVecDot_self_le_of_forall_dot_le {d : ℕ} (W : BlockVec d) (B : BlockMat d)
    (E K : ℝ) (hK : 0 < K)
    (hB : ∀ X : BlockVec d, blockVecDot X (blockMatVecMul B X) ≤ K * blockVecDot X X)
    (hvar : ∀ X : BlockVec d, blockVecDot X W ≤
      (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul B X) + (1 / 2 : ℝ) * E) :
    blockVecDot W W ≤ K * E := by
  have hKinv : 0 < K⁻¹ := inv_pos.mpr hK
  have hvar' := hvar (K⁻¹ • W)
  have h1 : blockVecDot (K⁻¹ • W) W = K⁻¹ * blockVecDot W W := by
    rw [blockVecDot_smul_left]
  have h2 : blockVecDot (K⁻¹ • W) (blockMatVecMul B (K⁻¹ • W)) =
      (K⁻¹ * K⁻¹) * blockVecDot W (blockMatVecMul B W) := by
    rw [blockMatVecMul_smul, blockVecDot_smul_right, blockVecDot_smul_left]
    ring
  rw [h1, h2] at hvar'
  have hcoef : 0 ≤ K⁻¹ * K⁻¹ := mul_nonneg (le_of_lt hKinv) (le_of_lt hKinv)
  have hsimp : (K⁻¹ * K⁻¹) * (K * blockVecDot W W) = K⁻¹ * blockVecDot W W := by
    field_simp
  have hP : (K⁻¹ * K⁻¹) * blockVecDot W (blockMatVecMul B W) ≤
      K⁻¹ * blockVecDot W W := by
    have hmono := mul_le_mul_of_nonneg_left (hB W) hcoef
    rwa [hsimp] at hmono
  have hstep : K⁻¹ * blockVecDot W W ≤
      (1 / 2 : ℝ) * (K⁻¹ * blockVecDot W W) + (1 / 2 : ℝ) * E := by
    have hhalf := mul_le_mul_of_nonneg_left hP (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith only [hvar', hhalf]
  have hfin : K⁻¹ * blockVecDot W W ≤ E := by linarith only [hstep]
  have hmul := mul_le_mul_of_nonneg_left hfin (le_of_lt hK)
  have hleft : K * (K⁻¹ * blockVecDot W W) = blockVecDot W W := by
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hK), one_mul]
  rwa [hleft] at hmul

/-- The quadratic form of a componentwise sum of doubled blocks is the sum of their quadratic
forms on a common doubled probe. -/
private theorem blockVecDot_blockMatVecMul_ofFullBlockMat_add {d : ℕ} (A B : BlockMat d)
    (X : BlockVec d) :
    blockVecDot X
        (blockMatVecMul (ofFullBlockMat (toFullBlockMat A + toFullBlockMat B)) X) =
      blockVecDot X (blockMatVecMul A X) + blockVecDot X (blockMatVecMul B X) := by
  rw [← dotProduct_toFullBlockVec, ← dotProduct_toFullBlockVec, ← dotProduct_toFullBlockVec,
    toFullBlockVec_blockMatVecMul, toFullBlockVec_blockMatVecMul, toFullBlockVec_blockMatVecMul,
    toFullBlockMat_ofFullBlockMat, Matrix.add_mulVec, dotProduct_add]

/-- The volume average of the scalar response integrand of a `b`-harmonic field on a cell is
minus one half of its pathwise symmetric energy, plus the pairing of `(-p, r)` with the
slot-swapped cell average of the optimizer field.  This is the algebraic expansion behind the
cell-average half of AK.HC (2.15). -/
private theorem volumeAverage_scalarResponseIntegrand_eq_blockVecDot {d : ℕ} {V : Set (Vec d)}
    {b : CoeffField d} (hInt : ResponseLinearIntegrabilityData V b)
    (p r : Vec d) (v : AHarmonicFunction b V) :
    volumeAverage V (scalarResponseIntegrand V b p r v) =
      - (1 / 2 : ℝ) * volumeAverage V (scalarVariationEnergyIntegrand b v)
        + blockVecDot (-p, r)
            (blockMatVecMul (blockSwap d) (cellAverage V (optimizerField b v))) := by
  have hE : MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand b v) V := hInt.energy v
  have hF : MeasureTheory.IntegrableOn
      (fun x => vecDot p (matVecMul (b x) (v.toH1.grad x))) V := hInt.flux p v
  have hG : MeasureTheory.IntegrableOn (fun x => vecDot r (v.toH1.grad x)) V := hInt.grad r v
  have hA : MeasureTheory.IntegrableOn
      (((-(1 / 2 : ℝ)) • scalarVariationEnergyIntegrand b v)) V :=
    hE.integrable.smul (-(1 / 2 : ℝ))
  have hAB : MeasureTheory.IntegrableOn
      (((-(1 / 2 : ℝ)) • scalarVariationEnergyIntegrand b v) -
        fun x => vecDot p (matVecMul (b x) (v.toH1.grad x))) V :=
    hA.integrable.sub hF.integrable
  have hcompF : ∀ i, MeasureTheory.IntegrableOn
      (fun x => matVecMul (b x) (v.toH1.grad x) i) V :=
    fun i => by simpa [vecDot_single_left] using hInt.flux (Pi.single i 1) v
  have hcompG : ∀ i, MeasureTheory.IntegrableOn (fun x => v.toH1.grad x i) V :=
    fun i => by simpa [vecDot_single_left] using hInt.grad (Pi.single i 1) v
  have hdecomp : scalarResponseIntegrand V b p r v =
      (((-(1 / 2 : ℝ)) • scalarVariationEnergyIntegrand b v) -
        (fun x => vecDot p (matVecMul (b x) (v.toH1.grad x)))) +
        (fun x => vecDot r (v.toH1.grad x)) := by
    funext x
    simp only [scalarResponseIntegrand, scalarVariationEnergyIntegrand, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  rw [hdecomp, volumeAverage_add hAB hG, volumeAverage_sub hA hF, volumeAverage_smul]
  rw [volumeAverage_vecDot_left p (fun x => matVecMul (b x) (v.toH1.grad x)) hcompF,
    volumeAverage_vecDot_left r (fun x => v.toH1.grad x) hcompG]
  have hZ1 : (cellAverage V (optimizerField b v)).1
      = fun i => volumeAverage V (fun x => v.toH1.grad x i) := rfl
  have hZ2 : (cellAverage V (optimizerField b v)).2
      = fun i => volumeAverage V (fun x => matVecMul (b x) (v.toH1.grad x) i) := rfl
  have hs1 : (blockMatVecMul (blockSwap d) (cellAverage V (optimizerField b v))).1
      = (cellAverage V (optimizerField b v)).2 := blockMatVecMul_blockSwap_fst _
  have hs2 : (blockMatVecMul (blockSwap d) (cellAverage V (optimizerField b v))).2
      = (cellAverage V (optimizerField b v)).1 := blockMatVecMul_blockSwap_snd _
  rw [blockVecDot, hs1, hs2, hZ1, hZ2, vecDot_neg_left]
  ring

/-- The variational (Fenchel) inequality for the doubled cell average of a `b`-harmonic field on
a cell `V`: for every doubled probe `X`, the pairing of `X` with the slot-swapped cell average of
the optimizer field is bounded by half the quadratic form of the coarse block of `b` augmented by
the swap block `𝐑`, plus half the pathwise symmetric energy of the field.  This is the
variational step of the cell-average half of AK.HC (2.15), stated with the hypotheses of the
canonical response--coarse-block identity on a bounded open convex domain. -/
theorem forall_blockVecDot_cellAverage_optimizerField_le {d : ℕ} [NeZero d]
    {V : Set (Vec d)} {lam Lam : ℝ} {b : CoeffField d}
    (hConv : IsOpenBoundedConvexDomain V) (hEll : IsEllipticFieldOn lam Lam V b)
    (hvol : 0 < (volume V).toReal) (v : AHarmonicFunction b V) :
    ∀ X : BlockVec d,
      blockVecDot X (blockMatVecMul (blockSwap d) (cellAverage V (optimizerField b v))) ≤
        (1 / 2 : ℝ) * blockVecDot X
            (blockMatVecMul
              (ofFullBlockMat (toFullBlockMat (coarseBlockMatrix V b) +
                toFullBlockMat (blockSwap d))) X)
          + (1 / 2 : ℝ) * volumeAverage V (scalarVariationEnergyIntegrand b v) := by
  intro X
  let : IsFiniteMeasure (volumeMeasureOn V) := hConv.isFiniteMeasure_restrict_volume
  have hInt : ResponseLinearIntegrabilityData V b :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have hscalar : volumeAverage V (scalarResponseIntegrand V b (-X.1) X.2 v) ≤
      ResponseJ V (-X.1) X.2 b :=
    le_responseJ_of_mem_responseJValueSet_of_isEllipticFieldOn hEll (ne_of_gt hvol)
      (-X.1) X.2 (responseJValueSet_mem V (-X.1) X.2 b v)
  rw [responseJ_eq_block_quadratic_of_isOpenBoundedConvexDomain hConv hEll hvol (-X.1) X.2,
    volumeAverage_scalarResponseIntegrand_eq_blockVecDot hInt (-X.1) X.2 v] at hscalar
  have hpair : (-(-X.1), X.2) = X := by
    ext <;> simp
  rw [hpair] at hscalar
  have hneg : - vecDot (-X.1) X.2 =
      (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul (blockSwap d) X) := by
    rw [blockVecDot, blockMatVecMul_blockSwap_fst, blockMatVecMul_blockSwap_snd,
      vecDot_neg_left, neg_neg, vecDot_comm X.2 X.1]
    ring
  have hrhs : (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul (coarseBlockMatrix V b) X)
        - vecDot (-X.1) X.2 =
      (1 / 2 : ℝ) * blockVecDot X
        (blockMatVecMul
          (ofFullBlockMat (toFullBlockMat (coarseBlockMatrix V b) +
            toFullBlockMat (blockSwap d))) X) := by
    rw [sub_eq_add_neg, hneg, ← mul_add, ← blockVecDot_blockMatVecMul_ofFullBlockMat_add]
  rw [hrhs] at hscalar
  linarith only [hscalar]

/-- The cell-average energy bound: the squared doubled cell average of a `b`-harmonic field on a
cell `V` is bounded by the pathwise symmetric energy of the field times any positive constant `K`
that bounds above the quadratic form of the coarse block of `b` on `V` augmented by the swap block
`𝐑`.  This is the cell-average half of AK.HC (2.15). -/
theorem blockVecDot_cellAverage_optimizerField_self_le {d : ℕ} [NeZero d]
    {V : Set (Vec d)} {lam Lam : ℝ} {b : CoeffField d}
    (hConv : IsOpenBoundedConvexDomain V) (hEll : IsEllipticFieldOn lam Lam V b)
    (hvol : 0 < (volume V).toReal) (v : AHarmonicFunction b V)
    (K : ℝ) (hK : 0 < K)
    (hB : ∀ X : BlockVec d,
      blockVecDot X
        (blockMatVecMul
          (ofFullBlockMat (toFullBlockMat (coarseBlockMatrix V b) +
            toFullBlockMat (blockSwap d))) X) ≤ K * blockVecDot X X) :
    blockVecDot (cellAverage V (optimizerField b v)) (cellAverage V (optimizerField b v)) ≤
      K * volumeAverage V (scalarVariationEnergyIntegrand b v) := by
  have hvar := forall_blockVecDot_cellAverage_optimizerField_le hConv hEll hvol v
  have h := blockVecDot_self_le_of_forall_dot_le
    (blockMatVecMul (blockSwap d) (cellAverage V (optimizerField b v)))
    (ofFullBlockMat (toFullBlockMat (coarseBlockMatrix V b) + toFullBlockMat (blockSwap d)))
    (volumeAverage V (scalarVariationEnergyIntegrand b v)) K hK hB hvar
  have hWW : blockVecDot
        (blockMatVecMul (blockSwap d) (cellAverage V (optimizerField b v)))
        (blockMatVecMul (blockSwap d) (cellAverage V (optimizerField b v))) =
      blockVecDot (cellAverage V (optimizerField b v)) (cellAverage V (optimizerField b v)) := by
    rw [blockVecDot, blockMatVecMul_blockSwap_fst, blockMatVecMul_blockSwap_snd, blockVecDot]
    ring
  rw [hWW] at h
  exact h

end

end HCPolySupport.HighContrast.Multiscale
end
