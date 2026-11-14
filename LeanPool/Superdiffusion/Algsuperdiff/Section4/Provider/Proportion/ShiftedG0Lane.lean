/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.RatioTailClosed
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.ShiftedConcentration

/-!
# ShiftedG0Lane

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `𝒢₀` proportion tail on a window based at an arbitrary scale `m₀`

ABK26, §4.1, `e.no.bad.scales.applied.for.lambdas` for the `𝒢₀` lane, on the
window `{m₀,…,m₀+n}` rather than `{0,…,n}`.

The level-uniform `𝒢₀` endpoint is stated for the base-`0` window that
`IndicatorDensity.scaleProp` hard-codes.  Downstream
consumers read the proportion over a window that starts at an arbitrary scale
`m₀`, and the manuscript's own reduction is "translate the array".
`ShiftedConcentration` carries out that translation once and generically; this
module feeds the `𝒢₀` lane's array and event family through it.

## Main results

* `hreduce_eventG0_all` — the proved deterministic reduction of the `𝒢₀` bad
  event into the Appendix-D threshold event, at **every** scale `m : ℤ`.
* `ratioTail_Ycal_shift` — the `𝒢₀`-lane proportion tail engine on the window
  `{m₀,…,m₀+n}`: the base-`0` hypothesis list, with the deterministic reduction
  asked at every `m : ℤ`.
* `exists_ratioTail_eventG0_uniform_shift` — the level-uniform endpoint on the
  window `{m₀,…,m₀+n}`, with the constant `C(d)` and the range `r(d)` chosen
  before `M`, before `θ` and before the base `m₀`.

## The base-independence of the constants

`m₀` and the window length `n` are quantified **last**, after `r`, `C`, the
model, the level and the rate.  So the numerical package — the three `θ`-free
floors, the budget `E = C c⋆^{−1}`, the atom exponent `u = c⋆²/(C_cg C² γ)`, the
moment exponent `p = exp(u/6)` and the normalizer `D` — is built once and does
not see the base scale.  The base enters only through the diagonal translation of
the Appendix-D array, which is what `ShiftedConcentration` proves is free.

## Scope

Provider material: proved local helpers.

## References

* ABK26, `l.good.scales.ratio.lambda`; `p.concentration.for.scales`.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory ProbabilityTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Probability
open Algsuperdiff.Section4.Probability.ScalesConcentration
open Algsuperdiff.Section4.Probability.IndicatorDensity
open scoped ENNReal

noncomputable section

/-! ## 1. The order-8 opening of the exponential

The abstract-real helper; the only transcendental atom in this file that a
numeric step ever sees, and it is discharged before any carrier appears. -/

/-- `exp(−w) ≤ 40320/w⁸` for `w > 0` (the order-8 companion of
`exp_neg_le_seven`). -/
private theorem exp_neg_le_eight {w : ℝ} (hw : 0 < w) :
    Real.exp (-w) ≤ 40320 / w ^ (8 : ℕ) := by
  have hbase := Real.pow_div_factorial_le_exp (x := w) hw.le 8
  have hfac : ((Nat.factorial 8 : ℕ) : ℝ) = 40320 := by norm_num [Nat.factorial]
  rw [hfac] at hbase
  have hwn : (0 : ℝ) < w ^ (8 : ℕ) := pow_pos hw 8
  rw [Real.exp_neg]
  have h := inv_anti₀ (div_pos hwn (by norm_num : (0 : ℝ) < 40320)) hbase
  rwa [inv_div] at h


/-! ## 2. The deterministic reduction, at every scale

A window based at `m₀ < 0` needs the deterministic reduction of the `𝒢₀` bad
event at negative scales.  The statement below carries no sign condition on `m`,
which costs nothing: `RowSumFinite.lt_Yk_of_notMem_eventG0` carries none
either. -/

/-- **The `hreduce` slot at every scale `m : ℤ`.**  `hthr` is the manuscript's
own threshold identification: the Appendix-D level `9 s'^{-1} C_⋆^{1/p}
θ^{-1/p}` must sit below the normalizer's reciprocal. -/
theorem hreduce_eventG0_all {d : ℕ} (M : ABKModel d) (Ccg : ℝ) {p theta D : ℝ}
    (hD : 0 < D)
    (hthr : 9 * (M.gamma / 4)⁻¹ * Cstar ^ (1 / p) * theta ^ (-1 / p) ≤ D⁻¹)
    (m : ℤ) (omega : Cutoff.CutoffSample d)
    (homega : omega ∈ (Support.eventG0 M Ccg m ∪ (goodRowSet M Ccg (M.gamma / 4))ᶜ)ᶜ) :
    9 * (M.gamma / 4)⁻¹ * Cstar ^ (1 / p) * theta ^ (-1 / p)
      < Yk (ycalArray M Ccg (M.gamma / 4) D) (M.gamma / 4) m omega := by
  have h1 : omega ∉ Support.eventG0 M Ccg m := fun hc => homega (Or.inl hc)
  have h2 : omega ∈ goodRowSet M Ccg (M.gamma / 4) := by
    by_contra hc
    exact homega (Or.inr hc)
  exact lt_of_le_of_lt hthr (lt_Yk_of_notMem_eventG0 M Ccg hD m h2 h1)

/-! ## 3. The `𝒢₀` engine on a window based at `m₀` -/

/-- **The `𝒢₀`-lane proportion tail on the window `{m₀,…,m₀+n}`.**

The base-`0` hypothesis list of the `𝒢₀` engine, with two changes: an extra
base scale `m₀ : ℤ`, and the deterministic reduction `hreduce` asked at **every**
scale `m : ℤ` rather than only at `m ≥ 0` (`hreduce_eventG0_all` supplies exactly
that for the `𝒢₀` lane).  The conclusion is the same tail bound

```
ℙ[ θ < (proportion of scales m₀ ≤ m ≤ m₀+n at which Ev m fails) ] ≤ exp(−c₁n)/Q ,
```

including the short windows `n < r`.

The proof is the proved engine with its last step routed through
`ShiftedConcentration.ratioTail_of_concentration_shift`: the four Appendix-D
inputs — entrywise measurability, entrywise nonnegativity, the unit moments
`lintegral_rpow_le_one_Ycal` and the `r`-dependence `columnsIndep_Ycal` — are
supplied for the base array, and the diagonal translation is free. -/
theorem ratioTail_Ycal_shift {d : ℕ} (M : ABKModel d) (Ccg sprime D : ℝ)
    {sigma p theta c1 Q K : ℝ} {r : ℕ} (Ev : ℤ → Set (Cutoff.CutoffSample d)) (m0 : ℤ)
    (hsigma : 0 < sigma) (hK : 0 < K) (hD : 0 < D)
    (hp : 1 ≤ p) (hs' : 0 < sprime) (hs'1 : sprime ≤ 1) (hsp : 1 ≤ sprime * p)
    (hr1 : 1 ≤ r) (hQ : 1 ≤ Q) (htheta0 : 0 < theta)
    (hthetar : theta * ((r : ℝ) + 1) < 1) (hc1 : 0 ≤ c1)
    (hrate : Real.log (Q * (r : ℝ)) + c1 * (r : ℝ) ≤ sprime * p * theta / (16 * (r : ℝ)))
    (htail : ∀ n : ℤ, IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma sigma)
      (Ycal M Ccg sprime n) K)
    (hnorm : gammaMomentConst sigma * p ^ sigma⁻¹ * K ≤ D)
    (hrgap : 3 + 2 * (3 : ℝ) ^ (1 - (2 : ℤ)) * Real.sqrt (d : ℝ) ≤ (3 : ℝ) ^ (r : ℕ))
    (hloc : ∀ n : ℤ,
      Measurable[Cutoff.cutoffSampleLocalSigma M (n - 2) (annulusRegion d n)]
        (Ycal M Ccg sprime n))
    (hreduce : ∀ m : ℤ, ∀ omega ∈ (Ev m)ᶜ,
      9 * sprime⁻¹ * Cstar ^ (1 / p) * theta ^ (-1 / p) <
        Yk (ycalArray M Ccg sprime D) sprime m omega)
    (n : ℕ) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | theta < scaleProp (fun k => (Ev (m0 + k))ᶜ) n omega}
      ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / Q) := by
  have hXmeas : ∀ k j : ℤ, Measurable (ycalArray M Ccg sprime D k j) := by
    intro _k j
    exact (measurable_Ycal M Ccg sprime j).const_mul D⁻¹
  have hXnn : ∀ (k j : ℤ) (omega : Cutoff.CutoffSample d),
      0 ≤ ycalArray M Ccg sprime D k j omega := by
    intro _k j omega
    exact mul_nonneg (inv_nonneg.2 hD.le) (Ycal_nonneg M Ccg sprime j omega)
  exact ratioTail_of_concentration_shift (Cutoff.cutoffSampleLaw M).toMeasure
    (ycalArray M Ccg sprime D) Ev m0 hp hs' hs'1 hsp hr1 hXmeas hXnn
    (lintegral_rpow_le_one_Ycal M Ccg hsigma hK hp hD htail hnorm)
    (columnsIndep_Ycal M Ccg sprime D hr1 hrgap hloc)
    hQ htheta0 hthetar hc1 hrate hreduce n

/-! ## 4. The level-uniform endpoint on a window based at `m₀` -/

private theorem shiftedG0Lane_comparisonBounds1 :
    ∀ (d : ℕ) (_ : (0 : ℝ) < cgEllipLowerConstant d) (_ : (0 : ℝ) < Cstar)
      (_ : (0 : ℝ) < gammaMomentConst (1 / 3 : ℝ)) (_ : (0 : ℝ) < gammaTriangleConst (1 / 3 : ℝ))
      (_ : (0 : ℝ) < penaltyNormalizer d) (r : ℕ) (L G0d : ℝ)
      (_ :
        G0d =
          (36 : ℝ) * ((1 : ℝ) + Cstar) * gammaMomentConst (1 / 3 : ℝ) * gammaTriangleConst (1 / 3
            : ℝ) *
            penaltyNormalizer d)
      (C : ℝ) (_ : (6 : ℝ) ≤ C) (M : ABKModel d) (theta : ℝ) (_ : (0 : ℝ) < theta)
      (_ : C ^ (9 : ℕ) * M.gamma ^ (2 : ℕ) ≤ theta * Disorder.cstar M ^ (8 : ℕ)) (_ : (0 : ℝ) < C)
      (_ : C ≠ (0 : ℝ)) (_ : (16174080 : ℝ) * cgEllipLowerConstant d ^ (4 : ℕ) ≤ C ^ (12 : ℕ))
      (_ : (1990656 : ℝ) * (↑r : ℝ) * L * cgEllipLowerConstant d ^ (4 : ℕ) ≤ C)
      (_ : (23224320 : ℝ) * G0d * cgEllipLowerConstant d ^ (8 : ℕ) ≤ C ^ (3 : ℕ)) (Rr : ℝ)
      (_ : Rr = max (4 : ℝ) ((64 : ℝ) * (↑r : ℝ) * L / theta)) (_ : (0 : ℝ) < Disorder.cstar M)
      (_ : Disorder.cstar M ≤ (3 / 2 : ℝ)) (_ : (0 : ℝ) < M.gamma) (_ : M.gamma ≠ (0 : ℝ))
      (_ : Disorder.cstar M ≠ (0 : ℝ)) (_ : cgEllipLowerConstant d ≠ (0 : ℝ)) (u : ℝ)
      (_ : u = Disorder.cstar M ^ (2 : ℕ) / (cgEllipLowerConstant d * C ^ (2 : ℕ) * M.gamma))
      (_ : M.gamma ≤ Disorder.cstar M ^ (10 : ℕ) / C ^ (10 : ℕ))
      (_ : M.gamma ^ (2 : ℕ) ≤ Disorder.cstar M ^ (20 : ℕ) / C ^ (20 : ℕ))
      (_ : Disorder.cstar M ^ (2 : ℕ) ≤ (9 / 4 : ℝ)),
      (31104 : ℝ) * Rr ≤ M.gamma ^ (2 : ℕ) * u ^ (4 : ℕ) ∧
        M.gamma ^ (5 : ℕ) * u ^ (8 : ℕ) =
            Disorder.cstar M ^ (16 : ℕ) / (cgEllipLowerConstant d ^ (8 : ℕ) * C ^ (16 : ℕ) *
              M.gamma ^ (3 : ℕ)) ∧
          (0 : ℝ) < cgEllipLowerConstant d ^ (8 : ℕ) * C ^ (16 : ℕ) * M.gamma ^ (3 : ℕ) ∧
            (10321920 : ℝ) * G0d * (cgEllipLowerConstant d ^ (8 : ℕ) * C ^ (16 : ℕ) * M.gamma ^ (3
              : ℕ)) ≤
              theta * Disorder.cstar M ^ (16 : ℕ) := by
  intro d _ hCs0 hgmc0 hgtc0 hPn0 r L G0d hG0ddef C _ M theta htheta0 hcouple hC0 _ hflA hflB hflC
    Rr hRrdef hcs0 hcs32 _ _ _ _ u hu' hgammale hgammasq hcs2
  have hcs12 : (Disorder.cstar M) ^ (12 : ℕ) ≤ 130 := by
    calc (Disorder.cstar M) ^ (12 : ℕ) ≤ (3 / 2 : ℝ) ^ (12 : ℕ) :=
        pow_le_pow_left₀ hcs0.le hcs32 12
      _ ≤ 130 := by norm_num
  -- 2: the rate branch, at Taylor order 4
  have hval4 : M.gamma ^ (2 : ℕ) * u ^ (4 : ℕ) = (Disorder.cstar M) ^ (8 : ℕ) /
      ((Support.cgEllipLowerConstant d) ^ (4 : ℕ) * C ^ (8 : ℕ) * M.gamma ^ (2 : ℕ)) := by
    rw [hu']
    field_simp
  have hden4 : (0 : ℝ) < (Support.cgEllipLowerConstant d) ^ (4 : ℕ) * C ^ (8 : ℕ) *
      M.gamma ^ (2 : ℕ) := by positivity
  have hbranchA : (4 : ℝ) ≤ M.gamma ^ (2 : ℕ) * u ^ (4 : ℕ) / 31104 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 31104), hval4, le_div_iff₀ hden4]
    have hfrac : 124416 * (Support.cgEllipLowerConstant d) ^ (4 : ℕ) *
        (Disorder.cstar M) ^ (12 : ℕ) / C ^ (12 : ℕ) ≤ 1 := by
      rw [div_le_one (pow_pos hC0 12)]
      calc 124416 * (Support.cgEllipLowerConstant d) ^ (4 : ℕ) * (Disorder.cstar M) ^ (12 : ℕ)
          ≤ 124416 * (Support.cgEllipLowerConstant d) ^ (4 : ℕ) * 130 :=
            mul_le_mul_of_nonneg_left hcs12 (by positivity)
        _ = 16174080 * (Support.cgEllipLowerConstant d) ^ (4 : ℕ) := by ring
        _ ≤ C ^ (12 : ℕ) := hflA
    calc (4 : ℝ) * 31104 * ((Support.cgEllipLowerConstant d) ^ (4 : ℕ) * C ^ (8 : ℕ) *
            M.gamma ^ (2 : ℕ))
        = 124416 * (Support.cgEllipLowerConstant d) ^ (4 : ℕ) * C ^ (8 : ℕ) *
            M.gamma ^ (2 : ℕ) := by ring
      _ ≤ 124416 * (Support.cgEllipLowerConstant d) ^ (4 : ℕ) * C ^ (8 : ℕ) *
            ((Disorder.cstar M) ^ (20 : ℕ) / C ^ (20 : ℕ)) :=
          mul_le_mul_of_nonneg_left hgammasq (by positivity)
      _ = 124416 * (Support.cgEllipLowerConstant d) ^ (4 : ℕ) * (Disorder.cstar M) ^ (12 : ℕ) /
            C ^ (12 : ℕ) * (Disorder.cstar M) ^ (8 : ℕ) := by
          field_simp
      _ ≤ 1 * (Disorder.cstar M) ^ (8 : ℕ) :=
          mul_le_mul_of_nonneg_right hfrac (by positivity)
      _ = (Disorder.cstar M) ^ (8 : ℕ) := one_mul _
  have hbranchB : 64 * (r : ℝ) * L / theta ≤ M.gamma ^ (2 : ℕ) * u ^ (4 : ℕ) / 31104 := by
    rw [div_le_div_iff₀ htheta0 (by norm_num : (0 : ℝ) < 31104), hval4, div_mul_eq_mul_div,
      le_div_iff₀ hden4]
    calc 64 * (r : ℝ) * L * 31104 * ((Support.cgEllipLowerConstant d) ^ (4 : ℕ) * C ^ (8 : ℕ) *
            M.gamma ^ (2 : ℕ))
        = (1990656 * (r : ℝ) * L * (Support.cgEllipLowerConstant d) ^ (4 : ℕ)) *
            (C ^ (8 : ℕ) * M.gamma ^ (2 : ℕ)) := by ring
      _ ≤ C * (C ^ (8 : ℕ) * M.gamma ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_right hflB (by positivity)
      _ = C ^ (9 : ℕ) * M.gamma ^ (2 : ℕ) := by ring
      _ ≤ theta * (Disorder.cstar M) ^ (8 : ℕ) := hcouple
      _ = (Disorder.cstar M) ^ (8 : ℕ) * theta := by ring
  have hgu4 : 31104 * Rr ≤ M.gamma ^ (2 : ℕ) * u ^ (4 : ℕ) := by
    have hRrle : Rr ≤ M.gamma ^ (2 : ℕ) * u ^ (4 : ℕ) / 31104 := by
      rw [hRrdef]
      exact max_le hbranchA hbranchB
    calc 31104 * Rr ≤ 31104 * (M.gamma ^ (2 : ℕ) * u ^ (4 : ℕ) / 31104) := by
          linarith only [hRrle]
      _ = M.gamma ^ (2 : ℕ) * u ^ (4 : ℕ) := by ring
  -- 3: the threshold branch, at Taylor order 8
  have hval8 : M.gamma ^ (5 : ℕ) * u ^ (8 : ℕ) = (Disorder.cstar M) ^ (16 : ℕ) /
      ((Support.cgEllipLowerConstant d) ^ (8 : ℕ) * C ^ (16 : ℕ) * M.gamma ^ (3 : ℕ)) := by
    rw [hu']
    field_simp
  have hden8 : (0 : ℝ) < (Support.cgEllipLowerConstant d) ^ (8 : ℕ) * C ^ (16 : ℕ) *
      M.gamma ^ (3 : ℕ) := by positivity
  have hinner : 10321920 * G0d * (Support.cgEllipLowerConstant d) ^ (8 : ℕ) * C ^ (7 : ℕ) *
      M.gamma ≤ (Disorder.cstar M) ^ (8 : ℕ) := by
    have hG0d0 : 0 < G0d := by
      rw [hG0ddef]
      exact mul_pos (mul_pos (mul_pos (by linarith only [hCs0]) hgmc0) hgtc0) hPn0
    have hfrac : 10321920 * G0d * (Support.cgEllipLowerConstant d) ^ (8 : ℕ) *
        (Disorder.cstar M) ^ (2 : ℕ) / C ^ (3 : ℕ) ≤ 1 := by
      rw [div_le_one (pow_pos hC0 3)]
      calc 10321920 * G0d * (Support.cgEllipLowerConstant d) ^ (8 : ℕ) *
            (Disorder.cstar M) ^ (2 : ℕ)
          ≤ 10321920 * G0d * (Support.cgEllipLowerConstant d) ^ (8 : ℕ) * (9 / 4) :=
            mul_le_mul_of_nonneg_left hcs2 (by positivity)
        _ = 23224320 * G0d * (Support.cgEllipLowerConstant d) ^ (8 : ℕ) := by ring
        _ ≤ C ^ (3 : ℕ) := hflC
    calc 10321920 * G0d * (Support.cgEllipLowerConstant d) ^ (8 : ℕ) * C ^ (7 : ℕ) * M.gamma
        = (10321920 * G0d * (Support.cgEllipLowerConstant d) ^ (8 : ℕ) * C ^ (7 : ℕ)) *
            M.gamma := by ring
      _ ≤ (10321920 * G0d * (Support.cgEllipLowerConstant d) ^ (8 : ℕ) * C ^ (7 : ℕ)) *
            ((Disorder.cstar M) ^ (10 : ℕ) / C ^ (10 : ℕ)) :=
          mul_le_mul_of_nonneg_left hgammale (by positivity)
      _ = 10321920 * G0d * (Support.cgEllipLowerConstant d) ^ (8 : ℕ) *
            (Disorder.cstar M) ^ (2 : ℕ) / C ^ (3 : ℕ) * (Disorder.cstar M) ^ (8 : ℕ) := by
          field_simp
      _ ≤ 1 * (Disorder.cstar M) ^ (8 : ℕ) :=
          mul_le_mul_of_nonneg_right hfrac (by positivity)
      _ = (Disorder.cstar M) ^ (8 : ℕ) := one_mul _
  have hcore8 : 10321920 * G0d * ((Support.cgEllipLowerConstant d) ^ (8 : ℕ) * C ^ (16 : ℕ) *
      M.gamma ^ (3 : ℕ)) ≤ theta * (Disorder.cstar M) ^ (16 : ℕ) := by
    calc 10321920 * G0d * ((Support.cgEllipLowerConstant d) ^ (8 : ℕ) * C ^ (16 : ℕ) *
            M.gamma ^ (3 : ℕ))
        = (10321920 * G0d * (Support.cgEllipLowerConstant d) ^ (8 : ℕ) * C ^ (7 : ℕ) * M.gamma) *
            (C ^ (9 : ℕ) * M.gamma ^ (2 : ℕ)) := by ring
      _ ≤ (Disorder.cstar M) ^ (8 : ℕ) * (C ^ (9 : ℕ) * M.gamma ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_right hinner (by positivity)
      _ ≤ (Disorder.cstar M) ^ (8 : ℕ) * (theta * (Disorder.cstar M) ^ (8 : ℕ)) :=
          mul_le_mul_of_nonneg_left hcouple (by positivity)
      _ = theta * (Disorder.cstar M) ^ (16 : ℕ) := by ring
  exact ⟨hgu4, hval8, hden8, hcore8⟩

private theorem shiftedG0Lane_comparisonBounds2 :
    ∀ (d : ℕ) (_ : (0 : ℝ) < Cstar) (_ : (0 : ℝ) < gammaMomentConst (1 / 3 : ℝ))
      (_ : (0 : ℝ) < gammaTriangleConst (1 / 3 : ℝ)) (_ : (0 : ℝ) < penaltyNormalizer d) (r : ℕ)
        (_ : (1 : ℕ) ≤ r)
      (_ : (1 : ℝ) ≤ (↑r : ℝ)) (L : ℝ) (_ : L = Real.log ((3 : ℝ) * (↑r : ℝ)) + (↑r : ℝ)) (M :
        ABKModel d) (theta : ℝ)
      (_ : (0 : ℝ) < theta) (c1 : ℝ) (_ : c1 * M.gamma ≤ (1 : ℝ)) (_ : theta ≤ (1 : ℝ))
      (_ : theta ≠ (0 : ℝ)) (Rr : ℝ) (_ : (4 : ℝ) ≤ Rr) (_ : (64 : ℝ) * (↑r : ℝ) * L / theta ≤ Rr)
        (G : ℝ)
      (_ :
        G =
          (36 : ℝ) * ((1 : ℝ) + Cstar) * gammaMomentConst (1 / 3 : ℝ) * gammaTriangleConst (1 / 3
            : ℝ) *
              penaltyNormalizer d /
            theta)
      (_ : (0 : ℝ) < G) (_ : (0 : ℝ) < M.gamma) (_ : M.gamma ≤ (1 / 4 : ℝ)) (_ : M.gamma ≠ (0 :
        ℝ)) (u : ℝ)
      (_ : (0 : ℝ) < u) (_ : (31104 : ℝ) * Rr ≤ M.gamma ^ (2 : ℕ) * u ^ (4 : ℕ))
      (_ : (10321920 : ℝ) * G ≤ M.gamma ^ (5 : ℕ) * u ^ (8 : ℕ)) (_ : (0 : ℝ) < M.gamma / (4 : ℝ))
        (S0 : ℝ)
      (_ : S0 = ∑' (j : ℕ), weightThird (M.gamma / (4 : ℝ)) j * annulusPenaltyThird d (j + (2 :
        ℕ))) (p : ℝ)
      (_ : (0 : ℝ) < p) (_ : (1 : ℝ) ≤ p) (D : ℝ) (_ : (0 : ℝ) < D)
      (_ : D = gammaMomentConst (1 / 3 : ℝ) * gammaTriangleConst (1 / 3 : ℝ) * S0 * Real.exp (-(u
        / (2 : ℝ))))
      (_ : u ^ (4 : ℕ) / (31104 : ℝ) ≤ p),
      (1 : ℝ) ≤ M.gamma / (4 : ℝ) * p ∧
        Real.log ((3 : ℝ) * (↑r : ℝ)) + c1 * (↑r : ℝ) ≤ M.gamma / (4 : ℝ) * p * theta / ((16 : ℝ)
          * (↑r : ℝ)) ∧
          (9 : ℝ) * (M.gamma / (4 : ℝ))⁻¹ * Cstar ^ ((1 : ℝ) / p) * theta ^ ((-1 : ℝ) / p) ≤
            D⁻¹ := by
  intro d hCs0 hgmc0 hgtc0 hPn0 r _ hrR L hLdef M theta htheta0 c1 hc1g htheta1 _ Rr hRr4 hRrL G
    hGdef hG0 hg0 hg4 _ u hu0 hgu4 hgu8 hsprime0 S0 hS0def p _ hp1 D hD0 hDval hplow4
  have hg2p : Rr ≤ M.gamma ^ (2 : ℕ) * p := by
    calc Rr = 31104 * Rr / 31104 := by ring
      _ ≤ M.gamma ^ (2 : ℕ) * u ^ (4 : ℕ) / 31104 := by
          exact div_le_div_of_nonneg_right hgu4 (by norm_num)
      _ = M.gamma ^ (2 : ℕ) * (u ^ (4 : ℕ) / 31104) := by ring
      _ ≤ M.gamma ^ (2 : ℕ) * p := mul_le_mul_of_nonneg_left hplow4 (by positivity)
  have hgp : (4 : ℝ) ≤ M.gamma * p := by
    have hstep : 4 * M.gamma ≤ M.gamma ^ (2 : ℕ) * p := by
      have h1 : 4 * M.gamma ≤ 4 := by linarith only [hg4]
      linarith only [h1, hRr4, hg2p]
    have hstep2 := mul_le_mul_of_nonneg_right hstep (inv_nonneg.2 hg0.le)
    calc (4 : ℝ) = 4 * M.gamma * M.gamma⁻¹ := by field_simp
      _ ≤ M.gamma ^ (2 : ℕ) * p * M.gamma⁻¹ := hstep2
      _ = M.gamma * p := by field_simp
  have hsp : 1 ≤ M.gamma / 4 * p := by linarith only [hgp]
  have hrate : Real.log ((3 : ℝ) * (r : ℝ)) + c1 * (r : ℝ)
      ≤ M.gamma / 4 * p * theta / (16 * (r : ℝ)) := by
    have hlog3r : (0 : ℝ) ≤ Real.log (3 * (r : ℝ)) :=
      Real.log_nonneg (by linarith only [hrR])
    have hrnn : (0 : ℝ) ≤ (r : ℝ) := by linarith only [hrR]
    have hstepA : (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) * M.gamma ≤ L := by
      rw [hLdef]
      have h1 : Real.log (3 * (r : ℝ)) * M.gamma ≤ Real.log (3 * (r : ℝ)) :=
        mul_le_of_le_one_right hlog3r (by linarith only [hg4, hg0])
      have h2 : c1 * M.gamma * (r : ℝ) ≤ 1 * (r : ℝ) :=
        mul_le_mul_of_nonneg_right hc1g hrnn
      linarith only [h1, h2]
    have h64 : 64 * (r : ℝ) * L ≤ M.gamma ^ (2 : ℕ) * p * theta := by
      calc 64 * (r : ℝ) * L = 64 * (r : ℝ) * L / theta * theta := by field_simp
        _ ≤ Rr * theta := mul_le_mul_of_nonneg_right hRrL htheta0.le
        _ ≤ M.gamma ^ (2 : ℕ) * p * theta := mul_le_mul_of_nonneg_right hg2p htheta0.le
    have hA : (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) * (64 * (r : ℝ)) * M.gamma
        ≤ M.gamma * p * theta * M.gamma := by
      calc (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) * (64 * (r : ℝ)) * M.gamma
          = (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) * M.gamma * (64 * (r : ℝ)) := by ring
        _ ≤ L * (64 * (r : ℝ)) :=
            mul_le_mul_of_nonneg_right hstepA (by linarith only [hrnn])
        _ = 64 * (r : ℝ) * L := by ring
        _ ≤ M.gamma ^ (2 : ℕ) * p * theta := h64
        _ = M.gamma * p * theta * M.gamma := by ring
    have hB : (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) * (64 * (r : ℝ))
        ≤ M.gamma * p * theta := by
      calc (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) * (64 * (r : ℝ))
          = (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) * (64 * (r : ℝ)) * M.gamma * M.gamma⁻¹ := by
            field_simp
        _ ≤ M.gamma * p * theta * M.gamma * M.gamma⁻¹ :=
            mul_le_mul_of_nonneg_right hA (inv_nonneg.2 hg0.le)
        _ = M.gamma * p * theta := by field_simp
    rw [le_div_iff₀ (by linarith only [hrR] : (0 : ℝ) < 16 * (r : ℝ)),
      show M.gamma / 4 * p * theta = M.gamma * p * theta / 4 by ring,
      le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
    calc (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) * (16 * (r : ℝ)) * 4
        = (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) * (64 * (r : ℝ)) := by ring
      _ ≤ M.gamma * p * theta := hB
  have hS0le : S0 ≤ penaltyNormalizer d / M.gamma ^ (4 : ℕ) := by
    rw [hS0def]
    exact tsum_weightThird_mul_annulusPenaltyThird_le d hg0 hg4
  have hu20 : (0 : ℝ) < u / 2 := by linarith only [hu0]
  have hE8 : Real.exp (-(u / 2)) ≤ M.gamma ^ (5 : ℕ) / G := by
    refine le_trans (exp_neg_le_eight hu20) ?_
    rw [div_le_div_iff₀ (pow_pos hu20 8) hG0,
      show M.gamma ^ (5 : ℕ) * (u / 2) ^ (8 : ℕ) = M.gamma ^ (5 : ℕ) * u ^ (8 : ℕ) / 256 by ring,
      le_div_iff₀ (by norm_num : (0 : ℝ) < 256)]
    linarith only [hgu8]
  have hkey : 9 * D * (1 + Cstar) ≤ M.gamma / 4 * theta := by
    have hprod : S0 * Real.exp (-(u / 2))
        ≤ penaltyNormalizer d / M.gamma ^ (4 : ℕ) * (M.gamma ^ (5 : ℕ) / G) :=
      mul_le_mul hS0le hE8 (Real.exp_pos _).le (div_pos hPn0 (pow_pos hg0 4)).le
    have hc1' : (0 : ℝ) ≤ gammaMomentConst (1 / 3 : ℝ) * gammaTriangleConst (1 / 3 : ℝ) :=
      (mul_pos hgmc0 hgtc0).le
    have hc2 : (0 : ℝ) ≤ 1 + Cstar := by linarith only [hCs0]
    have hstep3 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprod hc1')
        (by norm_num : (0 : ℝ) ≤ 9)) hc2
    have hne1 : (1 + Cstar) ≠ 0 := by
      have : (0 : ℝ) < 1 + Cstar := by linarith only [hCs0]
      exact ne_of_gt this
    have hne2 : gammaMomentConst (1 / 3 : ℝ) ≠ 0 := ne_of_gt hgmc0
    have hne3 : gammaTriangleConst (1 / 3 : ℝ) ≠ 0 := ne_of_gt hgtc0
    have hne4 : penaltyNormalizer d ≠ 0 := ne_of_gt hPn0
    have hRHS : 9 * (gammaMomentConst (1 / 3 : ℝ) * gammaTriangleConst (1 / 3 : ℝ) *
        (penaltyNormalizer d / M.gamma ^ (4 : ℕ) * (M.gamma ^ (5 : ℕ) / G))) * (1 + Cstar)
        = M.gamma / 4 * theta := by
      rw [hGdef]
      field_simp
      ring
    have hLHS : 9 * D * (1 + Cstar) = 9 * (gammaMomentConst (1 / 3 : ℝ) *
        gammaTriangleConst (1 / 3 : ℝ) * (S0 * Real.exp (-(u / 2)))) * (1 + Cstar) := by
      rw [hDval]
      ring
    rw [hLHS, ← hRHS]
    exact hstep3
  have hthr : 9 * (M.gamma / 4)⁻¹ * Cstar ^ (1 / p) * theta ^ (-1 / p) ≤ D⁻¹ :=
    threshold_le_inv hsprime0 htheta0 htheta1 hp1 hD0 hkey
  exact ⟨hsp, hrate, hthr⟩

/-- The level-uniform `𝒢₀` endpoint, with the proportion read over the window
based at `m₀`.  The base scale is quantified
last, after `r`, `C`, the model `M`, the level `θ`, the coupling `C⁹γ² ≤ θc⋆⁸`
and the rate `c₁`, so no constant in the statement depends on it.

The parameter chain is unchanged: `E = C c⋆^{−1}`, atom scale `A = exp(−u)` with
`u = c⋆²/(C_cg C² γ)`, `p = exp(u/6)`, so `p^{1/σ}A = exp(−u/2)`, and normalizer
`D = gammaMomentConst σ · p^{1/σ} · K`; the two `θ`-carrying floors are replaced
by the `θ`-free floors

```
16174080 C_cg⁴ ,   1990656 r L C_cg⁴ ,   23224320 G₀(d) C_cg⁸ ,
```

with `L = log(3r) + r` and
`G₀(d) = 36(1+C_⋆)·gammaMomentConst(1/3)·gammaTriangleConst(1/3)·penaltyNormalizer d`.
Only the final step differs from the base-`0` proof: the engine is
`ratioTail_Ycal_shift` and the reduction is `hreduce_eventG0_all`, neither of
which restricts the scale to `m ≥ 0`. -/
private theorem shiftedG0Lane_estimate1 :
    ∀ (d : ℕ) (G0d C : ℝ) (M : ABKModel d) (theta : ℝ) (_ : (0 : ℝ) < theta)
      (G : ℝ) (_ : G * theta = G0d) (u : ℝ)
      (_ :
        M.gamma ^ (5 : ℕ) * u ^ (8 : ℕ) =
          Disorder.cstar M ^ (16 : ℕ) / (cgEllipLowerConstant d ^ (8 : ℕ) * C ^ (16 : ℕ) * M.gamma
            ^ (3 : ℕ)))
      (_ : (0 : ℝ) < cgEllipLowerConstant d ^ (8 : ℕ) * C ^ (16 : ℕ) * M.gamma ^ (3 : ℕ))
      (_ :
        (10321920 : ℝ) * G0d * (cgEllipLowerConstant d ^ (8 : ℕ) * C ^ (16 : ℕ) * M.gamma ^ (3 :
          ℕ)) ≤
          theta * Disorder.cstar M ^ (16 : ℕ)),
      (10321920 : ℝ) * G ≤ M.gamma ^ (5 : ℕ) * u ^ (8 : ℕ) := by
  intro d G0d C M theta htheta0 G hGtheta _ hval8 hden8 hcore8
  rw [hval8, le_div_iff₀ hden8]
  refine le_of_mul_le_mul_right ?_ htheta0
  calc 10321920 * G * ((Support.cgEllipLowerConstant d) ^ (8 : ℕ) * C ^ (16 : ℕ) *
          M.gamma ^ (3 : ℕ)) * theta
      = 10321920 * (G * theta) * ((Support.cgEllipLowerConstant d) ^ (8 : ℕ) * C ^ (16 : ℕ) *
          M.gamma ^ (3 : ℕ)) := by ring
    _ = 10321920 * G0d * ((Support.cgEllipLowerConstant d) ^ (8 : ℕ) * C ^ (16 : ℕ) *
          M.gamma ^ (3 : ℕ)) := by rw [hGtheta]
    _ ≤ theta * (Disorder.cstar M) ^ (16 : ℕ) := hcore8
    _ = (Disorder.cstar M) ^ (16 : ℕ) * theta := by ring

theorem exists_ratioTail_eventG0_uniform_shift (d : ℕ) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ C : ℝ, 6 ≤ C ∧
      ∀ M : ABKModel d, M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        ∀ theta : ℝ, 0 < theta → theta * ((r : ℝ) + 1) < 1 →
          C ^ (9 : ℕ) * M.gamma ^ (2 : ℕ) ≤ theta * (Disorder.cstar M) ^ (8 : ℕ) →
            ∀ c1 : ℝ, 0 ≤ c1 → c1 * M.gamma ≤ 1 → ∀ (m0 : ℤ) (n : ℕ),
              (Cutoff.cutoffSampleLaw M).toMeasure
                  {omega | theta < scaleProp
                    (fun k => (Support.eventG0 M (Support.cgEllipLowerConstant d) (m0 + k))ᶜ)
                    n omega}
                ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3) := by
  classical
  have hCcg0 : (0 : ℝ) < Support.cgEllipLowerConstant d := Support.cgEllipLowerConstant_pos d
  have hCs0 : (0 : ℝ) < Cstar := Cstar_pos
  have hgmc0 : (0 : ℝ) < gammaMomentConst (1 / 3 : ℝ) := gammaMomentConst_pos (by norm_num)
  have hgtc0 : (0 : ℝ) < gammaTriangleConst (1 / 3 : ℝ) := gammaTriangleConst_pos
  have hPn0 : (0 : ℝ) < penaltyNormalizer d := penaltyNormalizer_pos d
  obtain ⟨r, hr1, hrgap⟩ := exists_dependence_range d
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log (3 * (r : ℝ)) + (r : ℝ) := ⟨_, rfl⟩
  obtain ⟨G0d, hG0ddef⟩ : ∃ x : ℝ, x = 36 * (1 + Cstar) * gammaMomentConst (1 / 3 : ℝ) *
      gammaTriangleConst (1 / 3 : ℝ) * penaltyNormalizer d := ⟨_, rfl⟩
  -- the three `θ`-free floors
  obtain ⟨C, hC6, hCfl, hall⟩ := exists_cgExcess_atomTail_of_floor d
      (max (16174080 * (Support.cgEllipLowerConstant d) ^ (4 : ℕ))
        (max (1990656 * (r : ℝ) * L * (Support.cgEllipLowerConstant d) ^ (4 : ℕ))
          (23224320 * G0d * (Support.cgEllipLowerConstant d) ^ (8 : ℕ))))
  refine ⟨r, hr1, C, hC6, ?_⟩
  intro M hreg theta htheta0 hthetar hcouple c1 hc10 hc1g m0
  have hC0 : (0 : ℝ) < C := by linarith only [hC6]
  have hC1 : (1 : ℝ) ≤ C := by linarith only [hC6]
  have hCne : C ≠ 0 := ne_of_gt hC0
  have hCpow12 : C ≤ C ^ (12 : ℕ) := by
    calc C = C ^ (1 : ℕ) := (pow_one C).symm
      _ ≤ C ^ (12 : ℕ) := pow_le_pow_right₀ hC1 (by norm_num)
  have hCpow3 : C ≤ C ^ (3 : ℕ) := by
    calc C = C ^ (1 : ℕ) := (pow_one C).symm
      _ ≤ C ^ (3 : ℕ) := pow_le_pow_right₀ hC1 (by norm_num)
  have hflA : 16174080 * (Support.cgEllipLowerConstant d) ^ (4 : ℕ) ≤ C ^ (12 : ℕ) :=
    le_trans (le_trans (le_max_left _ _) hCfl) hCpow12
  have hflB : 1990656 * (r : ℝ) * L * (Support.cgEllipLowerConstant d) ^ (4 : ℕ) ≤ C :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCfl
  have hflC : 23224320 * G0d * (Support.cgEllipLowerConstant d) ^ (8 : ℕ) ≤ C ^ (3 : ℕ) :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCfl) hCpow3
  have htheta1 : theta ≤ 1 := by
    have hstep : theta * 2 ≤ theta * ((r : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith only [hrR]) htheta0.le
    linarith only [hstep, hthetar, htheta0]
  have hthetane : theta ≠ 0 := ne_of_gt htheta0
  obtain ⟨Rr, hRrdef⟩ : ∃ x : ℝ, x = max 4 (64 * (r : ℝ) * L / theta) := ⟨_, rfl⟩
  have hRr4 : (4 : ℝ) ≤ Rr := by rw [hRrdef]; exact le_max_left _ _
  have hRrL : 64 * (r : ℝ) * L / theta ≤ Rr := by rw [hRrdef]; exact le_max_right _ _
  obtain ⟨G, hGdef⟩ : ∃ x : ℝ, x = 36 * (1 + Cstar) * gammaMomentConst (1 / 3 : ℝ) *
      gammaTriangleConst (1 / 3 : ℝ) * penaltyNormalizer d / theta := ⟨_, rfl⟩
  have hG0 : 0 < G := by
    rw [hGdef]
    refine div_pos ?_ htheta0
    exact mul_pos (mul_pos (mul_pos (by linarith only [hCs0]) hgmc0) hgtc0) hPn0
  have hGtheta : G * theta = G0d := by
    rw [hGdef, hG0ddef]
    field_simp
  obtain ⟨E, hEval, hwin, hatom⟩ := hall M hreg
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcs32 : Disorder.cstar M ≤ 3 / 2 :=
    Algsuperdiff.Section3.Provider.Disorder.cstar_le_three_halves M
  have hg0 : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hg4 : M.gamma ≤ 1 / 4 := M.shellPrefix.gamma_le_quarter
  have hE0 : (0 : ℝ) < (E : ℝ) := lt_of_lt_of_le zero_lt_one E.2
  have hgne : M.gamma ≠ 0 := ne_of_gt hg0
  have hcsne : Disorder.cstar M ≠ 0 := ne_of_gt hcs0
  have hCcgne : Support.cgEllipLowerConstant d ≠ 0 := ne_of_gt hCcg0
  obtain ⟨u, hudef⟩ : ∃ x : ℝ, x = (Support.cgEllipLowerConstant d)⁻¹ *
      (((E : ℝ))⁻¹) ^ (2 : ℕ) * M.gamma⁻¹ := ⟨_, rfl⟩
  have hu0 : 0 < u := by
    rw [hudef]
    exact mul_pos (mul_pos (inv_pos.2 hCcg0) (pow_pos (inv_pos.2 hE0) 2)) (inv_pos.2 hg0)
  have hAu : cgTailScale M (E : ℝ) = Real.exp (-u) := by rw [hudef, cgTailScale]
  have hu' : u = (Disorder.cstar M) ^ (2 : ℕ) /
      (Support.cgEllipLowerConstant d * C ^ (2 : ℕ) * M.gamma) := by
    rw [hudef, hEval]
    field_simp
  -- the printed regime, in product form
  have hkey10 : C ^ (10 : ℕ) * M.gamma ≤ (Disorder.cstar M) ^ (10 : ℕ) := by
    have hC10 : (0 : ℝ) < C ^ (10 : ℕ) := pow_pos hC0 10
    have h := mul_le_mul_of_nonneg_left hreg hC10.le
    rw [inv_pow, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hC10), one_mul] at h
    exact h
  have hgammale : M.gamma ≤ (Disorder.cstar M) ^ (10 : ℕ) / C ^ (10 : ℕ) := by
    rw [le_div_iff₀ (pow_pos hC0 10)]
    calc M.gamma * C ^ (10 : ℕ) = C ^ (10 : ℕ) * M.gamma := by ring
      _ ≤ (Disorder.cstar M) ^ (10 : ℕ) := hkey10
  have hgammasq : M.gamma ^ (2 : ℕ) ≤ (Disorder.cstar M) ^ (20 : ℕ) / C ^ (20 : ℕ) := by
    have hsq : (C ^ (10 : ℕ) * M.gamma) ^ (2 : ℕ) ≤ ((Disorder.cstar M) ^ (10 : ℕ)) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (by positivity) hkey10 2
    rw [le_div_iff₀ (pow_pos hC0 20)]
    calc M.gamma ^ (2 : ℕ) * C ^ (20 : ℕ) = (C ^ (10 : ℕ) * M.gamma) ^ (2 : ℕ) := by ring
      _ ≤ ((Disorder.cstar M) ^ (10 : ℕ)) ^ (2 : ℕ) := hsq
      _ = (Disorder.cstar M) ^ (20 : ℕ) := by ring
  have hcs2 : (Disorder.cstar M) ^ (2 : ℕ) ≤ 9 / 4 := by
    calc (Disorder.cstar M) ^ (2 : ℕ) ≤ (3 / 2 : ℝ) ^ (2 : ℕ) := pow_le_pow_left₀ hcs0.le hcs32 2
      _ = 9 / 4 := by norm_num
  obtain ⟨hgu4, hval8, hden8, hcore8⟩ :=
    (show (31104 * Rr ≤ M.gamma ^ (2 : ℕ) * u ^ (4 : ℕ)) ∧ (M.gamma ^ (5 : ℕ) * u ^ (8 : ℕ) =
      (Disorder.cstar M) ^ (16 : ℕ) /
      ((Support.cgEllipLowerConstant d) ^ (8 : ℕ) * C ^ (16 : ℕ) * M.gamma ^ (3 : ℕ))) ∧ ((0 : ℝ)
        < (Support.cgEllipLowerConstant d) ^ (8 : ℕ) * C ^ (16 : ℕ) *
      M.gamma ^ (3 : ℕ)) ∧ (10321920 * G0d * ((Support.cgEllipLowerConstant d) ^ (8 : ℕ) * C ^ (16
        : ℕ) *
      M.gamma ^ (3 : ℕ)) ≤ theta * (Disorder.cstar M) ^ (16 : ℕ)) from
      @shiftedG0Lane_comparisonBounds1 (d) (hCcg0) (hCs0) (hgmc0) (hgtc0) (hPn0) (r) (L) (G0d)
        (hG0ddef) (C) (hC6) (M) (theta) (htheta0) (hcouple) (hC0) (hCne) (hflA) (hflB) (hflC) (Rr)
          (hRrdef) (hcs0) (hcs32) (hg0) (hgne) (hcsne) (hCcgne) (u) (hu') (hgammale) (hgammasq)
            (hcs2))
  have hgu8 : 10321920 * G ≤ M.gamma ^ (5 : ℕ) * u ^ (8 : ℕ)  := @shiftedG0Lane_estimate1 (d)
    (G0d) (C) (M) (theta) (htheta0) (G) (hGtheta) (u) (hval8) (hden8) (hcore8)
  -- from here the proved proof, verbatim
  have hA0 : 0 < cgTailScale M (E : ℝ) := cgTailScale_pos M (E : ℝ)
  have hsprime0 : (0 : ℝ) < M.gamma / 4 := by linarith only [hg0]
  have hsprime1 : M.gamma / 4 ≤ 1 := by linarith only [hg4]
  have hdom : ∀ j : ℕ, annulusPenalty d (1 / 3 : ℝ) (j + 2) * cgTailScale M (E : ℝ)
      ≤ cgTailScale M (E : ℝ) * annulusPenaltyThird d (j + 2) := by
    intro j
    rw [annulusPenalty_third]
    exact le_of_eq (mul_comm _ _)
  have hapos : ∀ j : ℕ, 0 < cgTailScale M (E : ℝ) * annulusPenaltyThird d (j + 2) :=
    fun j => mul_pos hA0 (annulusPenaltyThird_pos d _)
  have hsum : Summable fun j : ℕ => weightThird (M.gamma / 4) j *
      (cgTailScale M (E : ℝ) * annulusPenaltyThird d (j + 2)) :=
    summable_weight_mul_annulusPenaltyThird d hsprime0 hA0.le
  obtain ⟨S0, hS0def⟩ : ∃ x : ℝ, x =
      ∑' j : ℕ, weightThird (M.gamma / 4) j * annulusPenaltyThird d (j + 2) := ⟨_, rfl⟩
  obtain ⟨Ssum, hSsumdef⟩ : ∃ x : ℝ, x = ∑' j : ℕ, weightThird (M.gamma / 4) j *
      (cgTailScale M (E : ℝ) * annulusPenaltyThird d (j + 2)) := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ x : ℝ, x = gammaTriangleConst (1 / 3 : ℝ) * Ssum := ⟨_, rfl⟩
  have hSsum_eq : Ssum = cgTailScale M (E : ℝ) * S0 := by
    rw [hSsumdef, hS0def, ← tsum_mul_left]
    exact tsum_congr fun j => by ring
  have hSsum0 : 0 < Ssum := by
    rw [hSsumdef]
    refine hsum.tsum_pos (fun j => ?_) 0 ?_
    · exact mul_nonneg (weightThird_pos j).le (hapos j).le
    · exact mul_pos (weightThird_pos 0) (hapos 0)
  have hK0 : 0 < K := by
    rw [hKdef]
    exact mul_pos hgtc0 hSsum0
  have htail : ∀ m : ℤ, IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma (1 / 3 : ℝ))
      (Ycal M (Support.cgEllipLowerConstant d) (M.gamma / 4) m) K := by
    intro m
    rw [hKdef, hSsumdef]
    exact isBigOWith_Ycal M (Support.cgEllipLowerConstant d) (by norm_num) hA0.le
      hatom hapos hdom hsum m
  obtain ⟨p, hpdef⟩ : ∃ x : ℝ, x = Real.exp (u / 6) := ⟨_, rfl⟩
  have hp0 : 0 < p := by rw [hpdef]; exact Real.exp_pos _
  have hp1 : 1 ≤ p := by
    rw [hpdef]
    have h := Real.add_one_le_exp (u / 6)
    linarith only [h, hu0]
  have hinv3 : ((1 / 3 : ℝ))⁻¹ = 3 := by norm_num
  have hp3 : p ^ ((1 / 3 : ℝ))⁻¹ = Real.exp (u / 2) := by
    rw [hinv3, hpdef, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  obtain ⟨D, hDdef⟩ : ∃ x : ℝ, x =
      gammaMomentConst (1 / 3 : ℝ) * p ^ ((1 / 3 : ℝ))⁻¹ * K := ⟨_, rfl⟩
  have hD0 : 0 < D := by
    rw [hDdef]
    exact mul_pos (mul_pos hgmc0 (Real.rpow_pos_of_pos hp0 _)) hK0
  have hnorm : gammaMomentConst (1 / 3 : ℝ) * p ^ ((1 / 3 : ℝ))⁻¹ * K ≤ D := le_of_eq hDdef.symm
  have hexpprod : Real.exp (u / 2) * Real.exp (-u) = Real.exp (-(u / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hDval : D = gammaMomentConst (1 / 3 : ℝ) * gammaTriangleConst (1 / 3 : ℝ) * S0 *
      Real.exp (-(u / 2)) := by
    rw [hDdef, hp3, hKdef, hSsum_eq, hAu, ← hexpprod]
    ring
  have hplow4 : u ^ (4 : ℕ) / 31104 ≤ p := by
    have h := Real.pow_div_factorial_le_exp (x := u / 6) (by linarith only [hu0]) 4
    have hf : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [hf] at h
    rw [hpdef]
    calc u ^ (4 : ℕ) / 31104 = (u / 6) ^ (4 : ℕ) / 24 := by ring
      _ ≤ Real.exp (u / 6) := h
  obtain ⟨hsp, hrate, hthr⟩ :=
    (show (1 ≤ M.gamma / 4 * p) ∧ (Real.log ((3 : ℝ) * (r : ℝ)) + c1 * (r : ℝ)
      ≤ M.gamma / 4 * p * theta / (16 * (r : ℝ))) ∧ (9 * (M.gamma / 4)⁻¹ * Cstar ^ (1 / p) * theta
        ^ (-1 / p) ≤ D⁻¹) from
      @shiftedG0Lane_comparisonBounds2 (d) (hCs0) (hgmc0) (hgtc0) (hPn0) (r) (hr1) (hrR) (L)
        (hLdef) (M) (theta) (htheta0) (c1) (hc1g) (htheta1) (hthetane) (Rr) (hRr4) (hRrL) (G)
          (hGdef) (hG0) (hg0) (hg4) (hgne) (u) (hu0) (hgu4) (hgu8) (hsprime0) (S0) (hS0def) (p)
            (hp0) (hp1) (D) (hD0) (hDval) (hplow4))
  have hnull : (Cutoff.cutoffSampleLaw M).toMeasure
      (goodRowSet M (Support.cgEllipLowerConstant d) (M.gamma / 4))ᶜ = 0 :=
    measure_compl_goodRowSet M (Support.cgEllipLowerConstant d) (by norm_num) hA0.le hK0
      hsprime0 (by linarith only [hg4]) hatom hapos hdom hsum htail
  have hmain := ratioTail_Ycal_shift M (Support.cgEllipLowerConstant d) (M.gamma / 4) D
    (fun k => Support.eventG0 M (Support.cgEllipLowerConstant d) k ∪
      (goodRowSet M (Support.cgEllipLowerConstant d) (M.gamma / 4))ᶜ) m0
    (by norm_num : (0 : ℝ) < 1 / 3) hK0 hD0 hp1 hsprime0 hsprime1 hsp hr1
    (by norm_num : (1 : ℝ) ≤ 3) htheta0 hthetar hc10 hrate htail hnorm
    hrgap
    (fun m => measurable_Ycal_annulusRegion_local M (Support.cgEllipLowerConstant d)
      (M.gamma / 4) m)
    (hreduce_eventG0_all M (Support.cgEllipLowerConstant d) hD0 hthr)
  exact fun n => le_trans (measure_scaleProp_le_of_null_enlargement _ _ _ hnull n) (hmain n)

end

end Algsuperdiff.Section4.Provider.Proportion
