/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.ResponseBlockObjects
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.DescendantEnergyAndFenchelSlots
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.DescendantHeadBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.TriadicRefinementIncrement
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.DiagonalDefectCarriers
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.OptimizerEnergyIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.ReferenceCubeAveragePullback
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.TerminalEnergyMeasurability
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# High-contrast homogenization: Entry.Response.Limit.DescendantLimitDomination

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Passing to the descendant limit of the cutoff-mean row by domination

The cutoff-mean rows of the cutoff estimate pair the cutoff's within-cell oscillation with the
crossed pairing `⟨Y₂,∇v⟩ + ⟨Y₁,a∇v⟩` of the optimizer state with the annealed mean, a quantity with
no sign; the exact partition identity underlying the cell decomposition still applies to this
signed integrand, and refining the terminal cell down to generation `t-(H+N)` leaves a defect
bounded by `32 d^2 Θ 3^{-(H+N)}` times the terminal cell average of its modulus. Passing `N` to
infinity does not need an annealed bound on this remainder: it is enough that the remainder tends
to zero along every sample, which it does, since the bound above is a fixed constant times
`3^{-N}`, and this pathwise vanishing is exactly the hypothesis a dominated-convergence argument
needs to replace the depth-`(H+N)` cell part, in the limit, by the full oscillation half of the
row. A Cauchy-Schwarz estimate over the generations splits the geometric weight `3^{-n}` of the
descendant sum as `3^{-n/4}·3^{-3n/4}` so as to pair it against the source-load weights.
This is the descendant-limit step of the cutoff-mean row of the response transfer, and it serves
`p.response.transfer`.
-/

section
/-!
## The cutoff cell decomposition against a signed integrand

The cutoff-mean rows of `p.response.transfer` pair the cutoff fluctuation with the crossed
pairing `⟨Y₂, ∇v⟩ + ⟨Y₁, a∇v⟩` of the optimizer state with the annealed mean, which has no sign.
The exact partition identity still writes the `(φ - 1)`-weighted average of a density `f` as the
normalized sum of the products of the cell means of `φ - 1` and of `f`, and on each depth-`n`
descendant cell the cutoff deviates from its own cell mean by at most
`32 d² responseCutoffProfileConst 3^{-n}`.  Because the integrand is signed, the cellwise
oscillation bound is applied against the cell average of `|f|`, so the remainder is controlled by
the terminal cell average of the absolute integrand rather than by the average of `f` itself.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- On a single descendant cell, the average of `(φ - 1) f` minus the product of the cell means
of `φ - 1` and `f` is the cell average of `(φ - (φ)_V) f`.  This is the exact per-cell identity
behind the scale gain of the cutoff estimate of `p.response.transfer`, and it requires no sign
hypothesis on the integrand. -/
private theorem volumeAverage_mul_sub_mul_volumeAverage_eq_signed
    {d : ℕ} {qq : Mat d} (t : ℤ) (n : ℕ) (w : Fin d → ℤ) {φ f : Vec d → ℝ}
    (hvol : (volume (adaptedCellAtCenter qq (t - (n : ℤ)) w)).toReal ≠ 0)
    (hfin : volume (adaptedCellAtCenter qq (t - (n : ℤ)) w) ≠ ⊤)
    (hfat : IntegrableOn f (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    (hφat : IntegrableOn φ (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    (hφfat : IntegrableOn (fun x => (φ x - 1) * f x) (adaptedCellAtCenter qq (t - (n : ℤ)) w)) :
    volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) (fun x => (φ x - 1) * f x)
      - (volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) (fun x => φ x - 1))
        * volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) f
      = volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w)
          (fun x => (φ x - volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) φ) * f x) := by
  have : IsFiniteMeasure (volumeMeasureOn (adaptedCellAtCenter qq (t - (n : ℤ)) w)) := by
    rw [volumeMeasureOn]
    exact isFiniteMeasure_restrict.mpr hfin
  set mw : ℝ := volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) φ with hmw
  have h1 : IntegrableOn (fun _ : Vec d => (1 : ℝ)) (adaptedCellAtCenter qq (t - (n : ℤ)) w) :=
    integrable_const 1
  have hc : volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) (fun x => φ x - 1) = mw - 1 := by
    rw [show (fun x : Vec d => φ x - 1) = φ - fun _ => (1 : ℝ) by funext x; simp]
    rw [volumeAverage_sub hφat h1, volumeAverage_const hvol, ← hmw]
  have hconst : IntegrableOn
      (fun x => (mw - 1) * f x) (adaptedCellAtCenter qq (t - (n : ℤ)) w) := hfat.const_mul _
  have hsubeq : volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) (fun x => (mw - 1) * f x)
      = (mw - 1) * volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) f :=
    volumeAverage_smul _ (mw - 1) f
  have hfun : ((fun x : Vec d => (φ x - 1) * f x) - fun x => (mw - 1) * f x)
      = fun x => (φ x - mw) * f x := by
    funext x
    change (φ x - 1) * f x - (mw - 1) * f x = (φ x - mw) * f x
    ring
  rw [hc, ← hsubeq, ← volumeAverage_sub hφfat hconst, hfun]

/-- On a single descendant cell, the cell average of `(φ - (φ)_V) f` is bounded by
`32 d² responseCutoffProfileConst 3^{-n}` times the cell average of `|f|`.  The oscillation of the
cutoff is paired with the absolute integrand, so no sign hypothesis on `f` is needed. -/
private theorem abs_volumeAverage_sub_cellAverage_mul_le_abs
    {d : ℕ} {qq : Mat d} (hq : IsUnit qq) {t : ℤ} {φ : Vec d → ℝ}
    (hφ : IsResponseCutoff qq t φ) (n : ℕ) (w : Fin d → ℤ) {f : Vec d → ℝ}
    (hvol : (volume (adaptedCellAtCenter qq (t - (n : ℤ)) w)).toReal ≠ 0)
    (hfin : volume (adaptedCellAtCenter qq (t - (n : ℤ)) w) ≠ ⊤)
    (hfat : IntegrableOn f (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    (habsat : IntegrableOn (fun x => |f x|) (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    (hφat : IntegrableOn φ (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    (hφfat : IntegrableOn (fun x => (φ x - 1) * f x) (adaptedCellAtCenter qq (t - (n : ℤ)) w)) :
    |volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w)
        (fun x => (φ x - volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) φ) * f x)|
      ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ))
          * volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) (fun x => |f x|) := by
  set Vw : Set (Vec d) := adaptedCellAtCenter qq (t - (n : ℤ)) w with hVw
  set K : ℝ := 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ)) with hK
  set mw : ℝ := volumeAverage Vw φ with hmw
  have hVmeas : MeasurableSet Vw :=
    (isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w).measurableSet
  have : IsFiniteMeasure (volumeMeasureOn Vw) := by
    rw [volumeMeasureOn, hVw]
    exact isFiniteMeasure_restrict.mpr hfin
  have hgint : IntegrableOn (fun x => (φ x - mw) * f x) Vw := by
    refine MeasureTheory.IntegrableOn.congr_fun
      (hφfat.sub (hfat.const_mul (mw - 1))) ?_ hVmeas
    intro x _
    change (φ x - 1) * f x - (mw - 1) * f x = (φ x - mw) * f x
    ring
  have hKint : IntegrableOn (fun x => K * |f x|) Vw := habsat.const_mul K
  have hbound : ∀ x ∈ Vw, |φ x - mw| ≤ K := by
    intro x hx
    have h := abs_sub_volumeAverage_le_of_isResponseCutoff hq hφ n w hvol hfin hφat hx
    have hmw' : mw = volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) φ := by rw [hmw, hVw]
    rw [hmw', hK]
    exact h
  have hpt : ∀ x ∈ Vw, |(φ x - mw) * f x| ≤ K * |f x| := by
    intro x hx
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hbound x hx) (abs_nonneg (f x))
  calc |volumeAverage Vw (fun x => (φ x - mw) * f x)|
      ≤ volumeAverage Vw (fun x => K * |f x|) :=
        volumeAverage_abs_le_of_le hVmeas hpt hgint hKint
    _ = K * volumeAverage Vw (fun x => |f x|) :=
        volumeAverage_smul Vw K (fun x => |f x|)

/-- **The cutoff cell decomposition against a signed integrand.**  Replacing the cutoff by its
cell averages on the depth-`n` triadic subdivision of the terminal cell costs at most the cutoff
oscillation `32 d² Θ 3^{-n}` times the terminal cell average of the absolute integrand.  This is
the cell decomposition of the cutoff-mean rows of `p.response.transfer`. -/
theorem abs_volumeAverage_sub_one_mul_sub_avsum_le_abs {d : ℕ} [NeZero d] {qq : Mat d}
    (hq : IsUnit qq) (t : ℤ) (n : ℕ) {φ : Vec d → ℝ} (hφ : IsResponseCutoff qq t φ)
    {f : Vec d → ℝ}
    (habsint : IntegrableOn (fun x => |f x|) (HighContrast.adaptedCell qq t))
    (hφfint : IntegrableOn (fun x => (φ x - 1) * f x) (HighContrast.adaptedCell qq t))
    (hfat : ∀ w ∈ triadicIndexBox d n, IntegrableOn f (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    (habsat : ∀ w ∈ triadicIndexBox d n,
      IntegrableOn (fun x => |f x|) (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    (hφat : ∀ w ∈ triadicIndexBox d n, IntegrableOn φ (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    (hφfat : ∀ w ∈ triadicIndexBox d n,
      IntegrableOn (fun x => (φ x - 1) * f x) (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    (hvol : ∀ w ∈ triadicIndexBox d n,
      (volume (adaptedCellAtCenter qq (t - (n : ℤ)) w)).toReal ≠ 0)
    (hfin : ∀ w ∈ triadicIndexBox d n, volume (adaptedCellAtCenter qq (t - (n : ℤ)) w) ≠ ⊤) :
    |volumeAverage (HighContrast.adaptedCell qq t) (fun x => (φ x - 1) * f x)
        - ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n,
            (volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) (fun x => φ x - 1)) *
              volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) f|
      ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ))
          * volumeAverage (HighContrast.adaptedCell qq t) (fun x => |f x|) := by
  let V : (Fin d → ℤ) → Set (Vec d) := fun w => adaptedCellAtCenter qq (t - (n : ℤ)) w
  let c : (Fin d → ℤ) → ℝ := fun w => volumeAverage (V w) (fun x => φ x - 1)
  let fbar : (Fin d → ℤ) → ℝ := fun w => volumeAverage (V w) f
  let fabsw : (Fin d → ℤ) → ℝ := fun w => volumeAverage (V w) (fun x => |f x|)
  let K : ℝ := 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ))
  let g : Vec d → ℝ := fun x => (φ x - 1) * f x
  change |volumeAverage (HighContrast.adaptedCell qq t) g
      - (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n, c w * fbar w|
    ≤ K * volumeAverage (HighContrast.adaptedCell qq t) (fun x => |f x|)
  have hpartg : (((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, volumeAverage (V w) g
      = volumeAverage (HighContrast.adaptedCell qq t) g :=
    avsum_volumeAverage_eq (d := d) qq hq t n (f := g) hφfint
  have hpartabs : (((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, fabsw w
      = volumeAverage (HighContrast.adaptedCell qq t) (fun x => |f x|) :=
    avsum_volumeAverage_eq (d := d) qq hq t n (f := fun x => |f x|) habsint
  have hcell : ∀ w ∈ triadicIndexBox d n,
      volumeAverage (V w) g - c w * fbar w
        = volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * f x) := by
    intro w hw
    exact volumeAverage_mul_sub_mul_volumeAverage_eq_signed t n w (hvol w hw) (hfin w hw)
      (hfat w hw) (hφat w hw) (hφfat w hw)
  have hboundw : ∀ w ∈ triadicIndexBox d n,
      |volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * f x)| ≤ K * fabsw w := by
    intro w hw
    exact abs_volumeAverage_sub_cellAverage_mul_le_abs (d := d) (qq := qq) hq hφ n w
      (hvol w hw) (hfin w hw) (hfat w hw) (habsat w hw) (hφat w hw) (hφfat w hw)
  have hsumcell : (∑ w ∈ triadicIndexBox d n, (volumeAverage (V w) g - c w * fbar w))
      = ∑ w ∈ triadicIndexBox d n,
          volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * f x) :=
    Finset.sum_congr rfl (fun w hw => hcell w hw)
  have hsumabs : |∑ w ∈ triadicIndexBox d n,
        volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * f x)|
      ≤ ∑ w ∈ triadicIndexBox d n, K * fabsw w := by
    calc |∑ w ∈ triadicIndexBox d n,
            volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * f x)|
        ≤ ∑ w ∈ triadicIndexBox d n,
            |volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * f x)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ w ∈ triadicIndexBox d n, K * fabsw w :=
          Finset.sum_le_sum (fun w hw => hboundw w hw)
  calc |volumeAverage (HighContrast.adaptedCell qq t) g
        - (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n, c w * fbar w|
      = |(((triadicIndexBox d n).card : ℝ))⁻¹ *
          (∑ w ∈ triadicIndexBox d n, volumeAverage (V w) g
            - ∑ w ∈ triadicIndexBox d n, c w * fbar w)| := by
            rw [← hpartg, ← mul_sub]
      _ = |(((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, (volumeAverage (V w) g - c w * fbar w)| := by
            rw [← Finset.sum_sub_distrib]
      _ = |(((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n,
            volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * f x)| := by
            rw [hsumcell]
      _ = (((triadicIndexBox d n).card : ℝ))⁻¹ *
          |∑ w ∈ triadicIndexBox d n,
            volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * f x)| := by
            rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
      _ ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, K * fabsw w :=
            mul_le_mul_of_nonneg_left hsumabs (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ = K * ((((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, fabsw w) := by
            rw [← Finset.mul_sum (triadicIndexBox d n) fabsw K]
            ring
      _ = K * volumeAverage (HighContrast.adaptedCell qq t) (fun x => |f x|) := by rw [hpartabs]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The vanishing remainder of the descendant refinement

The oscillation half of the cutoff-mean row of `p.response.transfer` refines the terminal cell
down to the generation `t - (H + N)` and keeps the defect of the depth-`(H+N)` cell part as a
remainder.  The cell decomposition against a signed integrand bounds that defect by
`32 d² Θ 3^{-(H+N)}` times the terminal cell average of the modulus of the integrand; splitting the
power as `3^{-H} · 3^{-N}` exhibits the printed factor `3^{-H}` of the row and leaves a remainder
that vanishes geometrically in the refinement depth `N`.  The `(φ-1)`-weighted integrand is
integrable wherever the integrand is, a response cutoff taking values in `[0, 2]`.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The `(φ-1)`-weighted integrand is integrable wherever the integrand is.**  A response cutoff
is smooth and takes values in `[0, 2]`, so `|φ - 1| ≤ 1` and multiplying by `φ - 1` preserves
integrability on any measurable set of finite volume. -/
theorem integrableOn_isResponseCutoff_sub_one_mul {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) (hUfin : volume U ≠ ⊤) {qq : Mat d} {t : ℤ} {φ : Vec d → ℝ}
    (hφ : IsResponseCutoff qq t φ) {f : Vec d → ℝ} (hf : IntegrableOn f U) :
    IntegrableOn (fun x => (φ x - 1) * f x) U := by
  obtain ⟨hφ0, hφ2, -, -, -, hsmooth, -⟩ := hφ
  have hmeas : Measurable fun x : Vec d => φ x - 1 :=
    (hsmooth.continuous.measurable).sub measurable_const
  have hbd : ∀ x : Vec d, |φ x - 1| ≤ 1 := by
    intro x
    rw [abs_le]
    constructor <;> linarith only [hφ0 x, hφ2 x]
  exact integrableOn_cutoff_mul_coord hU hUfin hmeas hbd hf

/-- **The remainder of the descendant refinement carries the printed `3^{-H}`.**  Replacing the
cutoff by its cell means on the depth-`(H+N)` triadic subdivision of the terminal cell costs at
most `(32 d² Θ 3^{-H}) · 3^{-N}` times the terminal cell average of the modulus of the integrand.
This is the remainder of the oscillation half of `p.response.transfer`, which vanishes as the
refinement depth `N` grows. -/
theorem abs_volumeAverage_sub_one_mul_sub_avsum_shift_le {d : ℕ} [NeZero d] {qq : Mat d}
    (hq : IsUnit qq) (t : ℤ) (H N : ℕ) {φ : Vec d → ℝ} (hφ : IsResponseCutoff qq t φ)
    {f : Vec d → ℝ}
    (habsint : IntegrableOn (fun x => |f x|) (HighContrast.adaptedCell qq t))
    (hfint : IntegrableOn f (HighContrast.adaptedCell qq t))
    (hfat : ∀ w ∈ triadicIndexBox d (H + N),
      IntegrableOn f (adaptedCellAtCenter qq (t - ((H + N : ℕ) : ℤ)) w))
    (habsat : ∀ w ∈ triadicIndexBox d (H + N),
      IntegrableOn (fun x => |f x|) (adaptedCellAtCenter qq (t - ((H + N : ℕ) : ℤ)) w)) :
    |volumeAverage (HighContrast.adaptedCell qq t) (fun x => (φ x - 1) * f x)
        - ((triadicIndexBox d (H + N)).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d (H + N),
            (volumeAverage (adaptedCellAtCenter qq (t - ((H + N : ℕ) : ℤ)) w) (fun x => φ x - 1)) *
              volumeAverage (adaptedCellAtCenter qq (t - ((H + N : ℕ) : ℤ)) w) f|
      ≤ (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
          * (3 : ℝ) ^ (-(N : ℝ))
          * volumeAverage (HighContrast.adaptedCell qq t) (fun x => |f x|) := by
  have hUmeas : MeasurableSet (HighContrast.adaptedCell qq t) :=
    (isOpen_adaptedCell_of_isUnit hq t).measurableSet
  have hUfin : volume (HighContrast.adaptedCell qq t) ≠ ⊤ := by
    have h0 : HighContrast.adaptedCellTranslate qq t 0 = HighContrast.adaptedCell qq t := by
      ext x; simp [HighContrast.adaptedCellTranslate]
    rw [← h0]
    exact Transport.volume_adaptedCellTranslate_ne_top qq t 0
  have hφfint : IntegrableOn (fun x => (φ x - 1) * f x) (HighContrast.adaptedCell qq t) :=
    integrableOn_isResponseCutoff_sub_one_mul hUmeas hUfin hφ hfint
  have hVmeas : ∀ w : Fin d → ℤ,
      MeasurableSet (adaptedCellAtCenter qq (t - ((H + N : ℕ) : ℤ)) w) :=
    fun w => (isOpen_adaptedCellAtCenter_of_isUnit hq (t - ((H + N : ℕ) : ℤ)) w).measurableSet
  have hVfin : ∀ w : Fin d → ℤ,
      volume (adaptedCellAtCenter qq (t - ((H + N : ℕ) : ℤ)) w) ≠ ⊤ :=
    fun w => Geometry.volume_adaptedCellAtCenter_ne_top qq _ w
  have hVpos : ∀ w : Fin d → ℤ,
      (volume (adaptedCellAtCenter qq (t - ((H + N : ℕ) : ℤ)) w)).toReal ≠ 0 :=
    fun w => ne_of_gt (volume_adaptedCellAtCenter_toReal_pos qq hq _ w)
  have hmain := abs_volumeAverage_sub_one_mul_sub_avsum_le_abs (d := d) (qq := qq) hq t (H + N)
    hφ habsint hφfint hfat habsat
    (fun w _ => integrableOn_isResponseCutoff hq hφ _ w)
    (fun w _ => integrableOn_isResponseCutoff_sub_one_mul (hVmeas w) (hVfin w) hφ (hfat w ‹_›))
    (fun w _ => hVpos w) (fun w _ => hVfin w)
  have hpow : (3 : ℝ) ^ (-(((H + N : ℕ) : ℝ))) =
      (3 : ℝ) ^ (-(H : ℝ)) * (3 : ℝ) ^ (-(N : ℝ)) := by
    rw [show -(((H + N : ℕ) : ℝ)) = -(H : ℝ) + -(N : ℝ) by push_cast; ring]
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  calc |volumeAverage (HighContrast.adaptedCell qq t) (fun x => (φ x - 1) * f x)
        - ((triadicIndexBox d (H + N)).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d (H + N),
            (volumeAverage (adaptedCellAtCenter qq (t - ((H + N : ℕ) : ℤ)) w) (fun x => φ x - 1)) *
              volumeAverage (adaptedCellAtCenter qq (t - ((H + N : ℕ) : ℤ)) w) f|
      ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(((H + N : ℕ) : ℝ)))
          * volumeAverage (HighContrast.adaptedCell qq t) (fun x => |f x|) := hmain
    _ = (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
          * (3 : ℝ) ^ (-(N : ℝ))
          * volumeAverage (HighContrast.adaptedCell qq t) (fun x => |f x|) := by
        rw [hpow]; ring

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The descendant limit by domination instead of a remainder bound

The descendant telescoping of the cutoff-mean row of `p.response.transfer` writes the annealed
functional, at every refinement depth, as its cell part plus the first `N` generation increments
plus a remainder.  The passage to the limit does NOT need an annealed bound on the remainder: it
needs only that the remainder tends to zero along every sample, together with an integrable
envelope for the whole series of increments.  Since the increments are flat averages of pairings
of a deterministic dual variable with cell averages of the optimizer state, such an envelope is
supplied by the scale-average seminorm of those cell averages, whereas a bound on the remainder
would need the annealed mean of a pointwise modulus.  This module records the limit in that form,
and concludes the integrability of the annealed functional as well as the bound.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory Filter

open scoped Topology

noncomputable section

/-- **The descendant limit from a pathwise vanishing remainder and an integrable envelope.**  If a
sample functional `Phi` splits, at every refinement depth `N`, into a cell part `Tcell`, the first
`N` generation increments and a remainder `rem N`; if the remainder tends to zero along every
sample; if the increments are dominated by a nonnegative family `g` whose sample sum is
`P`-integrable; and if every partial sum of the annealed increments is at most `B`; then `Phi` is
`P`-integrable and its annealed mean differs from that of the cell part by at most `B`.

This replaces the annealed remainder bound of
`abs_integral_sub_integral_le_of_descendant_bound` by hypotheses that the carriers supply: the
pathwise vanishing of the remainder needs only ellipticity along each sample, and the envelope
needs only the cell averages of the state, never a pointwise modulus. -/
theorem integrable_and_abs_integral_sub_integral_le_of_dominated_descendant
    {α : Type*} [MeasurableSpace α] (P : Measure α)
    (Phi Tcell : α → ℝ) (inc rem : ℕ → α → ℝ) (g : ℕ → α → ℝ) (B : ℝ)
    (hdec : ∀ (N : ℕ) (a : α),
      Phi a = Tcell a + (∑ n ∈ Finset.range N, inc n a) + rem N a)
    (hg0 : ∀ (n : ℕ) (a : α), 0 ≤ g n a)
    (hdom : ∀ (n : ℕ) (a : α), |inc n a| ≤ g n a)
    (hgsum : ∀ᵐ a ∂P, Summable (fun n : ℕ => g n a))
    (hgsumI : Integrable (fun a => ∑' n : ℕ, g n a) P)
    (hrem0 : ∀ a : α, Tendsto (fun N : ℕ => rem N a) atTop (𝓝 0))
    (hB : ∀ N : ℕ, |∑ n ∈ Finset.range N, ∫ a, inc n a ∂P| ≤ B)
    (hT : Integrable Tcell P)
    (hPhiM : AEStronglyMeasurable Phi P)
    (hinc : ∀ n : ℕ, Integrable (inc n) P) :
    Integrable Phi P
      ∧ |(∫ a, Phi a ∂P) - ∫ a, Tcell a ∂P| ≤ B := by
  -- The partial sums are the functional minus the remainder.
  have hSeq : ∀ (N : ℕ) (a : α),
      Tcell a + ∑ n ∈ Finset.range N, inc n a = Phi a - rem N a := by
    intro N a
    rw [hdec N a]
    ring
  -- Hence they converge to the functional along every sample.
  have hlim : ∀ a : α,
      Tendsto (fun N : ℕ => Tcell a + ∑ n ∈ Finset.range N, inc n a) atTop (𝓝 (Phi a)) := by
    intro a
    have h : Tendsto (fun N : ℕ => Phi a - rem N a) atTop (𝓝 (Phi a - 0)) :=
      tendsto_const_nhds.sub (hrem0 a)
    rw [sub_zero] at h
    exact h.congr fun N => (hSeq N a).symm
  -- The envelope dominates every partial sum, along almost every sample.
  have hbd : ∀ᵐ a ∂P, ∀ N : ℕ,
      |Tcell a + ∑ n ∈ Finset.range N, inc n a| ≤ |Tcell a| + ∑' n : ℕ, g n a := by
    filter_upwards [hgsum] with a hsa
    intro N
    have h1 : |∑ n ∈ Finset.range N, inc n a| ≤ ∑ n ∈ Finset.range N, |inc n a| :=
      Finset.abs_sum_le_sum_abs _ _
    have h2 : (∑ n ∈ Finset.range N, |inc n a|) ≤ ∑ n ∈ Finset.range N, g n a :=
      Finset.sum_le_sum fun n _ => hdom n a
    have h3 : (∑ n ∈ Finset.range N, g n a) ≤ ∑' n : ℕ, g n a :=
      hsa.sum_le_tsum (Finset.range N) fun n _ => hg0 n a
    have h0 : |Tcell a + ∑ n ∈ Finset.range N, inc n a|
        ≤ |Tcell a| + |∑ n ∈ Finset.range N, inc n a| := abs_add_le _ _
    linarith only [h0, h1, h2, h3]
  have hGint : Integrable (fun a => |Tcell a| + ∑' n : ℕ, g n a) P := hT.abs.add hgsumI
  -- The envelope dominates the functional itself, so the functional is integrable.
  have hPhibd : ∀ᵐ a ∂P, |Phi a| ≤ |Tcell a| + ∑' n : ℕ, g n a := by
    filter_upwards [hbd] with a ha
    exact le_of_tendsto (hlim a).abs (Eventually.of_forall fun N => ha N)
  have hPhiI : Integrable Phi P :=
    hGint.mono' hPhiM (hPhibd.mono fun a ha => by
      rw [Real.norm_eq_abs]; exact ha)
  refine ⟨hPhiI, ?_⟩
  -- Dominated convergence transfers the limit to the annealed means.
  have hSint : ∀ N : ℕ,
      Integrable (fun a => Tcell a + ∑ n ∈ Finset.range N, inc n a) P := fun N =>
    hT.add (integrable_finsetSum _ fun n _ => hinc n)
  have hconv : Tendsto (fun N : ℕ => ∫ a, (Tcell a + ∑ n ∈ Finset.range N, inc n a) ∂P)
      atTop (𝓝 (∫ a, Phi a ∂P)) :=
    tendsto_integral_of_dominated_convergence (fun a => |Tcell a| + ∑' n : ℕ, g n a)
      (fun N => (hSint N).aestronglyMeasurable) hGint
      (fun N => hbd.mono fun a ha => by rw [Real.norm_eq_abs]; exact ha N)
      (Eventually.of_forall hlim)
  have hSval : ∀ N : ℕ, (∫ a, (Tcell a + ∑ n ∈ Finset.range N, inc n a) ∂P)
      = (∫ a, Tcell a ∂P) + ∑ n ∈ Finset.range N, ∫ a, inc n a ∂P := by
    intro N
    rw [integral_add hT (integrable_finsetSum _ fun n _ => hinc n),
      integral_finsetSum (Finset.range N) fun n _ => hinc n]
  have hconst : Tendsto (fun _ : ℕ => (∫ a, Tcell a ∂P)) atTop (𝓝 (∫ a, Tcell a ∂P)) :=
    tendsto_const_nhds
  have hconv2 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, ∫ a, inc n a ∂P)
      atTop (𝓝 ((∫ a, Phi a ∂P) - ∫ a, Tcell a ∂P)) :=
    ((hconv.congr hSval).sub hconst).congr fun N => by ring
  exact le_of_tendsto hconv2.abs (Eventually.of_forall hB)

/-- **A geometrically small pathwise remainder vanishes.**  If the modulus of `rem N a` is at most
`C a · 3^{-N}` for a finite sample constant `C a`, then `rem N a → 0` along every sample.  This is
the `hrem0` hypothesis of
`integrable_and_abs_integral_sub_integral_le_of_dominated_descendant`, and it is all that the
descendant remainder of the cutoff-mean row has to supply: the sample constant is the cell average
of the modulus of the crossed pairing, which is finite along every sample by pathwise ellipticity
but has no annealed bound. -/
theorem tendsto_zero_of_abs_le_geometric {α : Type*} (rem : ℕ → α → ℝ) (C : α → ℝ)
    (hbd : ∀ (N : ℕ) (a : α), |rem N a| ≤ C a * (3 : ℝ) ^ (-(N : ℝ))) (a : α) :
    Tendsto (fun N : ℕ => rem N a) atTop (𝓝 0) := by
  have hpow : Tendsto (fun N : ℕ => ((3 : ℝ)⁻¹) ^ N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (r := (3 : ℝ)⁻¹) (by norm_num) (by norm_num)
  have hmul : Tendsto (fun N : ℕ => C a * ((3 : ℝ)⁻¹) ^ N) atTop (𝓝 0) := by
    have h := hpow.const_mul (C a)
    rwa [mul_zero] at h
  have hfun : (fun N : ℕ => C a * (3 : ℝ) ^ (-(N : ℝ)))
      = fun N : ℕ => C a * ((3 : ℝ)⁻¹) ^ N := by
    funext N
    rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast]
  have hbound : Tendsto (fun N : ℕ => C a * (3 : ℝ) ^ (-(N : ℝ))) atTop (𝓝 0) := by
    rw [hfun]; exact hmul
  refine squeeze_zero_norm ?_ hbound
  intro N
  rw [Real.norm_eq_abs]
  exact hbd N a

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The descendant remainder of the cutoff-mean row vanishes along every sample

The passage to the limit in the oscillation half of the cutoff-mean row of `p.response.transfer`
needs only that the depth-`(H+N)` remainder tends to zero along every sample.  It does: the
remainder is at most `(32 d² Θ 3^{-H}) 3^{-N}` times the terminal-cell average of the modulus of
the crossed pairing, and that average is a finite constant of the sample — finite by the pathwise
ellipticity of the coefficient, with no bound uniform in the sample and no integrability in the
law.  This module records the resulting vanishing for both signs, which is the `hrem0` hypothesis
of the dominated descendant limit.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory Filter

open scoped Topology

noncomputable section

/-- **The descendant remainder vanishes along every sample, minus sign.**  For the terminal
optimizer family of the recentred coefficient `a_- = a - g` and a deterministic dual variable `Y`,
the difference between the `(φ-1)`-weighted terminal cell average of the crossed pairing and its
depth-`(H+N)` cell part tends to zero as `N → ∞`, for every sample. -/
theorem tendsto_zero_descendantRemainder_respCoeffMinus {d : ℕ} [NeZero d]
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (H : ℕ) {φ : Vec d → ℝ}
    (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (Y : BlockVec d) (a : CoeffSpace d) :
    Tendsto (fun N : ℕ =>
        volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
            (vecDot Y.2 (optimizerField (respCoeffMinus F a) (uM a) x).1
              + vecDot Y.1 (optimizerField (respCoeffMinus F a) (uM a) x).2))
          - ((triadicIndexBox d (H + N)).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d (H + N),
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + N : ℕ) : ℤ)) w)
                  (fun x => φ x - 1)) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + N : ℕ) : ℤ)) w)
                  (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) (uM a) x).1
                    + vecDot Y.1 (optimizerField (respCoeffMinus F a) (uM a) x).2))
      atTop (𝓝 0) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hzero : (0 : Fin d → ℤ) ∈ triadicIndexBox d 0 := by
    rw [mem_triadicIndexBox_iff]
    intro i
    simp
  have hcell : adaptedCellAtCenter (respGrid jStar F) (t - ((0 : ℕ) : ℤ)) 0 = respCell jStar F t := by
    rw [respCell]
    simpa using adaptedCellAtCenter_zero (respGrid jStar F) t
  refine tendsto_zero_of_abs_le_geometric
    (fun N a' =>
      volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
          (vecDot Y.2 (optimizerField (respCoeffMinus F a') (uM a') x).1
            + vecDot Y.1 (optimizerField (respCoeffMinus F a') (uM a') x).2))
        - ((triadicIndexBox d (H + N)).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d (H + N),
            (volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + N : ℕ) : ℤ)) w)
                (fun x => φ x - 1)) *
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + N : ℕ) : ℤ)) w)
                (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a') (uM a') x).1
                  + vecDot Y.1 (optimizerField (respCoeffMinus F a') (uM a') x).2))
    (fun a' => (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
      * volumeAverage (respCell jStar F t)
          (fun x => |vecDot Y.2 (optimizerField (respCoeffMinus F a') (uM a') x).1
            + vecDot Y.1 (optimizerField (respCoeffMinus F a') (uM a') x).2|)) ?_ a
  intro N a'
  obtain ⟨hfU, habsU⟩ := integrableOn_cross_optimizerField_respCoeffMinus_adaptedCellAtCenter jStar
    hjStar F hm t 0 a' (uM a') Y hzero
  rw [hcell] at hfU habsU
  have hat := fun w (hw : w ∈ triadicIndexBox d (H + N)) =>
    integrableOn_cross_optimizerField_respCoeffMinus_adaptedCellAtCenter jStar hjStar F hm t (H + N)
      a' (uM a') Y hw
  have hmain := abs_volumeAverage_sub_one_mul_sub_avsum_shift_le (qq := respGrid jStar F) hq t H N
    hφ (f := fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a') (uM a') x).1
      + vecDot Y.1 (optimizerField (respCoeffMinus F a') (uM a') x).2)
    habsU hfU (fun w hw => (hat w hw).1) (fun w hw => (hat w hw).2)
  calc |volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
          (vecDot Y.2 (optimizerField (respCoeffMinus F a') (uM a') x).1
            + vecDot Y.1 (optimizerField (respCoeffMinus F a') (uM a') x).2))
        - ((triadicIndexBox d (H + N)).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d (H + N),
            (volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + N : ℕ) : ℤ)) w)
                (fun x => φ x - 1)) *
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + N : ℕ) : ℤ)) w)
                (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a') (uM a') x).1
                  + vecDot Y.1 (optimizerField (respCoeffMinus F a') (uM a') x).2)|
      ≤ (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
          * (3 : ℝ) ^ (-(N : ℝ))
          * volumeAverage (respCell jStar F t)
              (fun x => |vecDot Y.2 (optimizerField (respCoeffMinus F a') (uM a') x).1
                + vecDot Y.1 (optimizerField (respCoeffMinus F a') (uM a') x).2|) := hmain
    _ = (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
          * volumeAverage (respCell jStar F t)
              (fun x => |vecDot Y.2 (optimizerField (respCoeffMinus F a') (uM a') x).1
                + vecDot Y.1 (optimizerField (respCoeffMinus F a') (uM a') x).2|)
        * (3 : ℝ) ^ (-(N : ℝ)) := by ring

/-- **The descendant remainder vanishes along every sample, plus sign.**  For the terminal
optimizer family of the recentred coefficient `a_- = a - g` and a deterministic dual variable `Y`,
the difference between the `(φ-1)`-weighted terminal cell average of the crossed pairing and its
depth-`(H+N)` cell part tends to zero as `N → ∞`, for every sample. -/
theorem tendsto_zero_descendantRemainder_respCoeffPlus {d : ℕ} [NeZero d]
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (H : ℕ) {φ : Vec d → ℝ}
    (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (Y : BlockVec d) (a : CoeffSpace d) :
    Tendsto (fun N : ℕ =>
        volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
            (vecDot Y.2 (optimizerField (respCoeffPlus F a) (uM a) x).1
              + vecDot Y.1 (optimizerField (respCoeffPlus F a) (uM a) x).2))
          - ((triadicIndexBox d (H + N)).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d (H + N),
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + N : ℕ) : ℤ)) w)
                  (fun x => φ x - 1)) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + N : ℕ) : ℤ)) w)
                  (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) (uM a) x).1
                    + vecDot Y.1 (optimizerField (respCoeffPlus F a) (uM a) x).2))
      atTop (𝓝 0) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hzero : (0 : Fin d → ℤ) ∈ triadicIndexBox d 0 := by
    rw [mem_triadicIndexBox_iff]
    intro i
    simp
  have hcell : adaptedCellAtCenter (respGrid jStar F) (t - ((0 : ℕ) : ℤ)) 0 = respCell jStar F t := by
    rw [respCell]
    simpa using adaptedCellAtCenter_zero (respGrid jStar F) t
  refine tendsto_zero_of_abs_le_geometric
    (fun N a' =>
      volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
          (vecDot Y.2 (optimizerField (respCoeffPlus F a') (uM a') x).1
            + vecDot Y.1 (optimizerField (respCoeffPlus F a') (uM a') x).2))
        - ((triadicIndexBox d (H + N)).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d (H + N),
            (volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + N : ℕ) : ℤ)) w)
                (fun x => φ x - 1)) *
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + N : ℕ) : ℤ)) w)
                (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a') (uM a') x).1
                  + vecDot Y.1 (optimizerField (respCoeffPlus F a') (uM a') x).2))
    (fun a' => (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
      * volumeAverage (respCell jStar F t)
          (fun x => |vecDot Y.2 (optimizerField (respCoeffPlus F a') (uM a') x).1
            + vecDot Y.1 (optimizerField (respCoeffPlus F a') (uM a') x).2|)) ?_ a
  intro N a'
  obtain ⟨hfU, habsU⟩ := integrableOn_cross_optimizerField_respCoeffPlus_adaptedCellAtCenter jStar
    hjStar F hm t 0 a' (uM a') Y hzero
  rw [hcell] at hfU habsU
  have hat := fun w (hw : w ∈ triadicIndexBox d (H + N)) =>
    integrableOn_cross_optimizerField_respCoeffPlus_adaptedCellAtCenter jStar hjStar F hm t (H + N)
      a' (uM a') Y hw
  have hmain := abs_volumeAverage_sub_one_mul_sub_avsum_shift_le (qq := respGrid jStar F) hq t H N
    hφ (f := fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a') (uM a') x).1
      + vecDot Y.1 (optimizerField (respCoeffPlus F a') (uM a') x).2)
    habsU hfU (fun w hw => (hat w hw).1) (fun w hw => (hat w hw).2)
  calc |volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
          (vecDot Y.2 (optimizerField (respCoeffPlus F a') (uM a') x).1
            + vecDot Y.1 (optimizerField (respCoeffPlus F a') (uM a') x).2))
        - ((triadicIndexBox d (H + N)).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d (H + N),
            (volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + N : ℕ) : ℤ)) w)
                (fun x => φ x - 1)) *
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + N : ℕ) : ℤ)) w)
                (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a') (uM a') x).1
                  + vecDot Y.1 (optimizerField (respCoeffPlus F a') (uM a') x).2)|
      ≤ (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
          * (3 : ℝ) ^ (-(N : ℝ))
          * volumeAverage (respCell jStar F t)
              (fun x => |vecDot Y.2 (optimizerField (respCoeffPlus F a') (uM a') x).1
                + vecDot Y.1 (optimizerField (respCoeffPlus F a') (uM a') x).2|) := hmain
    _ = (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
          * volumeAverage (respCell jStar F t)
              (fun x => |vecDot Y.2 (optimizerField (respCoeffPlus F a') (uM a') x).1
                + vecDot Y.1 (optimizerField (respCoeffPlus F a') (uM a') x).2|)
        * (3 : ℝ) ^ (-(N : ℝ)) := by ring

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The descendant sum against the source-load weights

For the response transfer of `p.response.transfer`, the within-cell oscillation of the cutoff is
paired with the gradient and the flux at every descendant generation, the generation-`n` term
carrying the factor `3^{-H-n}`.  Summing the descendants against the source-load weights and
applying Cauchy--Schwarz across the generations splits `3^{-n} = 3^{-n/4} · 3^{-3n/4}` and bounds
the descendant sum by the square root of the load times the square root of a convergent geometric
series.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The geometric series `∑ n, 3^{-n/2}` converges: its terms are `(3^{-1/2})^n` and
`3^{-1/2} < 1`. -/
theorem summable_rpow_neg_half : Summable fun n : ℕ => (3 : ℝ) ^ (-((n : ℝ) / 2)) := by
  have hlt : (3 : ℝ) ^ (-(1 : ℝ) / 2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hnn : 0 ≤ (3 : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  refine (summable_geometric_of_lt_one hnn hlt).congr fun n => ?_
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  rw [show (-(1 : ℝ) / 2) * (n : ℝ) = -((n : ℝ) / 2) by ring]

/-- Cauchy--Schwarz across the descendant generations bounds the descendant sum
`∑ n, 3^{-n} √(L n)` by the square root of the source-load weighted sum `∑ n, 3^{-3n/2} L n`,
multiplied by the square root of the convergent geometric series `∑ n, 3^{-n/2}`.  Splitting
`3^{-n} = 3^{-n/4} · 3^{-3n/4}` is what keeps the printed factor `3^{-H}(E[J_t]𝓛_s)^{1/2}` of
`p.response.transfer`. -/
theorem tsum_weighted_sqrt_le_sqrt_mul_sqrt (L : ℕ → ℝ) (hL : ∀ n, 0 ≤ L n)
    (hsum : Summable fun n : ℕ => (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n)
    (hsum' : Summable fun n : ℕ => (3 : ℝ) ^ (-(n : ℝ)) * Real.sqrt (L n)) :
    (∑' n : ℕ, (3 : ℝ) ^ (-(n : ℝ)) * Real.sqrt (L n))
      ≤ Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)))
        * Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n) := by
  let u : ℕ → ℝ := fun n => (3 : ℝ) ^ (-(1 : ℝ) / 4 * (n : ℝ))
  let v : ℕ → ℝ := fun n => (3 : ℝ) ^ (-(3 : ℝ) / 4 * (n : ℝ)) * Real.sqrt (L n)
  have hu_sq : ∀ n, u n ^ 2 = (3 : ℝ) ^ (-((n : ℝ) / 2)) := by
    intro n
    change ((3 : ℝ) ^ (-(1 : ℝ) / 4 * (n : ℝ))) ^ 2 = (3 : ℝ) ^ (-((n : ℝ) / 2))
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    rw [show (-(1 : ℝ) / 4 * (n : ℝ)) * ((2 : ℕ) : ℝ) = -((n : ℝ) / 2) by ring]
  have hv_sq : ∀ n, v n ^ 2 = (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n := by
    intro n
    change ((3 : ℝ) ^ (-(3 : ℝ) / 4 * (n : ℝ)) * Real.sqrt (L n)) ^ 2
      = (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n
    rw [← Real.rpow_natCast]
    rw [Real.mul_rpow (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _) (Real.sqrt_nonneg _)]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    rw [Real.rpow_natCast, Real.sq_sqrt (hL n)]
    rw [show (-(3 : ℝ) / 4 * (n : ℝ)) * ((2 : ℕ) : ℝ) = -((3 : ℝ) / 2) * (n : ℝ) by ring]
  have huv : ∀ n, u n * v n = (3 : ℝ) ^ (-(n : ℝ)) * Real.sqrt (L n) := by
    intro n
    change (3 : ℝ) ^ (-(1 : ℝ) / 4 * (n : ℝ))
        * ((3 : ℝ) ^ (-(3 : ℝ) / 4 * (n : ℝ)) * Real.sqrt (L n))
      = (3 : ℝ) ^ (-(n : ℝ)) * Real.sqrt (L n)
    rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    rw [show (-(1 : ℝ) / 4 * (n : ℝ)) + (-(3 : ℝ) / 4 * (n : ℝ)) = -(n : ℝ) by ring]
  have huv_fun : (fun n : ℕ => u n * v n)
      = fun n : ℕ => (3 : ℝ) ^ (-(n : ℝ)) * Real.sqrt (L n) := funext huv
  have hpartial : ∀ s : Finset ℕ, ∑ n ∈ s, u n * v n
      ≤ Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)))
        * Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n) := by
    intro s
    refine (Real.sum_mul_le_sqrt_mul_sqrt s u v).trans ?_
    have hu_fin : ∑ n ∈ s, u n ^ 2 ≤ ∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)) := by
      calc ∑ n ∈ s, u n ^ 2 = ∑ n ∈ s, (3 : ℝ) ^ (-((n : ℝ) / 2)) :=
            Finset.sum_congr rfl fun n _ => hu_sq n
        _ ≤ ∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)) :=
            summable_rpow_neg_half.sum_le_tsum s fun _ _ =>
              Real.rpow_nonneg (by norm_num) _
    have hv_fin : ∑ n ∈ s, v n ^ 2
        ≤ ∑' n : ℕ, (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n := by
      calc ∑ n ∈ s, v n ^ 2
          = ∑ n ∈ s, (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n :=
            Finset.sum_congr rfl fun n _ => hv_sq n
        _ ≤ ∑' n : ℕ, (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n :=
            hsum.sum_le_tsum s fun _ _ =>
              mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hL _)
    exact mul_le_mul (Real.sqrt_le_sqrt hu_fin) (Real.sqrt_le_sqrt hv_fin)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsum_uv : Summable fun n : ℕ => u n * v n := by
    rw [huv_fun]
    exact hsum'
  have hmain := hsum_uv.tsum_le_of_sum_le hpartial
  rw [huv_fun] at hmain
  exact hmain

end

end HCPolySupport.HighContrast.Multiscale
end
