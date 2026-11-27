/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.MeasureSpaces.Martingales.Filtration
public import LeanPool.FunctionSpaces.MeasureSpaces.Martingales.Partition
public import LeanPool.FunctionSpaces.Domains.Interval.PiecewisePoly
public import LeanPool.FunctionSpaces.Wavelets.DyadicNormalisation
public import LeanPool.FunctionSpaces.ApproximationSpaces.Decompositions.Atomic
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The Haar system on `[0, 1]`

The dyadic intervals of level `j` are `I_{j,n} = [n 2^(-j), (n + 1) 2^(-j))`, the fibres of
`x ↦ ⌊2^j x⌋` (`Haar.dyadicInterval`; for `n ∈ ℕ` this is `Interval.dyadicIco j n`).  They
generate the dyadic σ-algebras `ℱ_j`, an increasing filtration of `ℝ` (`Haar.dyadicFiltration`),
and on `[0, 1]` with Lebesgue measure (`Haar.vol`, which is `Interval.unitVol`) the
conditional expectation `E[f | ℱ_j]` is the average of `f` over the dyadic interval of level `j`
(`Haar.condExp_dyadic_ae_eq`, from the general formula `MeasureTheory.condExp_comap_ae_eq` for
countable partitions).  The filtration scheme `MeasureTheory.Filtration.scheme` is then the
scheme of dyadic step functions (`Haar.scheme`).

The Haar function `h_{j,m} = 2^(j/2) (1_{I_{j+1,2m}} - 1_{I_{j+1,2m+1}})`
(`Haar.haarFunction`) lives on `I_{j,m}`, and the martingale differences are Haar sums of one
level (`Haar.condExpLp_succ_sub_ae_eq`):

`E[f | ℱ_{k+1}] - E[f | ℱ_k] = ∑_{m < 2^k} ⟨f, h_{k,m}⟩ h_{k,m}`.

The Haar functions of one level have disjoint supports, so
`‖∑_m c_m h_{j,m}‖_p = 2^(j(1/2 - 1/p)) ‖c‖_{ℓ_p}` (`Haar.eLpNorm_sum_haar`).  With the density
of dyadic step functions in `L_p[0, 1]`, `p < ∞` (`Haar.closure_iUnion_scheme`), the
martingale-difference characterisation of filtration schemes becomes the **Haar coefficient
characterisation** (`Haar.memApprox_iff_haarCoeff`): for `s > 0`,

`f ∈ A^s_q(L_p[0, 1], Haar)`  iff
`|∫ f| + ‖(2^(k(s + 1/2 - 1/p)) ‖(⟨f, h_{k,m}⟩)_m‖_{ℓ_p})_k‖_{ℓ_q} < ∞`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BoundedContinuousFunction

namespace Haar

/-- Lebesgue measure on `[0, 1]`, as a measure on `ℝ` (`Interval.unitVol`). -/
noncomputable abbrev vol : Measure ℝ := Interval.unitVol

/-- The index `⌊2^j x⌋` of the dyadic interval of level `j` containing `x`. -/
noncomputable def dyadicIndex (j : ℕ) (x : ℝ) : ℤ := ⌊(2 : ℝ) ^ j * x⌋

/-- The dyadic interval `I_{j,n} = [n 2^(-j), (n + 1) 2^(-j))`, the fibre of `dyadicIndex j`
over `n` (`Haar.dyadicInterval_eq_Ico`). -/
noncomputable def dyadicInterval (j : ℕ) (n : ℤ) : Set ℝ := dyadicIndex j ⁻¹' {n}

/-- `x ∈ I_{j,n}` iff `⌊2^j x⌋ = n`. -/
theorem mem_dyadicInterval {j : ℕ} {n : ℤ} {x : ℝ} :
    x ∈ dyadicInterval j n ↔ dyadicIndex j x = n := Iff.rfl

/-- The dyadic index is measurable. -/
theorem measurable_dyadicIndex (j : ℕ) : Measurable (dyadicIndex j) :=
  Int.measurable_floor.comp (measurable_const_mul _)

/-- Dyadic intervals are measurable. -/
theorem measurableSet_dyadicInterval (j : ℕ) (n : ℤ) : MeasurableSet (dyadicInterval j n) :=
  measurable_dyadicIndex j (measurableSet_singleton n)

/-- `I_{j,n} = [n 2^(-j), (n + 1) 2^(-j))`. -/
theorem dyadicInterval_eq_Ico (j : ℕ) (n : ℤ) :
    dyadicInterval j n = Ico ((n : ℝ) / 2 ^ j) ((n + 1) / 2 ^ j) := by
  ext x
  have h : (0 : ℝ) < 2 ^ j := by positivity
  rw [mem_dyadicInterval, dyadicIndex, Int.floor_eq_iff, mem_Ico, div_le_iff₀ h, lt_div_iff₀ h,
    mul_comm x]

/-- For `n ∈ ℕ` the dyadic interval `I_{j,n}` is `Interval.dyadicIco j n`. -/
theorem dyadicInterval_natCast (j n : ℕ) : dyadicInterval j n = Interval.dyadicIco j n := by
  rw [dyadicInterval_eq_Ico, Int.cast_natCast]
  rfl

/-- Dyadic intervals of the same level with different indices are disjoint. -/
theorem disjoint_dyadicInterval (j : ℕ) {n n' : ℤ} (h : n ≠ n') :
    Disjoint (dyadicInterval j n) (dyadicInterval j n') :=
  Disjoint.preimage _ (disjoint_singleton.2 h)

/-- The index of a point of `[0, 1)` is nonnegative. -/
theorem dyadicIndex_nonneg {j : ℕ} {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) : 0 ≤ dyadicIndex j x :=
  Int.floor_nonneg.2 (mul_nonneg (by positivity) hx.1)

/-- The index of a point of `[0, 1)` is `< 2^j`. -/
theorem dyadicIndex_lt {j : ℕ} {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) : dyadicIndex j x < 2 ^ j := by
  rw [dyadicIndex, Int.floor_lt]
  push_cast
  exact mul_lt_of_lt_one_right (by positivity) hx.2

/-- For `0 ≤ n < 2^j`, the dyadic interval `I_{j,n}` lies in `[0, 1)`
(`Interval.dyadicIco_subset`). -/
theorem dyadicInterval_subset {j : ℕ} {n : ℤ} (h0 : 0 ≤ n) (h1 : n < 2 ^ j) :
    dyadicInterval j n ⊆ Ico 0 1 := by
  lift n to ℕ using h0
  rw [dyadicInterval_natCast]
  exact Interval.dyadicIco_subset (by exact_mod_cast h1)

/-- `|I_{j,n}| = 2^(-j)` for `0 ≤ n < 2^j`. -/
theorem vol_real_dyadicInterval {j : ℕ} {n : ℤ} (h0 : 0 ≤ n) (h1 : n < 2 ^ j) :
    vol.real (dyadicInterval j n) = ((2 : ℝ) ^ j)⁻¹ := by
  rw [measureReal_def, Measure.restrict_apply (measurableSet_dyadicInterval j n),
    inter_eq_left.2 ((dyadicInterval_subset h0 h1).trans Ico_subset_Icc_self),
    dyadicInterval_eq_Ico, Real.volume_Ico,
    show ((n : ℝ) + 1) / 2 ^ j - n / 2 ^ j = ((2 : ℝ) ^ j)⁻¹ by
      rw [← sub_div, add_sub_cancel_left, one_div],
    ENNReal.toReal_ofReal (by positivity)]

/-- `|I_{j,n}| = 2^(-j)` for `0 ≤ n < 2^j`, in `ℝ≥0∞`. -/
theorem vol_dyadicInterval {j : ℕ} {n : ℤ} (h0 : 0 ≤ n) (h1 : n < 2 ^ j) :
    vol (dyadicInterval j n) = ENNReal.dyadicWeight (-1) j := by
  have h := vol_real_dyadicInterval h0 h1
  rw [measureReal_def] at h
  rw [← ENNReal.ofReal_toReal (measure_ne_top vol _), h, ENNReal.dyadicWeight_neg,
    ENNReal.dyadicWeight_eq_pow, ENNReal.rpow_one, ENNReal.ofReal_inv_of_pos (by positivity),
    ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

/-- `⌊2^j x⌋ = ⌊2^(j+1) x⌋ / 2`: the dyadic interval of level `j` containing `x` is the parent of
the one of level `j + 1`. -/
theorem dyadicIndex_succ_div (j : ℕ) (x : ℝ) : dyadicIndex (j + 1) x / 2 = dyadicIndex j x := by
  have h := Int.floor_div_natCast ((2 : ℝ) ^ (j + 1) * x) 2
  rw [show (2 : ℝ) ^ (j + 1) * x / ((2 : ℕ) : ℝ) = 2 ^ j * x by push_cast; ring] at h
  rw [dyadicIndex, dyadicIndex, h]
  norm_num

/-- `I_{j,n} = I_{j+1,2n} ∪ I_{j+1,2n+1}`. -/
theorem dyadicInterval_eq_union (j : ℕ) (n : ℤ) :
    dyadicInterval j n = dyadicInterval (j + 1) (2 * n) ∪ dyadicInterval (j + 1) (2 * n + 1) := by
  ext x
  simp only [mem_union, mem_dyadicInterval, ← dyadicIndex_succ_div j x]
  omega

/-- The dyadic σ-algebra `ℱ_j`, generated by the dyadic intervals of level `j`. -/
@[instance_reducible]
noncomputable def dyadicSigma (j : ℕ) : MeasurableSpace ℝ :=
  MeasurableSpace.comap (dyadicIndex j) ⊤

/-- The dyadic σ-algebras increase. -/
theorem dyadicSigma_mono : Monotone dyadicSigma := by
  refine monotone_nat_of_le_succ fun j => ?_
  have h : dyadicIndex j = (fun n : ℤ => n / 2) ∘ dyadicIndex (j + 1) :=
    funext fun x => (dyadicIndex_succ_div j x).symm
  change MeasurableSpace.comap (dyadicIndex j) ⊤ ≤ MeasurableSpace.comap (dyadicIndex (j + 1)) ⊤
  rw [h, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono le_top

/-- The **dyadic filtration** `ℱ_0 ≤ ℱ_1 ≤ ⋯` of `ℝ`. -/
noncomputable def dyadicFiltration : Filtration ℕ Real.measurableSpace where
  seq := dyadicSigma
  mono' := dyadicSigma_mono
  le' j := comap_top_le (φ := dyadicIndex j) (measurableSet_dyadicInterval j)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (p) in
/-- The **Haar scheme** in `L_p[0, 1]`: the approximants of complexity `2^j` are the step
functions on the dyadic intervals of level `j`. -/
noncomputable abbrev scheme : ApproximationScheme (Lp ℂ p vol) := dyadicFiltration.scheme p vol

/-- **Conditional expectation onto `ℱ_j`**: `E[f | ℱ_j](x) = 2^j ∫_{I_{j,⌊2^j x⌋}} f`, the
average of `f` over the dyadic interval of level `j` containing `x`. -/
theorem condExp_dyadic_ae_eq (j : ℕ) {f : ℝ → ℂ} (hf : Integrable f vol) :
    vol[f | dyadicFiltration j] =ᵐ[vol]
      fun x => ((2 : ℝ) ^ j) • ∫ y in dyadicInterval j (dyadicIndex j x), f y ∂vol := by
  change vol[f | MeasurableSpace.comap (dyadicIndex j) ⊤] =ᵐ[vol] _
  filter_upwards [condExp_comap_ae_eq (φ := dyadicIndex j) (measurableSet_dyadicInterval j) hf,
    Interval.ae_mem_Ico_unitVol] with x hx hx01
  rw [hx, show dyadicIndex j ⁻¹' {dyadicIndex j x} = dyadicInterval j (dyadicIndex j x) from rfl,
    vol_real_dyadicInterval (dyadicIndex_nonneg hx01) (dyadicIndex_lt hx01), inv_inv]

/-- `E[f | ℱ_j]` on `L_p[0, 1]` is the average over the dyadic interval of level `j`. -/
theorem condExpLp_dyadic_ae_eq (j : ℕ) (f : Lp ℂ p vol) :
    Lp.condExpLp (dyadicFiltration j) f =ᵐ[vol]
      fun x => ((2 : ℝ) ^ j) • ∫ y in dyadicInterval j (dyadicIndex j x), f y ∂vol :=
  (Lp.coeFn_condExpLp f).trans (condExp_dyadic_ae_eq j ((Lp.memLp f).integrable Fact.out))

/-- `E[f | ℱ_0] = ∫_0^1 f`, a constant. -/
theorem condExpLp_zero_ae_eq (f : Lp ℂ p vol) :
    Lp.condExpLp (dyadicFiltration 0) f =ᵐ[vol] fun _ => ∫ x, f x ∂vol := by
  filter_upwards [condExpLp_dyadic_ae_eq 0 f, Interval.ae_mem_Ico_unitVol] with x h hx
  have h0 : dyadicIndex 0 x = 0 := by
    have h1 := dyadicIndex_nonneg (j := 0) hx
    have h2 := dyadicIndex_lt (j := 0) hx
    rw [pow_zero] at h2
    omega
  rw [h, pow_zero, one_smul, h0,
    show dyadicInterval 0 0 = Ico 0 1 by rw [dyadicInterval_eq_Ico]; norm_num,
    Measure.restrict_eq_self_of_ae_mem Interval.ae_mem_Ico_unitVol]

/-- `‖E[f | ℱ_0]‖_p = |∫_0^1 f|`. -/
theorem enorm_condExpLp_zero (f : Lp ℂ p vol) :
    ‖Lp.condExpLp (dyadicFiltration 0) f‖ₑ = ‖∫ x, f x ∂vol‖ₑ := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  rw [Lp.eNorm_def, eLpNorm_congr_ae (condExpLp_zero_ae_eq f),
    eLpNorm_const _ hp0 (IsProbabilityMeasure.ne_zero vol), measure_univ, ENNReal.one_rpow,
    mul_one]

/-- A sum over the positions of level `j` whose terms vanish away from the index of a point
`x ∈ [0, 1)` is the term at that index. -/
theorem sum_fin_eq_of_ne {M : Type*} [AddCommMonoid M] {j : ℕ} {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1)
    (G : ℤ → M) (hG : ∀ m, m ≠ dyadicIndex j x → G m = 0) :
    ∑ m : Fin (2 ^ j), G ((m : ℕ) : ℤ) = G (dyadicIndex j x) := by
  have h0 := dyadicIndex_nonneg (j := j) hx
  have h1 : dyadicIndex j x < ((2 ^ j : ℕ) : ℤ) := by exact_mod_cast dyadicIndex_lt (j := j) hx
  let i : Fin (2 ^ j) := ⟨(dyadicIndex j x).toNat, by omega⟩
  have hi : (((i : ℕ) : ℤ)) = dyadicIndex j x := Int.toNat_of_nonneg h0
  rw [Finset.sum_eq_single i (fun b _ hb => hG _ fun h => hb (Fin.ext (by omega)))
    (fun h => absurd (Finset.mem_univ i) h), hi]

/-- The **Haar function** `h_{j,m} = 2^(j/2) (1_{I_{j+1,2m}} - 1_{I_{j+1,2m+1}})`, supported on
`I_{j,m}` and normalised in `L_2`. -/
noncomputable def haarFunction (j : ℕ) (m : ℤ) (x : ℝ) : ℝ :=
  if dyadicIndex (j + 1) x = 2 * m then (2 : ℝ) ^ ((j : ℝ) / 2)
  else if dyadicIndex (j + 1) x = 2 * m + 1 then -(2 : ℝ) ^ ((j : ℝ) / 2) else 0

/-- Haar functions are measurable: they are functions of `⌊2^(j+1) x⌋`. -/
theorem measurable_haarFunction (j : ℕ) (m : ℤ) : Measurable (haarFunction j m) :=
  (measurable_of_countable (fun n : ℤ => if n = 2 * m then (2 : ℝ) ^ ((j : ℝ) / 2)
    else if n = 2 * m + 1 then -(2 : ℝ) ^ ((j : ℝ) / 2) else 0)).comp
    (measurable_dyadicIndex (j + 1))

/-- `h_{j,m}` vanishes outside `I_{j,m}`. -/
theorem haarFunction_eq_zero {j : ℕ} {m : ℤ} {x : ℝ} (hx : dyadicIndex j x ≠ m) :
    haarFunction j m x = 0 := by
  rw [← dyadicIndex_succ_div] at hx
  have h1 : dyadicIndex (j + 1) x ≠ 2 * m := by omega
  have h2 : dyadicIndex (j + 1) x ≠ 2 * m + 1 := by omega
  simp [haarFunction, h1, h2]

/-- `|h_{j,m}| = 2^(j/2)` on `I_{j,m}`. -/
theorem abs_haarFunction {j : ℕ} {m : ℤ} {x : ℝ} (hx : dyadicIndex j x = m) :
    |haarFunction j m x| = (2 : ℝ) ^ ((j : ℝ) / 2) := by
  rw [← dyadicIndex_succ_div] at hx
  unfold haarFunction
  split_ifs with h1 h2
  · exact abs_of_pos (by positivity)
  · rw [abs_neg]; exact abs_of_pos (by positivity)
  · omega

/-- Haar functions are bounded: `|h_{j,m}| ≤ 2^(j/2)`. -/
theorem abs_haarFunction_le (j : ℕ) (m : ℤ) (x : ℝ) :
    |haarFunction j m x| ≤ (2 : ℝ) ^ ((j : ℝ) / 2) := by
  by_cases hx : dyadicIndex j x = m
  · exact (abs_haarFunction hx).le
  · rw [haarFunction_eq_zero hx, abs_zero]
    positivity

/-- `h_{j,m} f = 2^(j/2) (1_{I_{j+1,2m}} f - 1_{I_{j+1,2m+1}} f)` pointwise. -/
theorem haarFunction_mul (j : ℕ) (m : ℤ) (f : ℝ → ℂ) (x : ℝ) :
    (haarFunction j m x : ℂ) * f x = (((2 : ℝ) ^ ((j : ℝ) / 2) : ℝ) : ℂ) *
      ((dyadicInterval (j + 1) (2 * m)).indicator f x -
        (dyadicInterval (j + 1) (2 * m + 1)).indicator f x) := by
  unfold haarFunction
  split_ifs with h1 h2
  · have h2' : x ∉ dyadicInterval (j + 1) (2 * m + 1) := by rw [mem_dyadicInterval, h1]; omega
    rw [indicator_of_mem (mem_dyadicInterval.2 h1), indicator_of_notMem h2', sub_zero]
  · rw [indicator_of_notMem (mem_dyadicInterval.not.2 h1),
      indicator_of_mem (mem_dyadicInterval.2 h2), zero_sub, Complex.ofReal_neg]
    ring
  · rw [indicator_of_notMem (mem_dyadicInterval.not.2 h1),
      indicator_of_notMem (mem_dyadicInterval.not.2 h2)]
    simp

/-- The **Haar coefficient** `⟨f, h_{j,m}⟩ = ∫ h_{j,m} f` of `f` on `[0, 1]`. -/
noncomputable def haarCoeff (f : ℝ → ℂ) (j : ℕ) (m : ℤ) : ℂ :=
  ∫ x, (haarFunction j m x : ℂ) * f x ∂vol

/-- `⟨f, h_{j,m}⟩ = 2^(j/2) (∫_{I_{j+1,2m}} f - ∫_{I_{j+1,2m+1}} f)`. -/
theorem haarCoeff_eq {f : ℝ → ℂ} (hf : Integrable f vol) (j : ℕ) (m : ℤ) :
    haarCoeff f j m = (((2 : ℝ) ^ ((j : ℝ) / 2) : ℝ) : ℂ) *
      (∫ x in dyadicInterval (j + 1) (2 * m), f x ∂vol -
        ∫ x in dyadicInterval (j + 1) (2 * m + 1), f x ∂vol) := by
  simp_rw [haarCoeff, haarFunction_mul]
  rw [integral_const_mul, integral_sub (hf.indicator (measurableSet_dyadicInterval _ _))
      (hf.indicator (measurableSet_dyadicInterval _ _)),
    integral_indicator (measurableSet_dyadicInterval _ _),
    integral_indicator (measurableSet_dyadicInterval _ _)]

/-- Functions that agree almost everywhere have the same Haar coefficients. -/
theorem haarCoeff_congr_ae {f g : ℝ → ℂ} (h : f =ᵐ[vol] g) (j : ℕ) (m : ℤ) :
    haarCoeff f j m = haarCoeff g j m := by
  unfold haarCoeff
  exact integral_congr_ae (h.mono fun x hx => by simp only [hx])

/-- The integral over `I_{j,n}` is the sum of the integrals over its two halves. -/
theorem setIntegral_dyadicInterval {f : ℝ → ℂ} (hf : Integrable f vol) (j : ℕ) (n : ℤ) :
    ∫ x in dyadicInterval j n, f x ∂vol = ∫ x in dyadicInterval (j + 1) (2 * n), f x ∂vol +
      ∫ x in dyadicInterval (j + 1) (2 * n + 1), f x ∂vol := by
  rw [dyadicInterval_eq_union j n]
  exact setIntegral_union (disjoint_dyadicInterval _ (by omega))
    (measurableSet_dyadicInterval _ _) hf.integrableOn hf.integrableOn

/-- **Martingale differences are Haar sums**:
`E[f | ℱ_{k+1}] - E[f | ℱ_k] = ∑_{m < 2^k} ⟨f, h_{k,m}⟩ h_{k,m}`. -/
theorem condExpLp_succ_sub_ae_eq (k : ℕ) (f : Lp ℂ p vol) :
    ⇑(Lp.condExpLp (dyadicFiltration (k + 1)) f - Lp.condExpLp (dyadicFiltration k) f) =ᵐ[vol]
      fun x => ∑ m : Fin (2 ^ k), haarCoeff f k ((m : ℕ) : ℤ) *
        (haarFunction k ((m : ℕ) : ℤ) x : ℂ) := by
  have hf := (Lp.memLp f).integrable (Fact.out : 1 ≤ p)
  filter_upwards [Lp.coeFn_sub (Lp.condExpLp (dyadicFiltration (k + 1)) f)
      (Lp.condExpLp (dyadicFiltration k) f), condExpLp_dyadic_ae_eq (k + 1) f,
    condExpLp_dyadic_ae_eq k f, Interval.ae_mem_Ico_unitVol] with x h1 h2 h3 hx
  rw [h1, Pi.sub_apply, h2, h3,
    sum_fin_eq_of_ne hx (fun m => haarCoeff f k m * (haarFunction k m x : ℂ))
      fun m hm => by rw [haarFunction_eq_zero (Ne.symm hm), Complex.ofReal_zero, mul_zero],
    haarCoeff_eq hf, setIntegral_dyadicInterval hf k (dyadicIndex k x)]
  have hc := ofReal_two_rpow_half_mul_self k
  have hn := dyadicIndex_succ_div k x
  rcases (by omega : dyadicIndex (k + 1) x = 2 * dyadicIndex k x ∨
      dyadicIndex (k + 1) x = 2 * dyadicIndex k x + 1) with h | h
  · have hh : haarFunction k (dyadicIndex k x) x = (2 : ℝ) ^ ((k : ℝ) / 2) := by
      simp [haarFunction, h]
    rw [hh, h]
    simp only [Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_ofNat]
    linear_combination (∫ y in dyadicInterval (k + 1) (2 * dyadicIndex k x + 1), f y ∂vol -
      ∫ y in dyadicInterval (k + 1) (2 * dyadicIndex k x), f y ∂vol) * hc
  · have hh : haarFunction k (dyadicIndex k x) x = -(2 : ℝ) ^ ((k : ℝ) / 2) := by
      simp [haarFunction, h]
    rw [hh, h]
    simp only [Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_ofNat, Complex.ofReal_neg]
    linear_combination (∫ y in dyadicInterval (k + 1) (2 * dyadicIndex k x), f y ∂vol -
      ∫ y in dyadicInterval (k + 1) (2 * dyadicIndex k x + 1), f y ∂vol) * hc

/-- `|h_{j,m}| = 2^(j/2)` on `I_{j,m}`, as a dyadic weight in `ℝ≥0∞`. -/
theorem enorm_haarFunction {j : ℕ} {m : ℤ} {x : ℝ} (hx : dyadicIndex j x = m) :
    ‖(haarFunction j m x : ℂ)‖ₑ = ENNReal.dyadicWeight (1 / 2) j := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_haarFunction hx,
    ← ENNReal.ofReal_rpow_of_pos (by norm_num), ENNReal.ofReal_ofNat, ENNReal.dyadicWeight]
  congr 1
  ring

/-- **Level-wise norm of Haar sums**: for `1 ≤ p < ∞`,
`‖∑_{m < 2^j} c_m h_{j,m}‖_p = 2^(j(1/2 - 1/p)) ‖c‖_{ℓ_p}`, since the Haar functions of one level
have disjoint supports of measure `2^(-j)` and modulus `2^(j/2)` there. -/
theorem eLpNorm_sum_haar (hp : p ≠ ∞) (j : ℕ) (c : Fin (2 ^ j) → ℂ) :
    eLpNorm (fun x => ∑ m : Fin (2 ^ j), c m * (haarFunction j ((m : ℕ) : ℤ) x : ℂ)) p vol =
      ENNReal.dyadicWeight (1 / 2 - 1 / p.toReal) j * ENNReal.lqNorm p (fun m => ‖c m‖ₑ) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  set r := p.toReal
  set C : ℤ → ℂ := fun m => if h : 0 ≤ m ∧ m < ((2 ^ j : ℕ) : ℤ) then c ⟨m.toNat, by omega⟩ else 0
  have hC : ∀ m : Fin (2 ^ j), C ((m : ℕ) : ℤ) = c m := fun m => by
    have h1 : ((m : ℕ) : ℤ) < ((2 ^ j : ℕ) : ℤ) := by exact_mod_cast m.isLt
    simp only [C, Int.natCast_nonneg, h1, and_self, ↓reduceDIte, Int.toNat_natCast]
  have hpt : ∀ᵐ x ∂vol, ‖∑ m : Fin (2 ^ j), c m * (haarFunction j ((m : ℕ) : ℤ) x : ℂ)‖ₑ ^ r =
      ∑ m : Fin (2 ^ j), (dyadicInterval j ((m : ℕ) : ℤ)).indicator
        (fun _ => ‖c m‖ₑ ^ r * ENNReal.dyadicWeight (1 / 2 * r) j) x := by
    filter_upwards [Interval.ae_mem_Ico_unitVol] with x hx
    simp_rw [← hC]
    rw [sum_fin_eq_of_ne hx (fun m => C m * (haarFunction j m x : ℂ))
        fun m hm => by rw [haarFunction_eq_zero (Ne.symm hm), Complex.ofReal_zero, mul_zero],
      sum_fin_eq_of_ne hx (fun m => (dyadicInterval j m).indicator
        (fun _ => ‖C m‖ₑ ^ r * ENNReal.dyadicWeight (1 / 2 * r) j) x)
        fun m hm => indicator_of_notMem (fun h => hm (mem_dyadicInterval.1 h).symm) _,
      indicator_of_mem (mem_dyadicInterval.2 rfl), eNorm_mul, ENNReal.mul_rpow_of_nonneg _ _ hr.le,
      enorm_haarFunction rfl, ENNReal.dyadicWeight_rpow]
  have hmeas : AEStronglyMeasurable
      (fun x => ∑ m : Fin (2 ^ j), c m * (haarFunction j ((m : ℕ) : ℤ) x : ℂ)) vol :=
    (Finset.measurable_sum _ fun m _ => measurable_const.mul
      (Complex.measurable_ofReal.comp (measurable_haarFunction _ _))).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp hmeas, lintegral_congr_ae hpt,
    lintegral_finsetSum _ fun m _ => measurable_const.indicator (measurableSet_dyadicInterval _ _)]
  simp_rw [lintegral_indicator_const (measurableSet_dyadicInterval _ _)]
  have hvol : ∀ m : Fin (2 ^ j), vol (dyadicInterval j ((m : ℕ) : ℤ)) =
      ENNReal.dyadicWeight (-1) j := fun m =>
    vol_dyadicInterval (Int.natCast_nonneg _) (by exact_mod_cast m.isLt)
  simp_rw [hvol, mul_assoc, ← Finset.sum_mul, mul_comm (∑ m : Fin (2 ^ j), ‖c m‖ₑ ^ r)]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.dyadicWeight_add,
    ENNReal.dyadicWeight_rpow]
  simp only [ENNReal.lqNorm_eq_sum hp0 hp]
  rw [show p.toReal = r from rfl]
  congr 2
  field_simp
  ring

/-- The dyadic step function `x ↦ g(⌊2^j x⌋ 2^(-j))` of `g`: the value of `g` at the left end
point of the dyadic interval of level `j` containing `x`. -/
noncomputable def stepFun (g : ℝ → ℂ) (j : ℕ) (x : ℝ) : ℂ := g ((dyadicIndex j x : ℝ) / 2 ^ j)

/-- The step function of level `j` is `ℱ_j`-measurable. -/
theorem stronglyMeasurable_stepFun (g : ℝ → ℂ) (j : ℕ) :
    StronglyMeasurable[dyadicFiltration j] (stepFun g j) :=
  ((measurable_from_top (f := fun n : ℤ => g ((n : ℝ) / 2 ^ j))).comp
    (comap_measurable (m := ⊤) (dyadicIndex j))).stronglyMeasurable

/-- A uniformly continuous `g` on `[0, 1]` is uniformly close to its step functions: given
`ε > 0` there is a level `j` with `|g(x) - g(⌊2^j x⌋ 2^(-j))| ≤ ε` on `[0, 1)`. -/
theorem exists_norm_sub_stepFun_le {g : ℝ → ℂ} (hg : Continuous g) {ε : ℝ} (hε : 0 < ε) :
    ∃ j : ℕ, ∀ x ∈ Ico (0 : ℝ) 1, ‖g x - stepFun g j x‖ ≤ ε := by
  obtain ⟨δ, hδ, hgδ⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hg.continuousOn) ε hε
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨j, fun x hx => ?_⟩
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  have hmem : x ∈ dyadicInterval j (dyadicIndex j x) := rfl
  rw [dyadicInterval_eq_Ico, mem_Ico] at hmem
  have h0 : (0 : ℝ) ≤ dyadicIndex j x := by exact_mod_cast dyadicIndex_nonneg hx
  have h1 : (dyadicIndex j x : ℝ) + 1 ≤ 2 ^ j := by
    exact_mod_cast Int.add_one_le_iff.2 (dyadicIndex_lt hx)
  have hy : (dyadicIndex j x : ℝ) / 2 ^ j ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg h0 h2.le, (div_le_one h2).2 (by linarith)⟩
  have hdist : dist x ((dyadicIndex j x : ℝ) / 2 ^ j) < δ := by
    rw [Real.dist_eq, abs_of_nonneg (by linarith [hmem.1])]
    calc x - (dyadicIndex j x : ℝ) / 2 ^ j
        < ((dyadicIndex j x : ℝ) + 1) / 2 ^ j - (dyadicIndex j x : ℝ) / 2 ^ j := by
          linarith [hmem.2]
      _ = (1 / 2) ^ j := by rw [← sub_div, add_sub_cancel_left, one_div_pow]
      _ < δ := hj
  rw [← dist_eq_norm]
  exact (hgδ x (Ico_subset_Icc_self hx) _ hy hdist).le

/-- **Bounded continuous functions are limits of dyadic step functions** in `L_p[0, 1]`, even
uniformly on `[0, 1)`: they lie in the closure of the Haar approximants. -/
theorem toLp_mem_closure (g : ℝ →ᵇ ℂ) :
    BoundedContinuousFunction.toLp (E := ℂ) p vol ℝ g ∈ closure (⋃ n, scheme p n) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨j, hj⟩ := exists_norm_sub_stepFun_le g.continuous (half_pos hε)
  have hsm := stronglyMeasurable_stepFun g j
  have hmeas : AEStronglyMeasurable (stepFun g j) vol :=
    (hsm.mono (dyadicFiltration.le j)).aestronglyMeasurable
  have hmem : MemLp (stepFun g j) p vol :=
    MemLp.of_bound hmeas ‖g‖ (ae_of_all _ fun x => g.norm_coe_le_norm _)
  refine ⟨hmem.toLp _, mem_iUnion.2 ⟨2 ^ j, ?_⟩, ?_⟩
  · rw [dyadicFiltration.mem_scheme (pow_ne_zero j two_ne_zero), Nat.log_pow Nat.one_lt_two,
      mem_lpMeas_iff_aestronglyMeasurable]
    exact hsm.aestronglyMeasurable.congr (MemLp.coeFn_toLp hmem).symm
  · rw [dist_eq_norm, Lp.norm_def, eLpNorm_congr_ae ((Lp.coeFn_sub _ _).trans
      ((BoundedContinuousFunction.coeFn_toLp p vol ℝ g).sub (MemLp.coeFn_toLp hmem)))]
    have hb := eLpNorm_le_of_ae_bound (p := p) (g.continuous.aestronglyMeasurable.sub hmeas)
      (C := ε / 2) (by filter_upwards [Interval.ae_mem_Ico_unitVol] with x hx using hj x hx)
    rw [measure_univ, ENNReal.one_rpow, one_mul] at hb
    calc (eLpNorm (⇑g - stepFun g j) p vol).toReal ≤ (ENNReal.ofReal (ε / 2)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
      _ = ε / 2 := ENNReal.toReal_ofReal (by positivity)
      _ < ε := half_lt_self hε

/-- **The Haar approximants are dense** in `L_p[0, 1]` for `1 ≤ p < ∞`. -/
theorem closure_iUnion_scheme (hp : p ≠ ∞) : closure (⋃ n, scheme p n) = univ := by
  have hsub : range (BoundedContinuousFunction.toLp (E := ℂ) p vol ℝ) ⊆
      closure (⋃ n, scheme p n) := by
    rintro _ ⟨g, rfl⟩
    exact toLp_mem_closure g
  have h := closure_minimal hsub isClosed_closure
  rw [(BoundedContinuousFunction.toLp_denseRange ℂ vol ℝ hp).closure_range] at h
  exact eq_univ_of_univ_subset h

/-- **Haar coefficient characterisation**: for `1 ≤ p < ∞`, `s > 0` and `1 ≤ q ≤ ∞`, `f` lies in
the approximation space `A^s_q(L_p[0, 1], Haar)` iff
`|∫_0^1 f| + ‖(2^(k(s + 1/2 - 1/p)) ‖(⟨f, h_{k,m}⟩)_{m < 2^k}‖_{ℓ_p})_k‖_{ℓ_q} < ∞`.

For `0 < s < 1/p` this space is the classical Besov space `B^s_{p,q}[0, 1]`; for larger `s` it is
strictly smaller, since the Haar functions themselves are discontinuous.  That comparison is not
formalised here. -/
theorem memApprox_iff_haarCoeff (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (f : Lp ℂ p vol) :
    (scheme p).MemApprox s q f ↔ ‖∫ x, f x ∂vol‖ₑ + ENNReal.lqNorm q (fun k =>
      ENNReal.dyadicWeight (s + (1 / 2 - 1 / p.toReal)) k *
        ENNReal.lqNorm p (fun m : Fin (2 ^ k) => ‖haarCoeff f k ((m : ℕ) : ℤ)‖ₑ)) < ∞ := by
  have h : ∀ k, ‖Lp.condExpLp (dyadicFiltration (k + 1)) f -
      Lp.condExpLp (dyadicFiltration k) f‖ₑ = ENNReal.dyadicWeight (1 / 2 - 1 / p.toReal) k *
        ENNReal.lqNorm p (fun m : Fin (2 ^ k) => ‖haarCoeff f k ((m : ℕ) : ℤ)‖ₑ) :=
    fun k => by
      rw [Lp.eNorm_def, eLpNorm_congr_ae (condExpLp_succ_sub_ae_eq k f)]
      exact eLpNorm_sum_haar hp k _
  rw [dyadicFiltration.memApprox_iff_martingale (closure_iUnion_scheme hp) hs hq,
    enorm_condExpLp_zero]
  simp_rw [h, ← mul_assoc, ← ENNReal.dyadicWeight_add]

end Haar
