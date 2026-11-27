/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Interval.Modulus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Function.Floor

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Periodic functions and the periodic modulus of smoothness

A function `f` on `[0, 1)` extends to the `1`-periodic function `fTilde(x) = f(x - ⌊x⌋)`
(`Interval.perExt`). This identifies functions on the circle `𝕋 = ℝ/ℤ` with functions on
`[0, 1)`, and `L_p(𝕋)` with `L_p[0, 1]`; working with `fTilde` keeps everything on the real line.

The **periodic modulus of smoothness**
`ω_r^per(f, t)_p = sup_{0 ≤ h ≤ t} ‖Δ_h^r fTilde‖_{L_p[0, 1]}` (`Interval.perModulus`)
differs from the modulus on `[0, 1]` in that its differences wrap around and compare values near
`1` with values near `0`. It depends only on the class of `f` in `L_p[0, 1]`
(`Interval.perModulus_congr_ae`), since `fTilde` changes only on the integer translates of a
null set
(`Interval.perExt_ae_eq`), and it dominates the modulus on the interval
(`Interval.modulus_le_perModulus`). The `L_p` norm of a periodic function over a unit interval
does not depend on the interval (`Interval.lintegral_Icc_periodic`), from Mathlib's integration
over the circle (`UnitAddCircle.lintegral_preimage`).
-/

@[expose] public section

open MeasureTheory Set
open Rd (higherDiff measurable_higherDiff)
open scoped ENNReal

namespace Interval

/-- The **periodic extension** `fTilde(x) = f(x - ⌊x⌋)` of a function `f` on `[0, 1)`. -/
noncomputable def perExt (f : ℝ → ℂ) (x : ℝ) : ℂ := f (Int.fract x)

/-- The periodic extension has period `1`. -/
theorem perExt_periodic (f : ℝ → ℂ) : Function.Periodic (perExt f) 1 := fun x => by
  simp [perExt]

/-- The periodic extension agrees with `f` on `[0, 1)`. -/
theorem perExt_of_mem (f : ℝ → ℂ) {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) : perExt f x = f x := by
  rw [perExt, Int.fract_eq_self.2 hx]

/-- The periodic extension of a measurable function is measurable. -/
theorem measurable_perExt {f : ℝ → ℂ} (hf : Measurable f) : Measurable (perExt f) :=
  hf.comp measurable_fract

/-- The periodic extension is additive. -/
theorem perExt_add (f g : ℝ → ℂ) : perExt (f + g) = perExt f + perExt g := rfl

/-- A `1`-periodic function is its own periodic extension. -/
theorem perExt_eq_of_periodic {f : ℝ → ℂ} (hf : Function.Periodic f 1) : perExt f = f := by
  funext x
  rw [perExt, ← Int.self_sub_floor, ← mul_one ((⌊x⌋ : ℤ) : ℝ), hf.sub_int_mul_eq]

/-- The differences of a `1`-periodic function are `1`-periodic. -/
theorem higherDiff_periodic {f : ℝ → ℂ} (hf : Function.Periodic f 1) (r : ℕ) (h : ℝ) :
    Function.Periodic (higherDiff r h f) 1 := fun x => by
  rw [higherDiff_apply, higherDiff_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show x + 1 + k * h = x + k * h + 1 by ring, hf]

/-- **Periodic extensions of almost equal functions**: if `f = g` almost everywhere on `[0, 1]`,
then `fTilde = gTilde` almost everywhere on `ℝ`, since `{fTilde ≠ gTilde}` is the union of the
integer translates
of `{f ≠ g} ∩ [0, 1)`. -/
theorem perExt_ae_eq {f g : ℝ → ℂ} (hfg : f =ᵐ[volume.restrict (Icc 0 1)] g) :
    perExt f =ᵐ[volume] perExt g := by
  have h1 : ∀ᵐ x ∂volume.restrict (Ico (0 : ℝ) 1), f x = g x :=
    ae_restrict_of_ae_restrict_of_subset Ico_subset_Icc_self hfg
  rw [ae_restrict_iff' measurableSet_Ico, ae_iff] at h1
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (t := ⋃ n : ℤ,
    (fun x => x + (-(n : ℝ))) ⁻¹' {x | ¬(x ∈ Ico (0 : ℝ) 1 → f x = g x)}) ?_
    (measure_iUnion_null fun n => by rw [measure_preimage_add_right]; exact h1)
  intro x hx
  refine mem_iUnion.2 ⟨⌊x⌋, ?_⟩
  simp only [mem_preimage, mem_ofPred_eq, ← sub_eq_add_neg, Int.self_sub_floor]
  exact fun h => hx (h ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩)

/-- Differences of periodic extensions of almost equal functions agree almost everywhere. -/
theorem higherDiff_perExt_ae_eq {f g : ℝ → ℂ} (hfg : f =ᵐ[volume.restrict (Icc 0 1)] g)
    (r : ℕ) (h : ℝ) : higherDiff r h (perExt f) =ᵐ[volume] higherDiff r h (perExt g) :=
  Rd.higherDiff_congr_ae (perExt_ae_eq hfg) r h

/-- **Integrals of periodic functions over unit intervals**: for `1`-periodic `G`,
`∫_{[c, c + 1]} G = ∫_{[0, 1]} G`, both being the integral over the circle. -/
theorem lintegral_Icc_periodic {G : ℝ → ℝ≥0∞} (hG : Function.Periodic G 1) (c : ℝ) :
    ∫⁻ x in Icc c (c + 1), G x = ∫⁻ x in Icc 0 1, G x := by
  have key : ∀ t : ℝ, ∫⁻ x in Icc t (t + 1), G x = ∫⁻ y : UnitAddCircle, hG.lift y := fun t => by
    rw [← setLIntegral_congr Ioc_ae_eq_Icc, ← UnitAddCircle.lintegral_preimage t]
    simp only [Function.Periodic.lift_coe]
  rw [key c, ← key 0, zero_add]

/-- **Integrals of periodic functions over `n` periods**: `∫_{[0, n]} G ≤ n ∫_{[0, 1]} G` for
`1`-periodic `G`, since `[0, n]` is covered by the unit intervals `[i, i + 1]`, `i < n`. -/
theorem lintegral_Icc_nat_le {G : ℝ → ℝ≥0∞} (hG : Function.Periodic G 1) (n : ℕ) :
    ∫⁻ x in Icc 0 (n : ℝ), G x ≤ n * ∫⁻ x in Icc 0 1, G x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsub : Icc (0 : ℝ) ((n + 1 : ℕ) : ℝ) ⊆ Icc 0 (n : ℝ) ∪ Icc (n : ℝ) (n + 1) := by
      intro x hx
      push_cast at hx
      rcases le_or_gt x n with h | h
      · exact Or.inl ⟨hx.1, h⟩
      · exact Or.inr ⟨h.le, hx.2⟩
    calc ∫⁻ x in Icc 0 ((n + 1 : ℕ) : ℝ), G x
        ≤ ∫⁻ x in Icc 0 (n : ℝ) ∪ Icc (n : ℝ) (n + 1), G x := lintegral_mono_set hsub
      _ ≤ (∫⁻ x in Icc 0 (n : ℝ), G x) + ∫⁻ x in Icc (n : ℝ) (n + 1), G x :=
          lintegral_union_le _ _ _
      _ ≤ n * (∫⁻ x in Icc 0 1, G x) + ∫⁻ x in Icc 0 1, G x :=
          add_le_add ih (le_of_eq (lintegral_Icc_periodic hG n))
      _ = ((n + 1 : ℕ) : ℝ≥0∞) * ∫⁻ x in Icc 0 1, G x := by push_cast; ring

/-- The **periodic modulus of smoothness**
`ω_r^per(f, t)_p = sup_{0 ≤ h ≤ t} ‖Δ_h^r fTilde‖_{L_p[0, 1]}` of the periodic extension
`fTilde`. -/
noncomputable def perModulus (r : ℕ) (p : ℝ≥0∞) (f : ℝ → ℂ) (t : ℝ) : ℝ≥0∞ :=
  ⨆ (h : ℝ) (_ : h ∈ Icc 0 t), eLpNorm (higherDiff r h (perExt f)) p (volume.restrict (Icc 0 1))

/-- `‖Δ_h^r fTilde‖_{L_p[0, 1]} ≤ ω_r^per(f, t)` for `0 ≤ h ≤ t`. -/
theorem eLpNorm_higherDiff_le_perModulus {r : ℕ} {p : ℝ≥0∞} {f : ℝ → ℂ} {t h : ℝ}
    (hh : h ∈ Icc 0 t) :
    eLpNorm (higherDiff r h (perExt f)) p (volume.restrict (Icc 0 1)) ≤ perModulus r p f t :=
  le_iSup₂ (f := fun (h : ℝ) (_ : h ∈ Icc 0 t) =>
    eLpNorm (higherDiff r h (perExt f)) p (volume.restrict (Icc 0 1))) h hh

/-- The periodic modulus increases in `t`. -/
theorem perModulus_mono (r : ℕ) (p : ℝ≥0∞) (f : ℝ → ℂ) : Monotone (perModulus r p f) :=
  fun _ _ hst => iSup₂_le fun _ hh => eLpNorm_higherDiff_le_perModulus ⟨hh.1, hh.2.trans hst⟩

/-- **The periodic modulus depends only on the class in `L_p[0, 1]`.** -/
theorem perModulus_congr_ae {f g : ℝ → ℂ} (hfg : f =ᵐ[volume.restrict (Icc 0 1)] g) (r : ℕ)
    (p : ℝ≥0∞) (t : ℝ) : perModulus r p f t = perModulus r p g t := by
  simp only [perModulus]
  congr 1
  funext h
  congr 1
  funext _
  exact eLpNorm_congr_ae (ae_restrict_of_ae (higherDiff_perExt_ae_eq hfg r h))

/-- The periodic modulus is subadditive. -/
theorem perModulus_add_le {p : ℝ≥0∞} (hp : 1 ≤ p) (r : ℕ) (f g : ℝ → ℂ) (t : ℝ) :
    perModulus r p (f + g) t ≤ perModulus r p f t + perModulus r p g t := by
  refine iSup₂_le fun h hh => ?_
  rw [perExt_add, higherDiff_add]
  exact (eLpNorm_add_le hp).trans
    (add_le_add (eLpNorm_higherDiff_le_perModulus hh) (eLpNorm_higherDiff_le_perModulus hh))

/-- The `L_p` norm of the periodic extension over a unit interval `[c, c + 1]` is the `L_p` norm
of `f` on `[0, 1]`. -/
theorem eLpNorm_perExt_Icc {f : ℝ → ℂ} (hf : Measurable f) {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp : p ≠ ∞) (c : ℝ) :
    eLpNorm (perExt f) p (volume.restrict (Icc c (c + 1))) =
      eLpNorm f p (volume.restrict (Icc 0 1)) := by
  have hm := measurable_perExt hf
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp hm.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp hf.aestronglyMeasurable]
  congr 1
  rw [lintegral_Icc_periodic (G := fun x => ‖perExt f x‖ₑ ^ p.toReal)
    (fun x => by simp only [perExt_periodic f x]) c]
  rw [← setLIntegral_congr Ico_ae_eq_Icc, ← setLIntegral_congr Ico_ae_eq_Icc]
  exact setLIntegral_congr_fun measurableSet_Ico fun x hx => by rw [perExt_of_mem f hx]

/-- `ω_r^per(f, t)_p ≤ 2^r ‖f‖_{L_p[0, 1]}`. -/
theorem perModulus_le {f : ℝ → ℂ} (hf : Measurable f) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (r : ℕ) (t : ℝ) : perModulus r p f t ≤ 2 ^ r * eLpNorm f p (volume.restrict (Icc 0 1)) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  refine iSup₂_le fun h _ => eLpNorm_higherDiff_le_of_forall hp fun k _ => le_of_eq ?_
  rw [eLpNorm_comp_add_Icc (measurable_perExt hf), zero_add, add_comm (1 : ℝ),
    eLpNorm_perExt_Icc hf hp0 hp']

/-- **The periodic modulus dominates the modulus on `[0, 1]`**: on `[0, 1 - rh)` the differences
of `fTilde` and of `f` agree, since `x, …, x + rh` stay in `[0, 1)`. -/
theorem modulus_le_perModulus (r : ℕ) (p : ℝ≥0∞) (f : ℝ → ℂ) (t : ℝ) :
    modulus r p 0 1 f t ≤ perModulus r p f t := by
  rw [modulus_eq_iSup_nonneg]
  refine iSup₂_le fun h hh => ?_
  have hrh : (0 : ℝ) ≤ r * h := mul_nonneg (Nat.cast_nonneg r) hh.1
  have hae : higherDiff r h f =ᵐ[volume.restrict (Icc 0 (1 - r * h))]
      higherDiff r h (perExt f) := by
    rw [← Measure.restrict_congr_set Ico_ae_eq_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    rw [higherDiff_apply, higherDiff_apply]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : (i : ℝ) ≤ r := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hih : (i : ℝ) * h ≤ r * h := mul_le_mul_of_nonneg_right hi' hh.1
    rw [perExt_of_mem f ⟨by nlinarith [hx.1, mul_nonneg (Nat.cast_nonneg i) hh.1],
      by linarith [hx.2]⟩]
  rw [eLpNorm_congr_ae hae]
  exact (eLpNorm_Icc_mono _ p le_rfl (by linarith)).trans (eLpNorm_higherDiff_le_perModulus hh)

/-- **The modulus of a periodic extension over `n` periods**:
`ω_r(fTilde, t, [0, n])_p ≤ n^(1/p) ω_r^per(f, t)_p`, since `Δ_h^r fTilde` is `1`-periodic
(`Interval.lintegral_Icc_nat_le`). -/
theorem modulus_perExt_le {f : ℝ → ℂ} (hf : Measurable f) {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp : p ≠ ∞) (r n : ℕ) (t : ℝ) :
    modulus r p 0 n (perExt f) t ≤ (n : ℝ≥0∞) ^ (1 / p.toReal) * perModulus r p f t := by
  have hθ : (0 : ℝ) ≤ 1 / p.toReal := by positivity
  rw [modulus_eq_iSup_nonneg]
  refine iSup₂_le fun h hh => ?_
  have hm := measurable_higherDiff (measurable_perExt hf) r h
  have hrh : (0 : ℝ) ≤ r * h := mul_nonneg (Nat.cast_nonneg r) hh.1
  have hper : Function.Periodic (fun x => ‖higherDiff r h (perExt f) x‖ₑ ^ p.toReal) 1 :=
    fun x => by simp only [higherDiff_periodic (perExt_periodic f) r h x]
  calc eLpNorm (higherDiff r h (perExt f)) p (volume.restrict (Icc 0 (n - r * h)))
      ≤ eLpNorm (higherDiff r h (perExt f)) p (volume.restrict (Icc 0 n)) :=
        eLpNorm_Icc_mono _ p le_rfl (by linarith)
    _ ≤ (n : ℝ≥0∞) ^ (1 / p.toReal) *
          eLpNorm (higherDiff r h (perExt f)) p (volume.restrict (Icc 0 1)) := by
        rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp hm.aestronglyMeasurable,
          eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp hm.aestronglyMeasurable,
          ← ENNReal.mul_rpow_of_nonneg _ _ hθ]
        exact ENNReal.rpow_le_rpow (lintegral_Icc_nat_le hper n) hθ
    _ ≤ (n : ℝ≥0∞) ^ (1 / p.toReal) * perModulus r p f t :=
        mul_le_mul' le_rfl (eLpNorm_higherDiff_le_perModulus hh)

end Interval
