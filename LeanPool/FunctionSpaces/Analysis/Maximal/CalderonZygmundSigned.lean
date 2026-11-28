/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Analysis.Maximal.FeffermanStein

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The signed Calderón–Zygmund decomposition

For a function `f : V → E` with values in a real normed space `E`, such as `ℂ`, and the maximal
big cubes of a function `G : V → [0, ∞]` at height `t`, with exceptional set `Ω`, the **good
part** `Rd.czGoodC` keeps `f` outside `Ω` and replaces it by its mean `⨍_Q f` on every maximal
big cube `Q` (the averages `Rd.czAverageC`). The suffix `C` marks these signed versions of the
`[0, ∞]`-valued `Rd.czAverage` and `Rd.czGood`. The **bad part** `Rd.czBadC = f - czGoodC`
(`Rd.czGoodC_add_czBadC`) is the sum of the pieces `Rd.czBadPart`, which live on one cube each
and have mean zero there (`Rd.hasSum_czBadPart`, `Rd.integral_czBadPart`), with total mass at
most `2 ∫ ‖f‖` (`Rd.tsum_lintegral_enorm_czBadPart_le`). For `G = ‖f‖` the good part is
bounded by `2^n t` almost everywhere (`Rd.ae_enorm_czGoodC_le`) and has
`∫ ‖czGoodC‖² ≤ 2^n t ∫ ‖f‖` (`Rd.lintegral_enorm_czGoodC_sq_le`). For a family `(g_j)_j` and
`G = ‖(‖g_j‖)_j‖_{ℓ_q}` the same cubes serve every `g_j`, and the bounds hold for the pointwise
`ℓ_q` norms (`Rd.ae_lqNorm_czGoodC_le`, `Rd.lintegral_lqNorm_czGoodC_sq_le`,
`Rd.tsum_lintegral_lqNorm_czBadPart_le`).

The definitions take the cube function `G` as an argument, so the scalar case and the family
case use the same definitions. The bounds of the good part follow from the comparison
`‖czGoodC f‖ ≤ czGood ‖f‖` (`Rd.enorm_czGoodC_le`) with the nonnegative good part, and those of
the bad pieces from general facts on means: `‖⨍ f‖ ≤ ⨍ ‖f‖` for every measure
(`MeasureTheory.enorm_average_le`) and, for a set `s` of finite measure,
`∫_s ‖f - ⨍_s f‖ ≤ 2 ∫_s ‖f‖` (`MeasureTheory.setLIntegral_enorm_sub_setAverage_le`) and its
`ℓ_q`-valued form. The `L_2` bounds of the good part use `∫ u² ≤ c ∫ u` for `u ≤ c`
(`MeasureTheory.lintegral_sq_le_mul_lintegral_of_ae_le`).

The Carleson project (`github.com/fpvandoorn/carleson`) has a scalar Calderón–Zygmund
decomposition on doubling metric measure spaces (`czApproximation`, `czRemainder`).
-/

@[expose] public section

open MeasureTheory Module Set Filter
open scoped ENNReal
open ENNReal (lqNorm)

namespace MeasureTheory

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
  [NormedSpace ℝ E]

section Countable

variable {ι : Type*} [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {q : ℝ≥0∞} {s : Set α} {g : ι → α → E}

/-- `μ(s) ‖(‖⨍_s g_i‖)_i‖_{ℓ_q} ≤ ∫_s ‖(‖g_i‖)_i‖_{ℓ_q}` for `1 ≤ q ≤ ∞`, every set `s` of finite
measure and every countable family of functions `g_i` with values in a real normed space that
are almost everywhere strongly measurable on `s`, by `MeasureTheory.enorm_average_le` and
Minkowski's inequality for means (`MeasureTheory.lqNorm_laverage_le`). -/
theorem measure_mul_lqNorm_setAverage_le (hq : 1 ≤ q)
    (hg : ∀ i, AEStronglyMeasurable (g i) (μ.restrict s)) (hs : μ s ≠ ∞) :
    μ s * lqNorm q (fun i => ‖⨍ x in s, g i x ∂μ‖ₑ) ≤ ∫⁻ x in s, lqNorm q (fun i => ‖g i x‖ₑ) ∂μ :=
  (mul_le_mul_right ((ENNReal.lqNorm_mono fun i => enorm_average_le (g i)).trans
    (lqNorm_laverage_le hq fun i => (hg i).eNorm)) _).trans_eq (measure_mul_setLAverage _ hs)

/-- **The mass of a family minus its means**: for `1 ≤ q ≤ ∞`, every set `s` of finite measure
and every countable family of functions `g_i` with values in a real normed space that are almost
everywhere strongly measurable on `s`,
`∫_s ‖(‖g_i - ⨍_s g_i‖)_i‖_{ℓ_q} ≤ 2 ∫_s ‖(‖g_i‖)_i‖_{ℓ_q}`, by Minkowski's inequality in `ℓ_q`
and `MeasureTheory.measure_mul_lqNorm_setAverage_le`. -/
theorem setLIntegral_lqNorm_sub_setAverage_le (hq : 1 ≤ q)
    (hg : ∀ i, AEStronglyMeasurable (g i) (μ.restrict s)) (hs : μ s ≠ ∞) :
    ∫⁻ x in s, lqNorm q (fun i => ‖g i x - ⨍ y in s, g i y ∂μ‖ₑ) ∂μ ≤
      2 * ∫⁻ x in s, lqNorm q (fun i => ‖g i x‖ₑ) ∂μ :=
  calc ∫⁻ x in s, lqNorm q (fun i => ‖g i x - ⨍ y in s, g i y ∂μ‖ₑ) ∂μ
      ≤ ∫⁻ x in s, (lqNorm q (fun i => ‖g i x‖ₑ) +
          lqNorm q (fun i => ‖⨍ y in s, g i y ∂μ‖ₑ)) ∂μ :=
        lintegral_mono fun _ => (ENNReal.lqNorm_mono fun _ => eNorm_sub_le).trans
          (ENNReal.lqNorm_add_le hq _ _)
    _ = (∫⁻ x in s, lqNorm q (fun i => ‖g i x‖ₑ) ∂μ) +
          μ s * lqNorm q (fun i => ‖⨍ y in s, g i y ∂μ‖ₑ) := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const, mul_comm]
    _ ≤ (∫⁻ x in s, lqNorm q (fun i => ‖g i x‖ₑ) ∂μ) +
          ∫⁻ x in s, lqNorm q (fun i => ‖g i x‖ₑ) ∂μ :=
        add_le_add le_rfl (measure_mul_lqNorm_setAverage_le hq hg hs)
    _ = 2 * ∫⁻ x in s, lqNorm q (fun i => ‖g i x‖ₑ) ∂μ := (two_mul _).symm

end Countable

end MeasureTheory

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {G : V → ℝ≥0∞} {t : ℝ≥0∞}

/-! ### Signed averages over the maximal big cubes -/

/-- The **signed Calderón–Zygmund averages** of `f : V → E`: on each maximal big cube `Q` of `G`
at height `t` the mean `⨍_Q f`, and `0` outside the exceptional set `Ω`. -/
noncomputable def czAverageC (G : V → ℝ≥0∞) (t : ℝ≥0∞) (f : V → E) (x : V) : E :=
  ∑' km : czMaximal G t,
    (zcell km.1.1 km.1.2).indicator (fun _ => ⨍ z in zcell km.1.1 km.1.2, f z) x

/-- At every point the series defining the signed averages converges, since at most one of its
terms is nonzero. -/
theorem hasSum_czAverageC (f : V → E) (x : V) :
    HasSum (fun km : czMaximal G t =>
      (zcell km.1.1 km.1.2).indicator (fun _ => ⨍ z in zcell km.1.1 km.1.2, f z) x)
      (czAverageC G t f x) := by
  refine (summable_of_hasFiniteSupport ((subsingleton_czMaximal_mem_zcell x).finite.subset
    fun km hkm => ?_)).hasSum
  by_contra hx
  exact hkm (Set.indicator_of_notMem (show x ∉ zcell km.1.1 km.1.2 from hx) _)

/-- On a maximal big cube `Q`, the signed average of `f` is `⨍_Q f`. -/
theorem czAverageC_eq_of_mem {k : ℤ} {m : Fin (finrank ℝ V) → ℤ} (hkm : (k, m) ∈ czMaximal G t)
    (f : V → E) {x : V} (hx : x ∈ zcell k m) :
    czAverageC G t f x = ⨍ z in zcell k m, f z := by
  rw [czAverageC, tsum_eq_single ⟨(k, m), hkm⟩ fun km hne => ?_]
  · exact Set.indicator_of_mem hx _
  refine Set.indicator_of_notMem (fun hx' => hne ?_) _
  exact subsingleton_czMaximal_mem_zcell (G := G) (t := t) x hx' (show x ∈ zcell k m from hx)

/-- Outside the exceptional set `Ω` the signed averages vanish. -/
theorem czAverageC_eq_zero_of_notMem (f : V → E) {x : V} (hx : x ∉ czSet G t) :
    czAverageC G t f x = 0 :=
  (tsum_congr fun km =>
    Set.indicator_of_notMem (fun hx' => hx (zcell_subset_czSet km.2 hx')) _).trans tsum_zero

/-- The signed averages are strongly measurable: they are the pointwise limit of the finite
partial sums, which are finite sums of constants times indicators of cubes. -/
theorem stronglyMeasurable_czAverageC (f : V → E) : StronglyMeasurable (czAverageC G t f) := by
  have := (czMaximal_countable (V := V) (G := G) (t := t)).to_subtype
  exact stronglyMeasurable_of_tendsto atTop
    (fun s => Finset.stronglyMeasurable_fun_sum s fun km _ =>
      stronglyMeasurable_const.indicator (measurableSet_zcell _ _))
    (tendsto_pi_nhds.2 fun x => hasSum_czAverageC f x)

/-- The norm of the signed average is at most the nonnegative average of the norm:
`‖czAverageC f (x)‖ ≤ czAverage ‖f‖ (x)`, by `MeasureTheory.enorm_average_le` on each cube. -/
theorem enorm_czAverageC_le (f : V → E) (x : V) :
    ‖czAverageC G t f x‖ₑ ≤ czAverage G t (fun y => ‖f y‖ₑ) x := by
  by_cases hx : x ∈ czSet G t
  · obtain ⟨km, hkm, hxkm⟩ := Set.mem_iUnion₂.1 hx
    rw [czAverageC_eq_of_mem hkm f hxkm, czAverage_eq_of_mem hkm _ hxkm]
    exact enorm_average_le f
  · rw [czAverageC_eq_zero_of_notMem f hx, eNorm_zero]
    exact zero_le

/-! ### The signed good part -/

/-- The **signed good part** of `f : V → E` in the Calderón–Zygmund decomposition of `G` at
height `t`: `f` outside the exceptional set `Ω`, and its mean `⨍_Q f` on each maximal big cube
`Q`. -/
noncomputable def czGoodC (G : V → ℝ≥0∞) (t : ℝ≥0∞) (f : V → E) (x : V) : E :=
  (czSet G t)ᶜ.indicator f x + czAverageC G t f x

/-- The signed good part of an almost everywhere strongly measurable function is almost
everywhere strongly measurable. -/
theorem aestronglyMeasurable_czGoodC {f : V → E} (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (czGoodC G t f) volume :=
  (hf.indicator measurableSet_czSet.compl).add
    (stronglyMeasurable_czAverageC f).aestronglyMeasurable

/-- **Comparison with the nonnegative good part**: `‖czGoodC f (x)‖ ≤ czGood ‖f‖ (x)` at every
point `x` (outside `Ω` both sides are `‖f(x)‖`). -/
theorem enorm_czGoodC_le (f : V → E) (x : V) :
    ‖czGoodC G t f x‖ₑ ≤ czGood G t (fun y => ‖f y‖ₑ) x := by
  refine (eNorm_add_le _ _).trans (add_le_add ?_ (enorm_czAverageC_le f x))
  rw [eNorm_indicator_eq_indicator_eNorm]

/-- **The integral of the norm of the signed good part is at most that of `f`**:
`∫ ‖czGoodC f‖ ≤ ∫ ‖f‖` for every `f : V → E`, since the nonnegative good part keeps the integral
(`Rd.lintegral_czGood`). -/
theorem lintegral_enorm_czGoodC_le (f : V → E) :
    ∫⁻ x, ‖czGoodC G t f x‖ₑ ≤ ∫⁻ x, ‖f x‖ₑ :=
  (lintegral_mono fun x => enorm_czGoodC_le f x).trans_eq (lintegral_czGood _)

/-- The signed good part of an integrable function is integrable. -/
theorem integrable_czGoodC {f : V → E} (hf : Integrable f volume) :
    Integrable (czGoodC G t f) volume :=
  ⟨aestronglyMeasurable_czGoodC hf.1, (lintegral_enorm_czGoodC_le f).trans_lt hf.2⟩

/-- **The good part is bounded**: in dimension `n ≥ 1`, for integrable `f` and `0 < t`, the good
part of `f` in the decomposition of `‖f‖` at height `t` satisfies `‖czGoodC f (x)‖ ≤ 2^n t` for
almost every `x`. -/
theorem ae_enorm_czGoodC_le [Nontrivial V] {f : V → E} (hf : Integrable f volume) (ht0 : 0 < t) :
    ∀ᵐ x, ‖czGoodC (fun y => ‖f y‖ₑ) t f x‖ₑ ≤ 2 ^ finrank ℝ V * t := by
  filter_upwards [ae_czGood_self_le hf.1.eNorm hf.2.ne ht0] with x hx
  exact (enorm_czGoodC_le f x).trans hx

/-- **The square of the good part**: in dimension `n ≥ 1`, for integrable `f` and `0 < t`, the
good part of `f` in the decomposition of `‖f‖` at height `t` satisfies
`∫ ‖czGoodC f‖² ≤ 2^n t ∫ ‖f‖`: it is bounded by `2^n t`, and the integral of its norm is at
most `∫ ‖f‖`. -/
theorem lintegral_enorm_czGoodC_sq_le [Nontrivial V] {f : V → E} (hf : Integrable f volume)
    (ht0 : 0 < t) :
    ∫⁻ x, ‖czGoodC (fun y => ‖f y‖ₑ) t f x‖ₑ ^ 2 ≤ 2 ^ finrank ℝ V * t * ∫⁻ x, ‖f x‖ₑ :=
  (lintegral_sq_le_mul_lintegral_of_ae_le (aestronglyMeasurable_czGoodC hf.1).eNorm
    (ae_enorm_czGoodC_le hf ht0)).trans (mul_le_mul_right (lintegral_enorm_czGoodC_le f) _)

/-! ### The signed bad part and its pieces -/

/-- The **signed bad part** `f - czGoodC f` of the Calderón–Zygmund decomposition of `G` at
height `t`. -/
noncomputable def czBadC (G : V → ℝ≥0∞) (t : ℝ≥0∞) (f : V → E) (x : V) : E :=
  f x - czGoodC G t f x

/-- The signed good and bad parts add up to the function: `czGoodC f + czBadC f = f` for every
`f : V → E`. -/
theorem czGoodC_add_czBadC (f : V → E) : czGoodC G t f + czBadC G t f = f :=
  funext fun x => add_sub_cancel (czGoodC G t f x) (f x)

/-- The **bad piece** of `f : V → E` on the dyadic cube `Q = Q_{k,m}`: `f - ⨍_Q f` on `Q` and `0`
outside. -/
noncomputable def czBadPart (f : V → E) (km : ℤ × (Fin (finrank ℝ V) → ℤ)) : V → E :=
  (zcell km.1 km.2).indicator fun z => f z - ⨍ z' in zcell km.1 km.2, f z'

/-- On its cube `Q` the bad piece is `f - ⨍_Q f`. -/
theorem czBadPart_of_mem (f : V → E) {km : ℤ × (Fin (finrank ℝ V) → ℤ)} {x : V}
    (hx : x ∈ zcell km.1 km.2) : czBadPart f km x = f x - ⨍ z in zcell km.1 km.2, f z :=
  Set.indicator_of_mem hx _

/-- Outside its cube the bad piece vanishes. -/
theorem czBadPart_of_notMem (f : V → E) {km : ℤ × (Fin (finrank ℝ V) → ℤ)} {x : V}
    (hx : x ∉ zcell km.1 km.2) : czBadPart f km x = 0 :=
  Set.indicator_of_notMem hx _

/-- Outside the exceptional set `Ω` the bad part vanishes. -/
theorem czBadC_eq_zero_of_notMem (f : V → E) {x : V} (hx : x ∉ czSet G t) :
    czBadC G t f x = 0 := by
  rw [czBadC, czGoodC, Set.indicator_of_mem (show x ∈ (czSet G t)ᶜ from hx),
    czAverageC_eq_zero_of_notMem f hx, add_zero, sub_self]

/-- On a maximal big cube `Q` the bad part is `f - ⨍_Q f`. -/
theorem czBadC_eq_of_mem {k : ℤ} {m : Fin (finrank ℝ V) → ℤ} (hkm : (k, m) ∈ czMaximal G t)
    (f : V → E) {x : V} (hx : x ∈ zcell k m) :
    czBadC G t f x = f x - ⨍ z in zcell k m, f z := by
  rw [czBadC, czGoodC, Set.indicator_of_notMem (Set.notMem_compl_iff.2 (zcell_subset_czSet hkm hx)),
    zero_add, czAverageC_eq_of_mem hkm f hx]

/-- **The bad part is the sum of the bad pieces** on the maximal big cubes, at every point; at
most one piece is nonzero there. -/
theorem hasSum_czBadPart (f : V → E) (x : V) :
    HasSum (fun km : czMaximal G t => czBadPart f km.1 x) (czBadC G t f x) := by
  by_cases hx : x ∈ czSet G t
  · obtain ⟨km, hkm, hxkm⟩ := Set.mem_iUnion₂.1 hx
    have h1 := hasSum_single (f := fun km : czMaximal G t => czBadPart f km.1 x)
      (⟨km, hkm⟩ : czMaximal G t) fun km' hne => czBadPart_of_notMem f fun hx' => hne
        (subsingleton_czMaximal_mem_zcell x hx' (show x ∈ zcell km.1 km.2 from hxkm))
    rw [czBadC_eq_of_mem hkm f hxkm, ← czBadPart_of_mem f hxkm]
    exact h1
  · rw [czBadC_eq_zero_of_notMem f hx]
    convert hasSum_zero with km
    exact czBadPart_of_notMem f fun hx' => hx (zcell_subset_czSet km.2 hx')

/-- The bad part as the series of the bad pieces, `czBadC f = ∑_Q czBadPart_Q f`. -/
theorem czBadC_eq_tsum (f : V → E) (x : V) :
    czBadC G t f x = ∑' km : czMaximal G t, czBadPart f km.1 x :=
  (hasSum_czBadPart f x).tsum_eq.symm

/-- **The bad pieces have mean zero**: `∫ czBadPart_Q f = 0` for every function `f : V → E` and
every cube `Q`. For `f` not integrable on `Q`, or `E` not complete, both the mean and the
integral are `0` by convention. -/
theorem integral_czBadPart (f : V → E) (km : ℤ × (Fin (finrank ℝ V) → ℤ)) :
    ∫ z, czBadPart f km z = 0 := by
  by_cases hE : CompleteSpace E
  · rw [czBadPart, integral_indicator (measurableSet_zcell _ _)]
    exact setAverage_sub_setAverage (volume_zcell_lt_top _ _).ne f
  · exact integral_of_not_completeSpace hE

/-- **The bad part has mean zero on every maximal big cube** `Q`: `∫_Q czBadC f = 0` for every
function `f : V → E`. -/
theorem setIntegral_czBadC {k : ℤ} {m : Fin (finrank ℝ V) → ℤ} (hkm : (k, m) ∈ czMaximal G t)
    (f : V → E) : ∫ z in zcell k m, czBadC G t f z = 0 := by
  rw [setIntegral_congr_fun (measurableSet_zcell k m) fun x hx => czBadC_eq_of_mem hkm f hx]
  by_cases hE : CompleteSpace E
  · exact setAverage_sub_setAverage (volume_zcell_lt_top _ _).ne f
  · exact integral_of_not_completeSpace hE

/-- A bad piece of a function that is integrable on its cube is integrable. -/
theorem integrable_czBadPart {f : V → E} {km : ℤ × (Fin (finrank ℝ V) → ℤ)}
    (hf : IntegrableOn f (zcell km.1 km.2) volume) : Integrable (czBadPart f km) volume :=
  (hf.sub (integrableOn_const (volume_zcell_lt_top _ _).ne)).integrable_indicator
    (measurableSet_zcell _ _)

/-- **The mass of a bad piece**: `∫ ‖czBadPart_Q f‖ ≤ 2 ∫_Q ‖f‖` for every cube `Q` and every
`f : V → E` (`MeasureTheory.setLIntegral_enorm_sub_setAverage_le`). -/
theorem lintegral_enorm_czBadPart_le (f : V → E) (km : ℤ × (Fin (finrank ℝ V) → ℤ)) :
    ∫⁻ z, ‖czBadPart f km z‖ₑ ≤ 2 * ∫⁻ z in zcell km.1 km.2, ‖f z‖ₑ := by
  simp only [czBadPart, eNorm_indicator_eq_indicator_eNorm]
  rw [lintegral_indicator (measurableSet_zcell _ _)]
  exact setLIntegral_enorm_sub_setAverage_le (volume_zcell_lt_top _ _).ne f

/-- **The total mass of the bad pieces**: `∑_Q ∫ ‖czBadPart_Q f‖ ≤ 2 ∫ ‖f‖`, the sum over the
maximal big cubes `Q` of `G` at height `t`, for every `f : V → E`. -/
theorem tsum_lintegral_enorm_czBadPart_le (f : V → E) :
    ∑' km : czMaximal G t, ∫⁻ z, ‖czBadPart f km.1 z‖ₑ ≤ 2 * ∫⁻ z, ‖f z‖ₑ :=
  tsum_le_mul_lintegral_of_le_setLIntegral 2 fun km => lintegral_enorm_czBadPart_le f km.1

/-- The bad part of an integrable function is integrable. -/
theorem integrable_czBadC {f : V → E} (hf : Integrable f volume) :
    Integrable (czBadC G t f) volume :=
  hf.sub (integrable_czGoodC hf)

/-- **The mass of the bad part**: `∫ ‖czBadC f‖ ≤ 2 ∫ ‖f‖` for every almost everywhere strongly
measurable `f`. -/
theorem lintegral_enorm_czBadC_le {f : V → E} (hf : AEStronglyMeasurable f volume) :
    ∫⁻ x, ‖czBadC G t f x‖ₑ ≤ 2 * ∫⁻ x, ‖f x‖ₑ :=
  calc ∫⁻ x, ‖czBadC G t f x‖ₑ ≤ ∫⁻ x, (‖f x‖ₑ + ‖czGoodC G t f x‖ₑ) :=
        lintegral_mono fun _ => eNorm_sub_le
    _ = (∫⁻ x, ‖f x‖ₑ) + ∫⁻ x, ‖czGoodC G t f x‖ₑ := lintegral_add_left' hf.eNorm _
    _ ≤ (∫⁻ x, ‖f x‖ₑ) + ∫⁻ x, ‖f x‖ₑ := add_le_add le_rfl (lintegral_enorm_czGoodC_le f)
    _ = 2 * ∫⁻ x, ‖f x‖ₑ := (two_mul _).symm

/-! ### Families: the vector-valued decomposition -/

variable {q : ℝ≥0∞} {g : ℕ → V → E}

/-- **The good parts of a family are bounded**: in dimension `n ≥ 1`, for `1 ≤ q ≤ ∞`, almost
everywhere strongly measurable `g_j` with `G = ‖(‖g_j‖)_j‖_{ℓ_q}` integrable, and `0 < t`, the
good parts of the `g_j` for the cubes of `G` at height `t` satisfy
`‖(‖czGoodC g_j (x)‖)_j‖_{ℓ_q} ≤ 2^n t` for almost every `x`. -/
theorem ae_lqNorm_czGoodC_le [Nontrivial V] (hq : 1 ≤ q)
    (hg : ∀ j, AEStronglyMeasurable (g j) volume)
    (hG : ∫⁻ x, lqNorm q (fun j => ‖g j x‖ₑ) ≠ ∞) (ht0 : 0 < t) :
    ∀ᵐ x, lqNorm q (fun j => ‖czGoodC (fun y => lqNorm q (fun j => ‖g j y‖ₑ)) t (g j) x‖ₑ) ≤
      2 ^ finrank ℝ V * t := by
  filter_upwards [ae_lqNorm_czGood_le hq (fun j => (hg j).eNorm) hG ht0] with x hx
  exact (ENNReal.lqNorm_mono fun j => enorm_czGoodC_le (g j) x).trans hx

/-- **The integral of the `ℓ_q` norm of the good parts of a family is at most `∫ G`**:
`∫ ‖(‖czGoodC g_j‖)_j‖_{ℓ_q} ≤ ∫ G` with `G = ‖(‖g_j‖)_j‖_{ℓ_q}`, for `1 ≤ q ≤ ∞`, almost
everywhere strongly measurable `g_j`, and the cubes of any function at any height. -/
theorem lintegral_lqNorm_czGoodC_le (hq : 1 ≤ q) (hg : ∀ j, AEStronglyMeasurable (g j) volume) :
    ∫⁻ x, lqNorm q (fun j => ‖czGoodC G t (g j) x‖ₑ) ≤ ∫⁻ x, lqNorm q (fun j => ‖g j x‖ₑ) :=
  (lintegral_mono fun x => ENNReal.lqNorm_mono fun j => enorm_czGoodC_le (g j) x).trans
    (lintegral_lqNorm_czGood_le hq fun j => (hg j).eNorm)

/-- **The square of the good parts of a family**: in dimension `n ≥ 1`, for `1 ≤ q ≤ ∞`, almost
everywhere strongly measurable `g_j` with `G = ‖(‖g_j‖)_j‖_{ℓ_q}` integrable, and `0 < t`,
`∫ ‖(‖czGoodC g_j‖)_j‖_{ℓ_q}² ≤ 2^n t ∫ G` for the cubes of `G` at height `t`. -/
theorem lintegral_lqNorm_czGoodC_sq_le [Nontrivial V] (hq : 1 ≤ q)
    (hg : ∀ j, AEStronglyMeasurable (g j) volume)
    (hG : ∫⁻ x, lqNorm q (fun j => ‖g j x‖ₑ) ≠ ∞) (ht0 : 0 < t) :
    ∫⁻ x, lqNorm q (fun j => ‖czGoodC (fun y => lqNorm q (fun j => ‖g j y‖ₑ)) t (g j) x‖ₑ) ^ 2 ≤
      2 ^ finrank ℝ V * t * ∫⁻ x, lqNorm q (fun j => ‖g j x‖ₑ) :=
  (lintegral_sq_le_mul_lintegral_of_ae_le
    (aemeasurable_lqNorm_comp (fun j => (aestronglyMeasurable_czGoodC (hg j)).eNorm) q)
    (ae_lqNorm_czGoodC_le hq hg hG ht0)).trans
    (mul_le_mul_right (lintegral_lqNorm_czGoodC_le hq hg) _)

/-- **The mass of the bad pieces of a family on one cube**: for `1 ≤ q ≤ ∞`, almost everywhere
strongly measurable `g_j` and every cube `Q`,
`∫ ‖(‖czBadPart_Q g_j‖)_j‖_{ℓ_q} ≤ 2 ∫_Q ‖(‖g_j‖)_j‖_{ℓ_q}`
(`MeasureTheory.setLIntegral_lqNorm_sub_setAverage_le`). -/
theorem lintegral_lqNorm_czBadPart_le (hq : 1 ≤ q) (hg : ∀ j, AEStronglyMeasurable (g j) volume)
    (km : ℤ × (Fin (finrank ℝ V) → ℤ)) :
    ∫⁻ z, lqNorm q (fun j => ‖czBadPart (g j) km z‖ₑ) ≤
      2 * ∫⁻ z in zcell km.1 km.2, lqNorm q (fun j => ‖g j z‖ₑ) := by
  simp only [czBadPart, eNorm_indicator_eq_indicator_eNorm, ENNReal.lqNorm_indicator]
  rw [lintegral_indicator (measurableSet_zcell _ _)]
  exact setLIntegral_lqNorm_sub_setAverage_le hq (fun j => (hg j).restrict)
    (volume_zcell_lt_top _ _).ne

/-- **The total mass of the bad pieces of a family**: for `1 ≤ q ≤ ∞` and almost everywhere
strongly measurable `g_j`, `∑_Q ∫ ‖(‖czBadPart_Q g_j‖)_j‖_{ℓ_q} ≤ 2 ∫ ‖(‖g_j‖)_j‖_{ℓ_q}`, the
sum over the maximal big cubes `Q` of any function at any height. -/
theorem tsum_lintegral_lqNorm_czBadPart_le (hq : 1 ≤ q)
    (hg : ∀ j, AEStronglyMeasurable (g j) volume) :
    ∑' km : czMaximal G t, ∫⁻ z, lqNorm q (fun j => ‖czBadPart (g j) km.1 z‖ₑ) ≤
      2 * ∫⁻ z, lqNorm q (fun j => ‖g j z‖ₑ) :=
  tsum_le_mul_lintegral_of_le_setLIntegral 2 fun km => lintegral_lqNorm_czBadPart_le hq hg km.1

end Rd
