/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Interval.PiecewisePoly
public import LeanPool.FunctionSpaces.Domains.Interval.Smoothing
public import Mathlib.MeasureTheory.Integral.Marginal
public import Mathlib.MeasureTheory.Constructions.Pi

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The unit cube and slices

The unit cube `Q = [0, 1]^d` carries the product of Lebesgue measure on `[0, 1]`
(`Cube.cubeVol`), a probability measure on `Fin d → ℝ`. Functions on the cube are
functions `(Fin d → ℝ) → ℂ`, and `L_p(Q) = Lp ℂ p (cubeVol d)`.

The theory on the cube is built from the theory on the interval through **slices**: the slice of
`f` through `x` in coordinate `i` is the function `t ↦ f(x₁, …, x_{i-1}, t, x_{i+1}, …, x_d)`
(`Cube.slice`). Tonelli's theorem in one coordinate, in Mathlib's form of marginals
(`MeasureTheory.lmarginal_singleton`, `MeasureTheory.lintegral_eq_of_lmarginal_eq`), integrates
out the coordinate `i`: `∫_Q G = ∫_Q (∫_0^1 G(x with t in place i) dt) dx`
(`Cube.lintegral_cubeVol_eq_slice`); the inner integral does not depend on `x_i`. So `L_p` norms
on the cube, also over the regions `{x ∈ Q : x_i ∈ S}`, are `L_p` norms over `x` of the
`L_p[0, 1]` norms of the slices (`Cube.eLpNorm_rpow_region_eq_slice`), and functions equal
almost everywhere on the cube have almost everywhere equal slices for almost every `x`
(`Cube.ae_slice_ae_eq`). The same holds over `R ∩ {x_i ∈ S}` for every measurable set `R` that
does not depend on `x_i` (`Cube.lintegral_inter_eq_slice`): there
`‖f‖_{L_p(R ∩ {x_i ∈ S})} = ‖x ↦ ‖slice f x i‖_{L_p(S ∩ [0, 1])}‖_{L_p(R)}`
(`Cube.eLpNorm_inter_eq_slice`, on `Q` and on the regions `{x ∈ Q : x_i ∈ [a, b]}` with the
restricted measures `Cube.regionVol`: `Cube.eLpNorm_cubeVol_eq_slice`,
`Cube.eLpNorm_regionVol_eq_slice`), so bounds of the slices give bounds on the cube
(`Cube.eLpNorm_inter_le_of_slice_le`, `Cube.eLpNorm_cubeVol_le_of_slice_le`).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Cube

open Interval

/-- On `[a, b] ⊆ [0, 1]`, Lebesgue measure on `[0, 1]` restricted to `[a, b]` is Lebesgue measure
on `[a, b]`. -/
theorem unitVol_restrict_Icc_of_subset {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    unitVol.restrict (Icc a b) = volume.restrict (Icc a b) := by
  rw [Measure.restrict_restrict measurableSet_Icc, Set.inter_eq_left.2 (Icc_subset_Icc ha hb)]

/-- **Lebesgue measure on the unit cube** `[0, 1]^d`, the product of Lebesgue measure on
`[0, 1]`. -/
noncomputable abbrev cubeVol (d : ℕ) : Measure (Fin d → ℝ) := Measure.pi fun _ : Fin d => unitVol

variable {d : ℕ}

/-- The **slice** of `f` through `x` in coordinate `i`: `t ↦ f(x₁, …, t, …, x_d)`, with `t` in
place `i`. -/
def slice (f : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) (i : Fin d) (t : ℝ) : ℂ :=
  f (Function.update x i t)

/-- The slices of a measurable function are measurable. -/
theorem measurable_slice {f : (Fin d → ℝ) → ℂ} (hf : Measurable f) (x : Fin d → ℝ)
    (i : Fin d) : Measurable (slice f x i) :=
  hf.comp (measurable_update x)

/-- The slices of a continuous function are continuous. -/
theorem continuous_slice {f : (Fin d → ℝ) → ℂ} (hf : Continuous f) (x : Fin d → ℝ) (i : Fin d) :
    Continuous (slice f x i) :=
  hf.comp (continuous_const.update i continuous_id)

/-- The slices of a measurable function are jointly measurable in the point and the variable. -/
theorem measurable_slice_uncurry {f : (Fin d → ℝ) → ℂ} (hf : Measurable f) (i : Fin d) :
    Measurable (fun q : (Fin d → ℝ) × ℝ => slice f q.1 i q.2) :=
  hf.comp measurable_update'

/-- A slice does not depend on the coordinate `i` of the point. -/
theorem slice_update (f : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) (i : Fin d) (s : ℝ) :
    slice f (Function.update x i s) i = slice f x i := by
  funext t
  simp only [slice, Function.update_idem]

/-- **Integrating out one coordinate**: for measurable `G ≥ 0` on the cube and every
coordinate `i`, `∫_Q G = ∫_Q (∫_0^1 G(update x i t) dt) dx`; the inner integral does not depend
on `x_i`. -/
theorem lintegral_cubeVol_eq_slice {G : (Fin d → ℝ) → ℝ≥0∞} (hG : Measurable G) (i : Fin d) :
    ∫⁻ x, G x ∂cubeVol d = ∫⁻ x, (∫⁻ t, G (Function.update x i t) ∂unitVol) ∂cubeVol d := by
  set F : (Fin d → ℝ) → ℝ≥0∞ := fun x => ∫⁻ t, G (Function.update x i t) ∂unitVol
  have hmarg : (∫⋯∫⁻_{i}, G ∂fun _ => unitVol) = F := lmarginal_singleton G i
  have hF : Measurable F := hmarg ▸ hG.lmarginal (fun _ => unitVol)
  refine lintegral_eq_of_lmarginal_eq {i} hG hF ?_
  rw [hmarg, lmarginal_singleton]
  funext x
  simp only [F, Function.update_idem]
  rw [lintegral_const, measure_univ, mul_one]

/-- **Integrating out one coordinate under a constraint that does not depend on it**: if the
measurable set `R` does not depend on the coordinate `i`, then
`∫_{R ∩ {x_i ∈ S}} G = ∫_R (∫_{S ∩ [0,1]} G(x with t in place i) dt) dx`. -/
theorem lintegral_inter_eq_slice {G : (Fin d → ℝ) → ℝ≥0∞} (hG : Measurable G) (i : Fin d)
    {R : Set (Fin d → ℝ)} (hR : MeasurableSet R)
    (hRi : ∀ x t, Function.update x i t ∈ R ↔ x ∈ R) {S : Set ℝ} (hS : MeasurableSet S) :
    ∫⁻ x in R ∩ {x | x i ∈ S}, G x ∂cubeVol d =
      ∫⁻ x in R, (∫⁻ t in S, G (Function.update x i t) ∂unitVol) ∂cubeVol d := by
  have hRS : MeasurableSet (R ∩ {x : Fin d → ℝ | x i ∈ S}) :=
    hR.inter (measurable_pi_apply i hS)
  rw [← lintegral_indicator hRS, lintegral_cubeVol_eq_slice (hG.indicator hRS) i,
    ← lintegral_indicator hR]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ R
  · rw [indicator_of_mem hx, ← lintegral_indicator hS]
    refine lintegral_congr fun t => ?_
    by_cases ht : t ∈ S
    · rw [indicator_of_mem ht, indicator_of_mem (show Function.update x i t ∈
        R ∩ {x | x i ∈ S} from ⟨(hRi x t).2 hx, by simpa using ht⟩)]
    · rw [indicator_of_notMem ht, indicator_of_notMem fun h => ht (by simpa using h.2)]
  · rw [indicator_of_notMem hx]
    have h0 : ∀ t, (R ∩ {x | x i ∈ S}).indicator G (Function.update x i t) = 0 := fun t =>
      indicator_of_notMem
        (fun h : Function.update x i t ∈ R ∩ {x | x i ∈ S} => hx ((hRi x t).1 h.1)) _
    simp only [h0, lintegral_zero]

/-- **Integrating out one coordinate over a region** `{x ∈ Q : x_i ∈ S}`:
`∫_{x_i ∈ S} G = ∫_Q (∫_{S ∩ [0,1]} G(update x i t) dt) dx`, the case `R = ℝ^d` of
`Cube.lintegral_inter_eq_slice`. -/
theorem lintegral_region_eq_slice {G : (Fin d → ℝ) → ℝ≥0∞} (hG : Measurable G) (i : Fin d)
    {S : Set ℝ} (hS : MeasurableSet S) :
    ∫⁻ x in {x | x i ∈ S}, G x ∂cubeVol d =
      ∫⁻ x, (∫⁻ t in S, G (Function.update x i t) ∂unitVol) ∂cubeVol d := by
  simpa using lintegral_inter_eq_slice hG i MeasurableSet.univ (fun _ _ => Iff.rfl) hS

/-- **`L_p` norms over a region through slices**: for measurable `f`, `0 < p < ∞`,
`‖f‖_{L_p({x_i ∈ S})}^p = ∫_Q ‖slice f x i‖_{L_p(S)}^p dx`. -/
theorem eLpNorm_rpow_region_eq_slice {f : (Fin d → ℝ) → ℂ} (hf : Measurable f) {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (i : Fin d) {S : Set ℝ} (hS : MeasurableSet S) :
    eLpNorm f p ((cubeVol d).restrict {x | x i ∈ S}) ^ p.toReal =
      ∫⁻ x, eLpNorm (slice f x i) p (unitVol.restrict S) ^ p.toReal ∂cubeVol d := by
  rw [eLpNorm_rpow_eq hf.aestronglyMeasurable hp0 hp,
    lintegral_region_eq_slice (hf.eNorm.pow_const _) i hS]
  refine lintegral_congr fun x => ?_
  rw [eLpNorm_rpow_eq (measurable_slice hf x i).aestronglyMeasurable hp0 hp]
  rfl

/-- **`L_p` norms on the cube through slices**: for measurable `f`, `0 < p < ∞`,
`‖f‖_{L_p(Q)}^p = ∫_Q ‖slice f x i‖_{L_p[0,1]}^p dx`. -/
theorem eLpNorm_rpow_cubeVol_eq_slice {f : (Fin d → ℝ) → ℂ} (hf : Measurable f) {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (i : Fin d) :
    eLpNorm f p (cubeVol d) ^ p.toReal =
      ∫⁻ x, eLpNorm (slice f x i) p unitVol ^ p.toReal ∂cubeVol d := by
  have h := eLpNorm_rpow_region_eq_slice hf hp0 hp i MeasurableSet.univ
  simpa using h

/-- The `L_p` norms of the slices of a measurable function are measurable in the point. -/
theorem measurable_eLpNorm_slice {f : (Fin d → ℝ) → ℂ} (hf : Measurable f) {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (i : Fin d) (μ : Measure ℝ) [SFinite μ] :
    Measurable fun x => eLpNorm (slice f x i) p μ := by
  have h : Measurable fun x => ∫⁻ t, ‖slice f x i t‖ₑ ^ p.toReal ∂μ :=
    ((measurable_slice_uncurry hf i).eNorm.pow_const p.toReal).lintegral_prod_right'
  have heq : (fun x => eLpNorm (slice f x i) p μ) =
      fun x => (∫⁻ t, ‖slice f x i t‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) := funext fun x =>
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp (measurable_slice hf x i).aestronglyMeasurable
  rw [heq]
  exact h.pow_const _

/-- **`L_p` norms as mixed norms of slices**: let the measurable set `R` not depend on the
coordinate `i`. For measurable `f` and `0 < p < ∞`,
`‖f‖_{L_p(R ∩ {x_i ∈ S})} = ‖x ↦ ‖slice f x i‖_{L_p(S ∩ [0, 1])}‖_{L_p(R)}`, by integrating out the
coordinate `i` in `|f|^p` (`Cube.lintegral_inter_eq_slice`). -/
theorem eLpNorm_inter_eq_slice {f : (Fin d → ℝ) → ℂ} (hf : Measurable f) {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (i : Fin d) {R : Set (Fin d → ℝ)} (hR : MeasurableSet R)
    (hRi : ∀ x t, Function.update x i t ∈ R ↔ x ∈ R) {S : Set ℝ} (hS : MeasurableSet S) :
    eLpNorm f p ((cubeVol d).restrict (R ∩ {x | x i ∈ S})) =
      eLpNorm (fun x => eLpNorm (slice f x i) p (unitVol.restrict S)) p
        ((cubeVol d).restrict R) := by
  refine (ENNReal.rpow_left_injective (ENNReal.toReal_pos hp0 hp).ne').eq_iff.1 ?_
  simp only [eLpNorm_rpow_eq hf.aestronglyMeasurable hp0 hp, eLpNorm_rpow_eq
    (measurable_eLpNorm_slice hf hp0 hp i _).aestronglyMeasurable hp0 hp, eNorm_eq_self]
  rw [lintegral_inter_eq_slice (hf.eNorm.pow_const _) i hR hRi hS]
  refine setLIntegral_congr_fun hR fun x _ => ?_
  rw [eLpNorm_rpow_eq (measurable_slice hf x i).aestronglyMeasurable hp0 hp]
  rfl

/-- **Bounds through slices**: let the measurable set `R` not depend on the coordinate `i`. For
measurable `F, G`, `0 < p < ∞`, measurable `S, S' ⊆ ℝ` and `C ∈ [0, ∞]`, if
`‖slice F x i‖_{L_p(S ∩ [0, 1])} ≤ C ‖slice G x i‖_{L_p(S' ∩ [0, 1])}` for every point `x`, then
`‖F‖_{L_p(R ∩ {x_i ∈ S})} ≤ C ‖G‖_{L_p(R ∩ {x_i ∈ S'})}` (`Cube.eLpNorm_inter_eq_slice`). -/
theorem eLpNorm_inter_le_of_slice_le {F G : (Fin d → ℝ) → ℂ} (hF : Measurable F)
    (hG : Measurable G) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) (i : Fin d)
    {R : Set (Fin d → ℝ)} (hR : MeasurableSet R) (hRi : ∀ x t, Function.update x i t ∈ R ↔ x ∈ R)
    {S S' : Set ℝ} (hS : MeasurableSet S) (hS' : MeasurableSet S') {C : ℝ≥0∞}
    (h : ∀ x, eLpNorm (slice F x i) p (unitVol.restrict S) ≤
      C * eLpNorm (slice G x i) p (unitVol.restrict S')) :
    eLpNorm F p ((cubeVol d).restrict (R ∩ {x | x i ∈ S})) ≤
      C * eLpNorm G p ((cubeVol d).restrict (R ∩ {x | x i ∈ S'})) := by
  rw [eLpNorm_inter_eq_slice hF hp0 hp i hR hRi hS, eLpNorm_inter_eq_slice hG hp0 hp i hR hRi hS',
    ← eLpNorm_const_mul_ennreal (c := C)
      (measurable_eLpNorm_slice hG hp0 hp i _).aestronglyMeasurable]
  exact eLpNorm_mono_eNorm (measurable_eLpNorm_slice hF hp0 hp i _).aestronglyMeasurable
    fun x => by simpa only [eNorm_eq_self] using h x

/-- **Bounds through slices on the whole cube**: for measurable `F, G`, `0 < p < ∞` and
`C ∈ [0, ∞]`, if `‖slice F x i‖_{L_p[0,1]} ≤ C ‖slice G x i‖_{L_p[0,1]}` for every point `x`,
then `‖F‖_{L_p(Q)} ≤ C ‖G‖_{L_p(Q)}`. -/
theorem eLpNorm_cubeVol_le_of_slice_le {F G : (Fin d → ℝ) → ℂ} (hF : Measurable F)
    (hG : Measurable G) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) (i : Fin d) {C : ℝ≥0∞}
    (h : ∀ x, eLpNorm (slice F x i) p unitVol ≤ C * eLpNorm (slice G x i) p unitVol) :
    eLpNorm F p (cubeVol d) ≤ C * eLpNorm G p (cubeVol d) := by
  simpa using eLpNorm_inter_le_of_slice_le hF hG hp0 hp i MeasurableSet.univ
    (fun _ _ => Iff.rfl) MeasurableSet.univ MeasurableSet.univ (C := C) fun x => by simpa using h x

/-- The cube measure restricted to the region `{x ∈ Q : x_i ∈ [a, b]}`. -/
noncomputable abbrev regionVol (d : ℕ) (i : Fin d) (a b : ℝ) : Measure (Fin d → ℝ) :=
  (cubeVol d).restrict {x | x i ∈ Icc a b}

/-- **`L_p` norms over a region through slices**, with Lebesgue measure on the slices:
`‖f‖_{L_p({x_i ∈ [a, b]})}^p = ∫_Q ‖slice f x i‖_{L_p[a, b]}^p dx` for `[a, b] ⊆ [0, 1]`. -/
theorem eLpNorm_rpow_regionVol_eq_slice {f : (Fin d → ℝ) → ℂ} (hf : Measurable f) {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (i : Fin d) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    eLpNorm f p (regionVol d i a b) ^ p.toReal =
      ∫⁻ x, eLpNorm (slice f x i) p (volume.restrict (Icc a b)) ^ p.toReal ∂cubeVol d := by
  rw [regionVol, eLpNorm_rpow_region_eq_slice hf hp0 hp i measurableSet_Icc,
    unitVol_restrict_Icc_of_subset ha hb]

/-- **`L_p` norms on the cube as mixed norms of slices**: for measurable `f` and `0 < p < ∞`,
`‖f‖_{L_p(Q)} = ‖x ↦ ‖slice f x i‖_{L_p[0, 1]}‖_{L_p(Q)}` (`Cube.eLpNorm_inter_eq_slice`). -/
theorem eLpNorm_cubeVol_eq_slice {f : (Fin d → ℝ) → ℂ} (hf : Measurable f) {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (i : Fin d) :
    eLpNorm f p (cubeVol d) = eLpNorm (fun x => eLpNorm (slice f x i) p unitVol) p (cubeVol d) := by
  simpa using eLpNorm_inter_eq_slice hf hp0 hp i MeasurableSet.univ (fun _ _ => Iff.rfl)
    MeasurableSet.univ

/-- **`L_p` norms over a region as mixed norms of slices**: for measurable `f`, `0 < p < ∞` and
`[a, b] ⊆ [0, 1]`, `‖f‖_{L_p({x_i ∈ [a, b]})} = ‖x ↦ ‖slice f x i‖_{L_p[a, b]}‖_{L_p(Q)}`
(`Cube.eLpNorm_inter_eq_slice`). -/
theorem eLpNorm_regionVol_eq_slice {f : (Fin d → ℝ) → ℂ} (hf : Measurable f) {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (i : Fin d) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    eLpNorm f p (regionVol d i a b) =
      eLpNorm (fun x => eLpNorm (slice f x i) p (volume.restrict (Icc a b))) p (cubeVol d) := by
  have h := eLpNorm_inter_eq_slice hf hp0 hp i MeasurableSet.univ (fun _ _ => Iff.rfl)
    (measurableSet_Icc (a := a) (b := b))
  rwa [univ_inter, Measure.restrict_univ, unitVol_restrict_Icc_of_subset ha hb] at h

/-- **Slices of almost equal functions**: if `f = g` almost everywhere on the cube, then for
almost every `x` the slices of `f` and `g` through `x` in coordinate `i` agree almost
everywhere on `[0, 1]`. -/
theorem ae_slice_ae_eq {f g : (Fin d → ℝ) → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hfg : f =ᵐ[cubeVol d] g) (i : Fin d) :
    ∀ᵐ x ∂cubeVol d, slice f x i =ᵐ[unitVol] slice g x i := by
  have hset : MeasurableSet {x : Fin d → ℝ | f x ≠ g x} :=
    (measurableSet_eq_fun hf hg).compl
  have h0 : ∫⁻ x, {x | f x ≠ g x}.indicator 1 x ∂cubeVol d = 0 := by
    rw [lintegral_indicator_one hset]
    exact ae_iff.1 hfg
  rw [lintegral_cubeVol_eq_slice ((measurable_one.indicator hset)) i,
    lintegral_eq_zero_iff (by
      have : Measurable ((∫⋯∫⁻_{i}, {x | f x ≠ g x}.indicator 1 ∂fun _ => unitVol)) :=
        (measurable_one.indicator hset).lmarginal (fun _ => unitVol)
      rwa [lmarginal_singleton] at this)] at h0
  filter_upwards [h0] with x hx
  have hx' : ∫⁻ t, {t | slice f x i t ≠ slice g x i t}.indicator 1 t ∂unitVol = 0 := hx
  rw [lintegral_indicator_one (s := {t | slice f x i t ≠ slice g x i t})
    (measurableSet_eq_fun (measurable_slice hf x i) (measurable_slice hg x i)).compl] at hx'
  exact ae_iff.2 hx'

end Cube
