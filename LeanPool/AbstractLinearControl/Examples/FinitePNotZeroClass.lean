/-
Copyright (c) 2026 Frédéric Marbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Marbach
-/
module

public import LeanPool.AbstractLinearControl.Definitions


/-!
# For `p < ∞`, not every system is zero-class (Proposition 3.1)

**Proposition 3.1** (`prop:example-finite-p-not-zero-class`). Let `p ∈ [1, ∞)`. There
exist Banach spaces `X` and `U` and an abstract linear control system `(𝕋, Φ)` such that
`κ(t) = 1` for all `t > 0`.

As in the paper, `X = L^p(ℝ₊)`, `U = ℝ`, and
* `T t` is the right shift: `(T t f)(s) = f (s - t)` for `s ≥ t` and `0` for `s < t`;
* `Φ t` reverses the input on `[0, t]`: `(Φ t u)(s) = u (t - s)` for `0 < s ≤ t` and `0`
  otherwise. (The paper uses `0 ≤ s < t`; this changes a null set only, and makes the
  concatenation identity hold pointwise.)

## Main declarations

* `ShiftExample.shiftSystem` : the system, an `ALCS ℝ (Lp ℝ p muPlus) ℝ p`.
* `ShiftExample.norm_Phi_eq_one` : `‖Φ t‖ = 1` for all `t > 0`.
* `exists_system_norm_Phi_eq_one` : Proposition 3.1, as an existence statement.
* `ShiftExample.not_zero_class` : the system is not of the zero-class (Definition 1.4).

## Implementation

All operators are built in one way (`op`): extend `f` by zero to `ℝ` (`zext`), compose
with a measure-preserving map `φ : ℝ → ℝ`, multiply by the indicator of a set `A`, and
restrict to `ℝ₊`. Then `T t = op (· - t) univ` and `Φ t = op (t - ·) (Ioc 0 t)`.
Strong continuity of the shift reduces to the continuity of translations in `L^p(ℝ)`,
which is `Filter.Tendsto.compMeasurePreservingLp` in Mathlib; it fails for `p = ∞`.
-/

namespace AbstractLinearControl

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace ShiftExample

/-! ## Raw functions -/

section Raw

/-- Extension by zero of `f` from `[0, ∞)` to `ℝ`. -/
def zext (f : ℝ → ℝ) : ℝ → ℝ := (Set.Ici (0 : ℝ)).indicator f

/-- The raw operator: `s ↦ 1_A(s) · (zext f)(φ s)`. -/
def rawOp (φ : ℝ → ℝ) (A : Set ℝ) (f : ℝ → ℝ) : ℝ → ℝ := A.indicator (zext f ∘ φ)

lemma zext_of_nonneg (f : ℝ → ℝ) (y : ℝ) (h : 0 ≤ y) : zext f y = f y := by
  have h' : y ∈ Set.Ici (0 : ℝ) := h
  exact Set.indicator_of_mem h' f

lemma zext_of_neg (f : ℝ → ℝ) (y : ℝ) (h : y < 0) : zext f y = 0 := by
  have h' : y ∉ Set.Ici (0 : ℝ) := not_le.2 h
  exact Set.indicator_of_notMem h' f

variable {φ : ℝ → ℝ} {A : Set ℝ}

lemma rawOp_add (f g : ℝ → ℝ) (x : ℝ) :
    rawOp φ A (f + g) x = rawOp φ A f x + rawOp φ A g x := by
  by_cases hx : x ∈ A
  · by_cases hy : φ x ∈ Set.Ici (0 : ℝ)
    · simp only [rawOp, zext, Function.comp_apply, Set.indicator_of_mem hx,
        Set.indicator_of_mem hy, Pi.add_apply]
    · simp only [rawOp, zext, Function.comp_apply, Set.indicator_of_mem hx,
        Set.indicator_of_notMem hy, add_zero]
  · simp only [rawOp, Set.indicator_of_notMem hx, add_zero]

lemma rawOp_smul (c : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    rawOp φ A (c • f) x = c • rawOp φ A f x := by
  by_cases hx : x ∈ A
  · by_cases hy : φ x ∈ Set.Ici (0 : ℝ)
    · simp only [rawOp, zext, Function.comp_apply, Set.indicator_of_mem hx,
        Set.indicator_of_mem hy, Pi.smul_apply]
    · simp only [rawOp, zext, Function.comp_apply, Set.indicator_of_mem hx,
        Set.indicator_of_notMem hy, smul_zero]
  · simp only [rawOp, Set.indicator_of_notMem hx, smul_zero]

/-- `rawOp` only depends on the a.e. class of `f` on `ℝ₊`. -/
lemma rawOp_congr (hφ : MeasurePreserving φ volume volume) (A : Set ℝ) {f g : ℝ → ℝ}
    (h : f =ᵐ[muPlus] g) : rawOp φ A f =ᵐ[muPlus] rawOp φ A g := by
  have h1 : ∀ᵐ x ∂volume, x ∈ Set.Ici (0 : ℝ) → f x = g x :=
    (ae_restrict_iff' measurableSet_Ici).1 h
  -- the zero extensions agree a.e. on `ℝ`
  have h2 : zext f =ᵐ[volume] zext g := by
    filter_upwards [h1] with x hx
    by_cases hx0 : x ∈ Set.Ici (0 : ℝ)
    · simp only [zext, Set.indicator_of_mem hx0, hx hx0]
    · simp only [zext, Set.indicator_of_notMem hx0]
  -- composing with a measure-preserving map keeps a.e. equality
  have h3 : zext f ∘ φ =ᵐ[volume] zext g ∘ φ := hφ.quasiMeasurePreserving.ae_eq_comp h2
  have h4 : rawOp φ A f =ᵐ[volume] rawOp φ A g := by
    filter_upwards [h3] with x hx
    by_cases hxA : x ∈ A
    · simp only [rawOp, Set.indicator_of_mem hxA]
      exact hx
    · simp only [rawOp, Set.indicator_of_notMem hxA]
  exact ae_restrict_of_ae h4

/-! ### Evaluation of the raw shift and of the raw input map -/

/-- Raw shift: `rawOp (· - t) univ f x = zext f (x - t)`. -/
lemma rawT_apply (f : ℝ → ℝ) (t x : ℝ) :
    rawOp (fun y => y - t) Set.univ f x = zext f (x - t) := by
  simp only [rawOp, Set.indicator_univ, Function.comp_apply]

/-- Raw input map, for `0 < y ≤ a`: the value is `f (a - y)`. -/
lemma rawPhi_of_mem (f : ℝ → ℝ) (a y : ℝ) (h : 0 < y ∧ y ≤ a) :
    rawOp (fun z => a - z) (Set.Ioc 0 a) f y = f (a - y) := by
  have h1 : y ∈ Set.Ioc 0 a := h
  simp only [rawOp, Set.indicator_of_mem h1, Function.comp_apply]
  exact zext_of_nonneg f (a - y) (by linarith [h.2])

/-- Raw input map, outside `(0, a]`: the value is `0`. -/
lemma rawPhi_of_not (f : ℝ → ℝ) (a y : ℝ) (h : ¬ (0 < y ∧ y ≤ a)) :
    rawOp (fun z => a - z) (Set.Ioc 0 a) f y = 0 := by
  have h1 : y ∉ Set.Ioc 0 a := h
  simp only [rawOp, Set.indicator_of_notMem h1]

/-- The raw input map vanishes on `(-∞, 0]`, also after extension by zero. -/
lemma zext_rawPhi_of_nonpos (f : ℝ → ℝ) (a y : ℝ) (hy : y ≤ 0) :
    zext (rawOp (fun z => a - z) (Set.Ioc 0 a) f) y = 0 := by
  by_cases h0 : 0 ≤ y
  · rw [zext_of_nonneg _ y h0]
    exact rawPhi_of_not f a y (fun h => by linarith [h.1])
  · exact zext_of_neg _ y (not_le.1 h0)

lemma concat_of_lt (u v : ℝ → ℝ) (τ y : ℝ) (h : y < τ) : concat τ u v y = u y := by
  simp only [concat, ite_eq_left h]

lemma concat_of_ge (u v : ℝ → ℝ) (τ y : ℝ) (h : τ ≤ y) : concat τ u v y = v (y - τ) := by
  simp only [concat, ite_eq_right (not_lt.2 h)]

/-- The concatenation identity, pointwise, for raw functions:
`Φ (τ + t) (u ⋄_τ v) = T t (Φ τ u) + Φ t v`. -/
lemma concat_pointwise (u v : ℝ → ℝ) {τ t : ℝ} (hτ : 0 ≤ τ) (ht : 0 ≤ t) (x : ℝ) :
    rawOp (fun y => τ + t - y) (Set.Ioc 0 (τ + t)) (concat τ u v) x =
      rawOp (fun y => y - t) Set.univ (rawOp (fun y => τ - y) (Set.Ioc 0 τ) u) x
        + rawOp (fun y => t - y) (Set.Ioc 0 t) v x := by
  rw [rawT_apply]
  by_cases hx0 : 0 < x
  · by_cases hxt : x ≤ t
    · -- case `0 < x ≤ t`: only `v` contributes
      have h1 : x ≤ τ + t := by linarith
      have h2 : x - t ≤ 0 := by linarith
      have h3 : τ ≤ τ + t - x := by linarith
      rw [rawPhi_of_mem _ (τ + t) x ⟨hx0, h1⟩, rawPhi_of_mem v t x ⟨hx0, hxt⟩,
        zext_rawPhi_of_nonpos u τ (x - t) h2, zero_add, concat_of_ge u v τ (τ + t - x) h3,
        show τ + t - x - τ = t - x by ring]
    · by_cases hxτt : x ≤ τ + t
      · -- case `t < x ≤ τ + t`: only `u` contributes
        have h1 : 0 ≤ x - t := by linarith
        have h2 : 0 < x - t := by linarith
        have h3 : x - t ≤ τ := by linarith
        have h4 : τ + t - x < τ := by linarith
        rw [rawPhi_of_mem _ (τ + t) x ⟨hx0, hxτt⟩, rawPhi_of_not v t x (fun h => hxt h.2),
          zext_of_nonneg _ (x - t) h1, rawPhi_of_mem u τ (x - t) ⟨h2, h3⟩, add_zero,
          concat_of_lt u v τ (τ + t - x) h4, show τ - (x - t) = τ + t - x by ring]
      · -- case `x > τ + t`: everything vanishes
        have h1 : 0 ≤ x - t := by linarith
        have h2 : ¬ (x - t ≤ τ) := by intro h; exact hxτt (by linarith)
        rw [rawPhi_of_not _ (τ + t) x (fun h => hxτt h.2), rawPhi_of_not v t x (fun h => hxt h.2),
          zext_of_nonneg _ (x - t) h1, rawPhi_of_not u τ (x - t) (fun h => h2 h.2), add_zero]
  · -- case `x ≤ 0`: everything vanishes
    have h1 : x - t ≤ 0 := by linarith
    rw [rawPhi_of_not _ (τ + t) x (fun h => hx0 h.1), rawPhi_of_not v t x (fun h => hx0 h.1),
      zext_rawPhi_of_nonpos u τ (x - t) h1, add_zero]

end Raw

/-! ## Bounded operators on `L^p(ℝ₊)` -/

section Operators

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {φ : ℝ → ℝ} {A : Set ℝ}

omit [Fact (1 ≤ p)] in
lemma memLp_zext (f : Lp ℝ p muPlus) : MemLp (zext ⇑f) p volume :=
  (memLp_indicator_iff_restrict measurableSet_Ici).2 (Lp.memLp f)

omit [Fact (1 ≤ p)] in
lemma eLpNorm_zext (f : Lp ℝ p muPlus) : eLpNorm (zext ⇑f) p volume = eLpNorm (⇑f) p muPlus :=
  eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ici

omit [Fact (1 ≤ p)] in
lemma memLp_rawOp (hφ : MeasurePreserving φ volume volume) (hA : MeasurableSet A)
    (f : Lp ℝ p muPlus) : MemLp (rawOp φ A ⇑f) p muPlus :=
  (((memLp_zext f).comp_measurePreserving hφ).indicator hA).mono_measure
    Measure.restrict_le_self

omit [Fact (1 ≤ p)] in
lemma eLpNorm_rawOp_le (hφ : MeasurePreserving φ volume volume) (hA : MeasurableSet A)
    (f : Lp ℝ p muPlus) : eLpNorm (rawOp φ A ⇑f) p muPlus ≤ eLpNorm (⇑f) p muPlus := by
  calc eLpNorm (rawOp φ A ⇑f) p muPlus
      ≤ eLpNorm (rawOp φ A ⇑f) p volume := eLpNorm_mono_measure _ Measure.restrict_le_self
    _ ≤ eLpNorm (zext ⇑f ∘ φ) p volume :=
        eLpNorm_indicator_le (zext ⇑f ∘ φ) hA
    _ = eLpNorm (zext ⇑f) p volume :=
        eLpNorm_comp_measurePreserving (memLp_zext f).aestronglyMeasurable hφ
    _ = eLpNorm (⇑f) p muPlus := eLpNorm_zext f

/-- `f ↦ rawOp φ A f`, as a map on `L^p(ℝ₊)`. -/
def opFun (φ : ℝ → ℝ) (hφ : MeasurePreserving φ volume volume) (A : Set ℝ)
    (hA : MeasurableSet A) (f : Lp ℝ p muPlus) : Lp ℝ p muPlus :=
  (memLp_rawOp hφ hA f).toLp (rawOp φ A ⇑f)

omit [Fact (1 ≤ p)] in
lemma opFun_ae (hφ : MeasurePreserving φ volume volume) (hA : MeasurableSet A)
    (f : Lp ℝ p muPlus) : ⇑(opFun φ hφ A hA f) =ᵐ[muPlus] rawOp φ A ⇑f :=
  (memLp_rawOp hφ hA f).coeFn_toLp

omit [Fact (1 ≤ p)] in
lemma opFun_congr (hφ : MeasurePreserving φ volume volume) (hA : MeasurableSet A)
    (f : Lp ℝ p muPlus) {g : ℝ → ℝ} (h : ⇑f =ᵐ[muPlus] g) :
    ⇑(opFun φ hφ A hA f) =ᵐ[muPlus] rawOp φ A g :=
  (opFun_ae hφ hA f).trans (rawOp_congr hφ A h)

omit [Fact (1 ≤ p)] in
lemma opFun_add (hφ : MeasurePreserving φ volume volume) (hA : MeasurableSet A)
    (f g : Lp ℝ p muPlus) : opFun φ hφ A hA (f + g) = opFun φ hφ A hA f + opFun φ hφ A hA g := by
  apply Lp.ext
  filter_upwards [opFun_congr hφ hA (f + g) (Lp.coeFn_add f g), opFun_ae hφ hA f,
    opFun_ae hφ hA g, Lp.coeFn_add (opFun φ hφ A hA f) (opFun φ hφ A hA g)] with x e1 e2 e3 e4
  rw [e1, e4, Pi.add_apply, e2, e3]
  exact rawOp_add ⇑f ⇑g x

omit [Fact (1 ≤ p)] in
lemma opFun_smul (hφ : MeasurePreserving φ volume volume) (hA : MeasurableSet A)
    (c : ℝ) (f : Lp ℝ p muPlus) : opFun φ hφ A hA (c • f) = c • opFun φ hφ A hA f := by
  apply Lp.ext
  filter_upwards [opFun_congr hφ hA (c • f) (Lp.coeFn_smul c f), opFun_ae hφ hA f,
    Lp.coeFn_smul c (opFun φ hφ A hA f)] with x e1 e2 e3
  rw [e1, e3, Pi.smul_apply, e2]
  exact rawOp_smul c ⇑f x

omit [Fact (1 ≤ p)] in
lemma norm_opFun_le (hφ : MeasurePreserving φ volume volume) (hA : MeasurableSet A)
    (f : Lp ℝ p muPlus) : ‖opFun φ hφ A hA f‖ ≤ ‖f‖ := by
  unfold opFun
  rw [Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_rawOp_le hφ hA f)

/-- `f ↦ rawOp φ A f`, as a bounded linear operator on `L^p(ℝ₊)`, of norm at most `1`. -/
def op (φ : ℝ → ℝ) (hφ : MeasurePreserving φ volume volume) (A : Set ℝ)
    (hA : MeasurableSet A) : Lp ℝ p muPlus →L[ℝ] Lp ℝ p muPlus :=
  LinearMap.mkContinuous
    { toFun := opFun φ hφ A hA
      map_add' := opFun_add hφ hA
      map_smul' := fun c f => by simpa using opFun_smul hφ hA c f }
    1 (fun f => by simpa using norm_opFun_le hφ hA f)

lemma op_apply (hφ : MeasurePreserving φ volume volume) (hA : MeasurableSet A)
    (f : Lp ℝ p muPlus) : op φ hφ A hA f = opFun φ hφ A hA f := rfl

lemma op_ae (hφ : MeasurePreserving φ volume volume) (hA : MeasurableSet A)
    (f : Lp ℝ p muPlus) : ⇑(op φ hφ A hA f) =ᵐ[muPlus] rawOp φ A ⇑f := by
  rw [op_apply]
  exact opFun_ae hφ hA f

lemma op_congr (hφ : MeasurePreserving φ volume volume) (hA : MeasurableSet A)
    (f : Lp ℝ p muPlus) {g : ℝ → ℝ} (h : ⇑f =ᵐ[muPlus] g) :
    ⇑(op φ hφ A hA f) =ᵐ[muPlus] rawOp φ A g := by
  rw [op_apply]
  exact opFun_congr hφ hA f h

lemma norm_op_le (hφ : MeasurePreserving φ volume volume) (hA : MeasurableSet A) :
    ‖(op φ hφ A hA : Lp ℝ p muPlus →L[ℝ] Lp ℝ p muPlus)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [op_apply, one_mul]
  exact norm_opFun_le hφ hA f

/-! ## The right-shift semigroup -/

variable (p) in
/-- The right shift `T t`: `(T t f)(s) = f (s - t)` for `s ≥ t`, `0` for `s < t`. -/
def shiftT (t : ℝ) : Lp ℝ p muPlus →L[ℝ] Lp ℝ p muPlus :=
  op (fun x => x - t) (measurePreserving_sub_right volume t) Set.univ MeasurableSet.univ

lemma shiftT_ae (t : ℝ) (f : Lp ℝ p muPlus) :
    ⇑(shiftT p t f) =ᵐ[muPlus] rawOp (fun x => x - t) Set.univ ⇑f :=
  op_ae (measurePreserving_sub_right volume t) MeasurableSet.univ f

lemma shiftT_congr (t : ℝ) (f : Lp ℝ p muPlus) {g : ℝ → ℝ} (h : ⇑f =ᵐ[muPlus] g) :
    ⇑(shiftT p t f) =ᵐ[muPlus] rawOp (fun x => x - t) Set.univ g :=
  op_congr (measurePreserving_sub_right volume t) MeasurableSet.univ f h

theorem shiftT_zero : shiftT p 0 = ContinuousLinearMap.id ℝ (Lp ℝ p muPlus) := by
  apply ContinuousLinearMap.ext
  intro f
  rw [ContinuousLinearMap.id_apply]
  apply Lp.ext
  filter_upwards [shiftT_ae 0 f, ae_restrict_mem measurableSet_Ici] with x e1 hx
  rw [e1, rawT_apply, sub_zero, zext_of_nonneg (⇑f) x hx]

theorem shiftT_add {t s : ℝ} (_ht : 0 ≤ t) (hs : 0 ≤ s) :
    shiftT p (t + s) = (shiftT p t).comp (shiftT p s) := by
  apply ContinuousLinearMap.ext
  intro f
  rw [ContinuousLinearMap.comp_apply]
  apply Lp.ext
  filter_upwards [shiftT_ae (t + s) f, shiftT_congr t (shiftT p s f) (shiftT_ae s f)]
    with x e1 e2
  rw [e1, e2, rawT_apply, rawT_apply]
  by_cases hx : 0 ≤ x - t
  · rw [zext_of_nonneg _ (x - t) hx, rawT_apply, show x - t - s = x - (t + s) by ring]
  · rw [zext_of_neg _ (x - t) (not_le.1 hx), zext_of_neg (⇑f) (x - (t + s)) (by linarith)]

/-! ### Strong continuity, from the continuity of translations in `L^p(ℝ)` -/

/-- The translations `x ↦ x - t`, as continuous maps depending continuously on `t`. -/
def transl : C(ℝ, C(ℝ, ℝ)) :=
  ContinuousMap.curry ⟨fun q : ℝ × ℝ => q.2 - q.1, continuous_snd.sub continuous_fst⟩

lemma transl_apply (t x : ℝ) : transl t x = x - t := by
  simp [transl]

lemma measurePreserving_transl (t : ℝ) : MeasurePreserving (transl t) volume volume := by
  have h : ⇑(transl t) = fun x => x - t := funext (transl_apply t)
  rw [h]
  exact measurePreserving_sub_right volume t

/-- The zero extension of `y`, as an element of `L^p(ℝ)`. -/
def zextLp (y : Lp ℝ p muPlus) : Lp ℝ p (volume : Measure ℝ) :=
  (memLp_zext y).toLp (zext ⇑y)

omit [Fact (1 ≤ p)] in
lemma zextLp_ae (y : Lp ℝ p muPlus) : ⇑(zextLp y) =ᵐ[volume] zext ⇑y :=
  (memLp_zext y).coeFn_toLp

/-- The zero extension of `y`, translated by `t`, as an element of `L^p(ℝ)`. -/
def transLp (y : Lp ℝ p muPlus) (t : ℝ) : Lp ℝ p (volume : Measure ℝ) :=
  Lp.compMeasurePreserving (transl t) (measurePreserving_transl t) (zextLp y)

omit [Fact (1 ≤ p)] in
lemma transLp_ae (y : Lp ℝ p muPlus) (t : ℝ) :
    ⇑(transLp y t) =ᵐ[volume] zext ⇑y ∘ transl t := by
  have h1 : ⇑(transLp y t) =ᵐ[volume] ⇑(zextLp y) ∘ transl t :=
    Lp.coeFn_compMeasurePreserving (zextLp y) (measurePreserving_transl t)
  exact h1.trans ((measurePreserving_transl t).quasiMeasurePreserving.ae_eq_comp (zextLp_ae y))

/-- `‖T t y - y‖_{L^p(ℝ₊)} ≤ ‖τ_t Y - Y‖_{L^p(ℝ)}`, where `Y` is the zero extension of `y`. -/
lemma norm_shiftT_sub_le (y : Lp ℝ p muPlus) (t : ℝ) :
    ‖shiftT p t y - y‖ ≤ ‖transLp y t - transLp y 0‖ := by
  have hae : ⇑(shiftT p t y - y) =ᵐ[muPlus] ⇑(transLp y t - transLp y 0) := by
    have a1 := Lp.coeFn_sub (shiftT p t y) y
    have a2 := shiftT_ae t y
    have a3 := ae_restrict_of_ae (s := Set.Ici (0 : ℝ))
      (Lp.coeFn_sub (transLp y t) (transLp y 0))
    have a4 := ae_restrict_of_ae (s := Set.Ici (0 : ℝ)) (transLp_ae y t)
    have a5 := ae_restrict_of_ae (s := Set.Ici (0 : ℝ)) (transLp_ae y 0)
    have a6 : ∀ᵐ x ∂muPlus, x ∈ Set.Ici (0 : ℝ) := ae_restrict_mem measurableSet_Ici
    filter_upwards [a1, a2, a3, a4, a5, a6] with x e1 e2 e3 e4 e5 hx
    rw [e1, Pi.sub_apply, e2, e3, Pi.sub_apply, e4, e5, Function.comp_apply,
      Function.comp_apply, transl_apply, transl_apply, rawT_apply, sub_zero,
      zext_of_nonneg (⇑y) x hx]
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae hae]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top _)
    (eLpNorm_mono_measure _ Measure.restrict_le_self)

/-- Strong continuity of the right shift (uses `p ≠ ∞`). -/
theorem shiftT_tendsto (hp : p ≠ ∞) (y : Lp ℝ p muPlus) :
    Tendsto (fun t => shiftT p t y) (nhdsWithin 0 (Set.Ici 0)) (𝓝 y) := by
  -- continuity of translations in `L^p(ℝ)`
  have hlim : Tendsto (fun t => transLp y t) (𝓝 0) (𝓝 (transLp y 0)) := by
    unfold transLp
    exact Filter.Tendsto.compMeasurePreservingLp tendsto_const_nhds
      (transl.continuous.tendsto 0) measurePreserving_transl (measurePreserving_transl 0) hp
  have hlim' : Tendsto (fun t => ‖transLp y t - transLp y 0‖) (nhdsWithin 0 (Set.Ici 0)) (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero.1 hlim).mono_left nhdsWithin_le_nhds
  apply tendsto_iff_norm_sub_tendsto_zero.2
  exact squeeze_zero (fun t => norm_nonneg _) (fun t => norm_shiftT_sub_le y t) hlim'

/-- The right-shift semigroup on `L^p(ℝ₊)`, for `p < ∞`. -/
def rightShift (hp : p ≠ ∞) : C0Semigroup ℝ (Lp ℝ p muPlus) where
  T := shiftT p
  T_zero := shiftT_zero
  T_add := fun _ _ ht hs => shiftT_add ht hs
  T_cont := shiftT_tendsto hp

/-! ## The input maps -/

variable (p) in
/-- The input map `Φ t`: `(Φ t u)(s) = u (t - s)` for `0 < s ≤ t`, `0` otherwise. -/
def inputPhi (t : ℝ) : Lp ℝ p muPlus →L[ℝ] Lp ℝ p muPlus :=
  op (fun x => t - x) (Measure.measurePreserving_sub_left volume t) (Set.Ioc 0 t)
    measurableSet_Ioc

lemma inputPhi_ae (t : ℝ) (f : Lp ℝ p muPlus) :
    ⇑(inputPhi p t f) =ᵐ[muPlus] rawOp (fun x => t - x) (Set.Ioc 0 t) ⇑f :=
  op_ae (Measure.measurePreserving_sub_left volume t) measurableSet_Ioc f

lemma inputPhi_congr (t : ℝ) (f : Lp ℝ p muPlus) {g : ℝ → ℝ} (h : ⇑f =ᵐ[muPlus] g) :
    ⇑(inputPhi p t f) =ᵐ[muPlus] rawOp (fun x => t - x) (Set.Ioc 0 t) g :=
  op_congr (Measure.measurePreserving_sub_left volume t) measurableSet_Ioc f h

/-- Composition property: `Φ (τ + t) (u ⋄_τ v) = T t (Φ τ u) + Φ t v`. -/
theorem inputPhi_composition {τ t : ℝ} (hτ : 0 ≤ τ) (ht : 0 ≤ t) (u v w : Lp ℝ p muPlus)
    (hw : ⇑w =ᵐ[muPlus] concat τ ⇑u ⇑v) :
    inputPhi p (τ + t) w = shiftT p t (inputPhi p τ u) + inputPhi p t v := by
  apply Lp.ext
  have e1 := inputPhi_congr (τ + t) w hw
  have e2 := shiftT_congr t (inputPhi p τ u) (inputPhi_ae τ u)
  have e3 := inputPhi_ae t v
  have e4 := Lp.coeFn_add (shiftT p t (inputPhi p τ u)) (inputPhi p t v)
  filter_upwards [e1, e2, e3, e4] with x h1 h2 h3 h4
  rw [h1, h4, Pi.add_apply, h2, h3]
  exact concat_pointwise ⇑u ⇑v hτ ht x

/-- The abstract linear control system of Proposition 3.1 (right shift on `L^p(ℝ₊)`). -/
def shiftSystem (hp : p ≠ ∞) : ALCS ℝ (Lp ℝ p muPlus) ℝ p where
  toC0Semigroup := rightShift hp
  Φ := inputPhi p
  composition := fun _ _ hτ ht u v w hw => inputPhi_composition hτ ht u v w hw

/-! ## `κ(t) = 1` for all `t > 0` -/

lemma p_ne_zero : p ≠ 0 := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  exact (lt_of_lt_of_le zero_lt_one hp1).ne'

lemma muPlus_Ico (t : ℝ) : muPlus (Set.Ico 0 t) = ENNReal.ofReal t := by
  have hsub : Set.Ico (0 : ℝ) t ⊆ Set.Ici 0 := by
    intro x hx
    exact Set.mem_Ici.2 hx.1
  rw [Measure.restrict_apply measurableSet_Ico, Set.inter_eq_left.2 hsub, Real.volume_Ico,
    sub_zero]

lemma muPlus_Ioc (t : ℝ) : muPlus (Set.Ioc 0 t) = ENNReal.ofReal t := by
  have hsub : Set.Ioc (0 : ℝ) t ⊆ Set.Ici 0 := by
    intro x hx
    exact Set.mem_Ici.2 hx.1.le
  rw [Measure.restrict_apply measurableSet_Ioc, Set.inter_eq_left.2 hsub, Real.volume_Ioc,
    sub_zero]

lemma muPlus_Ico_ne_top (t : ℝ) : muPlus (Set.Ico 0 t) ≠ ∞ := by
  rw [muPlus_Ico]
  exact ENNReal.ofReal_ne_top

lemma muPlus_Ioc_ne_top (t : ℝ) : muPlus (Set.Ioc 0 t) ≠ ∞ := by
  rw [muPlus_Ioc]
  exact ENNReal.ofReal_ne_top

variable (p) in
/-- The test input `1_{[0,t)}`. -/
def testInput (t : ℝ) : Lp ℝ p muPlus :=
  indicatorConstLp p (measurableSet_Ico : MeasurableSet (Set.Ico (0 : ℝ) t))
    (muPlus_Ico_ne_top t) (1 : ℝ)

variable (p) in
/-- The corresponding output `1_{(0,t]}`. -/
def testOutput (t : ℝ) : Lp ℝ p muPlus :=
  indicatorConstLp p (measurableSet_Ioc : MeasurableSet (Set.Ioc (0 : ℝ) t))
    (muPlus_Ioc_ne_top t) (1 : ℝ)

lemma inputPhi_testInput (t : ℝ) : inputPhi p t (testInput p t) = testOutput p t := by
  apply Lp.ext
  have hu : ⇑(testInput p t) =ᵐ[muPlus] (Set.Ico 0 t).indicator (fun _ => (1 : ℝ)) :=
    indicatorConstLp_coeFn
  have hw : ⇑(testOutput p t) =ᵐ[muPlus] (Set.Ioc 0 t).indicator (fun _ => (1 : ℝ)) :=
    indicatorConstLp_coeFn
  filter_upwards [inputPhi_congr t (testInput p t) hu, hw] with x e1 e2
  rw [e1, e2]
  by_cases hx : 0 < x ∧ x ≤ t
  · have h1 : t - x ∈ Set.Ico 0 t := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have h2 : x ∈ Set.Ioc 0 t := hx
    rw [rawPhi_of_mem _ t x hx, Set.indicator_of_mem h1, Set.indicator_of_mem h2]
  · have h2 : x ∉ Set.Ioc 0 t := hx
    rw [rawPhi_of_not _ t x hx, Set.indicator_of_notMem h2]

lemma norm_testInput (hp : p ≠ ∞) {t : ℝ} (ht : 0 ≤ t) :
    ‖testInput p t‖ = t ^ (1 / p.toReal) := by
  rw [testInput, norm_indicatorConstLp p_ne_zero hp, norm_one, one_mul, measureReal_def,
    muPlus_Ico, ENNReal.toReal_ofReal ht]

lemma norm_testOutput (hp : p ≠ ∞) {t : ℝ} (ht : 0 ≤ t) :
    ‖testOutput p t‖ = t ^ (1 / p.toReal) := by
  rw [testOutput, norm_indicatorConstLp p_ne_zero hp, norm_one, one_mul, measureReal_def,
    muPlus_Ioc, ENNReal.toReal_ofReal ht]

lemma norm_inputPhi_le (t : ℝ) : ‖inputPhi p t‖ ≤ 1 :=
  norm_op_le (Measure.measurePreserving_sub_left volume t) measurableSet_Ioc

lemma one_le_norm_inputPhi (hp : p ≠ ∞) {t : ℝ} (ht : 0 < t) : 1 ≤ ‖inputPhi p t‖ := by
  -- `‖Φ t u_t‖ = ‖u_t‖ > 0` for the test input `u_t`
  have h1 : ‖inputPhi p t (testInput p t)‖ ≤ ‖inputPhi p t‖ * ‖testInput p t‖ :=
    (inputPhi p t).le_opNorm (testInput p t)
  rw [inputPhi_testInput, norm_testOutput hp ht.le, ← norm_testInput hp ht.le] at h1
  have hpos : 0 < ‖testInput p t‖ := by
    rw [norm_testInput hp ht.le]
    exact Real.rpow_pos_of_pos ht _
  by_contra h
  have h2 : ‖inputPhi p t‖ * ‖testInput p t‖ < 1 * ‖testInput p t‖ :=
    mul_lt_mul_of_pos_right (not_le.1 h) hpos
  linarith

/-- `κ(t) = ‖Φ t‖ = 1` for all `t > 0`. -/
theorem norm_Phi_eq_one (hp : p ≠ ∞) {t : ℝ} (ht : 0 < t) : ‖(shiftSystem hp).Φ t‖ = 1 :=
  le_antisymm (norm_inputPhi_le t) (one_le_norm_inputPhi hp ht)

/-- The system of Proposition 3.1 is not of the zero-class (Definition 1.4). -/
theorem not_zero_class (hp : p ≠ ∞) : ¬ (shiftSystem hp).IsZeroClass := by
  intro h0
  have h : Tendsto (fun t => ‖(shiftSystem hp).Φ t‖) (nhdsWithin 0 (Set.Ici 0)) (𝓝 0) := h0
  have h1 : Tendsto (fun t => ‖(shiftSystem hp).Φ t‖) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) :=
    h.mono_left (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)
  have hev : (fun _ : ℝ => (1 : ℝ)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      fun t => ‖(shiftSystem hp).Φ t‖ := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (norm_Phi_eq_one hp ht).symm
  have h2 : Tendsto (fun t => ‖(shiftSystem hp).Φ t‖) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 1) :=
    tendsto_const_nhds.congr' hev
  have h3 : (1 : ℝ) = 0 := tendsto_nhds_unique h2 h1
  exact one_ne_zero h3

end Operators

end ShiftExample

open ShiftExample

/-- **Proposition 3.1** (`prop:example-finite-p-not-zero-class`). For `p ∈ [1, ∞)`, there
exist (real) Banach spaces `X`, `U` and an abstract linear control system `(T, Φ)` with
`κ(t) = ‖Φ t‖ = 1` for all `t > 0`. -/
theorem exists_system_norm_Phi_eq_one (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    ∃ (X : Type) (_ : NormedAddCommGroup X) (_ : NormedSpace ℝ X) (_ : CompleteSpace X)
      (U : Type) (_ : NormedAddCommGroup U) (_ : NormedSpace ℝ U) (_ : CompleteSpace U)
      (S : ALCS ℝ X U p), ∀ t : ℝ, 0 < t → ‖S.Φ t‖ = 1 :=
  ⟨Lp ℝ p muPlus, inferInstance, inferInstance, inferInstance,
    ℝ, inferInstance, inferInstance, inferInstance,
    shiftSystem hp, fun _ ht => norm_Phi_eq_one hp ht⟩

end

end

end AbstractLinearControl
