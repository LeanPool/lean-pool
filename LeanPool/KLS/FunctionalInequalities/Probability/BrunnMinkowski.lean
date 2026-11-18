/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.Line.BrunnMinkowski
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Finite-dimensional Prékopa–Leindler and Brunn–Minkowski

The finite-dimensional inequalities follow from the line inequality by product induction and
transport. Existing Analysis declaration names are retained; no log-concavity assumption is added.
`lintegral_prekopaLeindler` states the `ℝ≥0∞`-valued inequality for an arbitrary additive Haar
measure, and `lintegral_slice_prekopaLeindler` its consequence for integrals over parallel affine
slices `W + a` of a linear subspace `W` (the slice step of the equality case of Prékopa–Leindler
used for uniqueness of moment measures, Cordero-Erausquin–Klartag arXiv:1304.0630v1, Theorem 2).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff Pointwise

namespace FunctionalInequalities

universe u

namespace Analysis

section Isodiametric

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The `ℝ≥0∞`-valued Prékopa–Leindler property at exponent `t`. -/
private def IsPL (X : Type*) [AddCommGroup X] [Module ℝ X] [MeasurableSpace X]
    (μ : Measure X) (t : ℝ) : Prop :=
  ∀ f g h : X → ℝ≥0∞, Measurable f → Measurable g → Measurable h →
    (∀ x y, f x ^ t * g y ^ (1 - t) ≤ h (t • x + (1 - t) • y)) →
    (∫⁻ x, f x ∂μ) ^ t * (∫⁻ y, g y ∂μ) ^ (1 - t) ≤ ∫⁻ z, h z ∂μ

private theorem iSup_min_natCast (a : ℝ≥0∞) : ⨆ n : ℕ, min a (n : ℝ≥0∞) = a := by
  refine le_antisymm (iSup_le fun n => min_le_left _ _) ?_
  by_cases ha : a = ⊤
  · subst ha
    have hmt : ∀ n : ℕ, min (⊤ : ℝ≥0∞) (n : ℝ≥0∞) = (n : ℝ≥0∞) := fun n => min_eq_right le_top
    simp_rw [hmt]
    exact le_of_eq ENNReal.iSup_natCast.symm
  · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt ha
    exact le_iSup_of_le n (le_min le_rfl hn.le)

private theorem isPL_real {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : IsPL ℝ (volume : Measure ℝ) t := by
  have ht1' : (0 : ℝ) < 1 - t := by linarith
  intro f g h hf hg hh hfgh
  have hmin : ∀ (u : ℝ → ℝ≥0∞) (N : ℕ) (x : ℝ), min (u x) (N : ℝ≥0∞) ≠ ⊤ := by
    intro u N x
    exact ne_top_of_le_ne_top (ENNReal.natCast_ne_top N) (min_le_right _ _)
  have hstep :
    ∀ N : ℕ,
      (∫⁻ x, min (f x) (N : ℝ≥0∞)) ^ t * (∫⁻ y, min (g y) (N : ℝ≥0∞)) ^ (1 - t) ≤ ∫⁻ z, h z := by
    intro N
    have hkey :
      ∀ x y : ℝ,
        (min (f x) (N : ℝ≥0∞)) ^ t * (min (g y) (N : ℝ≥0∞)) ^ (1 - t) ≤
          min (h (t * x + (1 - t) * y)) (N : ℝ≥0∞) := by
      intro x y
      refine le_min ?_ ?_
      · refine
          le_trans
            (mul_le_mul' (ENNReal.rpow_le_rpow (min_le_left _ _) ht0.le)
              (ENNReal.rpow_le_rpow (min_le_left _ _) ht1'.le))
            ?_
        simpa using hfgh x y
      · refine
          le_trans
            (mul_le_mul' (ENNReal.rpow_le_rpow (min_le_right _ _) ht0.le)
              (ENNReal.rpow_le_rpow (min_le_right _ _) ht1'.le))
            ?_
        rw [← ENNReal.rpow_add_of_nonneg _ _ ht0.le ht1'.le]
        simp
    have hreal :
      ∀ x y : ℝ,
        ((min (f x) (N : ℝ≥0∞)).toReal) ^ t * ((min (g y) (N : ℝ≥0∞)).toReal) ^ (1 - t) ≤
          (min (h (t * x + (1 - t) * y)) (N : ℝ≥0∞)).toReal := by
      intro x y
      rw [ENNReal.toReal_rpow, ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
      refine ENNReal.toReal_mono (hmin h N _) (hkey x y)
    have hmeas :
      ∀ u : ℝ → ℝ≥0∞, Measurable u → Measurable fun x => (min (u x) (N : ℝ≥0∞)).toReal :=
      fun u hu => (hu.min measurable_const).ennreal_toReal
    have hPL :=
      Probability.Line.prekopaLeindler (hmeas f hf) (hmeas g hg) (hmeas h hh)
        (fun x => ENNReal.toReal_nonneg) (fun y => ENNReal.toReal_nonneg) ht0 ht1 hreal
    have hof :
      ∀ (u : ℝ → ℝ≥0∞) (x : ℝ),
        ENNReal.ofReal ((min (u x) (N : ℝ≥0∞)).toReal) = min (u x) (N : ℝ≥0∞) :=
      fun u x => ENNReal.ofReal_toReal (hmin u N x)
    simp only [hof] at hPL
    exact hPL.trans (lintegral_mono fun z => min_le_left _ _)
  have hmono : ∀ u : ℝ → ℝ≥0∞, Monotone fun N : ℕ => ∫⁻ x, min (u x) (N : ℝ≥0∞) :=
    fun u a b hab => lintegral_mono fun x => min_le_min le_rfl (by exact_mod_cast hab)
  have hsup :
    ∀ u : ℝ → ℝ≥0∞, Measurable u → (⨆ N : ℕ, ∫⁻ x, min (u x) (N : ℝ≥0∞)) = ∫⁻ x, u x := by
    intro u hu
    rw [←
      lintegral_iSup (fun N => hu.min measurable_const)
        (fun a b hab x => min_le_min le_rfl (by exact_mod_cast hab))]
    exact lintegral_congr fun x => iSup_min_natCast (u x)
  rw [← hsup f hf, ← hsup g hg]
  simp_rw (config := { congrConsts := false }) [← ENNReal.orderIsoRpow_apply t ht0, ←
    ENNReal.orderIsoRpow_apply (1 - t) ht1']
  rw [(ENNReal.orderIsoRpow _ ht0).map_iSup _, (ENNReal.orderIsoRpow _ ht1').map_iSup _,
    ENNReal.iSup_mul]
  refine iSup_le fun N => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun M => ?_
  exact
    le_trans
      (mul_le_mul' (ENNReal.rpow_le_rpow (hmono f (le_max_left N M)) ht0.le)
        (ENNReal.rpow_le_rpow (hmono g (le_max_right N M)) ht1'.le))
      (hstep (max N M))

section MeasurableSpace

variable {X Y : Type*}
  [AddCommGroup X] [Module ℝ X] [MeasurableSpace X] [AddCommGroup Y] [Module ℝ Y]
  [MeasurableSpace Y]

private theorem IsPL.comp {μ : Measure X} {ν : Measure Y} {t : ℝ}
    (hX : IsPL X μ t) {e : X → Y} (hmp : MeasurePreserving e μ ν)
    (hlin : ∀ (a b : ℝ) (x y : X), e (a • x + b • y) = a • e x + b • e y) : IsPL Y ν t := by
  intro f g h hf hg hh hfgh
  have hyp : ∀ x y : X, (f ∘ e) x ^ t * ((g ∘ e) y) ^ (1 - t)
      ≤ (h ∘ e) (t • x + (1 - t) • y) := by
    intro x y
    simp only [Function.comp_apply, hlin]
    exact hfgh (e x) (e y)
  have h1 := hX (f ∘ e) (g ∘ e) (h ∘ e) (hf.comp hmp.measurable) (hg.comp hmp.measurable)
    (hh.comp hmp.measurable) hyp
  simp only [Function.comp_apply] at h1
  rwa [hmp.lintegral_comp hf, hmp.lintegral_comp hg, hmp.lintegral_comp hh] at h1

private theorem IsPL.symm {μ : Measure X} {ν : Measure Y} {t : ℝ}
    (hY : IsPL Y ν t) (e : X ≃ᵐ Y) (hmp : MeasurePreserving e μ ν)
    (hlin : ∀ (a b : ℝ) (x y : X), e (a • x + b • y) = a • e x + b • e y) : IsPL X μ t := by
  refine hY.comp (e := ⇑e.symm) (hmp.symm e) ?_
  intro a b x y
  refine e.injective ?_
  rw [hlin, e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply]

private theorem IsPL.prod {μ : Measure X} {ν : Measure Y}
    [SFinite ν] {t : ℝ}
    (hX : IsPL X μ t) (hY : IsPL Y ν t) : IsPL (X × Y) (μ.prod ν) t := by
  intro f g h hf hg hh hfgh
  have hslice : ∀ (u : X × Y → ℝ≥0∞), Measurable u → ∀ x : X, Measurable fun y => u (x, y) :=
    fun u hu x => hu.comp (measurable_const.prodMk measurable_id)
  have hFGH : ∀ x₁ x₂ : X,
      (∫⁻ y, f (x₁, y) ∂ν) ^ t * (∫⁻ y, g (x₂, y) ∂ν) ^ (1 - t)
        ≤ ∫⁻ y, h (t • x₁ + (1 - t) • x₂, y) ∂ν := by
    intro x₁ x₂
    refine hY (fun y => f (x₁, y)) (fun y => g (x₂, y))
      (fun y => h (t • x₁ + (1 - t) • x₂, y)) (hslice f hf x₁) (hslice g hg x₂)
      (hslice h hh _) ?_
    intro y₁ y₂
    have hxy := hfgh (x₁, y₁) (x₂, y₂)
    simpa [Prod.smul_mk, Prod.mk_add_mk] using hxy
  have h1 := hX (fun x => ∫⁻ y, f (x, y) ∂ν) (fun x => ∫⁻ y, g (x, y) ∂ν)
    (fun x => ∫⁻ y, h (x, y) ∂ν) hf.lintegral_prod_right' hg.lintegral_prod_right'
    hh.lintegral_prod_right' hFGH
  rwa [← lintegral_prod _ hf.aemeasurable, ← lintegral_prod _ hg.aemeasurable,
    ← lintegral_prod _ hh.aemeasurable] at h1

end MeasurableSpace

private theorem isPL_pi {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∀ n : ℕ, IsPL (Fin n → ℝ) (volume : Measure (Fin n → ℝ)) t
  | 0 => by
      intro f g h hf hg hh hfgh
      rw [Measure.volume_pi_eq_dirac 0, lintegral_dirac' _ hf, lintegral_dirac' _ hg,
        lintegral_dirac' _ hh]
      simpa using hfgh 0 0
  | (n + 1) => by
      have hprod : IsPL (ℝ × (Fin n → ℝ)) (volume : Measure (ℝ × (Fin n → ℝ))) t := by
        rw [show (volume : Measure (ℝ × (Fin n → ℝ)))
          = (volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)) from rfl]
        exact (isPL_real ht0 ht1).prod (isPL_pi ht0 ht1 n)
      exact hprod.symm (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0)
        (volume_preserving_piFinSuccAbove (fun _ => ℝ) 0) (by intro a b x y; rfl)

private theorem isPL_euclidean {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (n : ℕ) :
    IsPL (EuclideanSpace ℝ (Fin n)) (volume : Measure (EuclideanSpace ℝ (Fin n))) t :=
  (isPL_pi ht0 ht1 n).comp (PiLp.volume_preserving_toLp (Fin n)) (by intro a b x y; rfl)

private theorem isPL_volume {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) : IsPL E (volume : Measure E) t :=
  (isPL_euclidean ht0 ht1 (Module.finrank ℝ E)).comp
    ((stdOrthonormalBasis ℝ E).measurePreserving_repr_symm)
    (by intro a b x y; simp)

/-- **Prékopa–Leindler inequality** on a finite-dimensional inner-product space, for Lebesgue
measure.  The one-dimensional case is `FunctionalInequalities.Probability.Line.prekopaLeindler`;
the general case follows by induction on the dimension and Fubini along a line. -/
theorem prekopaLeindler {f g h : V → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) (hfgh : ∀ x y, f x ^ t * g y ^ (1 - t) ≤ h (t • x + (1 - t) • y)) :
    (∫⁻ x, ENNReal.ofReal (f x)) ^ t * (∫⁻ y, ENNReal.ofReal (g y)) ^ (1 - t) ≤
      ∫⁻ z, ENNReal.ofReal (h z) := by
  have ht1' : (0 : ℝ) < 1 - t := by linarith
  refine
    isPL_volume ht0 ht1 (fun x => ENNReal.ofReal (f x)) (fun y => ENNReal.ofReal (g y))
      (fun z => ENNReal.ofReal (h z)) hf.ennreal_ofReal hg.ennreal_ofReal hh.ennreal_ofReal ?_
  intro x y
  rw [ENNReal.ofReal_rpow_of_nonneg (hf0 x) ht0.le,
    ENNReal.ofReal_rpow_of_nonneg (hg0 y) ht1'.le, ←
    ENNReal.ofReal_mul (Real.rpow_nonneg (hf0 x) t)]
  exact ENNReal.ofReal_le_ofReal (hfgh x y)

/-- **Prékopa–Leindler inequality** for `ℝ≥0∞`-valued functions and an arbitrary additive Haar
measure `m` on a finite-dimensional inner-product space: if
`f x ^ t * g y ^ (1 - t) ≤ h (t x + (1 - t) y)` for all `x, y`, with `0 < t < 1`, then
`(∫ f dm) ^ t (∫ g dm) ^ (1 - t) ≤ ∫ h dm`. Infinite values and infinite integrals are allowed. -/
theorem lintegral_prekopaLeindler (m : Measure V) [m.IsAddHaarMeasure] {f g h : V → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) (hfgh : ∀ x y, f x ^ t * g y ^ (1 - t) ≤ h (t • x + (1 - t) • y)) :
    (∫⁻ x, f x ∂m) ^ t * (∫⁻ y, g y ∂m) ^ (1 - t) ≤ ∫⁻ z, h z ∂m := by
  have ht1' : (0:ℝ) ≤ 1 - t := by linarith
  have hm : m = Measure.addHaarScalarFactor m volume • volume :=
    Measure.isAddLeftInvariant_eq_smul m volume
  set c : ℝ≥0∞ := (Measure.addHaarScalarFactor m volume : ℝ≥0∞)
  have hPL := isPL_volume (E := V) ht0 ht1 f g h hf hg hh hfgh
  rw [hm, lintegral_smul_measure, lintegral_smul_measure, lintegral_smul_measure]
  change (c * ∫⁻ x, f x) ^ t * (c * ∫⁻ y, g y) ^ (1 - t) ≤ c * ∫⁻ z, h z
  rw [ENNReal.mul_rpow_of_nonneg _ _ ht0.le, ENNReal.mul_rpow_of_nonneg _ _ ht1']
  calc c ^ t * (∫⁻ x, f x) ^ t * (c ^ (1 - t) * (∫⁻ y, g y) ^ (1 - t))
      = c ^ (t + (1 - t)) * ((∫⁻ x, f x) ^ t * (∫⁻ y, g y) ^ (1 - t)) := by
        rw [ENNReal.rpow_add_of_nonneg _ _ ht0.le ht1']
        ring
    _ ≤ c * ∫⁻ z, h z := by
        rw [add_sub_cancel, ENNReal.rpow_one]
        exact mul_le_mul_right hPL c

/-- **Prékopa–Leindler along parallel affine slices.** For a linear subspace `W` with an additive
Haar measure `m`, the slice integrals `a ↦ ∫_W f(z + a) dm(z)` of functions satisfying the
Prékopa–Leindler hypothesis at exponent `t ∈ (0, 1)` satisfy the same hypothesis:
`(∫_W f(z + a))^t (∫_W g(z + b))^{1-t} ≤ ∫_W h(z + t a + (1 - t) b)`. -/
theorem lintegral_slice_prekopaLeindler (W : Submodule ℝ V) (m : Measure W)
    [m.IsAddHaarMeasure] {f g h : V → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hfgh : ∀ x y, f x ^ t * g y ^ (1 - t) ≤ h (t • x + (1 - t) • y)) (a b : V) :
    (∫⁻ z, f ((z : V) + a) ∂m) ^ t * (∫⁻ z, g ((z : V) + b) ∂m) ^ (1 - t) ≤
      ∫⁻ z, h ((z : V) + (t • a + (1 - t) • b)) ∂m := by
  have hs : ∀ (u : V → ℝ≥0∞) (c : V), Measurable u → Measurable fun z : W => u ((z : V) + c) :=
    fun u c hu => hu.comp (continuous_subtype_val.add continuous_const).measurable
  refine lintegral_prekopaLeindler m (hs f a hf) (hs g b hg) (hs h _ hh) ht0 ht1 ?_
  intro x y
  have harg : ((t • x + (1 - t) • y : W) : V) + (t • a + (1 - t) • b) =
      t • ((x : V) + a) + (1 - t) • ((y : V) + b) := by
    simp only [Submodule.coe_add, Submodule.coe_smul, smul_add]
    abel
  rw [harg]
  exact hfgh _ _

/-- The convolution integral of two measurable log-concave nonnegative densities is
log-concave. The extended-real formulation also covers integrals equal to infinity;
finiteness and smoothness are separate regularization obligations. -/
theorem lintegral_mul_translate_logConcave
    {p q : V → ENNReal} (hp : Measurable p) (hq : Measurable q)
    (hpLC : ∀ x y : V, ∀ t : ℝ, 0 < t → t < 1 →
      p x ^ t * p y ^ (1 - t) ≤ p (t • x + (1 - t) • y))
    (hqLC : ∀ x y : V, ∀ t : ℝ, 0 < t → t < 1 →
      q x ^ t * q y ^ (1 - t) ≤ q (t • x + (1 - t) • y))
    (a b : V) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (∫⁻ z, p z * q (a - z) ∂(volume : Measure V)) ^ t *
      (∫⁻ z, p z * q (b - z) ∂(volume : Measure V)) ^ (1 - t) ≤
        ∫⁻ z, p z * q ((t • a + (1 - t) • b) - z) ∂(volume : Measure V) := by
  have ht1' : 0 ≤ 1 - t := by linarith
  have hmeas (x : V) : Measurable (fun z : V => p z * q (x - z)) :=
    hp.mul (hq.comp (measurable_const.sub measurable_id))
  refine isPL_volume ht0 ht1 _ _ _ (hmeas a) (hmeas b)
    (hmeas (t • a + (1 - t) • b)) ?_
  intro x y
  have harg : t • (a - x) + (1 - t) • (b - y) =
      (t • a + (1 - t) • b) - (t • x + (1 - t) • y) := by
    simp only [smul_sub]
    abel
  calc
    (p x * q (a - x)) ^ t * (p y * q (b - y)) ^ (1 - t)
        = (p x ^ t * p y ^ (1 - t)) *
            (q (a - x) ^ t * q (b - y) ^ (1 - t)) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ ht0.le,
              ENNReal.mul_rpow_of_nonneg _ _ ht1']
            ac_rfl
    _ ≤ p (t • x + (1 - t) • y) *
        q (t • (a - x) + (1 - t) • (b - y)) :=
          mul_le_mul' (hpLC x y t ht0 ht1) (hqLC (a - x) (b - y) t ht0 ht1)
    _ = _ := by rw [harg]

/--
**Multiplicative Brunn–Minkowski inequality**: a convex combination of two nonempty measurable
sets carries at least the geometric mean of their volumes.  The combination set need not be
measurable; the outer-measure bound is what is used. -/
theorem volume_rpow_mul_le_volume_combination {S T : Set V} (hS : MeasurableSet S)
    (hSne : S.Nonempty) (hT : MeasurableSet T) (hTne : T.Nonempty) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) :
    volume S ^ t * volume T ^ (1 - t) ≤
      volume {z : V | ∃ x ∈ S, ∃ y ∈ T, z = t • x + (1 - t) • y} := by
  have ht1' : (0 : ℝ) < 1 - t := by linarith
  set C := {z : V | ∃ x ∈ S, ∃ y ∈ T, z = t • x + (1 - t) • y} with hC
  have hind :
    ∀ A : Set V,
      MeasurableSet A → ∫⁻ x, ENNReal.ofReal (A.indicator (fun _ => (1 : ℝ)) x) = volume A := by
    intro A hA
    rw [← lintegral_indicator_one hA]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ A <;> simp [hx]
  have key :
    ∀ K : Set V,
      K ⊆ S →
        IsCompact K →
          ∀ L : Set V, L ⊆ T → IsCompact L → volume K ^ t * volume L ^ (1 - t) ≤ volume C := by
    intro K hKS hK L hLT hL
    set D := t • K + (1 - t) • L with hD
    have hDc : IsCompact D := (hK.smul t).add (hL.smul (1 - t))
    have hDS : D ⊆ C := by
      rintro _ ⟨-, ⟨x, hx, rfl⟩, -, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨x, hKS hx, y, hLT hy, rfl⟩
    have hhyp :
      ∀ x y : V,
        (K.indicator (fun _ => (1 : ℝ)) x) ^ t * (L.indicator (fun _ => (1 : ℝ)) y) ^ (1 - t) ≤
          D.indicator (fun _ => (1 : ℝ)) (t • x + (1 - t) • y) := by
      intro x y
      by_cases hx : x ∈ K
      · by_cases hy : y ∈ L
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy,
            Set.indicator_of_mem
              (show t • x + (1 - t) • y ∈ D from
                ⟨t • x, ⟨x, hx, rfl⟩, (1 - t) • y, ⟨y, hy, rfl⟩, rfl⟩)]
          simp
        · rw [Set.indicator_of_notMem hy, Real.zero_rpow ht1'.ne', mul_zero]
          exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
      · rw [Set.indicator_of_notMem hx, Real.zero_rpow ht0.ne', zero_mul]
        exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hPL :=
      prekopaLeindler (measurable_const.indicator hK.measurableSet)
        (measurable_const.indicator hL.measurableSet)
        (measurable_const.indicator hDc.measurableSet)
        (fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x)
        (fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x) ht0 ht1 hhyp
    rw [hind K hK.measurableSet, hind L hL.measurableSet, hind D hDc.measurableSet] at hPL
    exact hPL.trans (measure_mono hDS)
  have hsup :
    ∀ U : Set V,
      MeasurableSet U →
        U.Nonempty →
          volume U =
            ⨆ K : { K : Set V // K ⊆ U ∧ IsCompact K ∧ K.Nonempty }, volume (K : Set V) := by
    intro U hU hUne
    refine le_antisymm ?_ (iSup_le fun K ↦ measure_mono K.2.1)
    rw [hU.measure_eq_iSup_isCompact volume]
    refine iSup_le fun K ↦ iSup_le fun hKU ↦ iSup_le fun hK ↦ ?_
    obtain ⟨x₀, hx₀⟩ := hUne
    exact
      le_iSup_of_le
        ⟨K ∪ { x₀ }, Set.union_subset hKU (by simpa using hx₀), hK.union isCompact_singleton,
          ⟨x₀, by simp⟩⟩
        (measure_mono Set.subset_union_left)
  obtain ⟨s₀, hs₀⟩ := hSne
  obtain ⟨t₀, ht₀⟩ := hTne
  have hnS : Nonempty { K : Set V // K ⊆ S ∧ IsCompact K ∧ K.Nonempty } :=
    ⟨⟨{ s₀ }, by simpa using hs₀, isCompact_singleton, ⟨s₀, rfl⟩⟩⟩
  have hnT : Nonempty { L : Set V // L ⊆ T ∧ IsCompact L ∧ L.Nonempty } :=
    ⟨⟨{ t₀ }, by simpa using ht₀, isCompact_singleton, ⟨t₀, rfl⟩⟩⟩
  rw [hsup S hS ⟨s₀, hs₀⟩, hsup T hT ⟨t₀, ht₀⟩]
  simp_rw (config := { congrConsts := false }) [← ENNReal.orderIsoRpow_apply t ht0, ←
    ENNReal.orderIsoRpow_apply (1 - t) ht1']
  rw [(ENNReal.orderIsoRpow _ ht0).map_iSup _, (ENNReal.orderIsoRpow _ ht1').map_iSup _,
    ENNReal.iSup_mul]
  refine iSup_le fun K ↦ ?_
  rw [ENNReal.mul_iSup]
  exact iSup_le fun L ↦ key (K : Set V) K.2.1 K.2.2.1 (L : Set V) L.2.1 L.2.2.1

/-- **Brunn–Minkowski inequality** in its additive form for nonempty compact sets in dimension
`n ≥ 1`: `|S|^{1/n} + |T|^{1/n} ≤ |S + T|^{1/n}`. -/
theorem volume_rpow_add_le_volume_add_rpow [Nontrivial V] {S T : Set V} (hS : IsCompact S)
    (hT : IsCompact T) (hSne : S.Nonempty) (hTne : T.Nonempty) :
    volume S ^ (1 / (Module.finrank ℝ V : ℝ)) + volume T ^ (1 / (Module.finrank ℝ V : ℝ)) ≤
      volume (S + T) ^ (1 / (Module.finrank ℝ V : ℝ)) := by
  have hmono : ∀ {A B : Set V}, A.Nonempty → volume B ≤ volume (A + B) := by
    rintro A B ⟨a, ha⟩
    have hsub : (a + ·) '' B ⊆ A + B := by rintro _ ⟨b, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
    calc
      volume B = volume ((a + ·) '' B) := by rw [Set.image_add_left, measure_preimage_add]
      _ ≤ volume (A + B) := measure_mono hsub
  have hmono' : volume S ≤ volume (S + T) := by rw [add_comm]; exact hmono hTne
  set n := Module.finrank ℝ V with hn
  have hn0 : 0 < n := Module.finrank_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hexp : (0 : ℝ) ≤ 1 / n := by
    positivity
  -- degenerate cases
  by_cases hA : volume S = 0
  · rw [hA, ENNReal.zero_rpow_of_pos (by positivity), zero_add]
    exact ENNReal.rpow_le_rpow (hmono hSne) hexp
  by_cases hB : volume T = 0
  · rw [hB, ENNReal.zero_rpow_of_pos (by positivity), add_zero]
    exact ENNReal.rpow_le_rpow hmono' hexp
  have hAtop : volume S ≠ ⊤ := hS.measure_lt_top.ne
  have hBtop : volume T ≠ ⊤ := hT.measure_lt_top.ne
  set α : ℝ := (volume S).toReal ^ ((1 : ℝ) / n) with hα
  set β : ℝ := (volume T).toReal ^ ((1 : ℝ) / n) with hβ
  have hApos : 0 < (volume S).toReal := ENNReal.toReal_pos hA hAtop
  have hBpos : 0 < (volume T).toReal := ENNReal.toReal_pos hB hBtop
  have hαpos : 0 < α := Real.rpow_pos_of_pos hApos _
  have hβpos : 0 < β := Real.rpow_pos_of_pos hBpos _
  have hαn : α ^ n = (volume S).toReal := by
    rw [hα, ← Real.rpow_natCast (_ ^ _) n, ← Real.rpow_mul hApos.le]
    rw [one_div, inv_mul_cancel₀ hnR.ne', Real.rpow_one]
  have hβn : β ^ n = (volume T).toReal := by
    rw [hβ, ← Real.rpow_natCast (_ ^ _) n, ← Real.rpow_mul hBpos.le]
    rw [one_div, inv_mul_cancel₀ hnR.ne', Real.rpow_one]
  have hαE : ENNReal.ofReal α = volume S ^ ((1 : ℝ) / n) := by
    rw [hα, ← ENNReal.ofReal_rpow_of_nonneg hApos.le hexp, ENNReal.ofReal_toReal hAtop]
  have hβE : ENNReal.ofReal β = volume T ^ ((1 : ℝ) / n) := by
    rw [hβ, ← ENNReal.ofReal_rpow_of_nonneg hBpos.le hexp, ENNReal.ofReal_toReal hBtop]
  set c : ℝ := α + β with hc
  have hcpos : 0 < c := by positivity
  set t : ℝ := α / c with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t < 1 := by rw [ht, div_lt_one hcpos, hc]; linarith
  have h1t : 1 - t = β / c := by rw [ht, hc]; field_simp; ring
  have e1 : t * α⁻¹ = c⁻¹ := by rw [ht]; field_simp
  have e2 : (1 - t) * β⁻¹ = c⁻¹ := by rw [h1t]; field_simp
  have hS'c : IsCompact (α⁻¹ • S) := by
    rw [← Set.image_smul];
    exact hS.image (continuous_const_smul _)
  have hT'c : IsCompact (β⁻¹ • T) := by
    rw [← Set.image_smul];
    exact hT.image (continuous_const_smul _)
  have hvolS' : volume (α⁻¹ • S) = 1 := by
    rw [Measure.addHaar_smul_of_nonneg _ (by positivity), inv_pow, hαn,
      ENNReal.ofReal_inv_of_pos hApos, ENNReal.ofReal_toReal hAtop,
      ENNReal.inv_mul_cancel hA hAtop]
  have hvolT' : volume (β⁻¹ • T) = 1 := by
    rw [Measure.addHaar_smul_of_nonneg _ (by positivity), inv_pow, hβn,
      ENNReal.ofReal_inv_of_pos hBpos, ENNReal.ofReal_toReal hBtop,
      ENNReal.inv_mul_cancel hB hBtop]
  have hset : {z : V | ∃ x ∈ α⁻¹ • S, ∃ y ∈ β⁻¹ • T, z = t • x + (1 - t) • y} = c⁻¹ • (S + T) := by
    ext z
    constructor
    · rintro ⟨-, ⟨x, hx, rfl⟩, -, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨x + y, ⟨x, hx, y, hy, rfl⟩, by rw [smul_smul, smul_smul, e1, e2, ← smul_add]⟩
    · rintro ⟨-, ⟨x, hx, y, hy, rfl⟩, rfl⟩
      exact
        ⟨α⁻¹ • x, ⟨x, hx, rfl⟩, β⁻¹ • y, ⟨y, hy, rfl⟩, by
          rw [smul_smul, smul_smul, e1, e2, ← smul_add]⟩
  have hBM :=
    volume_rpow_mul_le_volume_combination hS'c.measurableSet (hSne.image _) hT'c.measurableSet
      (hTne.image _) ht0 ht1
  rw [hvolS', hvolT', ENNReal.one_rpow, ENNReal.one_rpow, one_mul, hset,
    Measure.addHaar_smul_of_nonneg _ (by positivity : (0 : ℝ) ≤ c⁻¹), inv_pow,
    ENNReal.ofReal_inv_of_pos (by positivity)] at hBM
  have hK0 : ENNReal.ofReal (c ^ n) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hKtop : ENNReal.ofReal (c ^ n) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmain : ENNReal.ofReal (c ^ n) ≤ volume (S + T) := by
    calc
      ENNReal.ofReal (c ^ n) = ENNReal.ofReal (c ^ n) * 1 := (mul_one _).symm
      _ ≤ ENNReal.ofReal (c ^ n) * ((ENNReal.ofReal (c ^ n))⁻¹ * volume (S + T)) := by gcongr
      _ = volume (S + T) := by rw [← mul_assoc, ENNReal.mul_inv_cancel hK0 hKtop, one_mul]
  calc
    volume S ^ ((1 : ℝ) / n) + volume T ^ ((1 : ℝ) / n) = ENNReal.ofReal α + ENNReal.ofReal β := by
      rw [hαE, hβE]
    _ = ENNReal.ofReal c := (ENNReal.ofReal_add hαpos.le hβpos.le).symm
    _ = ENNReal.ofReal (c ^ n) ^ ((1 : ℝ) / n) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hexp]
      congr 1
      rw [← Real.rpow_natCast c n, ← Real.rpow_mul hcpos.le, mul_one_div, div_self hnR.ne',
        Real.rpow_one]
    _ ≤ volume (S + T) ^ ((1 : ℝ) / n) := ENNReal.rpow_le_rpow hmain hexp

end Isodiametric

end Analysis

end FunctionalInequalities
