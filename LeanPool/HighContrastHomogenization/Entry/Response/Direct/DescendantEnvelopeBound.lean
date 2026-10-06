/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.ResponseBlockObjects
public import LeanPool.HighContrastHomogenization.Entry.Response.Limit.DescendantLimitDomination
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.SourceLoadHeadBound
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# High-contrast homogenization: Entry.Response.Direct.DescendantEnvelopeBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The increment envelope of the descendant sum, and its summable bound against the source load

The generation increments of the descendant sum are flat averages, over one generation's cells, of
a cutoff weight of size `K 3^{-n}` against the crossed pairing of the dual variable with the cell
average of the optimizer state; Cauchy-Schwarz bounds such an increment by `K 3^{-n}` times the
square root of the annealed mean of the squared head, giving a nonnegative envelope whose series of
annealed means is summable because the source load bounds the head and the terminal energy bounds
the cell energy. Shifting the generation index up by one, to meet the layer below the scale-`s`
cells, costs only the fixed factor `3^{3/2}`, since every summand and the dropped head are
nonnegative and the weighted square roots this step consumes are themselves summable by the
arithmetic-geometric mean inequality. Summing the resulting bound over the descendant generations,
each weighted by `3^{3(k-s)/2}`, closes the descendant sum of the cutoff-oscillation pairings
against the source load.  This is the summability and domination input that the response transfer
`p.response.transfer` consumes for its descendant sum.
-/

section
/-!
## A nonnegative series with summable annealed means

The increment envelope of the descendant sum of `p.response.transfer` is built generation by
generation, and what the carriers control is the annealed mean of each generation: the layer load
bounds the head and the terminal energy bounds the cell energy, so the series of annealed means is
summable.  Monotone convergence turns that single fact into the two hypotheses the descendant
limit consumes: the series converges along almost every sample, and its sum is `P`-integrable.

Nothing here is specific to the response transfer; the statement is the Beppo Levi theorem for a
nonnegative family of integrable functions indexed by the generations.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Beppo Levi for a nonnegative generation series.**  A nonnegative family of `P`-integrable
functions whose annealed means form a summable series converges along almost every sample, and its
sample sum is `P`-integrable.

This is the producer of the `henvsum` and `henvI` hypotheses of the descendant limit: the carriers
supply a summable bound on `∫ env n` alone. -/
theorem aeSummable_and_integrable_tsum_of_summable_integral
    {α : Type*} [MeasurableSpace α] (P : Measure α) (g : ℕ → α → ℝ)
    (hg0 : ∀ (n : ℕ) (a : α), 0 ≤ g n a) (hgint : ∀ n : ℕ, Integrable (g n) P)
    (hgS : Summable fun n : ℕ => ∫ a, g n a ∂P) :
    (∀ᵐ a ∂P, Summable fun n : ℕ => g n a) ∧ Integrable (fun a => ∑' n : ℕ, g n a) P := by
  classical
  -- The `ℝ≥0∞` version of the family, and its sample sum.
  set G : ℕ → α → ENNReal := fun n a => ENNReal.ofReal (g n a) with hGdef
  have hGmeas : ∀ n : ℕ, AEMeasurable (G n) P := fun n =>
    ENNReal.measurable_ofReal.comp_aemeasurable (hgint n).aestronglyMeasurable.aemeasurable
  have hGlin : ∀ n : ℕ, ∫⁻ a, G n a ∂P = ENNReal.ofReal (∫ a, g n a ∂P) := by
    intro n
    exact (ofReal_integral_eq_lintegral_ofReal (hgint n)
      (Filter.Eventually.of_forall (hg0 n))).symm
  -- The total mass of the sample sum is the sum of the annealed means, which is finite.
  have hInt0 : ∀ n : ℕ, 0 ≤ ∫ a, g n a ∂P := fun n =>
    integral_nonneg (hg0 n)
  have htot : ∫⁻ a, (∑' n : ℕ, G n a) ∂P = ENNReal.ofReal (∑' n : ℕ, ∫ a, g n a ∂P) := by
    rw [lintegral_tsum hGmeas]
    rw [ENNReal.ofReal_tsum_of_nonneg hInt0 hgS]
    exact tsum_congr hGlin
  have htop : ∫⁻ a, (∑' n : ℕ, G n a) ∂P ≠ ⊤ := by
    rw [htot]
    exact ENNReal.ofReal_ne_top
  -- Hence the sample sum is finite almost everywhere.
  have hfin : ∀ᵐ a ∂P, (∑' n : ℕ, G n a) ≠ ⊤ := by
    have hmeas : AEMeasurable (fun a => ∑' n : ℕ, G n a) P :=
      AEMeasurable.tsum hGmeas
    exact (ae_lt_top' hmeas htop).mono fun a ha => ha.ne
  -- Finiteness of the `ℝ≥0∞` sum bounds every partial sum, hence gives summability.
  have hsummable : ∀ᵐ a ∂P, Summable fun n : ℕ => g n a := by
    filter_upwards [hfin] with a ha
    refine summable_of_sum_range_le (fun n => hg0 n a) (c := (∑' n : ℕ, G n a).toReal) ?_
    intro N
    have hle : ENNReal.ofReal (∑ n ∈ Finset.range N, g n a) ≤ ∑' n : ℕ, G n a := by
      have h1 : ENNReal.ofReal (∑ n ∈ Finset.range N, g n a)
          = ∑ n ∈ Finset.range N, G n a := by
        induction N with
        | zero => simp [hGdef]
        | succ M ih =>
            rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih,
              ← ENNReal.ofReal_add (Finset.sum_nonneg fun n _ => hg0 n a) (hg0 M a)]
      rw [h1]
      exact ENNReal.sum_le_tsum (Finset.range N)
    have h2 : (ENNReal.ofReal (∑ n ∈ Finset.range N, g n a)).toReal
        ≤ (∑' n : ℕ, G n a).toReal := ENNReal.toReal_mono ha hle
    rwa [ENNReal.toReal_ofReal (Finset.sum_nonneg fun n _ => hg0 n a)] at h2
  refine ⟨hsummable, ?_⟩
  -- The sample sum agrees almost everywhere with the real part of the `ℝ≥0∞` sum, which is
  -- measurable and of finite integral.
  have hcong : (fun a => ∑' n : ℕ, g n a)
      =ᵐ[P] fun a => (∑' n : ℕ, G n a).toReal := by
    filter_upwards [hsummable] with a ha
    have := ENNReal.ofReal_tsum_of_nonneg (fun n => hg0 n a) ha
    rw [← this, ENNReal.toReal_ofReal (tsum_nonneg fun n => hg0 n a)]
  have hmeasG : AEMeasurable (fun a => ∑' n : ℕ, G n a) P :=
    AEMeasurable.tsum hGmeas
  refine Integrable.congr ?_ hcong.symm
  refine ⟨hmeasG.ennreal_toReal.aestronglyMeasurable, ?_⟩
  have : ∫⁻ a, ‖(∑' n : ℕ, G n a).toReal‖ₑ ∂P ≤ ∫⁻ a, (∑' n : ℕ, G n a) ∂P := by
    refine lintegral_mono_ae ?_
    filter_upwards [hfin] with a ha
    rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal ha]
  exact lt_of_le_of_lt this (lt_top_iff_ne_top.2 htop)

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The increment envelope of the descendant sum

The generation increments of the descendant sum of `p.response.transfer` are flat averages, over
the cells of one generation, of a cutoff weight of size `K 3^{-n}` against the crossed pairing of
the deterministic dual variable with the cell average of the optimizer state.  Cauchy--Schwarz over
the cells bounds such an increment by `K 3^{-n}` times the square root of the flat head energy
times the square root of the flat cell energy, and Young's inequality with the weight `3^{-n/2}`
splits that product into

```
(K/2) (3^{-3n/2} · flat head energy + 3^{-n/2} · flat cell energy) ,
```

which is the envelope below.  Its annealed mean is summable, because the head energy is summable
against `3^{-3n/2}` (that is the source load) and the cell energy is bounded by the terminal energy
at every depth; monotone convergence then makes the envelope series converge along almost every
sample with a `P`-integrable sum.  Nothing here uses a moment of the coefficient field.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The increment envelope of the descendant sum: Young's splitting, with the weight `3^{-n/2}`,
of `K 3^{-n}` times the Cauchy--Schwarz product of the flat head energy and the flat cell energy of
the generation-`n` cells. -/
@[expose]
def descendantEnvelope {iota alpha : Type*} (Z : ℕ → Finset iota)
    (G D : ℕ → iota → alpha → ℝ) (K : ℝ) (n : ℕ) (a : alpha) : ℝ :=
  (K / 2) *
    ((3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) *
        (((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2)
      + (3 : ℝ) ^ (-((1 : ℝ) / 2) * (n : ℝ)) *
        (((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a))

/-- The envelope is nonnegative. -/
theorem descendantEnvelope_nonneg {iota alpha : Type*} (Z : ℕ → Finset iota)
    (G D : ℕ → iota → alpha → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hD : ∀ n : ℕ, ∀ W ∈ Z n, ∀ a, 0 ≤ D n W a) (n : ℕ) (a : alpha) :
    0 ≤ descendantEnvelope Z G D K n a := by
  have hF : (0 : ℝ) ≤ ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2 :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun W _ => sq_nonneg _)
  have hDd : (0 : ℝ) ≤ ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a :=
    mul_nonneg (by positivity)
      (Finset.sum_nonneg fun W hW => by
        have := hD n W hW a
        linarith only [this])
  have h1 : (0 : ℝ) ≤ (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) := by positivity
  have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ (-((1 : ℝ) / 2) * (n : ℝ)) := by positivity
  have : (0 : ℝ) ≤ K / 2 := by linarith only [hK]
  exact mul_nonneg this (add_nonneg (mul_nonneg h1 hF) (mul_nonneg h2 hDd))

/-- **Young's splitting of the geometric Cauchy--Schwarz product.**  For nonnegative `X`, `Y` and
`K`, the product `K 3^{-n} √X √Y` is at most `(K/2)(3^{-3n/2} X + 3^{-n/2} Y)`. -/
theorem mul_rpow_neg_sqrt_mul_sqrt_le {K X Y : ℝ} (hK : 0 ≤ K) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (n : ℕ) :
    K * (3 : ℝ) ^ (-(n : ℝ)) * (Real.sqrt X * Real.sqrt Y)
      ≤ (K / 2) * ((3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * X
          + (3 : ℝ) ^ (-((1 : ℝ) / 2) * (n : ℝ)) * Y) := by
  set u : ℝ := (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * X with hu
  set v : ℝ := (3 : ℝ) ^ (-((1 : ℝ) / 2) * (n : ℝ)) * Y with hv
  have hu0 : 0 ≤ u := mul_nonneg (by positivity) hX
  have hv0 : 0 ≤ v := mul_nonneg (by positivity) hY
  -- The arithmetic--geometric mean inequality.
  have hAM : 2 * (Real.sqrt u * Real.sqrt v) ≤ u + v := by
    have hexp : (Real.sqrt u - Real.sqrt v) ^ 2
        = u - 2 * (Real.sqrt u * Real.sqrt v) + v := by
      rw [sub_sq, Real.sq_sqrt hu0, Real.sq_sqrt hv0]; ring
    have := sq_nonneg (Real.sqrt u - Real.sqrt v)
    linarith only [this, hexp]
  -- The two geometric weights multiply to `3^{-n}`.
  have hw : Real.sqrt ((3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)))
      * Real.sqrt ((3 : ℝ) ^ (-((1 : ℝ) / 2) * (n : ℝ))) = (3 : ℝ) ^ (-(n : ℝ)) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  have hprod : Real.sqrt u * Real.sqrt v
      = (3 : ℝ) ^ (-(n : ℝ)) * (Real.sqrt X * Real.sqrt Y) := by
    rw [hu, hv, Real.sqrt_mul (by positivity) X, Real.sqrt_mul (by positivity) Y]
    calc Real.sqrt ((3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ))) * Real.sqrt X
            * (Real.sqrt ((3 : ℝ) ^ (-((1 : ℝ) / 2) * (n : ℝ))) * Real.sqrt Y)
        = (Real.sqrt ((3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)))
            * Real.sqrt ((3 : ℝ) ^ (-((1 : ℝ) / 2) * (n : ℝ))))
              * (Real.sqrt X * Real.sqrt Y) := by ring
      _ = (3 : ℝ) ^ (-(n : ℝ)) * (Real.sqrt X * Real.sqrt Y) := by rw [hw]
  have hmain : 2 * ((3 : ℝ) ^ (-(n : ℝ)) * (Real.sqrt X * Real.sqrt Y)) ≤ u + v := by
    rw [← hprod]; exact hAM
  have hfin := mul_le_mul_of_nonneg_left hmain (show (0 : ℝ) ≤ K / 2 by linarith only [hK])
  calc K * (3 : ℝ) ^ (-(n : ℝ)) * (Real.sqrt X * Real.sqrt Y)
      = K / 2 * (2 * ((3 : ℝ) ^ (-(n : ℝ)) * (Real.sqrt X * Real.sqrt Y))) := by ring
    _ ≤ K / 2 * (u + v) := hfin

/-- **The envelope dominates the generation increment.**  With cutoff weights of size `K 3^{-n}`
and a crossed pairing bounded by the head times the square root of twice the cell energy, the flat
average defining the generation-`n` increment is at most the envelope. -/
theorem abs_flat_weighted_pairing_le_descendantEnvelope {iota alpha : Type*}
    (Z : ℕ → Finset iota) (θ : ℕ → iota → ℝ) (pairing G D : ℕ → iota → alpha → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hθ : ∀ n : ℕ, ∀ W ∈ Z n, |θ n W| ≤ K * (3 : ℝ) ^ (-(n : ℝ)))
    (hG : ∀ n : ℕ, ∀ W ∈ Z n, ∀ a, 0 ≤ G n W a)
    (hD : ∀ n : ℕ, ∀ W ∈ Z n, ∀ a, 0 ≤ D n W a)
    (hbd : ∀ n : ℕ, ∀ W ∈ Z n, ∀ a, |pairing n W a| ≤ G n W a * Real.sqrt (2 * D n W a))
    (n : ℕ) (a : alpha) :
    |((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, θ n W * pairing n W a|
      ≤ descendantEnvelope Z G D K n a := by
  have hcard : (0 : ℝ) ≤ ((Z n).card : ℝ)⁻¹ := by positivity
  have hw0 : (0 : ℝ) ≤ K * (3 : ℝ) ^ (-(n : ℝ)) := by positivity
  -- Peel the weights off the flat average.
  have step1 : |((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, θ n W * pairing n W a|
      ≤ ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n,
          (K * (3 : ℝ) ^ (-(n : ℝ))) * (G n W a * Real.sqrt (2 * D n W a)) := by
    rw [abs_mul, abs_of_nonneg hcard]
    refine mul_le_mul_of_nonneg_left ?_ hcard
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun W hW => ?_)
    rw [abs_mul]
    have h1 : |θ n W| * |pairing n W a|
        ≤ (K * (3 : ℝ) ^ (-(n : ℝ))) * |pairing n W a| :=
      mul_le_mul_of_nonneg_right (hθ n W hW) (abs_nonneg _)
    have h2 : (K * (3 : ℝ) ^ (-(n : ℝ))) * |pairing n W a|
        ≤ (K * (3 : ℝ) ^ (-(n : ℝ))) * (G n W a * Real.sqrt (2 * D n W a)) :=
      mul_le_mul_of_nonneg_left (hbd n W hW a) hw0
    linarith only [h1, h2]
  -- Cauchy--Schwarz over the cells of the generation.
  have step2 : ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n,
        (K * (3 : ℝ) ^ (-(n : ℝ))) * (G n W a * Real.sqrt (2 * D n W a))
      = K * (3 : ℝ) ^ (-(n : ℝ)) * (((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n,
          Real.sqrt ((G n W a) ^ 2) * Real.sqrt (2 * D n W a)) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun W hW => ?_
    rw [Real.sqrt_sq (hG n W hW a)]
    ring
  have hCS : ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n,
        Real.sqrt ((G n W a) ^ 2) * Real.sqrt (2 * D n W a)
      ≤ Real.sqrt (((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2)
        * Real.sqrt (((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a) :=
    flat_average_sqrt_mul_sqrt_le (Z n) (fun W => (G n W a) ^ 2) (fun W => 2 * D n W a)
      (fun W _ => sq_nonneg _) (fun W hW => by have := hD n W hW a; linarith only [this])
  have hX : (0 : ℝ) ≤ ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2 :=
    mul_nonneg hcard (Finset.sum_nonneg fun W _ => sq_nonneg _)
  have hY : (0 : ℝ) ≤ ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a :=
    mul_nonneg hcard (Finset.sum_nonneg fun W hW => by
      have := hD n W hW a; linarith only [this])
  calc |((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, θ n W * pairing n W a|
      ≤ ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n,
          (K * (3 : ℝ) ^ (-(n : ℝ))) * (G n W a * Real.sqrt (2 * D n W a)) := step1
    _ = K * (3 : ℝ) ^ (-(n : ℝ)) * (((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n,
          Real.sqrt ((G n W a) ^ 2) * Real.sqrt (2 * D n W a)) := step2
    _ ≤ K * (3 : ℝ) ^ (-(n : ℝ)) *
          (Real.sqrt (((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2)
            * Real.sqrt (((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a)) :=
        mul_le_mul_of_nonneg_left hCS hw0
    _ ≤ descendantEnvelope Z G D K n a := mul_rpow_neg_sqrt_mul_sqrt_le hK hX hY n

/-- **The envelope series converges along almost every sample, with an integrable sum.**  The
annealed mean of the generation-`n` envelope is at most `(K/2)(3^{-3n/2} L n + 3^{-n/2} 2 E[J])`,
where `L` is the layer head energy of the source load and `E[J]` bounds the cell energy at every
depth.  That series is summable, so monotone convergence gives both hypotheses the descendant
limit consumes. -/
theorem aeSummable_and_integrable_tsum_descendantEnvelope {iota alpha : Type*}
    [MeasurableSpace alpha] (P : Measure alpha) (Z : ℕ → Finset iota)
    (G D : ℕ → iota → alpha → ℝ) (L : ℕ → ℝ) (K EJ : ℝ) (hK : 0 ≤ K)
    (hD : ∀ n : ℕ, ∀ W ∈ Z n, ∀ a, 0 ≤ D n W a)
    (hGsq : ∀ n : ℕ, (∫ a, ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2 ∂P) ≤ L n)
    (hDval : ∀ n : ℕ, (∫ a, ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a ∂P) ≤ 2 * EJ)
    (hFint : ∀ n : ℕ, Integrable (fun a => ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2) P)
    (hDint : ∀ n : ℕ, Integrable (fun a => ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a) P)
    (hsum : Summable fun n : ℕ => (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n) :
    (∀ᵐ a ∂P, Summable fun n : ℕ => descendantEnvelope Z G D K n a)
      ∧ Integrable (fun a => ∑' n : ℕ, descendantEnvelope Z G D K n a) P := by
  have henvint : ∀ n : ℕ, Integrable (fun a => descendantEnvelope Z G D K n a) P := by
    intro n
    exact (((hFint n).const_mul _).add ((hDint n).const_mul _)).const_mul _
  have hval : ∀ n : ℕ, (∫ a, descendantEnvelope Z G D K n a ∂P)
      = (K / 2) * ((3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ))
            * (∫ a, ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2 ∂P)
          + (3 : ℝ) ^ (-((1 : ℝ) / 2) * (n : ℝ))
            * (∫ a, ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a ∂P)) := by
    intro n
    have e1 : (∫ a, (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ))
          * (((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2) ∂P)
        = (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ))
          * ∫ a, ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2 ∂P :=
      integral_const_mul _ _
    have e2 : (∫ a, (3 : ℝ) ^ (-((1 : ℝ) / 2) * (n : ℝ))
          * (((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a) ∂P)
        = (3 : ℝ) ^ (-((1 : ℝ) / 2) * (n : ℝ))
          * ∫ a, ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a ∂P :=
      integral_const_mul _ _
    simp only [descendantEnvelope]
    rw [integral_const_mul, integral_add ((hFint n).const_mul _) ((hDint n).const_mul _), e1, e2]
  -- The summable majorant of the annealed envelope means.
  have hmaj : Summable fun n : ℕ => (K / 2) * ((3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n
      + (3 : ℝ) ^ (-((1 : ℝ) / 2) * (n : ℝ)) * (2 * EJ)) := by
    refine Summable.mul_left _ (hsum.add ?_)
    refine Summable.mul_right _ ?_
    refine summable_rpow_neg_half.congr fun n => ?_
    rw [show -((n : ℝ) / 2) = -((1 : ℝ) / 2) * (n : ℝ) by ring]
  refine aeSummable_and_integrable_tsum_of_summable_integral P
    (fun n a => descendantEnvelope Z G D K n a)
    (fun n a => descendantEnvelope_nonneg Z G D K hK hD n a) henvint ?_
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj
  · exact integral_nonneg fun a => descendantEnvelope_nonneg Z G D K hK hD n a
  · rw [hval n]
    have hc1 : (0 : ℝ) ≤ (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) := by positivity
    have hc2 : (0 : ℝ) ≤ (3 : ℝ) ^ (-((1 : ℝ) / 2) * (n : ℝ)) := by positivity
    have h1 : (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ))
          * (∫ a, ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2 ∂P)
        ≤ (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n :=
      mul_le_mul_of_nonneg_left (hGsq n) hc1
    have h2 : (3 : ℝ) ^ (-((1 : ℝ) / 2) * (n : ℝ))
          * (∫ a, ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a ∂P)
        ≤ (3 : ℝ) ^ (-((1 : ℝ) / 2) * (n : ℝ)) * (2 * EJ) :=
      mul_le_mul_of_nonneg_left (hDval n) hc2
    exact mul_le_mul_of_nonneg_left (by linarith only [h1, h2])
      (by linarith only [hK] : (0 : ℝ) ≤ K / 2)

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The shifted descendant layers against the source load

The descendant sum of `p.response.transfer` meets the layer one generation below the scale-`s`
cells.  Shifting the generation index upward costs the single factor `3^{3/2}`, since every
summand is nonnegative and the dropped head is nonnegative; and the weighted square roots the
descendant Cauchy--Schwarz consumes are summable by the arithmetic--geometric mean inequality.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Summability of the weighted square roots of the descendant layers.**  If the load family
`3^{-3n/2} L n` is summable and every layer is nonnegative, then the family `3^{-n} √(L n)` that
the descendant Cauchy--Schwarz consumes is summable, because
`3^{-n} √(L n) ≤ ½ (3^{-n/2} + 3^{-3n/2} L n)`. -/
theorem summable_rpow_neg_mul_sqrt_of_summable (L : ℕ → ℝ) (hL : ∀ n, 0 ≤ L n)
    (hsum : Summable fun n : ℕ => (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n) :
    Summable fun n : ℕ => (3 : ℝ) ^ (-(n : ℝ)) * Real.sqrt (L n) := by
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have h3nn : (0 : ℝ) ≤ 3 := by norm_num
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    ((summable_rpow_neg_half.add hsum).mul_left (1 / 2))
  · exact mul_nonneg (Real.rpow_nonneg h3nn _) (Real.sqrt_nonneg _)
  · have hu_sq : ((3 : ℝ) ^ (-(1 : ℝ) / 4 * (n : ℝ))) ^ 2
        = (3 : ℝ) ^ (-((n : ℝ) / 2)) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul h3nn]
      rw [show (-(1 : ℝ) / 4 * (n : ℝ)) * ((2 : ℕ) : ℝ) = -((n : ℝ) / 2) by ring]
    have hv_sq : ((3 : ℝ) ^ (-(3 : ℝ) / 4 * (n : ℝ)) * Real.sqrt (L n)) ^ 2
        = (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n := by
      rw [← Real.rpow_natCast]
      rw [Real.mul_rpow (Real.rpow_nonneg h3nn _) (Real.sqrt_nonneg _)]
      rw [← Real.rpow_mul h3nn]
      rw [Real.rpow_natCast, Real.sq_sqrt (hL n)]
      rw [show (-(3 : ℝ) / 4 * (n : ℝ)) * ((2 : ℕ) : ℝ) = -((3 : ℝ) / 2) * (n : ℝ) by ring]
    have huv : (3 : ℝ) ^ (-(1 : ℝ) / 4 * (n : ℝ))
        * ((3 : ℝ) ^ (-(3 : ℝ) / 4 * (n : ℝ)) * Real.sqrt (L n))
        = (3 : ℝ) ^ (-(n : ℝ)) * Real.sqrt (L n) := by
      rw [← mul_assoc, ← Real.rpow_add h3pos]
      rw [show (-(1 : ℝ) / 4 * (n : ℝ)) + (-(3 : ℝ) / 4 * (n : ℝ)) = -(n : ℝ) by ring]
    rw [← huv, ← hu_sq, ← hv_sq]
    linarith only [two_mul_le_add_sq ((3 : ℝ) ^ (-(1 : ℝ) / 4 * (n : ℝ)))
      ((3 : ℝ) ^ (-(3 : ℝ) / 4 * (n : ℝ)) * Real.sqrt (L n))]

/-- **The shifted descendant layers are dominated by the source load.**  Summing the layers from
depth one, with the weights of depth zero, costs at most the factor `3^{3/2}` against the source
load `𝓛_s` of `p.response.transfer`. -/
theorem tsum_succ_layer_le_respSourceLoad {d : ℕ} [NeZero d] (P : Measure (CoeffSpace d))
    (jStar : ℕ) (F : BlockMat d) (s : ℤ) (b : CoeffSpace d → CoeffField d) (Y : BlockVec d)
    (hsum : Summable (fun n : ℕ => (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) *
      ((((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ z ∈ triadicIndexBox d n,
          (Real.sqrt (vecDot Y.1 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                  b).upperLeft
                Y.1)) +
            Real.sqrt (vecDot Y.2 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                  b).lowerRight
                Y.2))) ^ 2))) :
    (∑' n : ℕ, (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) *
        ((((triadicIndexBox d (n + 1)).card : ℝ))⁻¹ *
          ∑ z ∈ triadicIndexBox d (n + 1),
            (Real.sqrt (vecDot Y.1 (matVecMul
                  (annealedBlockOf P
                    (adaptedCellAtCenter (respGrid jStar F) (s - ((n + 1 : ℕ) : ℤ)) z) b).upperLeft
                  Y.1)) +
              Real.sqrt (vecDot Y.2 (matVecMul
                  (annealedBlockOf P
                    (adaptedCellAtCenter (respGrid jStar F) (s - ((n + 1 : ℕ) : ℤ)) z) b).lowerRight
                  Y.2))) ^ 2))
      ≤ (3 : ℝ) ^ ((3 : ℝ) / 2) * respSourceLoad P jStar F s b Y := by
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have _hd : d ≠ 0 := NeZero.ne d
  let g : ℕ → ℝ := fun n : ℕ => (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) *
    ((((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ z ∈ triadicIndexBox d n,
        (Real.sqrt (vecDot Y.1 (matVecMul
              (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                b).upperLeft
              Y.1)) +
          Real.sqrt (vecDot Y.2 (matVecMul
              (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                b).lowerRight
              Y.2))) ^ 2)
  have hg : Summable g := hsum
  have hg_nonneg : ∀ n : ℕ, 0 ≤ g n := fun n =>
    mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        (Finset.sum_nonneg fun z _ => sq_nonneg _))
  have hshift : (∑' n : ℕ, g (n + 1)) ≤ ∑' n : ℕ, g n := by
    have h := hg.tsum_eq_zero_add
    linarith only [h, hg_nonneg 0]
  have hterm : ∀ n : ℕ,
      (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) *
        ((((triadicIndexBox d (n + 1)).card : ℝ))⁻¹ *
          ∑ z ∈ triadicIndexBox d (n + 1),
            (Real.sqrt (vecDot Y.1 (matVecMul
                  (annealedBlockOf P
                    (adaptedCellAtCenter (respGrid jStar F) (s - ((n + 1 : ℕ) : ℤ)) z) b).upperLeft
                  Y.1)) +
              Real.sqrt (vecDot Y.2 (matVecMul
                  (annealedBlockOf P
                    (adaptedCellAtCenter (respGrid jStar F) (s - ((n + 1 : ℕ) : ℤ)) z) b).lowerRight
                  Y.2))) ^ 2)
        = (3 : ℝ) ^ ((3 : ℝ) / 2) * g (n + 1) := by
    intro n
    have hweight : (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ))
        = (3 : ℝ) ^ ((3 : ℝ) / 2)
          * (3 : ℝ) ^ (-((3 : ℝ) / 2) * ((n + 1 : ℕ) : ℝ)) := by
      rw [← Real.rpow_add h3pos]
      congr 1
      push_cast
      ring
    rw [hweight, mul_assoc]
  calc
    (∑' n : ℕ, (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) *
        ((((triadicIndexBox d (n + 1)).card : ℝ))⁻¹ *
          ∑ z ∈ triadicIndexBox d (n + 1),
            (Real.sqrt (vecDot Y.1 (matVecMul
                  (annealedBlockOf P
                    (adaptedCellAtCenter (respGrid jStar F) (s - ((n + 1 : ℕ) : ℤ)) z) b).upperLeft
                  Y.1)) +
              Real.sqrt (vecDot Y.2 (matVecMul
                  (annealedBlockOf P
                    (adaptedCellAtCenter (respGrid jStar F) (s - ((n + 1 : ℕ) : ℤ)) z) b).lowerRight
                  Y.2))) ^ 2))
        = ∑' n : ℕ, (3 : ℝ) ^ ((3 : ℝ) / 2) * g (n + 1) :=
          tsum_congr hterm
    _ = (3 : ℝ) ^ ((3 : ℝ) / 2) * ∑' n : ℕ, g (n + 1) := by rw [tsum_mul_left]
    _ ≤ (3 : ℝ) ^ ((3 : ℝ) / 2) * ∑' n : ℕ, g n :=
          mul_le_mul_of_nonneg_left hshift (le_of_lt (Real.rpow_pos_of_pos h3pos _))
    _ = (3 : ℝ) ^ ((3 : ℝ) / 2) * respSourceLoad P jStar F s b Y := rfl

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The descendant sum of the cutoff-oscillation pairings

The second cutoff-mean row of `p.response.transfer` pairs the within-cell oscillations of the
cutoff with the gradient and the flux, and then sums the descendants with weights
`3^{3(k-s)/2}`.  At each descendant depth a finite family of cells carries a weight of size at
most a fixed multiple of `3^{-n}` and a pairing controlled pathwise by the source-load head `G`
times the square root of twice the scalar deficit `D`.  The depth-`n` row bounds the expectation
of the weighted flat average, and summing over the depths after splitting `3^{-n}` into a
geometric factor and a load factor turns the descendant sum into the printed factor
`3^{-H}(E[J_t]𝓛_s)^{1/2}`.

The first declaration is the depth row with the normalisation of the weight made explicit; the
second sums those rows over the depths.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The cell pairing row against a weight bounded by `M`.**  The weighted flat average of a
full-dual pairing controlled pathwise by the source-load head `G` and the scalar deficit `D`,
against weights of size at most `M`, has sample expectation at most
`M · √Lhead · √(2 tau)`.  This is the cell pairing row of `p.response.transfer` with the
normalisation of the weight made explicit. -/
theorem abs_integral_flat_weighted_pairing_le_of_bound {iota alpha : Type*}
    [MeasurableSpace alpha] (P : Measure alpha) (Z : Finset iota) (c : iota → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hc : ∀ w ∈ Z, |c w| ≤ M)
    (pairing G D : iota → alpha → ℝ) (Lhead tau : ℝ)
    (hG : ∀ w ∈ Z, ∀ a, 0 ≤ G w a) (hD : ∀ w ∈ Z, ∀ a, 0 ≤ D w a)
    (hbd : ∀ w ∈ Z, ∀ a, |pairing w a| ≤ G w a * Real.sqrt (2 * D w a))
    (hGsq : (∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2 ∂P) ≤ Lhead)
    (hDval : (∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a ∂P) = 2 * tau)
    (hFint : Integrable (fun a => (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2) P)
    (hDint : Integrable (fun a => (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a) P)
    (hMidint : Integrable (fun a =>
      Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2)
        * Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a)) P)
    (hPint : Integrable (fun a => (Z.card : ℝ)⁻¹ * ∑ w ∈ Z,
      c w * (Real.sqrt ((G w a) ^ 2) * Real.sqrt (2 * D w a))) P)
    (hPint' : Integrable (fun a => (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w * pairing w a) P) :
    |∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w * pairing w a ∂P|
      ≤ M * (Real.sqrt Lhead * Real.sqrt (2 * tau)) := by
  have _ := hPint
  have habs : ∀ v : iota → ℝ,
      |(Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w * v w| ≤ M * ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, |v w|) := by
    intro v
    have hc0 : 0 ≤ (Z.card : ℝ)⁻¹ := by positivity
    have hS : |∑ w ∈ Z, c w * v w| ≤ M * ∑ w ∈ Z, |v w| := by
      calc
        |∑ w ∈ Z, c w * v w| ≤ ∑ w ∈ Z, |c w * v w| :=
          Finset.abs_sum_le_sum_abs (fun w => c w * v w) Z
        _ = ∑ w ∈ Z, |c w| * |v w| :=
          Finset.sum_congr rfl fun w _ => abs_mul (c w) (v w)
        _ ≤ ∑ w ∈ Z, M * |v w| :=
          Finset.sum_le_sum fun w hw =>
            mul_le_mul_of_nonneg_right (hc w hw) (abs_nonneg (v w))
        _ = M * ∑ w ∈ Z, |v w| := by rw [Finset.mul_sum]
    calc
      |(Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w * v w|
          = (Z.card : ℝ)⁻¹ * |∑ w ∈ Z, c w * v w| := by
            rw [abs_mul, abs_of_nonneg hc0]
      _ ≤ (Z.card : ℝ)⁻¹ * (M * ∑ w ∈ Z, |v w|) :=
            mul_le_mul_of_nonneg_left hS hc0
      _ = M * ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, |v w|) := by ring
  have hpt : ∀ a, |(Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w * pairing w a|
      ≤ M * (Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2)
        * Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a)) := by
    intro a
    have h1 := habs (fun w => pairing w a)
    have h2 : (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, |pairing w a|
        ≤ (Z.card : ℝ)⁻¹ * ∑ w ∈ Z,
            Real.sqrt ((G w a) ^ 2) * Real.sqrt (2 * D w a) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun w hw => by
          rw [Real.sqrt_sq (hG w hw a)]
          exact hbd w hw a)
        (by positivity)
    have h3 := flat_average_sqrt_mul_sqrt_le Z (fun w => (G w a) ^ 2)
      (fun w => 2 * D w a)
      (fun w _ => sq_nonneg (G w a))
      (fun w hw => mul_nonneg (by norm_num) (hD w hw a))
    exact h1.trans ((mul_le_mul_of_nonneg_left h2 hM).trans
      (mul_le_mul_of_nonneg_left h3 hM))
  have hF0 : ∀ a, 0 ≤ (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2 := by
    intro a
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun w _ => sq_nonneg (G w a))
  have hD0 : ∀ a, 0 ≤ (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a := by
    intro a
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun w hw => mul_nonneg (by norm_num) (hD w hw a))
  have hCS : (∫ a, Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2)
        * Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a) ∂P)
      ≤ Real.sqrt Lhead * Real.sqrt (2 * tau) := by
    calc
      (∫ a, Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2)
          * Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a) ∂P)
          ≤ Real.sqrt (∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2 ∂P)
            * Real.sqrt (∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a ∂P) :=
            integral_sqrt_mul_sqrt_le_sqrt_mul_sqrt P hFint hDint hF0 hD0 hMidint
      _ = Real.sqrt (∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2 ∂P)
            * Real.sqrt (2 * tau) := by rw [hDval]
      _ ≤ Real.sqrt Lhead * Real.sqrt (2 * tau) :=
            mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hGsq) (Real.sqrt_nonneg _)
  have hInt : Integrable (fun a => M * (Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2)
        * Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a))) P :=
    hMidint.const_mul M
  calc
    |∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w * pairing w a ∂P|
        ≤ ∫ a, |(Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w * pairing w a| ∂P :=
          abs_integral_le_integral_abs
    _ ≤ ∫ a, M * (Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2)
          * Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a)) ∂P :=
          integral_mono hPint'.abs hInt hpt
    _ = M * (∫ a, Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2)
          * Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a) ∂P) := by
          rw [integral_const_mul]
    _ ≤ M * (Real.sqrt Lhead * Real.sqrt (2 * tau)) :=
          mul_le_mul_of_nonneg_left hCS hM

/-- **The descendant sum of the cutoff-oscillation pairings.**  At each depth `n` the weights
`θ n w` are of size at most `K · 3^{-n}`, the pairings are controlled pathwise by the head
`G n w a` and the deficit `D n w a`, the annealed flat average of `G²` is at most `L n` and the
annealed flat average of `2 D` is at most `2 EJ`.  Then every partial descendant sum is bounded
by `K · √(∑ 3^{-n/2}) · √(∑ 3^{-3n/2} L n) · √(2 EJ)`: this is the term
`3^{-H}(E[J_t]𝓛_s)^{1/2}` of `p.response.transfer`. -/
theorem abs_sum_range_descendant_pairing_le {iota alpha : Type*} [MeasurableSpace alpha]
    (P : Measure alpha) (Nn : ℕ) (Z : ℕ → Finset iota) (θ : ℕ → iota → ℝ)
    (pairing G D : ℕ → iota → alpha → ℝ) (L : ℕ → ℝ) (K EJ : ℝ)
    (hK : 0 ≤ K) (hEJ : 0 ≤ EJ) (hL : ∀ n, 0 ≤ L n)
    (hθ : ∀ n, ∀ w ∈ Z n, |θ n w| ≤ K * (3 : ℝ) ^ (-(n : ℝ)))
    (hG : ∀ n, ∀ w ∈ Z n, ∀ a, 0 ≤ G n w a)
    (hD : ∀ n, ∀ w ∈ Z n, ∀ a, 0 ≤ D n w a)
    (hbd : ∀ n, ∀ w ∈ Z n, ∀ a, |pairing n w a| ≤ G n w a * Real.sqrt (2 * D n w a))
    (hGsq : ∀ n, (∫ a, ((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n, (G n w a) ^ 2 ∂P) ≤ L n)
    (hDval : ∀ n, (∫ a, ((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n, 2 * D n w a ∂P) ≤ 2 * EJ)
    (hFint : ∀ n, Integrable (fun a => ((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n, (G n w a) ^ 2) P)
    (hDint : ∀ n, Integrable (fun a => ((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n, 2 * D n w a) P)
    (hMidint : ∀ n, Integrable (fun a =>
      Real.sqrt (((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n, (G n w a) ^ 2)
        * Real.sqrt (((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n, 2 * D n w a)) P)
    (hPint : ∀ n, Integrable (fun a => ((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n,
      θ n w * (Real.sqrt ((G n w a) ^ 2) * Real.sqrt (2 * D n w a))) P)
    (hPint' : ∀ n, Integrable (fun a => ((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n,
      θ n w * pairing n w a) P)
    (hsum : Summable fun n : ℕ => (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n)
    (hsum' : Summable fun n : ℕ => (3 : ℝ) ^ (-(n : ℝ)) * Real.sqrt (L n)) :
    |∑ n ∈ Finset.range Nn,
        ∫ a, ((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n, θ n w * pairing n w a ∂P|
      ≤ K * (Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)))
            * Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n))
          * Real.sqrt (2 * EJ) := by
  have _ := hEJ
  have hdepth : ∀ n, |∫ a, ((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n, θ n w * pairing n w a ∂P|
      ≤ (K * Real.sqrt (2 * EJ)) * ((3 : ℝ) ^ (-(n : ℝ)) * Real.sqrt (L n)) := by
    intro n
    have hM : 0 ≤ K * (3 : ℝ) ^ (-(n : ℝ)) :=
      mul_nonneg hK (Real.rpow_nonneg (by norm_num) _)
    have h1 := abs_integral_flat_weighted_pairing_le_of_bound P (Z n) (θ n)
      (K * (3 : ℝ) ^ (-(n : ℝ))) hM (hθ n) (pairing n) (G n) (D n) (L n)
      ((1 / 2) * ∫ a, ((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n, 2 * D n w a ∂P)
      (hG n) (hD n) (hbd n) (hGsq n) (by ring)
      (hFint n) (hDint n) (hMidint n) (hPint n) (hPint' n)
    have hle : 2 * ((1 / 2) * ∫ a, ((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n, 2 * D n w a ∂P)
        ≤ 2 * EJ := by
      have h := hDval n
      linarith only [h]
    calc
      |∫ a, ((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n, θ n w * pairing n w a ∂P|
          ≤ (K * (3 : ℝ) ^ (-(n : ℝ)))
              * (Real.sqrt (L n)
                * Real.sqrt (2 * ((1 / 2) * ∫ a, ((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n, 2 * D n w a
                  ∂P))) :=
            h1
      _ ≤ (K * (3 : ℝ) ^ (-(n : ℝ))) * (Real.sqrt (L n) * Real.sqrt (2 * EJ)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle) (Real.sqrt_nonneg _)) hM
      _ = (K * Real.sqrt (2 * EJ)) * ((3 : ℝ) ^ (-(n : ℝ)) * Real.sqrt (L n)) := by ring
  have hK2 : 0 ≤ K * Real.sqrt (2 * EJ) := mul_nonneg hK (Real.sqrt_nonneg _)
  have hterm : ∀ n : ℕ, 0 ≤ (3 : ℝ) ^ (-(n : ℝ)) * Real.sqrt (L n) :=
    fun n => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)
  calc
    |∑ n ∈ Finset.range Nn,
        ∫ a, ((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n, θ n w * pairing n w a ∂P|
        ≤ ∑ n ∈ Finset.range Nn,
            |∫ a, ((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n, θ n w * pairing n w a ∂P| :=
          Finset.abs_sum_le_sum_abs
            (fun n => ∫ a, ((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n, θ n w * pairing n w a ∂P)
            (Finset.range Nn)
    _ ≤ ∑ n ∈ Finset.range Nn,
          (K * Real.sqrt (2 * EJ)) * ((3 : ℝ) ^ (-(n : ℝ)) * Real.sqrt (L n)) :=
          Finset.sum_le_sum fun n _ => hdepth n
    _ = (K * Real.sqrt (2 * EJ)) *
          ∑ n ∈ Finset.range Nn, ((3 : ℝ) ^ (-(n : ℝ)) * Real.sqrt (L n)) := by
          rw [Finset.mul_sum]
    _ ≤ (K * Real.sqrt (2 * EJ)) *
          ∑' n : ℕ, ((3 : ℝ) ^ (-(n : ℝ)) * Real.sqrt (L n)) :=
          mul_le_mul_of_nonneg_left
            (hsum'.sum_le_tsum (Finset.range Nn) fun n _ => hterm n) hK2
    _ ≤ (K * Real.sqrt (2 * EJ)) *
          (Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)))
            * Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n)) :=
          mul_le_mul_of_nonneg_left
            (tsum_weighted_sqrt_le_sqrt_mul_sqrt L hL hsum hsum') hK2
    _ = K * (Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)))
            * Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n))
          * Real.sqrt (2 * EJ) := by ring

end

end HCPolySupport.HighContrast.Multiscale
end
