/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.JSpaceFourierConverse

/-!
# JSpace Fourier Limit

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
open scoped ENNReal FourierTransform SchwartzMap Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

private theorem regularizedPotentialCurl_coord_error_eLpNorm_le
    {a : Vec3 → Vec3} (ha : IsWeakDivFreeL2 a) (δ : ℝ) (hδ : 0 < δ)
    (i : Fin 3) :
    eLpNorm (fun x : Vec3 => regularizedPotentialCurl ha.1 δ hδ x i - a x i)
      (2 : ℝ≥0∞) volume ≤
      eLpNorm (regularizedPotentialCurlComponentLp ha.1 δ hδ i -
        weakFieldFourierComponent ha.1 i) (2 : ℝ≥0∞) (volume : Measure L2Vec3) := by
  let c := regularizedPotentialCurlComponentLp ha.1 δ hδ i
  let f := weakFieldFourierComponent ha.1 i
  let e : Lp (α := L2Vec3) ℂ 2 := c - f
  let r : L2Vec3 → ℝ := fun y => Complex.re (e y)
  let g : Vec3 → ℝ := fun x => regularizedPotentialCurl ha.1 δ hδ x i - a x i
  have hc := regularizedPotentialCurlComponentLp_real_eq ha.1 δ hδ i
  have hf : (fun y : L2Vec3 => f y) =ᵐ[volume]
      (fun y => (a (WithLp.ofLp y) i : ℂ)) := by
    filter_upwards [(complexifyVec3_memLp ha.1).eval_piLp i |>.coeFn_toLp] with y hy
    simpa [f, weakFieldFourierComponent, complexifyVec3] using hy
  have htransport : MeasurePreserving (WithLp.toLp 2 : Vec3 → L2Vec3) volume volume :=
    PiLp.volume_preserving_toLp (Fin 3)
  have hsub : (fun y : L2Vec3 => (c - f) y) =ᵐ[volume]
      (fun y => c y - f y) := Lp.coeFn_sub c f
  have hc' : ∀ᵐ x : Vec3 ∂volume,
      Complex.re (c (WithLp.toLp 2 x)) = regularizedPotentialCurl ha.1 δ hδ x i := by
    have hcomp := htransport.quasiMeasurePreserving.ae_eq_comp hc
    filter_upwards [hcomp] with x hx
    simpa [c, Function.comp_def] using hx
  have hf' : ∀ᵐ x : Vec3 ∂volume,
      f (WithLp.toLp 2 x) = (a x i : ℂ) := by
    have hcomp := htransport.quasiMeasurePreserving.ae_eq_comp hf
    filter_upwards [hcomp] with x hx
    simpa [Function.comp_def] using hx
  have hsub' : ∀ᵐ x : Vec3 ∂volume,
      (c - f) (WithLp.toLp 2 x) = c (WithLp.toLp 2 x) - f (WithLp.toLp 2 x) := by
    have hcomp := htransport.quasiMeasurePreserving.ae_eq_comp hsub
    filter_upwards [hcomp] with x hx
    simpa [Function.comp_def] using hx
  have hreal : (r ∘ (WithLp.toLp 2 : Vec3 → L2Vec3)) =ᵐ[volume] g := by
    filter_upwards [hsub', hc', hf'] with x hs hcx hfx
    change Complex.re ((c - f) (WithLp.toLp 2 x)) = g x
    rw [hs, Complex.sub_re, hcx, hfx]
    rfl
  have hreMem : MemLp r (2 : ℝ≥0∞) (volume : Measure L2Vec3) := by
    exact (Lp.memLp e).continuousLinearMap_comp Complex.reCLM
  have hmono : eLpNorm r (2 : ℝ≥0∞) (volume : Measure L2Vec3) ≤
      eLpNorm e (2 : ℝ≥0∞) (volume : Measure L2Vec3) := by
    apply eLpNorm_mono (hreMem.aestronglyMeasurable)
    intro y
    change ‖Complex.re (e y)‖ ≤ ‖e y‖
    rw [Real.norm_eq_abs]
    exact Complex.abs_re_le_norm (e y)
  calc
    eLpNorm g (2 : ℝ≥0∞) volume =
        eLpNorm (r ∘ (WithLp.toLp 2 : Vec3 → L2Vec3))
          (2 : ℝ≥0∞) volume := eLpNorm_congr_ae hreal.symm
    _ = eLpNorm r (2 : ℝ≥0∞) (volume : Measure L2Vec3) :=
      eLpNorm_comp_measurePreserving hreMem.aestronglyMeasurable htransport
    _ ≤ eLpNorm e (2 : ℝ≥0∞) (volume : Measure L2Vec3) := hmono

private theorem regularizedPotentialCurl_coord_error_tendsto
    {a : Vec3 → Vec3} (ha : IsWeakDivFreeL2 a) (i : Fin 3) :
    Tendsto (fun n : ℕ => eLpNorm
      (fun x : Vec3 => regularizedPotentialCurl ha.1 (regularizationScale n)
        (regularizationScale_pos n) x i - a x i)
      (2 : ℝ≥0∞) volume) atTop (𝓝 0) := by
  have hcomplex := regularizedPotentialCurlComponentLp_error_tendsto ha i
  have hbound (n : ℕ) : eLpNorm
      (fun x : Vec3 => regularizedPotentialCurl ha.1 (regularizationScale n)
        (regularizationScale_pos n) x i - a x i)
      (2 : ℝ≥0∞) volume ≤
      eLpNorm (regularizedPotentialCurlComponentLp ha.1 (regularizationScale n)
        (regularizationScale_pos n) i - weakFieldFourierComponent ha.1 i)
        (2 : ℝ≥0∞) (volume : Measure L2Vec3) :=
    regularizedPotentialCurl_coord_error_eLpNorm_le ha _ _ i
  have hnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ eLpNorm
      (fun x : Vec3 => regularizedPotentialCurl ha.1 (regularizationScale n)
        (regularizationScale_pos n) x i - a x i)
      (2 : ℝ≥0∞) volume :=
    Filter.Eventually.of_forall fun _ => bot_le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcomplex
    hnonneg (Filter.Eventually.of_forall hbound)

@[expose]
def regularizedPotentialCurlSequence {a : Vec3 → Vec3}
    (ha : IsWeakDivFreeL2 a) : ℕ → Vec3 → Vec3 :=
  fun n => regularizedPotentialCurl ha.1 (regularizationScale n)
    (regularizationScale_pos n)

@[expose]
def regularizedPotentialCurlCoordError {a : Vec3 → Vec3}
    (ha : IsWeakDivFreeL2 a) (n : ℕ) (i : Fin 3) : Vec3 → ℝ :=
  fun x => regularizedPotentialCurlSequence ha n x i - a x i

@[expose]
def regularizedPotentialCurlErrorMajor {a : Vec3 → Vec3}
    (ha : IsWeakDivFreeL2 a) (n : ℕ) : Vec3 → ℝ :=
  fun x => ∑ i : Fin 3, ‖regularizedPotentialCurlCoordError ha n i x‖

private theorem regularizedPotentialCurl_error_tendsto
    {a : Vec3 → Vec3} (ha : IsWeakDivFreeL2 a) :
    Tendsto (fun n : ℕ => eLpNorm (regularizedPotentialCurlSequence ha n - a)
      (2 : ℝ≥0∞) volume) atTop (𝓝 0) := by
  have hcoordMemLp (n : ℕ) (i : Fin 3) :
      MemLp (regularizedPotentialCurlCoordError ha n i) (2 : ℝ≥0∞) volume := by
    have hcurlLp : MemLp (regularizedPotentialCurlSequence ha n)
        (2 : ℝ≥0∞) volume := (regularizedPotentialCurl_memJ ha.1
          (regularizationScale n) (regularizationScale_pos n)).1
    exact (hcurlLp.eval i).sub (ha.1.eval i)
  have hsumLimit : Tendsto
      (fun n : ℕ => ∑ i : Fin 3,
        eLpNorm (regularizedPotentialCurlCoordError ha n i) (2 : ℝ≥0∞) volume)
      atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => ∑ i : Fin 3, eLpNorm
      (fun x : Vec3 => regularizedPotentialCurl ha.1 (regularizationScale n)
        (regularizationScale_pos n) x i - a x i) (2 : ℝ≥0∞) volume)
      atTop (𝓝 0)
    have h := tendsto_finsetSum (s := Finset.univ)
      (fun i hi => regularizedPotentialCurl_coord_error_tendsto ha i)
    simpa using h
  have hmajorLimit : Tendsto
      (fun n : ℕ => eLpNorm (regularizedPotentialCurlErrorMajor ha n)
        (2 : ℝ≥0∞) volume) atTop (𝓝 0) := by
    have hbound (n : ℕ) : eLpNorm (regularizedPotentialCurlErrorMajor ha n)
        (2 : ℝ≥0∞) volume ≤
        ∑ i : Fin 3,
          eLpNorm (regularizedPotentialCurlCoordError ha n i) (2 : ℝ≥0∞) volume := by
      calc
        eLpNorm (regularizedPotentialCurlErrorMajor ha n) (2 : ℝ≥0∞) volume ≤
            ∑ i : Fin 3, eLpNorm
              (fun x => ‖regularizedPotentialCurlCoordError ha n i x‖)
              (2 : ℝ≥0∞) volume := by
                have hmajorEq : regularizedPotentialCurlErrorMajor ha n =
                    ∑ i : Fin 3,
                      (fun x => ‖regularizedPotentialCurlCoordError ha n i x‖) := by
                  funext x
                  simp [regularizedPotentialCurlErrorMajor]
                rw [hmajorEq]
                simpa using (eLpNorm_sum_le (μ := volume) (p := (2 : ℝ≥0∞))
                  (f := fun i x => ‖regularizedPotentialCurlCoordError ha n i x‖)
                  (s := Finset.univ) (by norm_num : (1 : ℝ≥0∞) ≤ 2))
        _ = ∑ i : Fin 3,
              eLpNorm (regularizedPotentialCurlCoordError ha n i)
                (2 : ℝ≥0∞) volume := by
                apply Finset.sum_congr rfl
                intro i hi
                exact eLpNorm_norm (regularizedPotentialCurlCoordError ha n i)
                  (hcoordMemLp n i).aestronglyMeasurable
    have hnonneg : ∀ᶠ n : ℕ in atTop,
        0 ≤ eLpNorm (regularizedPotentialCurlErrorMajor ha n)
          (2 : ℝ≥0∞) volume :=
      Filter.Eventually.of_forall fun n => bot_le
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsumLimit
      hnonneg (Filter.Eventually.of_forall hbound)
  have herrorMeas (n : ℕ) :
      AEStronglyMeasurable (regularizedPotentialCurlSequence ha n - a) volume := by
    have hcurlLp : MemLp (regularizedPotentialCurlSequence ha n)
        (2 : ℝ≥0∞) volume := (regularizedPotentialCurl_memJ ha.1
          (regularizationScale n) (regularizationScale_pos n)).1
    exact hcurlLp.aestronglyMeasurable.sub ha.1.aestronglyMeasurable
  have hpoint (n : ℕ) (x : Vec3) :
      ‖regularizedPotentialCurlSequence ha n x - a x‖ ≤
        ‖regularizedPotentialCurlErrorMajor ha n x‖ := by
    have hmajorNonneg : 0 ≤ regularizedPotentialCurlErrorMajor ha n x := by
      exact Finset.sum_nonneg fun i _ => norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hmajorNonneg]
    apply (pi_norm_le_iff_of_nonneg hmajorNonneg).2
    intro i
    calc
      ‖(regularizedPotentialCurlSequence ha n x - a x) i‖ ≤
          ∑ j : Fin 3, ‖(regularizedPotentialCurlSequence ha n x - a x) j‖ :=
        Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ i)
      _ = regularizedPotentialCurlErrorMajor ha n x := by
        simp [regularizedPotentialCurlErrorMajor, regularizedPotentialCurlCoordError,
          regularizedPotentialCurlSequence]
  have herrorBound (n : ℕ) :
      eLpNorm (regularizedPotentialCurlSequence ha n - a) (2 : ℝ≥0∞) volume ≤
        eLpNorm (regularizedPotentialCurlErrorMajor ha n) (2 : ℝ≥0∞) volume :=
    eLpNorm_mono (herrorMeas n) (fun x => hpoint n x)
  have hlimMajor : Tendsto
      (fun n : ℕ => eLpNorm (regularizedPotentialCurlSequence ha n - a)
        (2 : ℝ≥0∞) volume) atTop (𝓝 0) := by
    have hnonneg : ∀ᶠ n : ℕ in atTop,
        0 ≤ eLpNorm (regularizedPotentialCurlSequence ha n - a)
          (2 : ℝ≥0∞) volume :=
      Filter.Eventually.of_forall fun n => bot_le
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmajorLimit
      hnonneg (Filter.Eventually.of_forall herrorBound)
  exact hlimMajor

/-- A square-integrable weakly divergence-free field lies in the closure of
compactly supported smooth divergence-free fields. -/
theorem weakDivFreeL2_isInJ {a : Vec3 → Vec3} (ha : IsWeakDivFreeL2 a) : IsInJ a := by
  let cseq := regularizedPotentialCurlSequence ha
  have hseq (n : ℕ) : IsInJ (cseq n) := by
    exact regularizedPotentialCurl_memJ ha.1 (regularizationScale n)
      (regularizationScale_pos n)
  have hlimit : Tendsto (fun n : ℕ => eLpNorm (cseq n - a)
      (2 : ℝ≥0∞) volume) atTop (𝓝 0) := by
    simpa [cseq] using regularizedPotentialCurl_error_tendsto ha
  exact isInJ_closed_under_L2_limit ha.1 hseq hlimit

/-- The closure definition of `J` agrees with weak divergence-freeness in
`L²`. -/
theorem isInJ_iff_weakDivFree {a : Vec3 → Vec3} : IsInJ a ↔ IsWeakDivFreeL2 a := by
  constructor
  · exact isInJ_weakDivFree
  · exact weakDivFreeL2_isInJ

end CKN

end
