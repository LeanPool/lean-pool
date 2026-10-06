/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Transport
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpApproximation
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorRegularity
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# The transport cancellation for Sobolev velocities

For a smooth bounded divergence-free transport field `V` with bounded
derivatives and a square-integrable velocity `u` with square-integrable weak
gradient, `∑ᵢⱼ ∫ Vᵢ uⱼ ∂ᵢuⱼ = 0`. This is the cancellation of the transport
term in the energy equality of `lem:regularised-forced`: for smooth velocities
it is an integration by parts of `½ V·∇|u|²`, and it passes to Sobolev
velocities through spatial mollification.
-/

public section

open MeasureTheory Filter
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

noncomputable section

namespace CKN.Leray

/-- Integration by parts of `Vᵢ ∂ᵢ(w²)` for a smooth square-integrable
function with square-integrable derivative and a smooth bounded coefficient
with bounded derivative. -/
theorem integral_mul_fderiv_sq_eq_neg (V w : Vec3 → ℝ) (i : Fin 3)
    (hV : ContDiff ℝ 1 V) (hw : ContDiff ℝ 1 w) (M : ℝ)
    (hVb : ∀ x, ‖V x‖ ≤ M) (hdVb : ∀ x, ‖fderiv ℝ V x (CKN.basisVec i)‖ ≤ M)
    (hw2 : MemLp w 2 volume) (hdw2 : MemLp (fun x => fderiv ℝ w x (CKN.basisVec i)) 2 volume) :
    ∫ x, V x * (2 * (w x * fderiv ℝ w x (CKN.basisVec i))) =
      -∫ x, fderiv ℝ V x (CKN.basisVec i) * w x ^ 2 := by
  have hwd : ∀ x, HasFDerivAt (fun y => w y ^ 2)
      (w x • fderiv ℝ w x + w x • fderiv ℝ w x) x := by
    intro x
    have h := (hw.differentiable one_ne_zero x).hasFDerivAt
    have hmul := h.mul h
    convert hmul using 1
    funext y
    simp only [Pi.mul_apply, sq]
  have hgder : ∀ x, fderiv ℝ (fun y => w y ^ 2) x (CKN.basisVec i) =
      2 * (w x * fderiv ℝ w x (CKN.basisVec i)) := by
    intro x
    rw [(hwd x).fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hVmeas : AEStronglyMeasurable V volume := hV.continuous.aestronglyMeasurable
  have hdVmeas : AEStronglyMeasurable (fun x => fderiv ℝ V x (CKN.basisVec i)) volume :=
    ((hV.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable
  have hsq : Integrable (fun x => w x ^ 2) volume :=
    (memLp_two_iff_integrable_sq hw2.aestronglyMeasurable).1 hw2
  have hprod : Integrable (fun x => w x * fderiv ℝ w x (CKN.basisVec i)) volume :=
    hw2.integrable_mul hdw2
  have h1 : Integrable (fun x => fderiv ℝ V x (CKN.basisVec i) * w x ^ 2) volume :=
    hsq.bdd_mul hdVmeas (Eventually.of_forall hdVb)
  have h2 : Integrable (fun x => V x * fderiv ℝ (fun y => w y ^ 2) x (CKN.basisVec i)) volume := by
    simp_rw [hgder]
    exact (hprod.const_mul 2).bdd_mul hVmeas (Eventually.of_forall hVb)
  have h3 : Integrable (fun x => V x * w x ^ 2) volume :=
    hsq.bdd_mul hVmeas (Eventually.of_forall hVb)
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := V) (g := fun y => w y ^ 2) (v := CKN.basisVec i) h1 h2 h3
    (fun x _ => hV.differentiable one_ne_zero x)
    (fun x _ => (hwd x).differentiableAt)
  simp_rw [hgder] at hibp
  exact hibp

/-- The transport cancellation for smooth velocities. -/
theorem smooth_transport_cancellation (V w : Vec3 → Vec3)
    (hV : ∀ i, ContDiff ℝ 1 (fun x => V x i)) (hw : ∀ j, ContDiff ℝ 1 (fun x => w x j))
    (M : ℝ) (hVb : ∀ x i, ‖V x i‖ ≤ M)
    (hdVb : ∀ x i, ‖fderiv ℝ (fun y => V y i) x (CKN.basisVec i)‖ ≤ M)
    (hdiv : ∀ x, ∑ i : Fin 3, fderiv ℝ (fun y => V y i) x (CKN.basisVec i) = 0)
    (hw2 : ∀ j, MemLp (fun x => w x j) 2 volume)
    (hdw2 : ∀ i j, MemLp (fun x => fderiv ℝ (fun y => w y j) x (CKN.basisVec i)) 2 volume) :
    ∑ i : Fin 3, ∑ j : Fin 3,
      ∫ x, V x i * (w x j * fderiv ℝ (fun y => w y j) x (CKN.basisVec i)) = 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hibp := fun i => integral_mul_fderiv_sq_eq_neg (fun x => V x i) (fun x => w x j) i
    (hV i) (hw j) M (fun x => hVb x i) (fun x => hdVb x i) (hw2 j) (hdw2 i j)
  have hVmeas : ∀ i, AEStronglyMeasurable (fun x => V x i) volume := fun i =>
    (hV i).continuous.aestronglyMeasurable
  have hint : ∀ i, Integrable (fun x => V x i *
      (w x j * fderiv ℝ (fun y => w y j) x (CKN.basisVec i))) volume := fun i =>
    ((hw2 j).integrable_mul (hdw2 i j)).bdd_mul (hVmeas i) (Eventually.of_forall fun x => hVb x i)
  have hdint : ∀ i, Integrable (fun x => fderiv ℝ (fun y => V y i) x (CKN.basisVec i) *
      w x j ^ 2) volume := fun i =>
    ((memLp_two_iff_integrable_sq (hw2 j).aestronglyMeasurable).1 (hw2 j)).bdd_mul
      (((hV i).continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable
      (Eventually.of_forall fun x => hdVb x i)
  have hsum : ∑ i : Fin 3, ∫ x, fderiv ℝ (fun y => V y i) x (CKN.basisVec i) * w x j ^ 2 = 0 := by
    rw [← integral_finsetSum _ fun i _ => hdint i]
    simp_rw [← Finset.sum_mul, hdiv, zero_mul, integral_zero]
  have htwo : ∀ i, ∫ x, V x i * (2 * (w x j * fderiv ℝ (fun y => w y j) x (CKN.basisVec i))) =
      2 * ∫ x, V x i * (w x j * fderiv ℝ (fun y => w y j) x (CKN.basisVec i)) := by
    intro i
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  have hfinal : 2 * ∑ i : Fin 3, ∫ x, V x i * (w x j * fderiv ℝ (fun y => w y j) x (CKN.basisVec i))
      = 0 := by
    rw [Finset.mul_sum]
    simp_rw [← htwo, hibp]
    rw [Finset.sum_neg_distrib, hsum, neg_zero]
  linarith only [hfinal]

/-- Products of `L²`-convergent sequences have convergent integrals. -/
theorem tendsto_integral_mul_of_tendsto_eLpNorm_two {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (F G : ℕ → α → ℝ) (f g : α → ℝ)
    (hF : ∀ n, MemLp (F n) 2 μ) (hG : ∀ n, MemLp (G n) 2 μ) (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ)
    (hFc : Tendsto (fun n => eLpNorm (F n - f) 2 μ) atTop (𝓝 0))
    (hGc : Tendsto (fun n => eLpNorm (G n - g) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, F n x * G n x ∂μ) atTop (𝓝 (∫ x, f x * g x ∂μ)) := by
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  let FLp : ℕ → Lp ℝ 2 μ := fun n => (hF n).toLp (F n)
  let GLp : ℕ → Lp ℝ 2 μ := fun n => (hG n).toLp (G n)
  have hFLp : Tendsto FLp atTop (𝓝 (hf.toLp f)) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    refine hFc.congr fun n => (eLpNorm_congr_ae ?_).symm
    filter_upwards [(hF n).coeFn_toLp, hf.coeFn_toLp] with x h1 h2
    simp only [Pi.sub_apply, FLp, h1, h2]
  have hGLp : Tendsto GLp atTop (𝓝 (hg.toLp g)) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    refine hGc.congr fun n => (eLpNorm_congr_ae ?_).symm
    filter_upwards [(hG n).coeFn_toLp, hg.coeFn_toLp] with x h1 h2
    simp only [Pi.sub_apply, GLp, h1, h2]
  have hinner := hFLp.inner (𝕜 := ℝ) hGLp
  have heq : ∀ (a b : α → ℝ) (ha : MemLp a 2 μ) (hb : MemLp b 2 μ),
      inner ℝ (ha.toLp a) (hb.toLp b) = ∫ x, a x * b x ∂μ := by
    intro a b ha hb
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x h1 h2
    rw [h1, h2]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  rw [heq f g hf hg] at hinner
  exact hinner.congr fun n => heq (F n) (G n) (hF n) (hG n)

/-- The transport cancellation for velocities with square-integrable weak
gradients. -/
theorem transport_cancellation (V u : Vec3 → Vec3) (D : Vec3 → Fin 3 → Vec3)
    (hV : ∀ i, ContDiff ℝ 1 (fun x => V x i))
    (M : ℝ) (hVb : ∀ x i, ‖V x i‖ ≤ M)
    (hdVb : ∀ x i, ‖fderiv ℝ (fun y => V y i) x (CKN.basisVec i)‖ ≤ M)
    (hdiv : ∀ x, ∑ i : Fin 3, fderiv ℝ (fun y => V y i) x (CKN.basisVec i) = 0)
    (hu2 : ∀ j, MemLp (fun x => u x j) 2 volume)
    (hD2 : ∀ i j, MemLp (fun x => D x i j) 2 volume)
    (hweak : ∀ i j, CKN.HasWeakPartialDerivOn (Set.univ : Set Vec3) i (fun x => u x j)
      (fun x => D x i j)) :
    ∑ i : Fin 3, ∑ j : Fin 3, ∫ x, V x i * (u x j * D x i j) = 0 := by
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδ : ∀ n, 0 < δ n := fun n => by positivity
  have hδt : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let w : ℕ → Vec3 → Vec3 := fun n x j => CKN.mollify (fun y => u y j) (δ n) (hδ n) x
  let md : ℕ → Fin 3 → Fin 3 → Vec3 → ℝ := fun n i j =>
    CKN.mollify (fun y => D y i j) (δ n) (hδ n)
  have hloc : ∀ j, LocallyIntegrable (fun x => u x j) volume := fun j =>
    (hu2 j).locallyIntegrable (by norm_num)
  have hDloc : ∀ i j, LocallyIntegrable (fun x => D x i j) volume := fun i j =>
    (hD2 i j).locallyIntegrable (by norm_num)
  have hder : ∀ n i j x, fderiv ℝ (fun y => w n y j) x (CKN.basisVec i) = md n i j x := by
    intro n i j x
    exact CKN.fderiv_mollify_eq_mollify_of_hasWeakPartialDerivOn isOpen_univ (hloc j)
      (hDloc i j) (hweak i j) (hδ n) (Set.subset_univ _)
  have hwsmooth : ∀ n j, ContDiff ℝ 1 (fun x => w n x j) := fun n j =>
    CKN.mollify_contDiff (hδ n) (hloc j)
  have hw2 : ∀ n j, MemLp (fun x => w n x j) 2 volume := fun n j =>
    CKN.Foundation.Heat.mollify_memLp_of_memLp (by norm_num) (by norm_num) (hu2 j) (hδ n)
  have hmd2 : ∀ n i j, MemLp (md n i j) 2 volume := fun n i j =>
    CKN.Foundation.Heat.mollify_memLp_of_memLp (by norm_num) (by norm_num) (hD2 i j) (hδ n)
  have hsmooth : ∀ n, ∑ i : Fin 3, ∑ j : Fin 3,
      ∫ x, V x i * (w n x j * md n i j x) = 0 := by
    intro n
    have h := smooth_transport_cancellation V (w n) hV (hwsmooth n) M hVb hdVb hdiv (hw2 n)
      (fun i j => by simp_rw [hder]; exact hmd2 n i j)
    simp_rw [hder] at h
    exact h
  have hVmeas : ∀ i, AEStronglyMeasurable (fun x => V x i) volume := fun i =>
    (hV i).continuous.aestronglyMeasurable
  have hlim : ∀ i j, Tendsto (fun n => ∫ x, V x i * (w n x j * md n i j x)) atTop
      (𝓝 (∫ x, V x i * (u x j * D x i j))) := by
    intro i j
    have hVu : MemLp (fun x => V x i * u x j) 2 volume :=
      (hu2 j).of_le_mul (c := M) ((hVmeas i).mul (hu2 j).aestronglyMeasurable)
        (Eventually.of_forall fun x => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hVb x i) (norm_nonneg _))
    have hVw : ∀ n, MemLp (fun x => V x i * w n x j) 2 volume := fun n =>
      (hw2 n j).of_le_mul (c := M) ((hVmeas i).mul (hw2 n j).aestronglyMeasurable)
        (Eventually.of_forall fun x => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hVb x i) (norm_nonneg _))
    have hconvu := CKN.tendsto_eLpNorm_sub_zero_mollify (by norm_num) (by norm_num) (hu2 j)
      hδt hδ
    have hconvD := CKN.tendsto_eLpNorm_sub_zero_mollify (by norm_num) (by norm_num) (hD2 i j)
      hδt hδ
    have hVconv : Tendsto (fun n => eLpNorm ((fun x => V x i * w n x j) -
        fun x => V x i * u x j) 2 volume) atTop (𝓝 0) := by
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hVb 0 i)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by simpa using (ENNReal.Tendsto.const_mul hconvu (Or.inr ENNReal.ofReal_ne_top) :
          Tendsto (fun n => ENNReal.ofReal M * eLpNorm (fun x =>
            CKN.mollify (fun y => u y j) (δ n) (hδ n) x - u x j) 2 volume) atTop
            (𝓝 (ENNReal.ofReal M * 0)))) (fun _ => bot_le) fun n => ?_
      refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        (((hVw n).aestronglyMeasurable).sub hVu.aestronglyMeasurable)
        (Eventually.of_forall fun x => ?_) 2
      simp only [Pi.sub_apply, w]
      rw [← mul_sub, norm_mul]
      exact mul_le_mul_of_nonneg_right (hVb x i) (norm_nonneg _)
    have h := tendsto_integral_mul_of_tendsto_eLpNorm_two
      (fun n x => V x i * w n x j) (fun n => md n i j)
      (fun x => V x i * u x j) (fun x => D x i j) hVw (fun n => hmd2 n i j) hVu (hD2 i j)
      hVconv (by simpa [md, Pi.sub_def] using hconvD)
    refine h.congr' (Eventually.of_forall fun n => ?_) |>.trans ?_
    · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      ring
    · rw [show (∫ x, V x i * u x j * D x i j) = ∫ x, V x i * (u x j * D x i j) from
        integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)]
  have hsumlim : Tendsto (fun n => ∑ i : Fin 3, ∑ j : Fin 3,
      ∫ x, V x i * (w n x j * md n i j x)) atTop
      (𝓝 (∑ i : Fin 3, ∑ j : Fin 3, ∫ x, V x i * (u x j * D x i j))) :=
    tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => hlim i j
  simp_rw [hsmooth] at hsumlim
  exact tendsto_nhds_unique hsumlim tendsto_const_nhds

end CKN.Leray

end
