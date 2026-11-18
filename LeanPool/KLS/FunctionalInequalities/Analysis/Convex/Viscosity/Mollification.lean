/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.SecondOrder.Expansion
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Viscosity.Touching
public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.LogDet.Inequalities
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Mollified log-determinant inequality

Supporting the convex Monge–Ampère infrastructure for Letwin
arXiv:2607.24164v1 Lemma 2.2. The declarations retain their original
source hypotheses, dimensional scope and mathematical conclusions.
-/

@[expose] public section

noncomputable section
open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein

section MollifiedLogdetBound

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
open FunctionalInequalities.Probability.Stein

/-! The log-determinant of the Hessian bounds the mollified Monge–Ampère density from above at
points with positive definite Hessian. -/

namespace FunctionalInequalities.Analysis

private lemma expansion_secondDifference {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {x g : EuclideanSpace ℝ (Fin n)}
    {B : Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ ε > 0, ∀ᶠ y in 𝓝 x,
      |u y - quadraticAt B x g (u x) y| ≤ ε * ‖y - x‖ ^ 2)
    (v : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun t : ℝ =>
      (u (x + t • v) + u (x - t • v) - 2 * u x) / t ^ 2)
      (𝓝[>] 0) (𝓝 ⟪v, Matrix.toEuclideanLin B v⟫) := by
  let q := ⟪v, Matrix.toEuclideanLin B v⟫
  have hp (t : ℝ) :
      quadraticAt B x g (u x) (x + t • v) =
        u x + t * ⟪g, v⟫ + (1 / 2) * (t ^ 2 * q) := by
    have he : x + t • v - x = t • v := by abel
    simp only [quadraticAt, he, map_smul, real_inner_smul_left,
      real_inner_smul_right, q]
    ring
  have hm (t : ℝ) :
      quadraticAt B x g (u x) (x - t • v) =
        u x - t * ⟪g, v⟫ + (1 / 2) * (t ^ 2 * q) := by
    simpa only [neg_smul, ← sub_eq_add_neg, neg_mul, neg_sq] using hp (-t)
  have htp : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
    have hc : Continuous (fun t : ℝ => x + t • v) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa only [zero_smul, add_zero] using hc.tendsto 0
  have htm : Tendsto (fun t : ℝ => x - t • v) (𝓝 0) (𝓝 x) := by
    have hc : Continuous (fun t : ℝ => x - t • v) :=
      continuous_const.sub (continuous_id.smul continuous_const)
    simpa only [zero_smul, sub_zero] using hc.tendsto 0
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := ε / (4 * (‖v‖ ^ 2 + 1))
  have hd : 0 < 4 * (‖v‖ ^ 2 + 1) := by positivity
  have hη : 0 < η := div_pos hε hd
  have hηeq : η * (4 * (‖v‖ ^ 2 + 1)) = ε :=
    div_mul_cancel₀ _ (ne_of_gt hd)
  have hsmall : 2 * η * ‖v‖ ^ 2 < ε := by
    nlinarith [sq_nonneg ‖v‖]
  filter_upwards [(htp.eventually (h η hη)).filter_mono nhdsWithin_le_nhds,
    (htm.eventually (h η hη)).filter_mono nhdsWithin_le_nhds,
    eventually_mem_nhdsWithin] with t ht₁ ht₂ ht
  have htpos : 0 < t := ht
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos htpos
  have hnum :
      |(u (x + t • v) + u (x - t • v) - 2 * u x) - t ^ 2 * q| ≤
        2 * η * t ^ 2 * ‖v‖ ^ 2 := by
    calc
      _ = |(u (x + t • v) - quadraticAt B x g (u x) (x + t • v)) +
          (u (x - t • v) - quadraticAt B x g (u x) (x - t • v))| := by
        rw [hp, hm]
        congr 1
        ring
      _ ≤ |u (x + t • v) - quadraticAt B x g (u x) (x + t • v)| +
          |u (x - t • v) - quadraticAt B x g (u x) (x - t • v)| :=
        abs_add_le _ _
      _ ≤ η * ‖x + t • v - x‖ ^ 2 + η * ‖x - t • v - x‖ ^ 2 :=
        add_le_add ht₁ ht₂
      _ = _ := by
        have he₁ : x + t • v - x = t • v := by abel
        have he₂ : x - t • v - x = -(t • v) := by abel
        rw [he₁, he₂, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
        ring
  have heq :
      (u (x + t • v) + u (x - t • v) - 2 * u x) / t ^ 2 - q =
        ((u (x + t • v) + u (x - t • v) - 2 * u x) - t ^ 2 * q) / t ^ 2 := by
    field_simp
  change dist ((u (x + t • v) + u (x - t • v) - 2 * u x) / t ^ 2) q < ε
  rw [Real.dist_eq, heq, abs_div, abs_of_pos ht2]
  apply (div_lt_iff₀ ht2).mpr
  have hh := mul_lt_mul_of_pos_right hsmall ht2
  nlinarith

private lemma smooth_secondDifference {n : ℕ}
    {w : EuclideanSpace ℝ (Fin n) → ℝ} (hw : ContDiff ℝ 2 w)
    (x v : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun t : ℝ =>
      (w (x + t • v) + w (x - t • v) - 2 * w x) / t ^ 2)
      (𝓝[>] 0) (𝓝 ⟪v, Matrix.toEuclideanLin (hessianMatrix w x) v⟫) := by
  apply expansion_secondDifference
    (g := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
      (fderiv ℝ w x))
  intro ε hε
  obtain ⟨r, hr, hb⟩ := exists_taylor_two_hessianMatrix_bound hw.contDiffAt hε
  filter_upwards [ball_mem_nhds x hr] with y hy
  simpa only [quadraticAt, InnerProductSpace.toDual_symm_apply] using hb y hy

private lemma convolution_shift {n : ℕ}
    (ρ u : EuclideanSpace ℝ (Fin n) → ℝ)
    (x a : EuclideanSpace ℝ (Fin n)) :
    (∫ y, u (y + a) * ρ (x - y)) =
      convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume (x + a) := by
  rw [← integral_sub_left_eq_self (fun y => u (y + a) * ρ (x - y)) volume x]
  unfold convolution
  apply integral_congr_ae
  filter_upwards [] with y
  have he : x - y + a = x + a - y := by abel
  simp only [sub_sub_cancel, he, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  exact mul_comm _ _

private lemma convolution_hessian_integral {n : ℕ}
    {ρ u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hρ : ContDiff ℝ 2 ρ) (hρc : HasCompactSupport ρ) (hu : Continuous u)
    (x v : EuclideanSpace ℝ (Fin n)) :
    ⟪v, Matrix.toEuclideanLin
      (hessianMatrix (convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x) v⟫ =
      ∫ y, u y * iteratedFDeriv ℝ 2 (fun z => ρ (x - z)) y (fun _ => v) := by
  let χ := fun y => ρ (x - y)
  let w := convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hχ : ContDiff ℝ 2 χ := hρ.comp (contDiff_const.sub contDiff_id)
  have hχc : HasCompactSupport χ := hρc.comp_homeomorph (Homeomorph.subLeft x)
  have hi (a : EuclideanSpace ℝ (Fin n)) :
      Integrable (fun y => u (y + a) * χ y) volume := by
    have hc : Continuous (fun y => u (y + a) * χ y) :=
      (hu.comp (continuous_id.add continuous_const)).mul hχ.continuous
    exact hc.integrable_of_hasCompactSupport hχc.mul_left
  have hi₀ : Integrable (fun y => u y * χ y) volume := by
    simpa only [add_zero] using hi 0
  have he (t : ℝ) :
      (∫ y, (u (y + t • v) + u (y - t • v) - 2 * u y) / t ^ 2 * χ y) =
        (w (x + t • v) + w (x - t • v) - 2 * w x) / t ^ 2 := by
    have him : Integrable (fun y => u (y - t • v) * χ y) volume := by
      simpa only [neg_smul, ← sub_eq_add_neg] using hi ((-t) • v)
    have hip : Integrable
        (fun y => u (y + t • v) * χ y + u (y - t • v) * χ y) volume :=
      (hi (t • v)).add him
    calc
      _ = (∫ y, ((u (y + t • v) * χ y + u (y - t • v) * χ y) -
          2 * (u y * χ y)) / t ^ 2) := by
        apply integral_congr_ae
        filter_upwards [] with y
        ring
      _ = ((∫ y, u (y + t • v) * χ y) +
          (∫ y, u (y - t • v) * χ y) -
          2 * (∫ y, u y * χ y)) / t ^ 2 := by
        rw [integral_div,
          integral_sub
            (f := fun y => u (y + t • v) * χ y + u (y - t • v) * χ y)
            (g := fun y => 2 * (u y * χ y)) hip (hi₀.const_mul 2),
          integral_add
            (f := fun y => u (y + t • v) * χ y)
            (g := fun y => u (y - t • v) * χ y) (hi (t • v)) him,
          integral_const_mul]
      _ = _ := by
        have he₁ := convolution_shift ρ u x (t • v)
        have he₂ := convolution_shift ρ u x (-(t • v))
        have he₀ := convolution_shift ρ u x 0
        simpa only [χ, w, add_zero, ← sub_eq_add_neg] using
          congrArg (fun p : ℝ × ℝ × ℝ => (p.1 + p.2.1 - 2 * p.2.2) / t ^ 2)
            (show
              ((∫ y, u (y + t • v) * ρ (x - y)),
                (∫ y, u (y + -(t • v)) * ρ (x - y)),
                (∫ y, u (y + 0) * ρ (x - y))) =
              (convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume (x + t • v),
                convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume (x + -(t • v)),
                convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume (x + 0)) from
              by rw [he₁, he₂, he₀])
  have hw : ContDiff ℝ 2 w :=
    hρc.contDiff_convolution_left _ hρ hu.locallyIntegrable
  exact tendsto_nhds_unique (smooth_secondDifference hw x v)
    ((tendsto_integral_secondDifference_mul hu hχ hχc v).congr he)

private lemma convolution_convex {n : ℕ}
    {ρ u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hconv : ConvexOn ℝ univ u) :
    ConvexOn ℝ univ (convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume) := by
  have hu : Continuous u := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  have hi (z : EuclideanSpace ℝ (Fin n)) :
      Integrable (fun y => ρ y * u (z - y)) volume := by
    have hc : Continuous (fun y => ρ y * u (z - y)) :=
      hρ.mul (hu.comp (continuous_const.sub continuous_id))
    exact hc.integrable_of_hasCompactSupport hρc.mul_right
  refine ⟨convex_univ, ?_⟩
  intro a _ b _ s t hs ht hst
  change (∫ y, ρ y * u (s • a + t • b - y)) ≤
    s * (∫ y, ρ y * u (a - y)) + t * (∫ y, ρ y * u (b - y))
  calc
    _ ≤ ∫ y, s * (ρ y * u (a - y)) + t * (ρ y * u (b - y)) := by
      apply integral_mono (hi _) (((hi a).const_mul s).add ((hi b).const_mul t))
      intro y
      change ρ y * u (s • a + t • b - y) ≤
        s * (ρ y * u (a - y)) + t * (ρ y * u (b - y))
      have hc := hconv.2 (mem_univ (a - y)) (mem_univ (b - y)) hs ht hst
      have he : s • (a - y) + t • (b - y) = s • a + t • b - y := by
        calc
          _ = s • a + t • b - (s + t) • y := by module
          _ = _ := by rw [hst, one_smul]
      rw [he] at hc
      change u (s • a + t • b - y) ≤ s * u (a - y) + t * u (b - y) at hc
      calc
        _ ≤ ρ y * (s * u (a - y) + t * u (b - y)) :=
          mul_le_mul_of_nonneg_left hc (hρ0 y)
        _ = _ := by ring
    _ = _ := by
      rw [integral_add
        (f := fun y => s * (ρ y * u (a - y)))
        (g := fun y => t * (ρ y * u (b - y)))
        ((hi a).const_mul s) ((hi b).const_mul t),
        integral_const_mul, integral_const_mul]

private lemma matrix_quadratic_sum {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    ⟪v, Matrix.toEuclideanLin A v⟫ =
      ∑ i, ∑ j, v.ofLp i * (A i j * v.ofLp j) := by
  rw [Matrix.toLpLin_apply 2 2, PiLp.inner_apply]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial,
    Matrix.mulVec, dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma trace_spectral_quadratic {n : ℕ}
    {J : Matrix (Fin n) (Fin n) ℝ} (hJ : J.IsHermitian)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (J * A).trace =
      ∑ i, hJ.eigenvalues i *
        ⟪hJ.eigenvectorBasis i, Matrix.toEuclideanLin A (hJ.eigenvectorBasis i)⟫ := by
  classical
  let U : Matrix (Fin n) (Fin n) ℝ := hJ.eigenvectorUnitary
  let D := Matrix.diagonal hJ.eigenvalues
  have hs : J = U * D * star U := by
    simpa only [Unitary.conjStarAlgAut_apply, Function.comp_def,
      RCLike.ofReal_real_eq_id, id_eq] using hJ.spectral_theorem
  have he (i : Fin n) :
      (star U * A * U) i i =
        ⟪hJ.eigenvectorBasis i, Matrix.toEuclideanLin A (hJ.eigenvectorBasis i)⟫ := by
    rw [matrix_quadratic_sum]
    simp only [Matrix.mul_apply, Matrix.star_apply, star_trivial, Finset.sum_mul,
      U, Matrix.IsHermitian.eigenvectorUnitary_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  calc
    (J * A).trace = (U * D * star U * A).trace := by rw [hs]
    _ = (D * (star U * A) * U).trace := by
      rw [Matrix.mul_assoc U D (star U), Matrix.mul_assoc U (D * star U) A,
        Matrix.trace_mul_comm U ((D * star U) * A), Matrix.mul_assoc D (star U) A]
    _ = (D * (star U * A * U)).trace := by rw [Matrix.mul_assoc]
    _ = _ := by
      simp only [D, Matrix.trace, Matrix.diag, Matrix.diagonal_mul, he]

private lemma second_weight_integrable {n : ℕ}
    {u χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : Continuous u) (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (v : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y => u y * iteratedFDeriv ℝ 2 χ y (fun _ => v)) volume := by
  let L := ContinuousMultilinearMap.apply ℝ
    (fun _ : Fin 2 => EuclideanSpace ℝ (Fin n)) ℝ (fun _ => v)
  have hc : Continuous (fun y => iteratedFDeriv ℝ 2 χ y (fun _ => v)) := by
    change Continuous (L ∘ iteratedFDeriv ℝ 2 χ)
    exact L.continuous.comp (ContDiff.continuous_iteratedFDeriv (by norm_num) hχ)
  have hs : HasCompactSupport (fun y => iteratedFDeriv ℝ 2 χ y (fun _ => v)) := by
    change HasCompactSupport (L ∘ iteratedFDeriv ℝ 2 χ)
    exact (hχc.iteratedFDeriv 2).comp_left (g := L) (map_zero L)
  exact (hu.mul hc).integrable_of_hasCompactSupport hs.mul_left

private lemma trace_integral_bound {n : ℕ}
    {u F χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) (hF : Continuous F)
    (hae : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∃ B : Matrix (Fin n) (Fin n) ℝ, B.IsHermitian ∧ B.PosDef ∧
        F y ≤ Real.log B.det ∧ ∃ g : EuclideanSpace ℝ (Fin n),
          ∀ ε > 0, ∀ᶠ z in 𝓝 y,
            |u z - quadraticAt B y g (u y) z| ≤ ε * ‖z - y‖ ^ 2)
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) (hχ0 : ∀ y, 0 ≤ χ y)
    (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : ∀ v : EuclideanSpace ℝ (Fin n),
      ⟪v, Matrix.toEuclideanLin H v⟫ =
        ∫ y, u y * iteratedFDeriv ℝ 2 χ y (fun _ => v))
    (J : Matrix (Fin n) (Fin n) ℝ) (hJ : J.PosDef) :
    (∫ y, (F y + Real.log J.det + n) * χ y) ≤ (J * H).trace := by
  classical
  let v := hJ.isHermitian.eigenvectorBasis
  let c := hJ.isHermitian.eigenvalues
  have hc (i : Fin n) : 0 ≤ c i := (hJ.eigenvalues_pos i).le
  have hg : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∀ ε > 0, ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
        (F y + Real.log J.det + n) - ε ≤
          ∑ i, c i * ((u (y + t • v i) + u (y - t • v i) - 2 * u y) / t ^ 2) := by
    filter_upwards [hae] with y hy
    obtain ⟨B, _, hB, hFB, g, hexp⟩ := hy
    have hlim :
        Tendsto (fun t : ℝ => ∑ i, c i *
          ((u (y + t • v i) + u (y - t • v i) - 2 * u y) / t ^ 2))
          (𝓝[>] 0) (𝓝 ((J * B).trace)) := by
      rw [trace_spectral_quadratic hJ.isHermitian B]
      exact tendsto_finsetSum _ fun i _ =>
        (expansion_secondDifference hexp (v i)).const_mul (c i)
    have htr : F y + Real.log J.det + n ≤ (J * B).trace :=
      ((forall_posDef_add_log_det_le_trace_iff hB.posSemidef (F y)).mpr
        ⟨hB, (Real.le_log_iff_exp_le hB.det_pos).mp hFB⟩) J hJ
    intro ε hε
    have hev := hlim.eventually_const_lt (show
      F y + Real.log J.det + n - ε < (J * B).trace by linarith)
    obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhdsWithin_iff.mp hev
    refine ⟨δ, hδ, fun t ht htd => (hd ⟨?_, ht⟩).le⟩
    simpa only [mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht] using htd
  have hi := integral_mul_le_integral_mul_sum_iteratedFDeriv hconv
    (fun i : Fin n => v i) hc hχ hχc hχ0
    ((hF.add continuous_const).add continuous_const).aestronglyMeasurable hg
  have hu : Continuous u := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  have hdi (i : Fin n) := second_weight_integrable hu hχ hχc (v i)
  have he :
      (∫ y, u y * ∑ i, c i * iteratedFDeriv ℝ 2 χ y (fun _ => v i)) =
        (J * H).trace := by
    calc
      _ = ∫ y, ∑ i, c i * (u y * iteratedFDeriv ℝ 2 χ y (fun _ => v i)) := by
        apply integral_congr_ae
        filter_upwards [] with y
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ i, c i * ∫ y, u y * iteratedFDeriv ℝ 2 χ y (fun _ => v i) := by
        rw [integral_finsetSum _ (fun i _ => (hdi i).const_mul (c i))]
        simp only [integral_const_mul]
      _ = _ := by
        rw [trace_spectral_quadratic hJ.isHermitian H]
        apply Finset.sum_congr rfl
        intro i _
        rw [hH]
  exact he ▸ hi

/--
**Mollified log-det lower bound** (via Fatou instead of the viscosity–distribution lemma): if
the
convex `u` has at almost every point a second-order expansion with a positive definite symmetric
matrix
`B` with `F x ≤ log det B`, `F` continuous, then every mollification `uφ := φ.normed ⋆ u` has a
positive
definite Hessian with `(φ.normed ⋆ F)(x) ≤ log det ∇²uφ(x)`. -/
theorem posDef_and_convolution_le_log_det_hessianMatrix {n : ℕ}
    {u F : EuclideanSpace ℝ (Fin n) → ℝ} (hconv : ConvexOn ℝ univ u) (hF : Continuous F)
    (hae :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        ∃ B : Matrix (Fin n) (Fin n) ℝ,
          B.IsHermitian ∧
            B.PosDef ∧
              F x ≤ Real.log B.det ∧
                ∃ g : EuclideanSpace ℝ (Fin n),
                  ∀ ε > 0, ∀ᶠ y in 𝓝 x, |u y - quadraticAt B x g (u x) y| ≤ ε * ‖y - x‖ ^ 2)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) :
    (hessianMatrix (convolution (φ.normed volume) u (ContinuousLinearMap.lsmul ℝ ℝ) volume)
          x).PosDef ∧
      convolution (φ.normed volume) F (ContinuousLinearMap.lsmul ℝ ℝ) volume x ≤
        Real.log
          (hessianMatrix
              (convolution (φ.normed volume) u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x).det := by
  classical
  let ρ := φ.normed volume
  let w := convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume
  let χ := fun y => ρ (x - y)
  let H := hessianMatrix w x
  let b := convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume x
  have hρ : ContDiff ℝ 2 ρ := φ.contDiff_normed
  have hρc : HasCompactSupport ρ := φ.hasCompactSupport_normed
  have hρ0 : ∀ y, 0 ≤ ρ y := φ.nonneg_normed
  have hu : Continuous u := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  have hw : ContDiff ℝ 2 w := hρc.contDiff_convolution_left _ hρ hu.locallyIntegrable
  have hwconv : ConvexOn ℝ univ w := convolution_convex hρ.continuous hρc hρ0 hconv
  have hH : H.PosSemidef :=
    posSemidef_hessianMatrix_of_upper_touch hwconv hw.contDiffAt rfl
      (Filter.Eventually.of_forall fun _ => le_rfl)
  have hχ : ContDiff ℝ 2 χ := hρ.comp (contDiff_const.sub contDiff_id)
  have hχc : HasCompactSupport χ := hρc.comp_homeomorph (Homeomorph.subLeft x)
  have hχ0 : ∀ y, 0 ≤ χ y := fun y => hρ0 (x - y)
  have hχi : Integrable χ volume := hχ.continuous.integrable_of_hasCompactSupport hχc
  have hχone : (∫ y, χ y) = 1 := by
    dsimp only [χ]
    rw [integral_sub_left_eq_self]
    exact φ.integral_normed
  have hb : (∫ y, F y * χ y) = b := by
    simpa only [χ, b, add_zero] using convolution_shift ρ F x 0
  have hFi : Integrable (fun y => F y * χ y) volume :=
    (hF.mul hχ.continuous).integrable_of_hasCompactSupport hχc.mul_left
  have htrace :
    ∀ J : Matrix (Fin n) (Fin n) ℝ, J.PosDef → b + Real.log J.det + n ≤ (J * H).trace := by
    intro J hJ
    have ht :=
      trace_integral_bound hconv hF hae hχ hχc hχ0 H
        (fun v => convolution_hessian_integral hρ hρc hu x v) J hJ
    have he : (∫ y, (F y + Real.log J.det + n) * χ y) = b + Real.log J.det + n := by
      calc
        _ = ∫ y, (F y * χ y + Real.log J.det * χ y) + (n : ℝ) * χ y := by
          apply integral_congr_ae
          filter_upwards [] with y
          ring
        _ = _ := by
          rw [integral_add (f := fun y => F y * χ y + Real.log J.det * χ y) (g := fun y =>
              (n : ℝ) * χ y) (hFi.add (hχi.const_mul (Real.log J.det))) (hχi.const_mul (n : ℝ)),
            integral_add (f := fun y => F y * χ y) (g := fun y => Real.log J.det * χ y) hFi
              (hχi.const_mul (Real.log J.det)),
            integral_const_mul, integral_const_mul, hχone, hb, mul_one, mul_one]
    exact he ▸ ht
  obtain ⟨hpos, hdet⟩ := (forall_posDef_add_log_det_le_trace_iff hH b).mp htrace
  exact ⟨hpos, (Real.le_log_iff_exp_le hpos.det_pos).mpr hdet⟩

end FunctionalInequalities.Analysis

end MollifiedLogdetBound
