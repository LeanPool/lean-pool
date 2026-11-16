/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Generator.Range
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Curvature
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Bochner.Basic
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.BrascampLieb

/-!
# Dual gradient estimates and the H⁻¹ variance bound

Supports Letwin arXiv:2607.24164v1, Proposition 2.8, through three interfaces:
- nonnegativity of a compact-test dual constant for a positive-dimensional law
  with continuous tilted density;
- the integrated Bochner Hessian bound for a convex C² potential;
- `variance_le_sum_of_partial_dual_bounds`, retaining the C² convex potential,
  C¹/L² function and L² partial-derivative hypotheses stated below.

The variance assembly uses the heat-generator range density from
`HeatSemigroup/Generator/Range.lean`.
-/

@[expose] public section

section

open MeasureTheory
open scoped ContDiff

namespace FunctionalInequalities.KLS.LogConcave

/-- **A dual gradient bound has a nonnegative constant** (support for the `H⁻¹` variance lemma,
Letwin arXiv:2607.24164v1, Proposition 2.8): if `ν = e^{-W} dm` with `W` continuous on
`EuclideanSpace ℝ (Fin n)`, `n ≥ 1`, and `(∫ F h dν)² ≤ K ∫ ‖∇h‖² dν` for every `h ∈ C_c^∞`, then
`0 ≤ K` (some test has `∫ ‖∇h‖² dν > 0 because the density is positive). -/
theorem nonneg_of_forall_sq_integral_le_mul_integral_norm_fderiv_sq {n : ℕ} (hn : 0 < n)
    (m : Measure (EuclideanSpace ℝ (Fin n))) [m.IsAddHaarMeasure]
    {ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
    {W : EuclideanSpace ℝ (Fin n) → ℝ} (hνW : (ν : Measure _) = m.tilted (-W))
    (hW : Continuous W) {F : EuclideanSpace ℝ (Fin n) → ℝ} {K : ℝ}
    (hK : ∀ h : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ h → HasCompactSupport h →
      (∫ x, F x * h x ∂(ν : Measure _)) ^ 2 ≤
        K * ∫ x, ‖fderiv ℝ h x‖ ^ 2 ∂(ν : Measure _)) :
    0 ≤ K := by
  by_contra hK'
  have hKneg : K < 0 := lt_of_not_ge hK'
  let Z : ℝ := ∫ x, Real.exp (-W x) ∂m
  have hZne : Z ≠ 0 := by
    intro hZ
    have hUniv := congrArg
      (fun μ : Measure (EuclideanSpace ℝ (Fin n)) => μ Set.univ) hνW
    simp [Measure.tilted, Z, hZ] at hUniv
  have hZpos : 0 < Z := by
    have hZnonneg : 0 ≤ Z := by
      exact integral_nonneg (fun x => Real.exp_nonneg (-W x))
    exact lt_of_le_of_ne hZnonneg hZne.symm
  have hνopen :
      ∀ U : Set (EuclideanSpace ℝ (Fin n)), IsOpen U → U.Nonempty →
        (ν : Measure (EuclideanSpace ℝ (Fin n))) U ≠ 0 := by
    intro U hUopen hUnonempty
    rw [hνW]
    change
      (m.withDensity
          (fun x => ENNReal.ofReal (Real.exp ((-W) x) / Z))) U ≠ 0
    have hcontden :
        Continuous
          (fun x : EuclideanSpace ℝ (Fin n) =>
            ENNReal.ofReal (Real.exp ((-W) x) / Z)) := by
      exact
        ENNReal.continuous_ofReal.comp
          ((Real.continuous_exp.comp hW.neg).div_const Z)
    have haeden :
        AEMeasurable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            ENNReal.ofReal (Real.exp ((-W) x) / Z)) m :=
      hcontden.aemeasurable
    have hset :
        {x : EuclideanSpace ℝ (Fin n) |
            ENNReal.ofReal (Real.exp ((-W) x) / Z) ≠ 0} = Set.univ := by
      ext x
      change ENNReal.ofReal (Real.exp ((-W) x) / Z) ≠ 0 ↔ True
      exact iff_true_intro
        (ne_of_gt (ENNReal.ofReal_pos.mpr (div_pos (Real.exp_pos _) hZpos)))
    intro hzero
    have hmzero :
        m
            ({x : EuclideanSpace ℝ (Fin n) |
                ENNReal.ofReal (Real.exp ((-W) x) / Z) ≠ 0} ∩ U) = 0 :=
      (withDensity_apply_eq_zero' haeden).mp hzero
    have hmzeroU : m U = 0 := by
      rw [← Set.univ_inter U, ← hset]
      exact hmzero
    exact (Measure.IsOpenPosMeasure.open_pos U hUopen hUnonempty) hmzeroU
  let c : EuclideanSpace ℝ (Fin n) := 0
  let φ : ContDiffBump c := ⟨1, 2, by norm_num, by norm_num⟩
  let i : Fin n := ⟨0, hn⟩
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
  let h : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => φ x * (L x - L c)
  have hcφ : (φ c : ℝ) = 1 := by
    apply φ.one_of_mem_closedBall
    simpa [Metric.mem_closedBall] using φ.rIn_pos.le
  have hφdiff : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => (φ x : ℝ)) :=
    φ.contDiff
  have hφ :
      HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) => (φ x : ℝ))
        (fderiv ℝ (fun x : EuclideanSpace ℝ (Fin n) => (φ x : ℝ)) c) c := by
    exact ((hφdiff.differentiable (by simp)) c).hasFDerivAt
  have hL :
      HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) => L x - L c) L c := by
    simpa using L.hasFDerivAt.sub_const (L c)
  have hh : HasFDerivAt h L c := by
    change HasFDerivAt
      (fun x : EuclideanSpace ℝ (Fin n) => (φ x : ℝ) * (L x - L c)) L c
    have hm := hφ.mul hL
    rw [hcφ, sub_self, one_smul, zero_smul, add_zero] at hm
    exact hm
  have hcont : ContDiff ℝ ∞ h := by
    exact hφdiff.mul (L.contDiff.sub contDiff_const)
  have hcomp : HasCompactSupport h := by
    exact φ.hasCompactSupport.mul_right
  have hLne : L ≠ 0 := by
    intro hLzero
    have hLzero' := congrArg
      (fun q : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
        q (EuclideanSpace.single i 1)) hLzero
    simp [L] at hLzero'
  have hderivc : fderiv ℝ h c ≠ 0 := by
    rw [hh.fderiv]
    exact hLne
  have hfdcont : Continuous (fderiv ℝ h) := by
    exact hcont.continuous_fderiv (by simp)
  let g : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => ‖fderiv ℝ h x‖ ^ 2
  have hgcont : Continuous g := by
    exact (continuous_norm.comp hfdcont).pow 2
  have hgcomp : HasCompactSupport g := by
    have hderivcomp : HasCompactSupport (fderiv ℝ h) := hcomp.fderiv ℝ
    apply hderivcomp.norm.mono
    intro x hx
    apply Function.mem_support.mpr
    intro hzero
    apply hx
    simp [g, hzero]
  have hgint : Integrable g (ν : Measure (EuclideanSpace ℝ (Fin n))) := by
    exact hgcont.integrable_of_hasCompactSupport hgcomp
  have hgpos : 0 < g c := by
    have hnorm : 0 < ‖fderiv ℝ h c‖ := norm_pos_iff.mpr hderivc
    exact sq_pos_of_pos hnorm
  let U : Set (EuclideanSpace ℝ (Fin n)) := {x | 0 < g x}
  have hUopen : IsOpen U := by
    exact isOpen_lt continuous_const hgcont
  have hcU : c ∈ U := by
    exact hgpos
  have hUzero : (ν : Measure (EuclideanSpace ℝ (Fin n))) U ≠ 0 := by
    exact hνopen U hUopen ⟨c, hcU⟩
  have hUpos : 0 < (ν : Measure (EuclideanSpace ℝ (Fin n))) U :=
    pos_iff_ne_zero.mpr hUzero
  have hgsupp :
      0 < (ν : Measure (EuclideanSpace ℝ (Fin n))) (Function.support g) := by
    apply lt_of_lt_of_le hUpos
    apply measure_mono
    intro x hx
    exact Function.mem_support.mpr (ne_of_gt hx)
  have henergy :
      0 < ∫ x, ‖fderiv ℝ h x‖ ^ 2 ∂(ν : Measure (EuclideanSpace ℝ (Fin n))) := by
    exact
      (integral_pos_iff_support_of_nonneg (fun x => sq_nonneg _) hgint).mpr hgsupp
  have hineq := hK h hcont hcomp
  have hleft :
      0 ≤ (∫ x, F x * h x ∂(ν : Measure (EuclideanSpace ℝ (Fin n)))) ^ 2 :=
    sq_nonneg _
  have hright :
      K * ∫ x, ‖fderiv ℝ h x‖ ^ 2 ∂(ν : Measure (EuclideanSpace ℝ (Fin n))) < 0 :=
    mul_neg_of_neg_of_pos hKneg henergy
  have hcontra :
      (∫ x, F x * h x ∂(ν : Measure (EuclideanSpace ℝ (Fin n)))) ^ 2 < 0 :=
    lt_of_le_of_lt hineq hright
  exact (not_lt_of_ge hleft) hcontra

end FunctionalInequalities.KLS.LogConcave

namespace FunctionalInequalities.Analysis.BakryEmery

section BochnerHessianBound

open InnerProductSpace

/-! Bochner Hessian bound for a convex `C²` potential. -/

variable {n : ℕ}

private theorem partial_integrable
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasureOnCompacts μ]
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (i : Fin n) :
    Integrable
      (fun x =>
        ‖fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) x‖ ^ 2)
      μ := by
  let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1
  have hg3 : ContDiff ℝ 3 g :=
    hg.of_le (WithTop.coe_le_coe.mpr le_top)
  have hq : HasCompactSupport (fun y => fderiv ℝ g y e) := by
    have h :=
      (hgc.fderiv (𝕜 := ℝ)).comp_left
        (g := fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => A e) (by simp)
    simpa [e, Function.comp_def] using h
  have hq' : HasCompactSupport (fderiv ℝ (fun y => fderiv ℝ g y e)) :=
    hq.fderiv (𝕜 := ℝ)
  have hqcont :
      Continuous (fderiv ℝ (fun y => fderiv ℝ g y e)) := by
    exact
      (contDiff_fderiv_apply hg3 (m := 2) (by norm_num) e).continuous_fderiv
        (by norm_num)
  have hcont :
      Continuous
        (fun x => ‖fderiv ℝ (fun y => fderiv ℝ g y e) x‖ ^ 2) :=
    (hqcont.norm).pow 2
  have hn :
      HasCompactSupport
        (fun x => ‖fderiv ℝ (fun y => fderiv ℝ g y e) x‖ ^ 2) := by
    simpa [Function.comp_def] using
      (hq'.norm.comp_left (g := fun r : ℝ => r ^ 2) (by simp))
  have hi :
      Integrable
        (fun x => ‖fderiv ℝ (fun y => fderiv ℝ g y e) x‖ ^ 2) μ :=
    hcont.integrable_of_hasCompactSupport hn
  simpa [e] using hi

section HaarReference

/-! The two Haar-reference results share `m`; the compact-finiteness helper above does not. -/

variable (m : Measure (EuclideanSpace ℝ (Fin n)))

private theorem gammaTwo_integrable [m.IsAddHaarMeasure]
    {W g : EuclideanSpace ℝ (Fin n) → ℝ} (hW : ContDiff ℝ 2 W)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    Integrable (gammaTwo W g) (m.tilted (-W)) := by
  let ν := m.tilted (-W)
  have hg3 : ContDiff ℝ 3 g :=
    hg.of_le (WithTop.coe_le_coe.mpr le_top)
  have h₁ :
      Integrable
        ((fun x =>
            weightedLaplacian W (fun y => gamma g g y) x / 2) -
          (fun x => gamma g (weightedLaplacian W g) x)) ν := by
    dsimp [ν]
    exact
      ((integrable_weightedLaplacian_gamma m hW hg3 hgc).div_const 2).sub
        (integrable_gamma_weightedLaplacian m hW hg3 hgc)
  have hrepr :
      (fun x => gammaTwo W g x) =
        (fun x =>
          weightedLaplacian W (fun y => gamma g g y) x / 2 -
            gamma g (weightedLaplacian W g) x) := by
    funext x
    exact gammaTwo_apply W g x
  change Integrable (fun x => gammaTwo W g x) ν
  rw [hrepr]
  exact h₁

/-- **Bochner bound for the coordinate Hessian under a convex `C²` potential** (Letwin
arXiv:2607.24164v1, Proposition 2.8 via Barthe–Klartag): for
`ν = e^{-W} dm` with `W` convex and `C²`, and `g ∈ C_c^∞`,
`∑ᵢ ∫ ‖∇(∂ᵢ g)‖² dν ≤ ∫ (ℒg)² dν` with `ℒg = Δg − ⟪∇W, ∇g⟫` and `∂ᵢ g = Dg(eᵢ)` in the
standard coordinates of `EuclideanSpace ℝ (Fin n)`. -/
theorem sum_integral_norm_fderiv_partial_sq_le_integral_weightedLaplacian_sq [m.IsAddHaarMeasure]
    {W : EuclideanSpace ℝ (Fin n) → ℝ} (hW : ContDiff ℝ 2 W) (hWc : ConvexOn ℝ Set.univ W)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∑ i, ∫ x, ‖fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) x‖ ^ 2
        ∂(m.tilted (-W)) ≤
      ∫ x, weightedLaplacian W g x ^ 2 ∂(m.tilted (-W)) := by
  let ν := m.tilted (-W)
  let e : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
    EuclideanSpace.basisFun (Fin n) ℝ
  let b : OrthonormalBasis (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) ℝ
      (EuclideanSpace ℝ (Fin n)) :=
    stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))
  have hg3 : ContDiff ℝ 3 g :=
    hg.of_le (WithTop.coe_le_coe.mpr le_top)
  have hg2 : ContDiff ℝ 2 g :=
    hg.of_le (WithTop.coe_le_coe.mpr le_top)
  have hpoint :
      ∀ x,
        hessianSqStdBasis g x =
          ∑ i, ‖fderiv ℝ
            (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) x‖ ^ 2 := by
    intro x
    have hB (v w : EuclideanSpace ℝ (Fin n)) :
        inner ℝ (gradient (fun y => fderiv ℝ g y v) x) w =
          bilinearIteratedFDerivTwo ℝ g x w v := by
      calc
        inner ℝ (gradient (fun y => fderiv ℝ g y v) x) w =
            fderiv ℝ (fun y => fderiv ℝ g y v) x w :=
          inner_gradient_left
        _ = bilinearIteratedFDerivTwo ℝ g x w v :=
          (bilinearIteratedFDerivTwo_eq_fderiv_apply hg2 x w v).symm
    have hnorm (v : EuclideanSpace ℝ (Fin n)) :
        ‖fderiv ℝ (fun y => fderiv ℝ g y v) x‖ ^ 2 =
          ‖gradient (fun y => fderiv ℝ g y v) x‖ ^ 2 := by
      have heq :
          fderiv ℝ (fun y => fderiv ℝ g y v) x =
            (innerSL ℝ) (gradient (fun y => fderiv ℝ g y v) x) := by
        ext w
        calc
          fderiv ℝ (fun y => fderiv ℝ g y v) x w =
              inner ℝ (gradient (fun y => fderiv ℝ g y v) x) w :=
            (inner_gradient_left).symm
          _ = ((innerSL ℝ) (gradient (fun y => fderiv ℝ g y v) x)) w := by
            rw [innerSL_apply_apply]
      rw [heq, innerSL_apply_norm]
    have hmain :
        (∑ i, ‖gradient
            (fun y => fderiv ℝ g y (e i)) x‖ ^ 2) =
          ∑ j, ‖gradient
            (fun y => fderiv ℝ g y (b j)) x‖ ^ 2 := by
      calc
        (∑ i, ‖gradient
            (fun y => fderiv ℝ g y (e i)) x‖ ^ 2) =
            ∑ i, ∑ j, inner ℝ
              (gradient (fun y => fderiv ℝ g y (e i)) x) (b j) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [b.sum_sq_inner_left]
        _ = ∑ i, ∑ j,
            (bilinearIteratedFDerivTwo ℝ g x (b j) (e i)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          rw [hB]
        _ = ∑ j, ∑ i,
            (bilinearIteratedFDerivTwo ℝ g x (b j) (e i)) ^ 2 := by
          rw [Finset.sum_comm]
        _ = ∑ j, ∑ i,
            (bilinearIteratedFDerivTwo ℝ g x (e i) (b j)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro i hi
          exact congrArg (fun z : ℝ => z ^ 2)
            (bilinearIteratedFDerivTwo_symm hg2 x (b j) (e i))
        _ = ∑ j, ∑ i, inner ℝ
            (gradient (fun y => fderiv ℝ g y (b j)) x) (e i) ^ 2 := by
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro i hi
          rw [hB]
        _ = ∑ j, ‖gradient
            (fun y => fderiv ℝ g y (b j)) x‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [e.sum_sq_inner_left]
    have hb :
        hessianSqStdBasis g x =
          ∑ j, ‖gradient (fun y => fderiv ℝ g y (b j)) x‖ ^ 2 := by
      have hb' :
          (∑ i, ∑ j,
              (bilinearIteratedFDerivTwo ℝ g x (b i) (b j)) ^ 2) =
            ∑ j, ‖gradient
              (fun y => fderiv ℝ g y (b j)) x‖ ^ 2 := by
        calc
          (∑ i, ∑ j,
              (bilinearIteratedFDerivTwo ℝ g x (b i) (b j)) ^ 2) =
              ∑ j, ∑ i,
                (bilinearIteratedFDerivTwo ℝ g x (b i) (b j)) ^ 2 := by
            rw [Finset.sum_comm]
          _ = ∑ j, ∑ i, inner ℝ
              (gradient (fun y => fderiv ℝ g y (b j)) x) (b i) ^ 2 := by
            apply Finset.sum_congr rfl
            intro j hj
            apply Finset.sum_congr rfl
            intro i hi
            rw [hB]
          _ = ∑ j, ‖gradient
              (fun y => fderiv ℝ g y (b j)) x‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [b.sum_sq_inner_left]
      simpa [hessianSqStdBasis, b] using hb'
    have hcoord :
        (∑ i, ‖fderiv ℝ
            (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) x‖ ^ 2) =
          ∑ i, ‖gradient
            (fun y => fderiv ℝ g y (e i)) x‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [EuclideanSpace.basisFun_apply]
      exact hnorm _
    calc
      hessianSqStdBasis g x =
          ∑ j, ‖gradient (fun y => fderiv ℝ g y (b j)) x‖ ^ 2 := hb
      _ = ∑ i, ‖gradient
          (fun y => fderiv ℝ g y (e i)) x‖ ^ 2 := hmain.symm
      _ = ∑ i, ‖fderiv ℝ
          (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) x‖ ^ 2 :=
        hcoord.symm
  have hsum :
      (∫ x, ∑ i, ‖fderiv ℝ
          (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) x‖ ^ 2 ∂ν) =
        ∑ i, ∫ x, ‖fderiv ℝ
          (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) x‖ ^ 2 ∂ν := by
    rw [integral_finsetSum]
    intro i hi
    exact partial_integrable ν hg hgc i
  have hgamma : Integrable (gammaTwo W g) ν := by
    simpa [ν] using gammaTwo_integrable m hW hg hgc
  have hzero : 0 ≤ᵐ[ν] fun x => hessianSqStdBasis g x :=
    Filter.Eventually.of_forall (fun x => hessianSqStdBasis_nonneg g x)
  have hle :
      ∀ x, hessianSqStdBasis g x ≤ gammaTwo W g x := by
    intro x
    rw [gammaTwo_eq_hessianSqStdBasis_add hW hg3 x]
    exact le_add_of_nonneg_right
      (bilinearIteratedFDerivTwo_nonneg_of_convexOn hW hWc x (gradient g x))
  have hmono :
      (∫ x, hessianSqStdBasis g x ∂ν) ≤
        ∫ x, gammaTwo W g x ∂ν :=
    integral_mono_of_nonneg hzero hgamma
      (Filter.Eventually.of_forall hle)
  calc
    ∑ i, ∫ x, ‖fderiv ℝ
        (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) x‖ ^ 2 ∂ν =
        ∫ x, ∑ i, ‖fderiv ℝ
          (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) x‖ ^ 2 ∂ν :=
      hsum.symm
    _ = ∫ x, hessianSqStdBasis g x ∂ν := by
      congr 1
      funext x
      exact (hpoint x).symm
    _ ≤ ∫ x, gammaTwo W g x ∂ν := hmono
    _ = ∫ x, weightedLaplacian W g x ^ 2 ∂ν := by
      simpa [ν] using
        (integral_gammaTwo_eq m hW hg3 hgc)

end HaarReference

end BochnerHessianBound

end FunctionalInequalities.Analysis.BakryEmery

section Hminus1VarianceAssembly

/-! The `H⁻¹` variance bound for a convex `C²` potential (Letwin Proposition 2.8). -/

namespace FunctionalInequalities.KLS.LogConcave

open ProbabilityTheory InnerProductSpace
open Analysis.BakryEmery HeatSemigroup
open scoped RealInnerProductSpace

/-- **`H⁻¹` variance bound for a convex potential** (Letwin arXiv:2607.24164v1, Proposition 2.8,
quoted from Barthe–Klartag; here for a `C²` convex potential, the form used after Gaussian
smoothing of the target): if `ν = e^{-W} dm` with `W` convex and `C²`, `f ∈ C¹ ∩ L²(ν)` has square
integrable partial derivatives, and each partial derivative satisfies the dual bound
`(∫ ∂ᵢf · h dν)² ≤ Kᵢ ∫ ‖∇h‖² dν` for all compactly supported smooth `h`, then
`Var_ν f ≤ Σᵢ Kᵢ`. -/
theorem variance_le_sum_of_partial_dual_bounds {n : ℕ} (m : Measure (EuclideanSpace ℝ (Fin n)))
    [m.IsAddHaarMeasure] {ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
    (hν : FunctionalInequalities.KLS.LogConcave ν) {W : EuclideanSpace ℝ (Fin n) → ℝ}
    (hνW : (ν : Measure _) = m.tilted (-W)) (hW : ContDiff ℝ 2 W) (hWc : ConvexOn ℝ Set.univ W)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 1 f) (hf2 : MemLp f 2 (ν : Measure _))
    (hdf2 : ∀ i, MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) 2 (ν : Measure _))
    (K : Fin n → ℝ)
    (hK :
      ∀ i (h : EuclideanSpace ℝ (Fin n) → ℝ),
        ContDiff ℝ ∞ h →
          HasCompactSupport h →
            (∫ x, fderiv ℝ f x (EuclideanSpace.single i 1) * h x ∂(ν : Measure _)) ^ 2 ≤
              K i * ∫ x, ‖fderiv ℝ h x‖ ^ 2 ∂(ν : Measure _)) :
    variance f (ν : Measure _) ≤ ∑ i, K i := by
  have _ := hdf2
  have hU1 : ContDiff ℝ 1 W := hW.of_le (by norm_num)
  let F : Lp ℝ 2 (ν : Measure _) := hf2.toLp f
  let C : ℝ := ∑ i, K i
  have hKnonneg : ∀ i, 0 ≤ K i := by
    intro i
    exact
      nonneg_of_forall_sq_integral_le_mul_integral_norm_fderiv_sq (Fin.pos i) m hνW
        hW.continuous (hK i)
  have hQ :
    ∀ w ∈ compactSmoothDiffusionImage (ν := ν) hU1,
      2 * ⟪FunctionalInequalities.L2.center ν F, w⟫ - ‖w‖ ^ 2 ≤ C := by
    rintro w ⟨g, hg, hgc, rfl⟩
    let hL : MemLp (fun x => -weightedLaplacian W g x) 2 (ν : Measure _) :=
      memLp_neg_weightedLaplacian (ν := ν) hU1 hg hgc
    let G : Lp ℝ 2 (ν : Measure _) := hL.toLp (fun x => -weightedLaplacian W g x)
    change 2 * ⟪FunctionalInequalities.L2.center ν F, G⟫ - ‖G‖ ^ 2 ≤ C
    have hmean : FunctionalInequalities.L2.mean ν G = 0 :=
      compact_diffusion_toLp_mean_zero m hνW hU1 hg hgc
    have hinner : ⟪F, G⟫ = ∫ x, f x * (-weightedLaplacian W g x) ∂(ν : Measure _) :=
      real_inner_toLp hf2 hL
    have hnorm : ‖G‖ ^ 2 = ∫ x, weightedLaplacian W g x ^ 2 ∂(ν : Measure _) := by
      simpa only [G, Real.norm_eq_abs, abs_neg, sq_abs] using
        (FunctionalInequalities.L2.norm_toLp_sq hL)
    obtain ⟨_, _, hpair⟩ := compact_pairing_identity m hνW hU1 hf hg hgc
    have hcoord_f (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
      (gradient f x).ofLp i = fderiv ℝ f x (EuclideanSpace.single i 1) := by
      calc
        (gradient f x).ofLp i = inner ℝ (gradient f x) (EuclideanSpace.single i 1) := by
          simpa using (EuclideanSpace.inner_single_right i (1 : ℝ) (gradient f x)).symm
        _ = fderiv ℝ f x (EuclideanSpace.single i 1) := by
          simpa only [gradient] using
            (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n)) (x :=
              EuclideanSpace.single i 1) (y := fderiv ℝ f x))
    have hcoord_g (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
      (gradient g x).ofLp i = fderiv ℝ g x (EuclideanSpace.single i 1) := by
      calc
        (gradient g x).ofLp i = inner ℝ (gradient g x) (EuclideanSpace.single i 1) := by
          simpa using (EuclideanSpace.inner_single_right i (1 : ℝ) (gradient g x)).symm
        _ = fderiv ℝ g x (EuclideanSpace.single i 1) := by
          simpa only [gradient] using
            (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n)) (x :=
              EuclideanSpace.single i 1) (y := fderiv ℝ g x))
    let A : Fin n → ℝ := fun i =>
      ∫ x,
        fderiv ℝ f x (EuclideanSpace.single i 1) *
          fderiv ℝ g x (EuclideanSpace.single i 1) ∂(ν : Measure _)
    let D : Fin n → ℝ := fun i =>
      ∫ x, ‖fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) x‖ ^ 2 ∂(ν : Measure _)
    have hprod_int (i : Fin n) :
      Integrable
        (fun x =>
          fderiv ℝ f x (EuclideanSpace.single i 1) * fderiv ℝ g x (EuclideanSpace.single i 1))
        (ν : Measure _) := by
      have hp :
        Continuous (fun x : EuclideanSpace ℝ (Fin n) => (x, EuclideanSpace.single i (1 : ℝ))) :=
        Continuous.prodMk continuous_id continuous_const
      have hfc :
        Continuous
          (fun x : EuclideanSpace ℝ (Fin n) => fderiv ℝ f x (EuclideanSpace.single i 1)) := by
        simpa only [Function.comp_def] using (hf.continuous_fderiv_apply (by simp)).comp hp
      have hgccont :
        Continuous
          (fun x : EuclideanSpace ℝ (Fin n) => fderiv ℝ g x (EuclideanSpace.single i 1)) := by
        simpa only [Function.comp_def] using (hg.continuous_fderiv_apply (by simp)).comp hp
      have hgc' : HasCompactSupport (fun x => fderiv ℝ g x (EuclideanSpace.single i 1)) := by
        simpa only [Function.comp_def] using
          (hgc.fderiv ℝ).comp_left (g := fun q => q (EuclideanSpace.single i 1)) (by simp)
      exact (hfc.mul hgccont).integrable_of_hasCompactSupport hgc'.mul_left
    have hgrad_sum : (∫ x, ⟪gradient f x, gradient g x⟫ ∂(ν : Measure _)) = ∑ i, A i := by
      calc
        (∫ x, ⟪gradient f x, gradient g x⟫ ∂(ν : Measure _)) =
            ∫ x,
              ∑ i,
                fderiv ℝ f x (EuclideanSpace.single i 1) *
                  fderiv ℝ g x (EuclideanSpace.single i 1) ∂(ν : Measure _) := by
          apply integral_congr_ae
          filter_upwards [] with x
          rw [PiLp.inner_apply]
          apply Finset.sum_congr rfl
          intro i hi
          rw [hcoord_f i x, hcoord_g i x]
          simp [mul_comm]
        _ = ∑ i, A i := by
          rw [MeasureTheory.integral_finsetSum]
          intro i hi
          exact hprod_int i
    have hterm : ∀ i, 2 * A i ≤ K i + D i := by
      intro i
      have hsq :=
        hK i (fun x => fderiv ℝ g x (EuclideanSpace.single i 1))
          (by
            have hp :
              ContDiff ℝ ∞
                (fun x : EuclideanSpace ℝ (Fin n) => (x, EuclideanSpace.single i (1 : ℝ))) :=
              contDiff_id.prodMk contDiff_const
            simpa only [Function.comp_def] using
              (hg.contDiff_fderiv_apply (m := ∞) (by simp)).comp hp)
          (by
            simpa only [Function.comp_def] using
              (hgc.fderiv ℝ).comp_left (g := fun q => q (EuclideanSpace.single i 1)) (by simp))
      change
        2 *
            (∫ x,
              fderiv ℝ f x (EuclideanSpace.single i 1) *
                fderiv ℝ g x (EuclideanSpace.single i 1) ∂(ν : Measure _)) ≤
          K i +
            ∫ x,
              ‖fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) x‖ ^
                2 ∂(ν : Measure _)
      have hD :
        0 ≤
          ∫ x,
            ‖fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) x‖ ^
              2 ∂(ν : Measure _) :=
        integral_nonneg (fun x => sq_nonneg _)
      nlinarith [hsq, hKnonneg i, hD,
        sq_nonneg
          (K i -
            ∫ x,
              ‖fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) x‖ ^
                2 ∂(ν : Measure _))]
    have hsum : 2 * ∑ i, A i ≤ ∑ i, K i + ∑ i, D i := by
      have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun i hi => hterm i)
      simpa [Finset.mul_sum, Finset.sum_add_distrib] using h
    have hLT9c :=
      sum_integral_norm_fderiv_partial_sq_le_integral_weightedLaplacian_sq m hW hWc hg hgc
    rw [← hνW] at hLT9c
    have hLT9c' : ∑ i, D i ≤ ∫ x, weightedLaplacian W g x ^ 2 ∂(ν : Measure _) := by
      simpa [D] using hLT9c
    have hmain : 2 * ∑ i, A i - ∫ x, weightedLaplacian W g x ^ 2 ∂(ν : Measure _) ≤ C := by
      change 2 * ∑ i, A i - ∫ x, weightedLaplacian W g x ^ 2 ∂(ν : Measure _) ≤ ∑ i, K i
      linarith
    rw [inner_center_left_of_mean_zero ν F G hmean, hinner, hnorm, hpair, hgrad_sum]
    exact hmain
  have hclosure :
    FunctionalInequalities.L2.center ν F ∈ closure (compactSmoothDiffusionImage (ν := ν) hU1) :=
    center_mem_closure_compactSmoothDiffusionImage m hν hνW hU1 F
  have hnorm : ‖FunctionalInequalities.L2.center ν F‖ ^ 2 ≤ C :=
    norm_sq_le_of_mem_closure_quadratic_bound (FunctionalInequalities.L2.center ν F) hclosure hQ
  have hvariance : (FunctionalInequalities.L2.variance ν F : ℝ) = variance f (ν : Measure _) :=
    (FunctionalInequalities.L2.coe_variance_eq_pointwise ν F).trans
      (variance_congr hf2.coeFn_toLp)
  rw [← hvariance, FunctionalInequalities.L2.coe_variance]
  exact hnorm

end FunctionalInequalities.KLS.LogConcave

end Hminus1VarianceAssembly
