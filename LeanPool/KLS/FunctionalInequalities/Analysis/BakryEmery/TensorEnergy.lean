/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.ExponentialMoments.Temperate
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Bochner.Tensor

/-!
# The energy recursion of BKL Lemma 3.4 and Corollary 3.5

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), (33)–(39), (45)–(47), Lemma 3.4 and Corollary 3.5. Tensor
fields take values in finite-dimensional real inner product spaces, and the gradient of a tensor
field adds a first index: `gradCoord u = (Du(e_i))_i ∈ PiLp 2 (Fin n → G)`, whose norm is the
source's
Hilbert–Schmidt norm over the derivative index and all trailing indices. For a pair `g = h_i`,
`h = h_{i+1}` of temperate fields satisfying the defining Poisson relation (30)
`-ℒh = α ∇₀g` (`∇₀g = ∇g - ∫ ∇g`) and the normalization (33) `‖∇h‖² = ‖∇₀g‖²`, the orthogonality
`⟨∇²g, ∇h⟩ = α ‖∇h‖²`, the Pythagorean identity (39), the identities (46), (47) and the energy
inequality (45) `‖ℒg‖² ≥ ‖ℒh‖² + χ + a ‖∇g‖²` are derived (the zero scale `α = 0` included).
Corollary
3.5 is the telescoping/summability consequence, both for abstract real sequences and for a sequence
of
tensor iterates `h_k : E → G k`, where linear isometries `ι k : PiLp 2 (Fin n → G k) ≃ₗᵢ G (k+1)`
identify the gradient space of level `k` with level `k+1` and every consecutive pair satisfies (30)
and (33) with curvature `∇²V ≥ a > 0`. Also (35), (36) (the energy drop `v_i - v_{i+1} = ‖∫ ∇h_i‖²`
under
(33) and its telescoped form), the symmetry of `∇²f` in its first two indices, and Lemma 3.2: under
(30), `α² ≥ λ > 0` for `α ≠ 0`, `∇₀h` lies within squared distance `χ / λ` of a field symmetric in
its
first two indices, with Lemma 3.3 in the case `q = 2` (`S₂` symmetrizes the first two indices); and
(61): `∫ Dh = α T₁(∇₀g)`, so `‖∫ ∇h‖² = α² Σ_i ‖T₁(∇₀g)(e_i)‖²`, with the first energy drop
`‖∫ ∇f‖² ≤ λ² K ‖f‖²` of Lemma 3.9 for a supplied centered eigenfunction `ℒf = -λ f` (covariance `≤
K`). The existence
of such iterates (Lemma 2.1 on `𝒜` and the first eigenfunction) is not addressed: every theorem here
takes the pairs as hypotheses.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.Analysis.BakryEmery

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

/-- The coordinate gradient `∇u = (Du(e_i))_i` in the standard orthonormal basis; the derivative
index comes first and the norm is the Hilbert–Schmidt norm. -/
def gradCoord (f : E → G) (x : E) : PiLp 2 (fun _ : Fin (Module.finrank ℝ E) => G) :=
  WithLp.toLp 2 fun i => fderiv ℝ f x (stdOrthonormalBasis ℝ E i)

section CoordinateGradient

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ G]

theorem norm_sq_gradCoord (f : E → G) (x : E) :
    ‖gradCoord f x‖ ^ 2 = ∑ i, ‖fderiv ℝ f x (stdOrthonormalBasis ℝ E i)‖ ^ 2 := by
    unfold gradCoord
    rw [PiLp.norm_sq_eq_of_L2]

theorem inner_gradCoord (f g : E → G) (x : E) :
    ⟪gradCoord f x, gradCoord g x⟫ =
      ∑ i,
        ⟪fderiv ℝ f x (stdOrthonormalBasis ℝ E i), fderiv ℝ g x (stdOrthonormalBasis ℝ E i)⟫ := by
  simp [gradCoord, PiLp.inner_apply]

theorem hasTemperateGrowth_gradCoord {f : E → G} (hf : f.HasTemperateGrowth) :
    (gradCoord f).HasTemperateGrowth := by
  let L : (E →L[ℝ] G) →L[ℝ] PiLp 2 (fun _ : Fin (Module.finrank ℝ E) => G) :=
    (PiLp.continuousLinearEquiv 2 ℝ _).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun i =>
        ContinuousLinearMap.apply ℝ G (stdOrthonormalBasis ℝ E i))
  exact L.hasTemperateGrowth.comp (hasTemperateGrowth_fderiv hf)

theorem norm_sq_gradCoord_gradCoord {f : E → G} (hf : ContDiff ℝ ∞ f) (x : E) :
    ‖gradCoord (gradCoord f) x‖ ^ 2 =
      ∑ i,
        ∑ j,
          ‖iteratedFDeriv ℝ 2 f x ![stdOrthonormalBasis ℝ E i, stdOrthonormalBasis ℝ E j]‖ ^
            2 := by
  classical
  let L : (E →L[ℝ] G) →L[ℝ] PiLp 2 (fun _ : Fin (Module.finrank ℝ E) => G) :=
    (PiLp.continuousLinearEquiv 2 ℝ _).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun i =>
        ContinuousLinearMap.apply ℝ G (stdOrthonormalBasis ℝ E i))
  have heq : gradCoord f = L ∘ fderiv ℝ f := rfl
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  rw [norm_sq_gradCoord]
  apply Finset.sum_congr rfl
  intro i _
  rw [heq, (L.hasFDerivAt.comp x hd.hasFDerivAt).fderiv, ContinuousLinearMap.comp_apply,
    PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro j _
  change
    ‖fderiv ℝ (fderiv ℝ f) x (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j)‖ ^ 2 = _
  rw [iteratedFDeriv_two_apply]
  rfl

end CoordinateGradient

variable (m : Measure E) [m.IsAddHaarMeasure]

omit [BorelSpace E] [FiniteDimensional ℝ G] [m.IsAddHaarMeasure] in
/-- (46): `‖ℒh‖² = α² ‖∇h‖²` under (30) and (33). -/
theorem integral_norm_sq_weightedLaplacianVec_eq_of_poisson {V : E → ℝ}
    {g : E → G} {h : E → PiLp 2 (fun _ : Fin (Module.finrank ℝ E) => G)} {α : ℝ}
    (h30 : ∀ x, -weightedLaplacianVec V h x =
      α • (gradCoord g x - ∫ y, gradCoord g y ∂(m.tilted (-V))))
    (h33 : ∫ x, ‖gradCoord h x‖ ^ 2 ∂(m.tilted (-V)) =
      ∫ x, ‖gradCoord g x - ∫ y, gradCoord g y ∂(m.tilted (-V))‖ ^ 2 ∂(m.tilted (-V))) :
    ∫ x, ‖weightedLaplacianVec V h x‖ ^ 2 ∂(m.tilted (-V)) =
      α ^ 2 * ∫ x, ‖gradCoord h x‖ ^ 2 ∂(m.tilted (-V)) := by
    have hpoint (x : E) :
        ‖weightedLaplacianVec V h x‖ ^ 2 =
          α ^ 2 *
            ‖gradCoord g x -
              ∫ y, gradCoord g y ∂(m.tilted (-V))‖ ^ 2 := by
      calc
        ‖weightedLaplacianVec V h x‖ ^ 2 =
            ‖-weightedLaplacianVec V h x‖ ^ 2 := by
              rw [norm_neg]
        _ = ‖α •
            (gradCoord g x -
              ∫ y, gradCoord g y ∂(m.tilted (-V)))‖ ^ 2 := by
              rw [h30 x]
        _ = α ^ 2 *
            ‖gradCoord g x -
              ∫ y, gradCoord g y ∂(m.tilted (-V))‖ ^ 2 := by
              rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    calc
      ∫ x, ‖weightedLaplacianVec V h x‖ ^ 2 ∂(m.tilted (-V)) =
          ∫ x, α ^ 2 *
            ‖gradCoord g x -
              ∫ y, gradCoord g y ∂(m.tilted (-V))‖ ^ 2 ∂(m.tilted (-V)) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hpoint
      _ = α ^ 2 *
          ∫ x, ‖gradCoord g x -
            ∫ y, gradCoord g y ∂(m.tilted (-V))‖ ^ 2 ∂(m.tilted (-V)) := by
            rw [integral_const_mul]
      _ = α ^ 2 * ∫ x, ‖gradCoord h x‖ ^ 2 ∂(m.tilted (-V)) := by
            rw [h33]

/-- The orthogonality behind (39): `⟨∇²g, ∇h⟩ = α ‖∇h‖²`. -/
theorem integral_inner_gradCoord_gradCoord_eq {V : E → ℝ} (hV : V.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    {g : E → G} {h : E → PiLp 2 (fun _ : Fin (Module.finrank ℝ E) => G)} {α : ℝ}
    (hg : g.HasTemperateGrowth) (hh : h.HasTemperateGrowth)
    (h30 : ∀ x, -weightedLaplacianVec V h x =
      α • (gradCoord g x - ∫ y, gradCoord g y ∂(m.tilted (-V))))
    (h33 : ∫ x, ‖gradCoord h x‖ ^ 2 ∂(m.tilted (-V)) =
      ∫ x, ‖gradCoord g x - ∫ y, gradCoord g y ∂(m.tilted (-V))‖ ^ 2 ∂(m.tilted (-V))) :
    ∫ x, ⟪gradCoord (gradCoord g) x, gradCoord h x⟫ ∂(m.tilted (-V)) =
      α * ∫ x, ‖gradCoord h x‖ ^ 2 ∂(m.tilted (-V)) := by
    let c : PiLp 2 (fun _ : Fin (Module.finrank ℝ E) => G) :=
      ∫ y, gradCoord g y ∂(m.tilted (-V))
    let g₀ : E → PiLp 2 (fun _ : Fin (Module.finrank ℝ E) => G) :=
      fun x => gradCoord g x - c
    have hg₀ : g₀.HasTemperateGrowth := by
      dsimp [g₀]
      exact
        (hasTemperateGrowth_gradCoord hg).sub
          (Function.HasTemperateGrowth.const c)
    have hV1 : ContDiff ℝ 1 V := hV.1.of_le (by simp)
    obtain ⟨k, C, hC⟩ := hV.2 1
    have hVg : ∀ x : E, ‖gradient V x‖ ≤ C * (1 + ‖x‖) ^ k := by
      intro x
      rw [norm_gradient_eq_norm_iteratedFDeriv_one]
      exact hC x
    have hIBP :=
      integral_inner_weightedLaplacianVec_eq_neg
        (m := m) (V := V) (f := h) (g := g₀)
        hV1 hVg hexp hh hg₀
    have hIBP' :
        (∫ x, ⟪weightedLaplacianVec V h x, g₀ x⟫ ∂(m.tilted (-V))) =
          -∫ x, ⟪gradCoord h x, gradCoord (gradCoord g) x⟫
            ∂(m.tilted (-V)) := by
      calc
        (∫ x, ⟪weightedLaplacianVec V h x, g₀ x⟫ ∂(m.tilted (-V))) =
            -∫ x, ∑ i,
              ⟪fderiv ℝ h x (stdOrthonormalBasis ℝ E i),
                fderiv ℝ g₀ x (stdOrthonormalBasis ℝ E i)⟫
              ∂(m.tilted (-V)) := hIBP
        _ = -∫ x, ⟪gradCoord h x, gradCoord (gradCoord g) x⟫
              ∂(m.tilted (-V)) := by
          congr 1
          apply integral_congr_ae
          filter_upwards [] with x
          rw [inner_gradCoord]
          simp [g₀, c, fderiv_sub_const]
    have hleft :
        (∫ x, ⟪weightedLaplacianVec V h x, g₀ x⟫ ∂(m.tilted (-V))) =
          -α * ∫ x, ‖gradCoord h x‖ ^ 2 ∂(m.tilted (-V)) := by
      calc
        (∫ x, ⟪weightedLaplacianVec V h x, g₀ x⟫ ∂(m.tilted (-V))) =
            ∫ x, (-α) * ‖g₀ x‖ ^ 2 ∂(m.tilted (-V)) := by
          apply integral_congr_ae
          filter_upwards [] with x
          have hx :
              weightedLaplacianVec V h x = (-α) • g₀ x := by
            calc
              weightedLaplacianVec V h x = -(-weightedLaplacianVec V h x) := by
                simp
              _ = -(α • g₀ x) := by
                rw [h30]
              _ = (-α) • g₀ x := by
                rw [neg_smul]
          simp [hx, real_inner_smul_left]
        _ = (-α) * ∫ x, ‖g₀ x‖ ^ 2 ∂(m.tilted (-V)) := by
          rw [integral_const_mul]
        _ = (-α) * ∫ x, ‖gradCoord h x‖ ^ 2 ∂(m.tilted (-V)) := by
          rw [h33]
    have hcomm :
        (∫ x, ⟪gradCoord (gradCoord g) x, gradCoord h x⟫
            ∂(m.tilted (-V))) =
          ∫ x, ⟪gradCoord h x, gradCoord (gradCoord g) x⟫
            ∂(m.tilted (-V)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact real_inner_comm _ _
    calc
      (∫ x, ⟪gradCoord (gradCoord g) x, gradCoord h x⟫
          ∂(m.tilted (-V))) =
          ∫ x, ⟪gradCoord h x, gradCoord (gradCoord g) x⟫
            ∂(m.tilted (-V)) := hcomm
      _ = α * ∫ x, ‖gradCoord h x‖ ^ 2 ∂(m.tilted (-V)) := by
        linarith [hIBP', hleft]

/-- (39): `‖∇²g‖² = α² ‖∇h‖² + χ` with `χ = ‖∇²g - α ∇h‖²`. -/
theorem integral_norm_sq_gradCoord_gradCoord_eq {V : E → ℝ} (hV : V.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V))) {g : E → G}
    {h : E → PiLp 2 (fun _ : Fin (Module.finrank ℝ E) => G)} {α : ℝ} (hg : g.HasTemperateGrowth)
    (hh : h.HasTemperateGrowth)
    (h30 :
      ∀ x,
        -weightedLaplacianVec V h x = α • (gradCoord g x - ∫ y, gradCoord g y ∂(m.tilted (-V))))
    (h33 :
      ∫ x, ‖gradCoord h x‖ ^ 2 ∂(m.tilted (-V)) =
        ∫ x, ‖gradCoord g x - ∫ y, gradCoord g y ∂(m.tilted (-V))‖ ^ 2 ∂(m.tilted (-V))) :
    ∫ x, ‖gradCoord (gradCoord g) x‖ ^ 2 ∂(m.tilted (-V)) =
      α ^ 2 * ∫ x, ‖gradCoord h x‖ ^ 2 ∂(m.tilted (-V)) +
        ∫ x, ‖gradCoord (gradCoord g) x - α • gradCoord h x‖ ^ 2 ∂(m.tilted (-V)) := by
  let X := gradCoord (gradCoord g)
  let Y := gradCoord h
  have hX : X.HasTemperateGrowth :=
    hasTemperateGrowth_gradCoord (hasTemperateGrowth_gradCoord hg)
  have hY : Y.HasTemperateGrowth := hasTemperateGrowth_gradCoord hh
  have hXi : Integrable (fun x => ‖X x‖ ^ 2) (m.tilted (-V)) :=
    FunctionalInequalities.Probability.integrable_of_hasTemperateGrowth _ hexp
      ((Function.hasTemperateGrowth_norm_sq _).comp hX)
  have hYi : Integrable (fun x => ‖Y x‖ ^ 2) (m.tilted (-V)) :=
    FunctionalInequalities.Probability.integrable_of_hasTemperateGrowth _ hexp
      ((Function.hasTemperateGrowth_norm_sq _).comp hY)
  have hXYi : Integrable (fun x => ⟪X x, Y x⟫) (m.tilted (-V)) :=
    FunctionalInequalities.Probability.integrable_of_hasTemperateGrowth _ hexp
      ((innerSL ℝ).bilinear_hasTemperateGrowth hX hY)
  have hp := integral_inner_gradCoord_gradCoord_eq m hV hexp hg hh h30 h33
  have heq :
    (fun x => ‖X x - α • Y x‖ ^ 2) =
      (fun x => (‖X x‖ ^ 2 - (2 * α) * ⟪X x, Y x⟫) + α ^ 2 * ‖Y x‖ ^ 2) := by
    funext x
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs]
    rw [mul_pow, sq_abs]
    ring
  change
    ∫ x, ‖X x‖ ^ 2 ∂(m.tilted (-V)) =
      α ^ 2 * ∫ x, ‖Y x‖ ^ 2 ∂(m.tilted (-V)) + ∫ x, ‖X x - α • Y x‖ ^ 2 ∂(m.tilted (-V))
  have hsc : Integrable (fun x => (2 * α) * ⟪X x, Y x⟫) (m.tilted (-V)) := hXYi.const_mul _
  have hsub : Integrable (fun x => ‖X x‖ ^ 2 - (2 * α) * ⟪X x, Y x⟫) (m.tilted (-V)) :=
    hXi.sub hsc
  have hsy : Integrable (fun x => α ^ 2 * ‖Y x‖ ^ 2) (m.tilted (-V)) := hYi.const_mul _
  rw [heq, integral_add hsub hsy, integral_sub hXi hsc, integral_const_mul, integral_const_mul]
  change ∫ x, ⟪X x, Y x⟫ ∂(m.tilted (-V)) = α * ∫ x, ‖Y x‖ ^ 2 ∂(m.tilted (-V)) at hp
  rw [hp]
  ring

/-- (47): `‖∇²g‖² = ‖ℒh‖² + χ` under (30) and (33). -/
theorem integral_norm_sq_gradCoord_gradCoord_eq_add {V : E → ℝ} (hV : V.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    {g : E → G} {h : E → PiLp 2 (fun _ : Fin (Module.finrank ℝ E) => G)} {α : ℝ}
    (hg : g.HasTemperateGrowth) (hh : h.HasTemperateGrowth)
    (h30 : ∀ x, -weightedLaplacianVec V h x =
      α • (gradCoord g x - ∫ y, gradCoord g y ∂(m.tilted (-V))))
    (h33 : ∫ x, ‖gradCoord h x‖ ^ 2 ∂(m.tilted (-V)) =
      ∫ x, ‖gradCoord g x - ∫ y, gradCoord g y ∂(m.tilted (-V))‖ ^ 2 ∂(m.tilted (-V))) :
    ∫ x, ‖gradCoord (gradCoord g) x‖ ^ 2 ∂(m.tilted (-V)) =
      ∫ x, ‖weightedLaplacianVec V h x‖ ^ 2 ∂(m.tilted (-V)) +
        ∫ x, ‖gradCoord (gradCoord g) x - α • gradCoord h x‖ ^ 2 ∂(m.tilted (-V)) := by
  rw [integral_norm_sq_gradCoord_gradCoord_eq m hV hexp hg hh h30 h33,
    integral_norm_sq_weightedLaplacianVec_eq_of_poisson m h30 h33]

/-- **BKL Lemma 3.4**, (45), for a pair satisfying (30) and (33): with `∇²V ≥ a`,
`‖ℒg‖² ≥ ‖ℒh‖² + χ + a ‖∇g‖²`, `χ = ‖∇²g - α ∇h‖²`. -/
theorem integral_norm_sq_weightedLaplacianVec_ge {V : E → ℝ} (hV : V.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    {a : ℝ} (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x v v)
    {g : E → G} {h : E → PiLp 2 (fun _ : Fin (Module.finrank ℝ E) => G)} {α : ℝ}
    (hg : g.HasTemperateGrowth) (hh : h.HasTemperateGrowth)
    (h30 : ∀ x, -weightedLaplacianVec V h x =
      α • (gradCoord g x - ∫ y, gradCoord g y ∂(m.tilted (-V))))
    (h33 : ∫ x, ‖gradCoord h x‖ ^ 2 ∂(m.tilted (-V)) =
      ∫ x, ‖gradCoord g x - ∫ y, gradCoord g y ∂(m.tilted (-V))‖ ^ 2 ∂(m.tilted (-V))) :
    ∫ x, ‖weightedLaplacianVec V h x‖ ^ 2 ∂(m.tilted (-V)) +
        ∫ x, ‖gradCoord (gradCoord g) x - α • gradCoord h x‖ ^ 2 ∂(m.tilted (-V)) +
        a * ∫ x, ‖gradCoord g x‖ ^ 2 ∂(m.tilted (-V)) ≤
      ∫ x, ‖weightedLaplacianVec V g x‖ ^ 2 ∂(m.tilted (-V)) := by
    have hA :
        (∫ x, ‖gradCoord (gradCoord g) x‖ ^ 2 ∂(m.tilted (-V))) =
          ∫ x, ∑ i, ∑ j,
            ‖iteratedFDeriv ℝ 2 g x
                ![stdOrthonormalBasis ℝ E i, stdOrthonormalBasis ℝ E j]‖ ^ 2
              ∂(m.tilted (-V)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact norm_sq_gradCoord_gradCoord hg.1 x
    have hB :
        (∫ x, ‖gradCoord g x‖ ^ 2 ∂(m.tilted (-V))) =
          ∫ x, ∑ i,
            ‖fderiv ℝ g x (stdOrthonormalBasis ℝ E i)‖ ^ 2
              ∂(m.tilted (-V)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact norm_sq_gradCoord g x
    have hcurv :=
      integral_hessian_add_le_norm_sq_weightedLaplacianVec
        m hV hexp hg hH
    rw [← hA, ← hB] at hcurv
    have hdecomp :=
      integral_norm_sq_gradCoord_gradCoord_eq
        m hV hexp hg hh h30 h33
    have hpoisson :=
      integral_norm_sq_weightedLaplacianVec_eq_of_poisson
        m h30 h33
    linarith

/-- Telescoping (45): `L₀ ≥ L_N + ∑_{i<N} χ_i + a ∑_{i<N} v_i`. -/
theorem telescope_energy {L χ v : ℕ → ℝ} {a : ℝ}
    (h45 : ∀ i, L (i + 1) + χ i + a * v i ≤ L i) (N : ℕ) :
    L N + ∑ i ∈ Finset.range N, χ i + a * ∑ i ∈ Finset.range N, v i ≤ L 0 := by
    induction N with
    | zero =>
        simp
    | succ N ih =>
        simp only [Finset.sum_range_succ]
        linarith [h45 N]

/-- **BKL Corollary 3.5** (the summation argument): if (45) holds for every `i` with nonnegative
`L_i = ‖ℒh_i‖²`, `χ_i` and `v_i = ‖∇h_i‖²`, and `a > 0`, then `∑ v_i < ∞` and `v_N → 0`. -/
theorem summable_and_tendsto_zero_of_energy {L χ v : ℕ → ℝ} {a : ℝ} (ha : 0 < a)
    (hL : ∀ i, 0 ≤ L i) (hχ : ∀ i, 0 ≤ χ i) (hv : ∀ i, 0 ≤ v i)
    (h45 : ∀ i, L (i + 1) + χ i + a * v i ≤ L i) :
    Summable v ∧ Summable χ ∧ Tendsto v atTop (𝓝 0) := by
    have hv_bound : ∀ N, (∑ i ∈ Finset.range N, v i) ≤ L 0 / a := by
      intro N
      have htel := telescope_energy h45 N
      have hχsum : 0 ≤ ∑ i ∈ Finset.range N, χ i :=
        Finset.sum_nonneg (fun i _ => hχ i)
      have hprod : a * (∑ i ∈ Finset.range N, v i) ≤ L 0 := by
        linarith [hL N, htel, hχsum]
      apply (le_div_iff₀ ha).2
      calc
        (∑ i ∈ Finset.range N, v i) * a =
            a * (∑ i ∈ Finset.range N, v i) := by ring
        _ ≤ L 0 := hprod
    have hχ_bound : ∀ N, (∑ i ∈ Finset.range N, χ i) ≤ L 0 := by
      intro N
      have htel := telescope_energy h45 N
      have hLnon : 0 ≤ L N := hL N
      have hvsum : 0 ≤ ∑ i ∈ Finset.range N, v i :=
        Finset.sum_nonneg (fun i _ => hv i)
      have hprod : 0 ≤ a * (∑ i ∈ Finset.range N, v i) :=
        mul_nonneg (le_of_lt ha) hvsum
      linarith
    have hsumv : Summable v :=
      summable_of_sum_range_le hv hv_bound
    have hsumχ : Summable χ :=
      summable_of_sum_range_le hχ hχ_bound
    exact ⟨hsumv, hsumχ, hsumv.tendsto_atTop_zero⟩

section Transport

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ G] in
/-- The vector weighted Laplacian commutes with a linear isometry of the values. -/
theorem weightedLaplacianVec_linearIsometryEquiv (V : E → ℝ) {f : E → G} (hf : ContDiff ℝ 2 f)
    (L : G ≃ₗᵢ[ℝ] H) (x : E) :
    weightedLaplacianVec V (fun y => L (f y)) x = L (weightedLaplacianVec V f x) := by
  have hLap : Laplacian.laplacian (fun y => L (f y)) x =
      L (Laplacian.laplacian f x) := by
    simpa only [Function.comp_def, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe] using
      (hf.contDiffAt.laplacian_CLM_comp_left
        (l := L.toContinuousLinearEquiv.toContinuousLinearMap))
  have hderiv : fderiv ℝ (fun y => L (f y)) x =
      L.toContinuousLinearEquiv.toContinuousLinearMap.comp (fderiv ℝ f x) :=
    (L.hasFDerivAt.comp x
      (hf.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  unfold weightedLaplacianVec
  rw [hLap, hderiv, map_sub]
  rfl

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ G] in
/-- The coordinate gradient commutes with a linear isometry of the values (norm form). -/
theorem norm_gradCoord_linearIsometryEquiv {f : E → G} (hf : Differentiable ℝ f)
    (L : G ≃ₗᵢ[ℝ] H) (x : E) :
    ‖gradCoord (fun y => L (f y)) x‖ = ‖gradCoord f x‖ := by
    have hfd' :=
      (L.hasFDerivAt.comp x (hf x).hasFDerivAt).fderiv
    have hfd_apply (v : E) :
        fderiv ℝ (fun y => L (f y)) x v = L (fderiv ℝ f x v) := by
      have hv := congrArg (fun T : E →L[ℝ] H => T v) hfd'
      simpa [Function.comp_def] using hv
    have hs :
        ‖gradCoord (fun y => L (f y)) x‖ ^ 2 =
          ‖gradCoord f x‖ ^ 2 := by
      rw [norm_sq_gradCoord, norm_sq_gradCoord]
      apply Finset.sum_congr rfl
      intro i hi
      simp [hfd_apply]
    have h₁ : 0 ≤ ‖gradCoord (fun y => L (f y)) x‖ := norm_nonneg _
    have h₂ : 0 ≤ ‖gradCoord f x‖ := norm_nonneg _
    nlinarith

end Transport

section Chain

universe v

/-- **BKL Corollary 3.5** for a sequence of tensor iterates satisfying (30) and (33). -/
theorem summable_and_tendsto_zero_of_poisson_chain {V : E → ℝ} (hV : V.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    {a : ℝ} (ha : 0 < a) (hH : ∀ x w, a * ‖w‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x w w)
    (G : ℕ → Type v) [∀ k, NormedAddCommGroup (G k)] [∀ k, InnerProductSpace ℝ (G k)]
    [∀ k, FiniteDimensional ℝ (G k)]
    (ι : ∀ k, PiLp 2 (fun _ : Fin (Module.finrank ℝ E) => G k) ≃ₗᵢ[ℝ] G (k + 1))
    (h : ∀ k, E → G k) (hh : ∀ k, (h k).HasTemperateGrowth) (α : ℕ → ℝ)
    (h30 : ∀ k x, -weightedLaplacianVec V (h (k + 1)) x =
      α (k + 1) • ι k (gradCoord (h k) x - ∫ y, gradCoord (h k) y ∂(m.tilted (-V))))
    (h33 : ∀ k, ∫ x, ‖gradCoord (h (k + 1)) x‖ ^ 2 ∂(m.tilted (-V)) =
      ∫ x, ‖gradCoord (h k) x - ∫ y, gradCoord (h k) y ∂(m.tilted (-V))‖ ^ 2 ∂(m.tilted (-V))) :
    Summable (fun k => ∫ x, ‖gradCoord (h k) x‖ ^ 2 ∂(m.tilted (-V))) ∧
      Tendsto (fun k => ∫ x, ‖gradCoord (h k) x‖ ^ 2 ∂(m.tilted (-V))) atTop (𝓝 0) := by
  let L : ℕ → ℝ := fun k =>
    ∫ x, ‖weightedLaplacianVec V (h k) x‖ ^ 2 ∂(m.tilted (-V))
  let v : ℕ → ℝ := fun k =>
    ∫ x, ‖gradCoord (h k) x‖ ^ 2 ∂(m.tilted (-V))
  have hstep (k : ℕ) : L (k + 1) + 0 + a * v k ≤ L k := by
    let q : E → PiLp 2 (fun _ : Fin (Module.finrank ℝ E) => G k) :=
      fun x => (ι k).symm (h (k + 1) x)
    have hq : q.HasTemperateGrowth :=
      (ι k).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasTemperateGrowth.comp
        (hh (k + 1))
    have hq30 : ∀ x, -weightedLaplacianVec V q x =
        α (k + 1) •
          (gradCoord (h k) x - ∫ y, gradCoord (h k) y ∂(m.tilted (-V))) := by
      intro x
      rw [weightedLaplacianVec_linearIsometryEquiv V
        ((hh (k + 1)).1.of_le (WithTop.coe_le_coe.mpr le_top)) (ι k).symm x]
      rw [← map_neg, h30 k x]
      simp only [map_smul, LinearIsometryEquiv.symm_apply_apply]
    have hq33 :
        ∫ x, ‖gradCoord q x‖ ^ 2 ∂(m.tilted (-V)) =
          ∫ x, ‖gradCoord (h k) x - ∫ y, gradCoord (h k) y ∂(m.tilted (-V))‖ ^ 2
            ∂(m.tilted (-V)) := by
      calc
        ∫ x, ‖gradCoord q x‖ ^ 2 ∂(m.tilted (-V)) =
            ∫ x, ‖gradCoord (h (k + 1)) x‖ ^ 2 ∂(m.tilted (-V)) := by
          apply integral_congr_ae
          filter_upwards [] with x
          rw [norm_gradCoord_linearIsometryEquiv
            ((hh (k + 1)).1.differentiable (by simp)) (ι k).symm x]
        _ = _ := h33 k
    have hLap :
        ∫ x, ‖weightedLaplacianVec V q x‖ ^ 2 ∂(m.tilted (-V)) = L (k + 1) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [weightedLaplacianVec_linearIsometryEquiv V
        ((hh (k + 1)).1.of_le (WithTop.coe_le_coe.mpr le_top)) (ι k).symm x,
        LinearIsometryEquiv.norm_map]
    have hp := integral_norm_sq_weightedLaplacianVec_ge
      m hV hexp hH (hh k) hq hq30 hq33
    rw [hLap] at hp
    have hχ :
        0 ≤ ∫ x, ‖gradCoord (gradCoord (h k)) x -
          α (k + 1) • gradCoord q x‖ ^ 2 ∂(m.tilted (-V)) :=
      integral_nonneg (fun x => sq_nonneg _)
    change L (k + 1) +
      (∫ x, ‖gradCoord (gradCoord (h k)) x -
        α (k + 1) • gradCoord q x‖ ^ 2 ∂(m.tilted (-V))) + a * v k ≤ L k at hp
    linarith
  have hL : ∀ k, 0 ≤ L k := fun k => integral_nonneg (fun x => sq_nonneg _)
  have hv : ∀ k, 0 ≤ v k := fun k => integral_nonneg (fun x => sq_nonneg _)
  obtain ⟨hs, _, ht⟩ := summable_and_tendsto_zero_of_energy
    (χ := fun _ => 0) ha hL (fun _ => le_rfl) hv hstep
  exact ⟨hs, ht⟩

end Chain

section Symmetry

universe v

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [BorelSpace E] in
/-- Centering in `L²(μ; H)`: `∫ ‖F - ∫ F‖² = ∫ ‖F‖² - ‖∫ F‖²` for a probability measure. -/
private theorem integral_norm_sq_sub_integral {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (μ : Measure E) [IsProbabilityMeasure μ]
    {F : E → H} (hF : Integrable F μ) (hF2 : Integrable (fun x => ‖F x‖ ^ 2) μ) :
    ∫ x, ‖F x - ∫ y, F y ∂μ‖ ^ 2 ∂μ = ∫ x, ‖F x‖ ^ 2 ∂μ - ‖∫ y, F y ∂μ‖ ^ 2 := by
  set c := ∫ y, F y ∂μ
  have h1 : ∀ x, ‖F x - c‖ ^ 2 = ‖F x‖ ^ 2 - 2 * ⟪F x, c⟫ + ‖c‖ ^ 2 := fun x =>
    norm_sub_sq_real _ _
  have hi : Integrable (fun x => ⟪F x, c⟫) μ := hF.inner_const c
  simp_rw [h1]
  have hA : Integrable (fun x => ‖F x‖ ^ 2 - 2 * ⟪F x, c⟫) μ := hF2.sub (hi.const_mul 2)
  rw [integral_add hA (integrable_const _), integral_sub hF2 (hi.const_mul 2),
    integral_const_mul, integral_const, probReal_univ, one_smul]
  have hin : ∫ x, ⟪F x, c⟫ ∂μ = ⟪c, c⟫ := by
    simp_rw [real_inner_comm c]
    rw [integral_inner hF c]
  rw [hin]
  rw [real_inner_self_eq_norm_sq]
  ring

omit [CompleteSpace E] in
/-- Fields of temperate growth and their squared norms are integrable under all exponential
moments. -/
private theorem integrable_and_integrable_norm_sq_of_hasTemperateGrowth {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] (μ : Measure E)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {f : E → H}
    (hf : f.HasTemperateGrowth) : Integrable f μ ∧ Integrable (fun x => ‖f x‖ ^ 2) μ := by
  obtain ⟨k, C, hb⟩ := hf.2 0
  have hb' : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ k := fun x => by
    simpa only [norm_iteratedFDeriv_zero] using hb x
  refine
    ⟨FunctionalInequalities.Probability.integrable_of_norm_le_pow μ hexp
        hf.1.continuous.aestronglyMeasurable hb',
      ?_⟩
  refine
    FunctionalInequalities.Probability.integrable_of_norm_le_pow μ hexp
      (hf.1.continuous.aestronglyMeasurable.norm.pow 2) (C := C ^ 2) (k := 2 * k) (fun x => ?_)
  have h0 : 0 ≤ ‖f x‖ := norm_nonneg _
  have hsq : ‖f x‖ ^ 2 ≤ (C * (1 + ‖x‖) ^ k) ^ 2 := pow_le_pow_left₀ h0 (hb' x) 2
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    ‖f x‖ ^ 2 ≤ (C * (1 + ‖x‖) ^ k) ^ 2 := hsq
    _ = C ^ 2 * (1 + ‖x‖) ^ (2 * k) := by ring

section CoordinateSymmetry

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ G]

/-- The coefficients of `∇²f` are the second derivatives `D²f(x)(e_i, e_j)`. -/
theorem gradCoord_gradCoord_apply {f : E → G} (hf : ContDiff ℝ ∞ f) (x : E)
    (i j : Fin (Module.finrank ℝ E)) :
    gradCoord (gradCoord f) x i j =
      iteratedFDeriv ℝ 2 f x ![stdOrthonormalBasis ℝ E i, stdOrthonormalBasis ℝ E j] := by
  let L : (E →L[ℝ] G) →L[ℝ] PiLp 2 (fun _ : Fin (Module.finrank ℝ E) => G) :=
    (PiLp.continuousLinearEquiv 2 ℝ _).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun i =>
        ContinuousLinearMap.apply ℝ G (stdOrthonormalBasis ℝ E i))
  have heq : gradCoord f = L ∘ fderiv ℝ f := rfl
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  change (fderiv ℝ (gradCoord f) x (stdOrthonormalBasis ℝ E i)) j = _
  rw [heq, (L.hasFDerivAt.comp x hd.hasFDerivAt).fderiv, ContinuousLinearMap.comp_apply,
    iteratedFDeriv_two_apply]
  rfl

/-- `∇²f` is symmetric in its first two indices. -/
theorem gradCoord_gradCoord_symm {f : E → G} (hf : ContDiff ℝ ∞ f) (x : E)
    (i j : Fin (Module.finrank ℝ E)) :
    gradCoord (gradCoord f) x i j = gradCoord (gradCoord f) x j i := by
  rw [gradCoord_gradCoord_apply hf, gradCoord_gradCoord_apply hf]
  have :=
    iteratedFDeriv_comp_perm_of_contDiff hf 2 x
      ![stdOrthonormalBasis ℝ E i, stdOrthonormalBasis ℝ E j] (Equiv.swap 0 1)
  rw [← this]
  congr 1
  ext k
  fin_cases k <;> rfl

end CoordinateSymmetry

section GradientEnergyIdentities

omit [CompleteSpace E] [m.IsAddHaarMeasure]
/-- **BKL (35)**: under the normalization (33), the energy drop `v_i - v_{i+1}` is `‖∫ ∇h_i‖²`. -/
theorem integral_norm_sq_gradCoord_sub_eq_of_normalized {V : E → ℝ}
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    [IsProbabilityMeasure (m.tilted (-V))]
    {g : E → G} {h : E → PiLp 2 (fun _ : Fin (Module.finrank ℝ E) => G)}
    (hg : g.HasTemperateGrowth)
    (h33 : ∫ x, ‖gradCoord h x‖ ^ 2 ∂(m.tilted (-V)) =
      ∫ x, ‖gradCoord g x - ∫ y, gradCoord g y ∂(m.tilted (-V))‖ ^ 2 ∂(m.tilted (-V))) :
    ∫ x, ‖gradCoord g x‖ ^ 2 ∂(m.tilted (-V)) - ∫ x, ‖gradCoord h x‖ ^ 2 ∂(m.tilted (-V)) =
      ‖∫ x, gradCoord g x ∂(m.tilted (-V))‖ ^ 2 := by
  obtain ⟨hi, hi2⟩ := integrable_and_integrable_norm_sq_of_hasTemperateGrowth (m.tilted (-V)) hexp
    (hasTemperateGrowth_gradCoord hg)
  rw [h33, integral_norm_sq_sub_integral (m.tilted (-V)) hi hi2]
  ring

/--
**BKL (36)** along a sequence of iterates normalized by (33): `v_0 = v_N + Σ_{k<N} ‖∫ ∇h_k‖²`. -/
theorem integral_norm_sq_gradCoord_eq_add_sum {V : E → ℝ}
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    [IsProbabilityMeasure (m.tilted (-V))] (G : ℕ → Type v) [∀ k, NormedAddCommGroup (G k)]
    [∀ k, InnerProductSpace ℝ (G k)] [∀ k, FiniteDimensional ℝ (G k)] (h : ∀ k, E → G k)
    (hh : ∀ k, (h k).HasTemperateGrowth)
    (h33 :
      ∀ k,
        ∫ x, ‖gradCoord (h (k + 1)) x‖ ^ 2 ∂(m.tilted (-V)) =
          ∫ x,
            ‖gradCoord (h k) x - ∫ y, gradCoord (h k) y ∂(m.tilted (-V))‖ ^ 2 ∂(m.tilted (-V)))
    (N : ℕ) :
    ∫ x, ‖gradCoord (h 0) x‖ ^ 2 ∂(m.tilted (-V)) =
      ∫ x, ‖gradCoord (h N) x‖ ^ 2 ∂(m.tilted (-V)) +
        ∑ k ∈ Finset.range N, ‖∫ x, gradCoord (h k) x ∂(m.tilted (-V))‖ ^ 2 := by
  induction N with
  | zero => simp
  | succ N
    ih =>
    obtain ⟨hi, hi2⟩ :=
      integrable_and_integrable_norm_sq_of_hasTemperateGrowth (m.tilted (-V)) hexp
        (hasTemperateGrowth_gradCoord (hh N))
    have h := integral_norm_sq_sub_integral (m.tilted (-V)) hi hi2
    rw [← h33 N] at h
    rw [ih, Finset.sum_range_succ]
    linarith

end GradientEnergyIdentities

/--
**BKL Lemma 3.2** for a supplied pair satisfying (30) (the normalization (33) is not needed): if
`λ > 0` and `λ ≤ α²` whenever `α ≠ 0`, then `∇₀h` lies within squared `L²` distance `χ / λ`, `χ =
‖∇²g - α ∇h‖²`, of a tensor field
`T` symmetric in its first two indices (with `‖∇₀h - T‖²` integrable). -/
theorem exists_symm_integral_norm_sq_sub_le {V : E → ℝ} (hV : V.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    [IsProbabilityMeasure (m.tilted (-V))] {g : E → G}
    {h : E → PiLp 2 (fun _ : Fin (Module.finrank ℝ E) => G)} {α : ℝ} (hg : g.HasTemperateGrowth)
    (hh : h.HasTemperateGrowth)
    (h30 :
      ∀ x,
        -weightedLaplacianVec V h x = α • (gradCoord g x - ∫ y, gradCoord g y ∂(m.tilted (-V))))
    {lam : ℝ} (hlam : 0 < lam) (hαlam : α ≠ 0 → lam ≤ α ^ 2) :
    ∃ T :
      E →
        PiLp 2
          (fun _ : Fin (Module.finrank ℝ E) => PiLp 2 (fun _ : Fin (Module.finrank ℝ E) => G)),
      (∀ x i j, T x i j = T x j i) ∧
        Integrable (fun x => ‖(gradCoord h x - ∫ y, gradCoord h y ∂(m.tilted (-V))) - T x‖ ^ 2)
            (m.tilted (-V)) ∧
          ∫ x,
              ‖(gradCoord h x - ∫ y, gradCoord h y ∂(m.tilted (-V))) - T x‖ ^
                2 ∂(m.tilted (-V)) ≤
            (∫ x, ‖gradCoord (gradCoord g) x - α • gradCoord h x‖ ^ 2 ∂(m.tilted (-V))) / lam := by
  set μ := m.tilted (-V) with hμ
  set c1 := ∫ y, gradCoord h y ∂μ
  set c2 := ∫ y, gradCoord (gradCoord g) y ∂μ
  have hgg : (gradCoord (gradCoord g)).HasTemperateGrowth :=
    hasTemperateGrowth_gradCoord (hasTemperateGrowth_gradCoord hg)
  have hgh : (gradCoord h).HasTemperateGrowth := hasTemperateGrowth_gradCoord hh
  have hχ0 : 0 ≤ ∫ x, ‖gradCoord (gradCoord g) x - α • gradCoord h x‖ ^ 2 ∂μ :=
    integral_nonneg fun x => by positivity
  by_cases hα : α = 0
  · subst hα
    refine ⟨fun _ => 0, fun _ _ _ => rfl, ?_, ?_⟩
    · have :=
        (integrable_and_integrable_norm_sq_of_hasTemperateGrowth μ hexp
            (hgh.sub (Function.HasTemperateGrowth.const c1))).2
      simpa only [sub_zero, Pi.sub_apply] using this
    · have hV1 : ContDiff ℝ 1 V := hV.1.of_le (by simp)
      obtain ⟨k, C, hC⟩ := hV.2 1
      have hVg : ∀ x : E, ‖gradient V x‖ ≤ C * (1 + ‖x‖) ^ k := by
        intro x
        rw [norm_gradient_eq_norm_iteratedFDeriv_one]
        exact hC x
      have hIBP := integral_inner_weightedLaplacianVec_eq_neg m hV1 hVg hexp hh hh
      have hzero : ∀ x, weightedLaplacianVec V h x = 0 := fun x => by
        have := h30 x
        rw [zero_smul, neg_eq_zero] at this
        exact this
      simp only [hzero, inner_zero_left, integral_zero] at hIBP
      have hE : ∫ x, ‖gradCoord h x‖ ^ 2 ∂μ = 0 := by
        have :
          ∫ x, ‖gradCoord h x‖ ^ 2 ∂μ =
            ∫ x,
              ∑ i,
                ⟪fderiv ℝ h x (stdOrthonormalBasis ℝ E i),
                  fderiv ℝ h x (stdOrthonormalBasis ℝ E i)⟫ ∂μ := by
          congr 1
          funext x
          rw [norm_sq_gradCoord]
          simp only [real_inner_self_eq_norm_sq]
        linarith
      obtain ⟨hi, hi2⟩ := integrable_and_integrable_norm_sq_of_hasTemperateGrowth μ hexp hgh
      have hc := integral_norm_sq_sub_integral μ hi hi2
      simp only [sub_zero]
      have : 0 ≤ ‖c1‖ ^ 2 := by positivity
      have hdiv :
        0 ≤ (∫ x, ‖gradCoord (gradCoord g) x - (0 : ℝ) • gradCoord h x‖ ^ 2 ∂μ) / lam :=
        div_nonneg hχ0 hlam.le
      linarith
  · have hl : lam ≤ α ^ 2 := hαlam hα
    let F :
      E →
        PiLp 2
          (fun _ : Fin (Module.finrank ℝ E) =>
            PiLp 2 (fun _ : Fin (Module.finrank ℝ E) => G)) :=
      fun x => gradCoord (gradCoord g) x - α • gradCoord h x
    have hsm : (fun x => α • gradCoord h x).HasTemperateGrowth := by
      have :=
        (α •
              ContinuousLinearMap.id ℝ
                (PiLp 2
                  (fun _ : Fin (Module.finrank ℝ E) =>
                    PiLp 2 (fun _ : Fin (Module.finrank ℝ E) => G)))).hasTemperateGrowth.comp
          hgh
      simpa only [Function.comp_def, smul_apply, ContinuousLinearMap.id_apply] using this
    have hF : F.HasTemperateGrowth := hgg.sub hsm
    obtain ⟨hFi, hFi2⟩ := integrable_and_integrable_norm_sq_of_hasTemperateGrowth μ hexp hF
    obtain ⟨hggi, -⟩ := integrable_and_integrable_norm_sq_of_hasTemperateGrowth μ hexp hgg
    obtain ⟨hghi, -⟩ := integrable_and_integrable_norm_sq_of_hasTemperateGrowth μ hexp hgh
    have hintF : ∫ y, F y ∂μ = c2 - α • c1 := by
      simp only [F]
      rw [integral_sub hggi (by exact hghi.smul α : Integrable (fun x => α • gradCoord h x) μ),
        integral_smul]
    have hc2 : ∀ i j, c2 i j = c2 j i := by
      intro i j
      let P :
        PiLp 2
            (fun _ : Fin (Module.finrank ℝ E) =>
              PiLp 2 (fun _ : Fin (Module.finrank ℝ E) => G)) →L[ℝ]
          G :=
        (PiLp.proj 2 (fun _ : Fin (Module.finrank ℝ E) => G) j).comp
          (PiLp.proj 2
            (fun _ : Fin (Module.finrank ℝ E) => PiLp 2 (fun _ : Fin (Module.finrank ℝ E) => G))
            i)
      let Q :
        PiLp 2
            (fun _ : Fin (Module.finrank ℝ E) =>
              PiLp 2 (fun _ : Fin (Module.finrank ℝ E) => G)) →L[ℝ]
          G :=
        (PiLp.proj 2 (fun _ : Fin (Module.finrank ℝ E) => G) i).comp
          (PiLp.proj 2
            (fun _ : Fin (Module.finrank ℝ E) => PiLp 2 (fun _ : Fin (Module.finrank ℝ E) => G))
            j)
      have hP : P c2 = ∫ y, P (gradCoord (gradCoord g) y) ∂μ := (P.integral_comp_comm hggi).symm
      have hQ : Q c2 = ∫ y, Q (gradCoord (gradCoord g) y) ∂μ := (Q.integral_comp_comm hggi).symm
      change P c2 = Q c2
      rw [hP, hQ]
      congr 1
      funext y
      exact gradCoord_gradCoord_symm hg.1 y i j
    have hpt :
      ∀ x,
        ‖(gradCoord h x - c1) - α⁻¹ • (gradCoord (gradCoord g) x - c2)‖ ^ 2 =
          (α ^ 2)⁻¹ * ‖F x - ∫ y, F y ∂μ‖ ^ 2 := by
      intro x
      have hv :
        (gradCoord h x - c1) - α⁻¹ • (gradCoord (gradCoord g) x - c2) =
          -(α⁻¹ • (F x - ∫ y, F y ∂μ)) := by
        rw [hintF]
        simp only [F, smul_sub, smul_smul, inv_mul_cancel₀ hα, one_smul]
        abel
      rw [hv, norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow]
    obtain ⟨-, hFc2⟩ :=
      integrable_and_integrable_norm_sq_of_hasTemperateGrowth μ hexp
        (hF.sub (Function.HasTemperateGrowth.const (∫ y, F y ∂μ)))
    have hint : Integrable (fun x => (α ^ 2)⁻¹ * ‖F x - ∫ y, F y ∂μ‖ ^ 2) μ := hFc2.const_mul _
    refine ⟨fun x => α⁻¹ • (gradCoord (gradCoord g) x - c2), fun x i j => ?_, ?_, ?_⟩
    · simp only [PiLp.smul_apply, PiLp.sub_apply]
      rw [gradCoord_gradCoord_symm hg.1 x i j, hc2 i j]
    · simp_rw [hpt]
      exact hint
    · simp_rw [hpt]
      rw [integral_const_mul, integral_norm_sq_sub_integral μ hFi hFi2]
      have hinv : (α ^ 2)⁻¹ ≤ lam⁻¹ := inv_anti₀ hlam hl
      have hsq : 0 ≤ ‖∫ y, F y ∂μ‖ ^ 2 := by positivity
      have hα2 : 0 ≤ (α ^ 2)⁻¹ := by positivity
      calc
        (α ^ 2)⁻¹ * (∫ x, ‖F x‖ ^ 2 ∂μ - ‖∫ y, F y ∂μ‖ ^ 2) ≤ (α ^ 2)⁻¹ * ∫ x, ‖F x‖ ^ 2 ∂μ := by
          nlinarith
        _ ≤ lam⁻¹ * ∫ x, ‖F x‖ ^ 2 ∂μ := mul_le_mul_of_nonneg_right hinv hχ0
        _ = (∫ x, ‖gradCoord (gradCoord g) x - α • gradCoord h x‖ ^ 2 ∂μ) / lam := by
          rw [div_eq_inv_mul]

section TensorSymmetrization

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ G]

/-- Exchange of the first two indices of a tensor in `PiLp 2 (Fin n → PiLp 2 (Fin n → G))` (the
source's transposition `τ₁`). -/
def swapFirstTwo {n : ℕ} (A : PiLp 2 (fun _ : Fin n => PiLp 2 (fun _ : Fin n => G))) :
    PiLp 2 (fun _ : Fin n => PiLp 2 (fun _ : Fin n => G)) :=
  WithLp.toLp 2 fun i => WithLp.toLp 2 fun j => A j i

omit [NormedAddCommGroup G] [InnerProductSpace ℝ G] in
theorem swapFirstTwo_apply {n : ℕ} (A : PiLp 2 (fun _ : Fin n => PiLp 2 (fun _ : Fin n => G)))
    (i j : Fin n) : swapFirstTwo A i j = A j i := rfl

section TensorPermutation

omit [InnerProductSpace ℝ G]
theorem swapFirstTwo_sub {n : ℕ} (A B : PiLp 2 (fun _ : Fin n => PiLp 2 (fun _ : Fin n => G))) :
    swapFirstTwo (A - B) = swapFirstTwo A - swapFirstTwo B := rfl

theorem norm_swapFirstTwo {n : ℕ} (A : PiLp 2 (fun _ : Fin n => PiLp 2 (fun _ : Fin n => G))) :
    ‖swapFirstTwo A‖ = ‖A‖ := by
  have hsq : ‖swapFirstTwo A‖ ^ 2 = ‖A‖ ^ 2 := by
    simp only [PiLp.norm_sq_eq_of_L2, swapFirstTwo_apply]
    rw [Finset.sum_comm]
  nlinarith [norm_nonneg (swapFirstTwo A), norm_nonneg A]

end TensorPermutation

/-- The symmetrization `S₂ A = (A + τ₁ A) / 2` of the first two indices. -/
def symmetrizeFirstTwo {n : ℕ} (A : PiLp 2 (fun _ : Fin n => PiLp 2 (fun _ : Fin n => G))) :
    PiLp 2 (fun _ : Fin n => PiLp 2 (fun _ : Fin n => G)) :=
  (1 / 2 : ℝ) • (A + swapFirstTwo A)

/-- `S₂` is at least as close to `A` as any tensor symmetric in its first two indices. -/
theorem norm_sub_symmetrizeFirstTwo_le {n : ℕ}
    (A T : PiLp 2 (fun _ : Fin n => PiLp 2 (fun _ : Fin n => G))) (hT : ∀ i j, T i j = T j i) :
    ‖A - symmetrizeFirstTwo A‖ ≤ ‖A - T‖ := by
  have hsT : swapFirstTwo T = T := by
    ext i j
    exact (hT j i)
  have h : A - symmetrizeFirstTwo A = (1 / 2 : ℝ) • ((A - T) - swapFirstTwo (A - T)) := by
    rw [swapFirstTwo_sub, hsT, symmetrizeFirstTwo]
    module
  rw [h, norm_smul]
  calc ‖(1 / 2 : ℝ)‖ * ‖(A - T) - swapFirstTwo (A - T)‖
      ≤ ‖(1 / 2 : ℝ)‖ * (‖A - T‖ + ‖swapFirstTwo (A - T)‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
    _ = ‖A - T‖ := by
        rw [norm_swapFirstTwo]
        norm_num
        ring

end TensorSymmetrization

/-- **BKL Lemma 3.3 in the case `q = 2`** for a supplied pair satisfying (30): with `S₂` the
symmetrization of the first two indices, `‖∇₀h - S₂∇₀h‖² ≤ χ / λ` when `λ > 0` and `λ ≤ α²` for
`α ≠ 0` (it follows from Lemma 3.2 because `S₂` is the nearest symmetric tensor). -/
theorem integral_norm_sq_sub_symmetrizeFirstTwo_le {V : E → ℝ} (hV : V.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    [IsProbabilityMeasure (m.tilted (-V))]
    {g : E → G} {h : E → PiLp 2 (fun _ : Fin (Module.finrank ℝ E) => G)} {α : ℝ}
    (hg : g.HasTemperateGrowth) (hh : h.HasTemperateGrowth)
    (h30 : ∀ x, -weightedLaplacianVec V h x =
      α • (gradCoord g x - ∫ y, gradCoord g y ∂(m.tilted (-V))))
    {lam : ℝ} (hlam : 0 < lam) (hαlam : α ≠ 0 → lam ≤ α ^ 2) :
    ∫ x, ‖(gradCoord h x - ∫ y, gradCoord h y ∂(m.tilted (-V))) -
        symmetrizeFirstTwo (gradCoord h x - ∫ y, gradCoord h y ∂(m.tilted (-V)))‖ ^ 2
        ∂(m.tilted (-V)) ≤
      (∫ x, ‖gradCoord (gradCoord g) x - α • gradCoord h x‖ ^ 2 ∂(m.tilted (-V))) / lam := by
  obtain ⟨T, hT1, hT2, hT3⟩ :=
    exists_symm_integral_norm_sq_sub_le m hV hexp hg hh h30 hlam hαlam
  have hpt : ∀ x, ‖(gradCoord h x - ∫ y, gradCoord h y ∂(m.tilted (-V))) -
      symmetrizeFirstTwo (gradCoord h x - ∫ y, gradCoord h y ∂(m.tilted (-V)))‖ ^ 2 ≤
        ‖(gradCoord h x - ∫ y, gradCoord h y ∂(m.tilted (-V))) - T x‖ ^ 2 := fun x =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_sub_symmetrizeFirstTwo_le _ _ (hT1 x)) 2
  by_cases hI : Integrable (fun x => ‖(gradCoord h x - ∫ y, gradCoord h y ∂(m.tilted (-V))) -
      symmetrizeFirstTwo (gradCoord h x - ∫ y, gradCoord h y ∂(m.tilted (-V)))‖ ^ 2) (m.tilted (-V))
  · exact (integral_mono hI hT2 hpt).trans hT3
  · rw [integral_undef hI]
    exact div_nonneg (integral_nonneg fun x => by positivity) hlam.le

end Symmetry

section TaylorDrop

/-- **BKL (61)**, linear form, for a supplied pair satisfying (30): `∫ Dh = α T₁(∇₀g)`. -/
theorem integral_fderiv_apply_eq_smul_taylorTensor_one {V : E → ℝ} (hV : V.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    {g : E → G} {h : E → PiLp 2 (fun _ : Fin (Module.finrank ℝ E) => G)} {α : ℝ}
    (hh : h.HasTemperateGrowth)
    (h30 : ∀ x, -weightedLaplacianVec V h x =
      α • (gradCoord g x - ∫ y, gradCoord g y ∂(m.tilted (-V)))) (v : E) :
    (∫ x, fderiv ℝ h x ∂(m.tilted (-V))) v =
      α • taylorTensor (m.tilted (-V))
        (fun x => gradCoord g x - ∫ y, gradCoord g y ∂(m.tilted (-V))) 1 ![v] := by
  have hV1 : ContDiff ℝ 1 V := hV.1.of_le (by simp)
  obtain ⟨k, C, hC⟩ := hV.2 1
  have hVg : ∀ x : E, ‖gradient V x‖ ≤ C * (1 + ‖x‖) ^ k := fun x => by
    rw [norm_gradient_eq_norm_iteratedFDeriv_one]; exact hC x
  have h49 := taylorTensor_one_neg_weightedLaplacianVec (m := m) hV1 hVg hexp hh ![v]
  have hfun : (fun x => -weightedLaplacianVec V h x) =
      fun x => α • (gradCoord g x - ∫ y, gradCoord g y ∂(m.tilted (-V))) := funext h30
  rw [hfun, taylorTensor_const_smul] at h49
  simpa using h49.symm

/-- **BKL (61)** in Hilbert–Schmidt form, for a supplied pair satisfying (30):
`‖∫ ∇h‖² = α² Σ_i ‖T₁(∇₀g)(e_i)‖²`. -/
theorem norm_sq_integral_gradCoord_eq {V : E → ℝ} (hV : V.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V))) {g : E → G}
    {h : E → PiLp 2 (fun _ : Fin (Module.finrank ℝ E) => G)} {α : ℝ} (hh : h.HasTemperateGrowth)
    (h30 :
      ∀ x,
        -weightedLaplacianVec V h x =
          α • (gradCoord g x - ∫ y, gradCoord g y ∂(m.tilted (-V)))) :
    ‖∫ x, gradCoord h x ∂(m.tilted (-V))‖ ^ 2 =
      α ^ 2 *
        ∑ i,
          ‖taylorTensor (m.tilted (-V))
                (fun x => gradCoord g x - ∫ y, gradCoord g y ∂(m.tilted (-V))) 1
                ![stdOrthonormalBasis ℝ E i]‖ ^
            2 := by
  rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hint : Integrable (gradCoord h) (m.tilted (-V)) :=
    FunctionalInequalities.Probability.integrable_of_hasTemperateGrowth _ hexp
      (hasTemperateGrowth_gradCoord hh)
  let _ : NormedAddCommGroup (E →L[ℝ] PiLp 2 (fun _ : Fin (Module.finrank ℝ E) => G)) :=
    inferInstance
  have hintD : Integrable (fun x => fderiv ℝ h x) (m.tilted (-V)) := by
    obtain ⟨k, C, hb⟩ := hh.2 1
    refine
      FunctionalInequalities.Probability.integrable_of_norm_le_pow (m.tilted (-V)) hexp
        (hh.1.continuous_fderiv (by simp)).aestronglyMeasurable (C := C) (k := k) (fun x => ?_)
    rw [← norm_iteratedFDeriv_one]
    exact hb x
  let P :
    PiLp 2
        (fun _ : Fin (Module.finrank ℝ E) =>
          PiLp 2 (fun _ : Fin (Module.finrank ℝ E) => G)) →L[ℝ]
      PiLp 2 (fun _ : Fin (Module.finrank ℝ E) => G) :=
    PiLp.proj 2
      (fun _ : Fin (Module.finrank ℝ E) => PiLp 2 (fun _ : Fin (Module.finrank ℝ E) => G)) i
  have h1 :
    (∫ x, gradCoord h x ∂(m.tilted (-V))) i =
      (∫ x, fderiv ℝ h x ∂(m.tilted (-V))) (stdOrthonormalBasis ℝ E i) := by
    change P (∫ x, gradCoord h x ∂(m.tilted (-V))) = _
    rw [← P.integral_comp_comm hint, ContinuousLinearMap.integral_apply hintD]
    rfl
  rw [h1, integral_fderiv_apply_eq_smul_taylorTensor_one m hV hexp hh h30, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs]


/--
**The first energy drop of BKL Lemma 3.9** for a supplied eigenfunction: if `ℒf = -λ f`, `∫ f = 0`
and the covariance of `μ` is at most `K` (`∫ ⟪e, x - b⟫² ≤ K ‖e‖²` with `b` the barycenter), then
`‖∫ ∇f‖² ≤ λ² K ∫ f²` (the source's `p₁ = λ₁² |∫ x f|² ≤ λ₁² ‖Cov μ‖`, with `‖f‖₂ = 1`, `K = 1`). -/
theorem norm_sq_integral_gradient_le_of_eigen {V : E → ℝ} (hV : V.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    [IsProbabilityMeasure (m.tilted (-V))] {f : E → ℝ} (hf : f.HasTemperateGrowth) {lam : ℝ}
    (heig : ∀ x, weightedLaplacian V f x = -lam * f x) (hf0 : ∫ x, f x ∂(m.tilted (-V)) = 0)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hcov : ∀ e : E, ∫ x, ⟪e, x - ∫ y, y ∂(m.tilted (-V))⟫ ^ 2 ∂(m.tilted (-V)) ≤ K * ‖e‖ ^ 2) :
    ‖∫ x, gradient f x ∂(m.tilted (-V))‖ ^ 2 ≤ lam ^ 2 * K * ∫ x, f x ^ 2 ∂(m.tilted (-V)) := by
  set μ := m.tilted (-V) with hμ
  set w := ∫ x, gradient f x ∂μ
  set b := ∫ y, y ∂μ
  have hV1 : ContDiff ℝ 1 V := hV.1.of_le (by simp)
  obtain ⟨k, Cb, hCb⟩ := hV.2 1
  have hVg : ∀ x : E, ‖gradient V x‖ ≤ Cb * (1 + ‖x‖) ^ k := fun x => by
    rw [norm_gradient_eq_norm_iteratedFDeriv_one]; exact hCb x
  have hlin : (fun x : E => ⟪w, x⟫).HasTemperateGrowth :=
    Function.hasTemperateGrowth_inner_right w
  have hibp :=
    integral_weightedLaplacian_mul_eq_neg_of_hasTemperateGrowth m hV1 hVg hexp hf hlin
  have hgl : ∀ x, gradient (fun y : E => ⟪w, y⟫) x = w := by
    intro x
    have hd : fderiv ℝ (fun y : E => ⟪w, y⟫) x = InnerProductSpace.toDual ℝ E w := by
      change fderiv ℝ (⇑(innerSL ℝ w)) x = _
      rw [((innerSL ℝ w).hasFDerivAt (x := x)).fderiv]
      ext y
      simp
    simp only [gradient, hd, LinearIsometryEquiv.symm_apply_apply]
  simp only [heig, hgl] at hibp
  have hgi : Integrable (gradient f) μ :=
    (FunctionalInequalities.Probability.memLp_two_of_hasTemperateGrowth μ hexp
          (hasTemperateGrowth_gradient hf)).integrable
      (by norm_num)
  have hf2 := FunctionalInequalities.Probability.memLp_two_of_hasTemperateGrowth μ hexp hf
  have hg : (fun x : E => ⟪w, x - b⟫).HasTemperateGrowth := by
    have : (fun x : E => ⟪w, x - b⟫) = fun x => ⟪w, x⟫ - ⟪w, b⟫ := by
      funext x;
      rw [inner_sub_right]
    rw [this]
    exact hlin.sub (Function.HasTemperateGrowth.const _)
  have hg2 := FunctionalInequalities.Probability.memLp_two_of_hasTemperateGrowth μ hexp hg
  have hfi : Integrable f μ := hf2.integrable (by norm_num)
  have hfl : Integrable (fun x => f x * ⟪w, x⟫) μ :=
    (FunctionalInequalities.Probability.memLp_two_of_hasTemperateGrowth μ hexp
          (hf.mul hlin)).integrable
      (by norm_num)
  have h1 : ‖w‖ ^ 2 = lam * ∫ x, f x * ⟪w, x - b⟫ ∂μ := by
    have hww : ‖w‖ ^ 2 = ∫ x, ⟪gradient f x, w⟫ ∂μ := by
      rw [← real_inner_self_eq_norm_sq]
      have : ∫ x, ⟪gradient f x, w⟫ ∂μ = ∫ x, ⟪w, gradient f x⟫ ∂μ := by
        congr 1; funext x;
        exact real_inner_comm _ _
      rw [this, integral_inner hgi w]
    have hsplit : ∫ x, f x * ⟪w, x - b⟫ ∂μ = ∫ x, f x * ⟪w, x⟫ ∂μ := by
      have : (fun x => f x * ⟪w, x - b⟫) = fun x => f x * ⟪w, x⟫ - ⟪w, b⟫ * f x := by
        funext x;
        rw [inner_sub_right]; ring
      rw [this, integral_sub hfl (hfi.const_mul _), integral_const_mul, hf0, mul_zero, sub_zero]
    rw [hww, hsplit]
    have : ∫ x, -lam * f x * ⟪w, x⟫ ∂μ = -lam * ∫ x, f x * ⟪w, x⟫ ∂μ := by
      rw [← integral_const_mul]; congr 1; funext x; ring
    rw [this] at hibp
    linarith
  -- Cauchy–Schwarz in L²
  have hCS : (∫ x, f x * ⟪w, x - b⟫ ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * ∫ x, ⟪w, x - b⟫ ^ 2 ∂μ := by
    have hsq : ∀ (u : Lp ℝ 2 μ), ‖u‖ ^ 2 = ∫ x, u x ^ 2 ∂μ := by
      intro u
      rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
      congr 1; funext x; rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    have hin : ⟪hf2.toLp f, hg2.toLp (fun x : E => ⟪w, x - b⟫)⟫ = ∫ x, f x * ⟪w, x - b⟫ ∂μ := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hf2.coeFn_toLp, hg2.coeFn_toLp] with x hx hy
      rw [hx, hy, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real,
        mul_comm]
    have h1' : ∫ x, f x ^ 2 ∂μ = ‖hf2.toLp f‖ ^ 2 := by
      rw [hsq]; apply integral_congr_ae
      filter_upwards [hf2.coeFn_toLp] with x hx; rw [hx]
    have h2' : ∫ x, ⟪w, x - b⟫ ^ 2 ∂μ = ‖hg2.toLp (fun x : E => ⟪w, x - b⟫)‖ ^ 2 := by
      rw [hsq]; apply integral_congr_ae
      filter_upwards [hg2.coeFn_toLp] with x hx; rw [hx]
    rw [← hin, h1', h2', ← mul_pow]
    have := abs_real_inner_le_norm (hf2.toLp f) (hg2.toLp (fun x : E => ⟪w, x - b⟫))
    nlinarith [abs_nonneg ⟪hf2.toLp f, hg2.toLp (fun x : E => ⟪w, x - b⟫)⟫,
      sq_abs ⟪hf2.toLp f, hg2.toLp (fun x : E => ⟪w, x - b⟫)⟫,
      mul_nonneg (norm_nonneg (hf2.toLp f)) (norm_nonneg (hg2.toLp (fun x : E => ⟪w, x - b⟫)))]
  have hK := hcov w
  have hF0 : 0 ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg fun x => by positivity
  have hW0 : 0 ≤ ‖w‖ ^ 2 := by positivity
  have hmain : (‖w‖ ^ 2) ^ 2 ≤ lam ^ 2 * K * (∫ x, f x ^ 2 ∂μ) * ‖w‖ ^ 2 := by
    calc
      (‖w‖ ^ 2) ^ 2 = lam ^ 2 * (∫ x, f x * ⟪w, x - b⟫ ∂μ) ^ 2 := by rw [h1]; ring
      _ ≤ lam ^ 2 * ((∫ x, f x ^ 2 ∂μ) * ∫ x, ⟪w, x - b⟫ ^ 2 ∂μ) :=
        mul_le_mul_of_nonneg_left hCS (sq_nonneg _)
      _ ≤ lam ^ 2 * ((∫ x, f x ^ 2 ∂μ) * (K * ‖w‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK hF0) (sq_nonneg _)
      _ = lam ^ 2 * K * (∫ x, f x ^ 2 ∂μ) * ‖w‖ ^ 2 := by ring
  rcases hW0.lt_or_eq with hpos | hzero
  · nlinarith
  · rw [← hzero]
    positivity

end TaylorDrop

end FunctionalInequalities.Analysis.BakryEmery
