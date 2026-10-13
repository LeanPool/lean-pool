/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.InteriorEquationBridge
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.LocalRepresentativeGlue

/-!
# PenalizationInterior

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-
Uniform interior Hoelder estimate for the penalized resolvents.
-/

/-!
# Uniform interior estimate for the penalized resolvents

Inside the part domain the penalization potential vanishes, so the penalized
resolvent solves `α u_n − ∇·(a∇u_n) = f` there with no zeroth-order term.  The
energy bound `‖u_n‖ ≤ (min α lam)⁻¹ ‖f‖` and the essential bound `2 M` on the
scalar source are both independent of the penalization index, so the interior
Hölder estimate of the small-contrast chain, transported to a Euclidean ball
whose double lies inside the part domain, has an index-free constant.

The constant is `penalizationInteriorHolderConstant`.  Nothing is asserted on
the boundary of the part domain.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open scoped ENNReal RealInnerProductSpace

noncomputable section

variable {d : ℕ} {V U : Set (Vec d)}

/-- A Hölder bound is preserved when the constant is enlarged. -/
theorem euclideanHolderBoundOn_mono {W : Set (Vec d)} {alpha K K' : ℝ}
    {v : Vec d → ℝ} (hKK : K ≤ K')
    (h : EuclideanHolderBoundOn W alpha K v) :
    EuclideanHolderBoundOn W alpha K' v := by
  intro x hx y hy
  exact (h x hx y hy).trans
    (mul_le_mul_of_nonneg_right hKK
      (Real.rpow_nonneg (euclideanNorm_nonneg _) _))

/-- A Hölder bound with a positive exponent forces continuity. -/
theorem continuousOn_of_euclideanHolderBoundOn {W : Set (Vec d)} {alpha K : ℝ}
    (halpha : 0 < alpha) {v : Vec d → ℝ}
    (h : EuclideanHolderBoundOn W alpha K v) : ContinuousOn v W := by
  intro x hx
  have hofVec : Continuous fun y : Vec d => HilbertVec.ofVec (y - x) :=
    ((HilbertVec.continuousLinearEquivVec d).symm.continuous).comp
      (continuous_id.sub continuous_const)
  have hnorm : Continuous fun y : Vec d => euclideanNorm (y - x) := by
    have := hofVec.norm
    simpa only [← euclideanNorm_eq_norm_ofVec] using this
  have hmodulus : ContinuousAt
      (fun y : Vec d => K * euclideanNorm (y - x) ^ alpha) x :=
    continuousAt_const.mul
      ((Real.continuousAt_rpow_const _ _ (Or.inr halpha.le)).comp hnorm.continuousAt)
  have hval : K * euclideanNorm (x - x) ^ alpha = 0 := by
    simp [Real.zero_rpow halpha.ne']
  have hzero : Filter.Tendsto
      (fun y : Vec d => K * euclideanNorm (y - x) ^ alpha)
      (nhdsWithin x W) (nhds 0) := by
    have := hmodulus.continuousWithinAt (s := W)
    rwa [ContinuousWithinAt, hval] at this
  have hsub : Filter.Tendsto (fun y => v y - v x) (nhdsWithin x W) (nhds 0) := by
    refine squeeze_zero_norm' ?_ hzero
    filter_upwards [self_mem_nhdsWithin] with y hy
    simpa only [Real.norm_eq_abs] using h y hy x hx
  have hadd := hsub.add_const (v x)
  rw [ContinuousWithinAt]
  simpa using hadd

/-- A common Hölder bound on a pointwise decreasing family is inherited by its
pointwise infimum. -/
theorem euclideanHolderBoundOn_iInf {W : Set (Vec d)} {alpha K : ℝ}
    {rep : ℕ → Vec d → ℝ}
    (hbdd : ∀ x ∈ W, BddBelow (Set.range fun n => rep n x))
    (h : ∀ n, EuclideanHolderBoundOn W alpha K (rep n)) :
    EuclideanHolderBoundOn W alpha K (fun x => ⨅ n, rep n x) := by
  have hone : ∀ x ∈ W, ∀ y ∈ W,
      (⨅ n, rep n x) - (⨅ n, rep n y) ≤ K * euclideanNorm (x - y) ^ alpha := by
    intro x hx y hy
    have hle : ∀ n, (⨅ m, rep m x) - K * euclideanNorm (x - y) ^ alpha ≤ rep n y := by
      intro n
      have h1 : (⨅ m, rep m x) ≤ rep n x := ciInf_le (hbdd x hx) n
      have h2 := h n x hx y hy
      have h3 : rep n x - rep n y ≤ K * euclideanNorm (x - y) ^ alpha :=
        (le_abs_self _).trans h2
      linarith only [h1, h3]
    have := le_ciInf hle
    linarith only [this]
  intro x hx y hy
  have hxy := hone x hx y hy
  have hyx := hone y hy x hx
  have hsymm : euclideanNorm (y - x) = euclideanNorm (x - y) := by
    rw [show y - x = -(x - y) by ring, euclideanNorm_neg]
  rw [hsymm] at hyx
  rw [abs_le]
  exact ⟨by linarith only [hyx], hxy⟩

/-- The gradient part of the zero-trace norm. -/
theorem ZeroTraceSobolev.norm_gradient_le (u : ZeroTraceSobolev U) :
    ‖ZeroTraceSobolev.gradient u‖ ≤ ‖u‖ := by
  have hsq : ‖ZeroTraceSobolev.gradient u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    have hval : (0 : ℝ) ≤ ‖ZeroTraceSobolev.toL2 u‖ ^ 2 := sq_nonneg _
    linarith only [hval, ZeroTraceSobolev.norm_sq_eq u]
  calc ‖ZeroTraceSobolev.gradient u‖
      = Real.sqrt (‖ZeroTraceSobolev.gradient u‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖u‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖u‖ := Real.sqrt_sq (norm_nonneg _)

/-- The Euclidean `L²` size of the gradient on a subset of the domain is
bounded by the norm of its Hilbert-vector `L²` realization. -/
theorem vectorLpSizeOn_grad_le_norm_gradToHilbertVectorL2
    {W : Set (Vec d)} (hWU : W ⊆ U) (w : H1Function U) :
    vectorLpSizeOn W 2 w.grad ≤ ‖w.gradToHilbertVectorL2‖ := by
  have hnormEq : (fun x => euclideanNorm (w.grad x)) =
      fun x => ‖hilbertifyVecField w.grad x‖ := by
    funext x
    exact euclideanNorm_eq_norm_ofVec (w.grad x)
  have hU2 : eLpNorm (fun x => euclideanNorm (w.grad x)) 2 (volume.restrict U) =
      eLpNorm (hilbertifyVecField w.grad) 2 (volume.restrict U) := by
    rw [hnormEq]
    exact eLpNorm_norm _
      ((Lp.aestronglyMeasurable _).congr w.coeFn_gradToHilbertVectorL2)
  have hcoe : eLpNorm (hilbertifyVecField w.grad) 2 (volume.restrict U) =
      eLpNorm (w.gradToHilbertVectorL2 : Vec d → HilbertVec d) 2
        (volume.restrict U) :=
    (eLpNorm_congr_ae w.coeFn_gradToHilbertVectorL2).symm
  have hmono : eLpNorm (fun x => euclideanNorm (w.grad x)) 2 (volume.restrict W) ≤
      eLpNorm (fun x => euclideanNorm (w.grad x)) 2 (volume.restrict U) :=
    eLpNorm_mono_measure _ (Measure.restrict_mono hWU le_rfl)
  have htop : eLpNorm (fun x => euclideanNorm (w.grad x)) 2
      (volume.restrict U) ≠ ⊤ := by
    rw [hU2, hcoe]
    exact Lp.eLpNorm_ne_top _
  have htoReal := ENNReal.toReal_mono htop hmono
  unfold vectorLpSizeOn
  have htwo : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by
    simp [ENNReal.ofReal_ofNat]
  rw [htwo]
  refine htoReal.trans (le_of_eq ?_)
  rw [hU2, hcoe, Lp.norm_def]

/-- The index-free interior Hölder constant of the penalized resolvents on a
ball of radius `r` whose double lies inside the part domain.  It depends on
the data only through the gradient budget `G` and the essential bound `M` on
the forcing. -/
def penalizationInteriorHolderConstant (d : ℕ) [NeZero d]
    (alpha r G M : ℝ) : ℝ :=
  smallContrastZerothSchauderConstant d *
    ((2 * r) ^ (1 - alpha - (d : ℝ) / 2) * G +
      (2 * r) ^ (2 - alpha) * (2 * M))

/-- The interior equation for the penalized problem together with the
index-free bounds on its data. -/
theorem exists_interior_equation_penalized_with_gradient [NeZero d]
    (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U) (hV : IsOpen V)
    (hVU : V ⊆ U) {α lam Lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (f : ScalarL2 U) {M : ℝ} (hM : 0 ≤ M)
    (hfM : ∀ᵐ x ∂volumeMeasureOn U, |f x| ≤ M) (n : ℕ)
    {W : Set (Vec d)} (hW : IsOpen W) (hWV : W ⊆ V) :
    ∃ z : H1Function W, ∃ g : Vec d → ℝ,
      z.toFun =ᵐ[volume.restrict W]
        penalizedResolvent a hU.isOpen hV hα hlam hEll n f ∧
      MemScalarLInfOn W g ∧
      scalarLInfSizeOn W g ≤ 2 * M ∧
      vectorLpSizeOn W 2 z.grad ≤ (min α lam)⁻¹ * ‖f‖ ∧
      IsMatrixDivFormWeakSolutionZerothOrderOn a W z g 0 := by
  have hWU : W ⊆ U := hWV.trans hVU
  set q : Vec d → ℝ := penalizationPotential U V n with hqdef
  have hq : IsBoundedNonnegativePotential U q n :=
    penalizationPotential_isBoundedNonnegative hU.isOpen.measurableSet
      hV.measurableSet n
  set u : ZeroTraceSobolev U :=
    penalizedSolution a hU.isOpen hV hα hlam hEll n f with hudef
  have hu : IsPotentialWeakSolution a α q U u f :=
    potentialSolution_isPotentialWeakSolution a hα hlam hEll q hq f
  obtain ⟨w, hwvalue, hwgrad⟩ := ZeroTraceSobolev.exists_h10Function hU u
  have hgvalue : (fun x => interiorScalarSource α q hq f u x) =ᵐ[volume.restrict W]
      fun x => f x - α * ZeroTraceSobolev.toL2 u x -
        q x * ZeroTraceSobolev.toL2 u x :=
    ae_restrict_of_ae_restrict_of_subset hWU
      (interiorScalarSource_coeFn α q hq f u)
  have habs : ∀ᵐ x ∂volumeMeasureOn U,
      |α * ZeroTraceSobolev.toL2 u x| ≤ M :=
    abs_alpha_mul_potentialResolvent_le_ae a hU hα hlam hEll q hq f M hM hfM
  have hqzero : ∀ x ∈ W, q x = 0 := by
    intro x hx
    rw [hqdef, penalizationPotential, Set.indicator_of_notMem]
    exact fun hmem => hmem.2 (hWV hx)
  have hbound : ∀ᵐ x ∂volume.restrict W,
      |interiorScalarSource α q hq f u x| ≤ 2 * M := by
    filter_upwards [hgvalue, ae_restrict_mem hW.measurableSet,
      ae_restrict_of_ae_restrict_of_subset hWU hfM,
      ae_restrict_of_ae_restrict_of_subset hWU habs] with x hg hxW hf hau
    rw [hg, hqzero x hxW, zero_mul, sub_zero]
    have hrewrite : f x - α * ZeroTraceSobolev.toL2 u x =
        f x + -(α * ZeroTraceSobolev.toL2 u x) := by ring
    rw [hrewrite]
    calc |f x + -(α * ZeroTraceSobolev.toL2 u x)|
        ≤ |f x| + |-(α * ZeroTraceSobolev.toL2 u x)| := abs_add_le _ _
      _ = |f x| + |α * ZeroTraceSobolev.toL2 u x| := by rw [abs_neg]
      _ ≤ M + M := add_le_add hf hau
      _ = 2 * M := by ring
  have hmeas : AEStronglyMeasurable
      (fun x => interiorScalarSource α q hq f u x) (volume.restrict W) :=
    (Lp.aestronglyMeasurable (interiorScalarSource α q hq f u)).mono_measure
      (Measure.restrict_mono hWU le_rfl)
  obtain ⟨hmem, hsize⟩ := memScalarLInfOn_of_ae_bound
    (by positivity) hmeas hbound
  refine ⟨w.toH1Function.restrict hW hWU,
    fun x => interiorScalarSource α q hq f u x, ?_, hmem, hsize, ?_, ?_⟩
  · have hres : ZeroTraceSobolev.toL2 u =
        penalizedResolvent a hU.isOpen hV hα hlam hEll n f := rfl
    rw [← hres]
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hWU
      w.toH1Function.coeFn_toScalarL2] with x hx
    rw [← hwvalue]
    exact hx.symm
  · have hgrad := vectorLpSizeOn_grad_le_norm_gradToHilbertVectorL2
      (U := U) hWU w.toH1Function
    rw [hwgrad] at hgrad
    exact hgrad.trans ((ZeroTraceSobolev.norm_gradient_le u).trans
      (norm_penalizedSolution_le a hU.isOpen hV hα hlam hEll f n))
  · exact isMatrixDivFormWeakSolutionZerothOrderOn_restrict hU.isOpen hW hWU
      (isMatrixDivFormWeakSolutionZerothOrderOn_domain_of_isPotentialWeakSolution
        a q hq f hu w hwgrad)

end

end DivergenceFormProcess.Form
