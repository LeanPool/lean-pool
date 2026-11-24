/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.HolomorphicMaps
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.GeometricForms
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ExteriorDerivative
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional

/-!
# Pullback of real differential forms by holomorphic maps

Coefficients use actual chart derivatives. The target chart selected at each
point is immaterial by the tensor transformation law and the chain rule.
Local agreement with any fixed admissible target chart proves smoothness.
-/

@[expose] public section

open Set Filter
open scoped Manifold ContDiff Topology

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

open HolomorphicMaps

variable {k n p : ℕ} {V M : Type*}
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

namespace SmoothRealForm

/-- Smooth dependence of pullback on both the alternating tensor and the
linear map. The finite-dimensional multilinear inclusion has a continuous
linear left inverse, so smoothness can be checked before forgetting alternation. -/
theorem contDiffOn_compContinuousLinearMap
    {U : Set (ComplexModel k)}
    {a : ComplexModel k → (ComplexModel n) [⋀^Fin p]→L[ℝ] ℝ}
    {g : ComplexModel k → ComplexModel k →L[ℝ] ComplexModel n}
    (ha : ContDiffOn ℝ ∞ a U) (hg : ContDiffOn ℝ ∞ g U) :
    ContDiffOn ℝ ∞ (fun z => (a z).compContinuousLinearMap (g z)) U := by
  let A : (ContinuousMultilinearMap ℝ (fun _ : Fin p => ComplexModel k) ℝ) →ₗ[ℝ]
      MultilinearMap (RingHom.id ℝ) (fun _ : Fin p => ComplexModel k) ℝ :=
    { toFun := ContinuousMultilinearMap.toMultilinearMap
      map_add' := ContinuousMultilinearMap.toMultilinearMap_add
      map_smul' := ContinuousMultilinearMap.toMultilinearMap_smul }
  have : FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin p => ComplexModel k) ℝ) :=
    FiniteDimensional.of_injective A ContinuousMultilinearMap.toMultilinearMap_injective
  let L := ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ (𝕜 := ℝ)
    (E := ComplexModel k) (F := ℝ) (ι := Fin p)
  have hL : L.HasLeftInverse :=
    ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional
      ContinuousAlternatingMap.toContinuousMultilinearMap_injective
  have ha' : ContDiffOn ℝ ∞ (fun z => (a z).toContinuousMultilinearMap) U :=
    (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ (𝕜 := ℝ)
      (E := ComplexModel n) (F := ℝ) (ι := Fin p)).contDiff.comp_contDiffOn ha
  let P : ContinuousMultilinearMap ℝ (fun _ : Fin p => ComplexModel k →L[ℝ] ComplexModel n)
      ((ComplexModel n [×p]→L[ℝ] ℝ) →L[ℝ] ComplexModel k [×p]→L[ℝ] ℝ) :=
    ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
      (𝕜 := ℝ) (E := fun _ : Fin p => ComplexModel k)
      (E₁ := fun _ : Fin p => ComplexModel n) (G := ℝ)
  have hP0 : ContDiff ℝ ∞ P := ContinuousMultilinearMap.contDiff
    (𝕜 := ℝ) (F := (ComplexModel n [×p]→L[ℝ] ℝ) →L[ℝ] ComplexModel k [×p]→L[ℝ] ℝ)
    (n := ∞) P
  have hP := hP0.comp_contDiffOn (contDiffOn_pi.mpr (fun _ : Fin p => hg))
  have h := hL.leftInverse.contDiff.comp_contDiffOn (hP.clm_apply ha')
  exact h.congr (fun z _ => (hL.leftInverse_leftInverse ((a z).compContinuousLinearMap (g
    z))).symm)

/-- Pullback in a fixed pair of charts, as a total coefficient function. -/
def chartPullbackCoeff (a : SmoothRealForm n M p) (f : V → M)
    (e : ComplexChart k V) (d : ComplexChart n M) (z : ComplexModel k) :
    (ComplexModel k) [⋀^Fin p]→L[ℝ] ℝ :=
  (a.coeff d (coordinateMap f e d z)).compContinuousLinearMap
    (fderiv ℝ (coordinateMap f e d) z)

/-- The tensor law makes pullback independent of the admissible target chart. -/
theorem chartPullbackCoeff_change_target {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (a : SmoothRealForm n M p) (e : ComplexChart k V) (d d' : ComplexChart n M)
    {z : ComplexModel k} (hz : z ∈ coordinateDomain f e d)
    (hz' : z ∈ coordinateDomain f e d') :
    chartPullbackCoeff a f e d z = chartPullbackCoeff a f e d' z := by
  ext v
  change a.coeff d (coordinateMap f e d z)
      (fun i => fderiv ℝ (coordinateMap f e d) z (v i)) =
    a.coeff d' (coordinateMap f e d' z)
      (fun i => fderiv ℝ (coordinateMap f e d') z (v i))
  rw [coordinateMap_fderiv_change_target hf e d d' hz hz',
    coordinateMap_change_target (d' := d') hz]
  exact a.compatible d d' _ (coordinateMap_mem_transition_source hz hz') _

/-- Fixed-chart pullback is smooth on the domain where both charts are valid. -/
theorem chartPullbackCoeff_contDiffOn {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (a : SmoothRealForm n M p) (e : ComplexChart k V) (d : ComplexChart n M) :
    ContDiffOn ℝ ∞ (chartPullbackCoeff a f e d) (coordinateDomain f e d) := by
  apply contDiffOn_compContinuousLinearMap
  · exact (a.smooth d).comp (coordinateMap_contDiffOn_real hf e d)
      (fun _ hz => coordinateMap_mem_target hz)
  · exact (coordinateMap_contDiffOn_real hf e d).fderiv_of_isOpen
      (coordinateDomain_isOpen hf e d) (by simp)

/-- Coefficients obtained by selecting the preferred target chart pointwise. -/
def pullbackCoeff (a : SmoothRealForm n M p) (f : V → M)
    (e : ComplexChart k V) (z : ComplexModel k) :
    (ComplexModel k) [⋀^Fin p]→L[ℝ] ℝ :=
  chartPullbackCoeff a f e (complexChartAt (f (e.val.symm z))) z

/-- The chosen coefficients agree with every fixed target chart on its domain. -/
theorem pullbackCoeff_eq_chartPullbackCoeff {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (a : SmoothRealForm n M p) (e : ComplexChart k V) (d : ComplexChart n M)
    {z : ComplexModel k} (hz : z ∈ coordinateDomain f e d) :
    pullbackCoeff a f e z = chartPullbackCoeff a f e d z :=
  chartPullbackCoeff_change_target hf a e _ d
    ⟨hz.1, mem_complexChartAt_source _⟩ hz

/-- Fixed-chart agreement holds on a neighborhood, not merely at the basepoint. -/
theorem pullbackCoeff_eventuallyEq_chartPullbackCoeff {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (a : SmoothRealForm n M p) (e : ComplexChart k V) (d : ComplexChart n M)
    {z : ComplexModel k} (hz : z ∈ coordinateDomain f e d) :
    pullbackCoeff a f e =ᶠ[𝓝 z] chartPullbackCoeff a f e d := by
  filter_upwards [(coordinateDomain_isOpen hf e d).mem_nhds hz] with y hy
  exact pullbackCoeff_eq_chartPullbackCoeff hf a e d hy

/-- The pointwise chart selection defines smooth coefficients on each source chart. -/
theorem pullbackCoeff_contDiffOn {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (a : SmoothRealForm n M p) (e : ComplexChart k V) :
    ContDiffOn ℝ ∞ (pullbackCoeff a f e) e.val.target := by
  intro z hz
  let d := complexChartAt (n := n) (f (e.val.symm z))
  have hzd : z ∈ coordinateDomain f e d := ⟨hz, mem_complexChartAt_source _⟩
  exact ((chartPullbackCoeff_contDiffOn hf a e d).contDiffAt
    ((coordinateDomain_isOpen hf e d).mem_nhds hzd)).congr_of_eventuallyEq
      (pullbackCoeff_eventuallyEq_chartPullbackCoeff hf a e d hzd) |>.contDiffWithinAt

/-- Source-coordinate changes satisfy the required tensor transformation law. -/
theorem pullbackCoeff_compatible {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (a : SmoothRealForm n M p) (e e' : ComplexChart k V)
    {z : ComplexModel k} (hz : z ∈ (chartTransition e e').source)
    (v : Fin p → ComplexModel k) :
    pullbackCoeff a f e z v = pullbackCoeff a f e' (chartTransition e e' z)
      (fun i => chartTransitionDerivative e e' z (v i)) := by
  let d := complexChartAt (n := n) (f (e.val.symm z))
  have hzd : z ∈ coordinateDomain f e d := ⟨hz.1, mem_complexChartAt_source _⟩
  rw [pullbackCoeff_eq_chartPullbackCoeff hf a e d hzd,
    pullbackCoeff_eq_chartPullbackCoeff hf a e' d (coordinateDomain_change_source hz hzd)]
  simp only [chartPullbackCoeff, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  rw [coordinateMap_fderiv_change_source hf e e' d hz hzd,
    coordinateMap_change_source (d := d) hz]
  rfl

/-- Pullback of a smooth real differential form along an actual holomorphic map. -/
def pullback {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (a : SmoothRealForm n M p) : SmoothRealForm k V p where
  coeff := pullbackCoeff a f
  smooth := pullbackCoeff_contDiffOn hf a
  compatible := fun e e' _ hz v => pullbackCoeff_compatible hf a e e' hz v

/-- The geometric coordinate formula for the global pullback. -/
theorem pullback_coeff {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (a : SmoothRealForm n M p) (e : ComplexChart k V) (d : ComplexChart n M)
    {z : ComplexModel k} (hz : z ∈ coordinateDomain f e d) :
    (pullback hf a).coeff e z =
      (a.coeff d (coordinateMap f e d z)).compContinuousLinearMap
        (fderiv ℝ (coordinateMap f e d) z) :=
  pullbackCoeff_eq_chartPullbackCoeff hf a e d hz

/-- Exterior differentiation of global pullback is given by the pulled-back
exterior derivative in every admissible coordinate pair. -/
theorem extDeriv_pullback_coeff {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (a : SmoothRealForm n M p) (e : ComplexChart k V) (d : ComplexChart n M)
    {z : ComplexModel k} (hz : z ∈ coordinateDomain f e d) :
    extDeriv ((pullback hf a).coeff e) z =
      (extDeriv (a.coeff d) (coordinateMap f e d z)).compContinuousLinearMap
        (fderiv ℝ (coordinateMap f e d) z) := by
  change extDeriv (pullbackCoeff a f e) z = _
  rw [(pullbackCoeff_eventuallyEq_chartPullbackCoeff hf a e d hz).extDeriv_eq]
  exact extDeriv_pullback
    ((a.smooth d).contDiffAt (d.val.open_target.mem_nhds
      (coordinateMap_mem_target hz)) |>.differentiableAt (by simp))
    (coordinateMap_contDiffAt_real hf e d hz)
    (by simp)

/-- Pullback preserves closedness. -/
theorem IsClosed.pullback {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    {a : SmoothRealForm n M p} (ha : a.IsClosed) : (pullback hf a).IsClosed := by
  intro e z hz
  let d := complexChartAt (n := n) (f (e.val.symm z))
  have hzd : z ∈ coordinateDomain f e d := ⟨hz, mem_complexChartAt_source _⟩
  rw [extDeriv_pullback_coeff hf a e d hzd, ha d _ (coordinateMap_mem_target hzd)]
  ext v
  rfl

/-- Pullback respects equality on chart targets. -/
theorem GeometricallyEq.pullback {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    {a b : SmoothRealForm n M p} (hab : a.GeometricallyEq b) :
    (pullback hf a).GeometricallyEq (pullback hf b) := by
  intro e z hz
  let d := complexChartAt (n := n) (f (e.val.symm z))
  have hzd : z ∈ coordinateDomain f e d := ⟨hz, mem_complexChartAt_source _⟩
  rw [pullback_coeff hf a e d hzd, pullback_coeff hf b e d hzd,
    hab d (coordinateMap_mem_target hzd)]

/-- Holomorphic pullback preserves real type `(1,1)`. -/
theorem IsTypeOneOne.pullback {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    {a : SmoothRealForm n M 2} (ha : a.IsTypeOneOne) :
    (pullback hf a).IsTypeOneOne := by
  intro e z hz u v
  let d := complexChartAt (n := n) (f (e.val.symm z))
  have hzd : z ∈ coordinateDomain f e d := ⟨hz, mem_complexChartAt_source _⟩
  rw [pullback_coeff hf a e d hzd]
  let L := fderiv ℝ (coordinateMap f e d) z
  have hvec (u v : ComplexModel k) : L ∘ ![u, v] = ![L u, L v] := by
    funext i
    fin_cases i <;> rfl
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  change a.coeff d (coordinateMap f e d z) (L ∘ ![Complex.I • u, Complex.I • v]) =
    a.coeff d (coordinateMap f e d z) (L ∘ ![u, v])
  rw [hvec, hvec,
    coordinateMap_fderiv_map_smul_complex hf e d hzd Complex.I u,
    coordinateMap_fderiv_map_smul_complex hf e d hzd Complex.I v]
  exact ha d _ (coordinateMap_mem_target hzd) (L u) (L v)

/-- Holomorphic pullback preserves semipositivity, even for maps whose
differential is not injective. -/
theorem IsSemipositive.pullback {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    {a : SmoothRealForm n M 2} (ha : a.IsSemipositive) :
    (pullback hf a).IsSemipositive := by
  intro e z hz v
  let d := complexChartAt (n := n) (f (e.val.symm z))
  have hzd : z ∈ coordinateDomain f e d := ⟨hz, mem_complexChartAt_source _⟩
  rw [pullback_coeff hf a e d hzd]
  let L := fderiv ℝ (coordinateMap f e d) z
  have hvec : L ∘ ![v, Complex.I • v] = ![L v, Complex.I • L v] := by
    funext i
    fin_cases i
    · rfl
    · exact coordinateMap_fderiv_map_smul_complex hf e d hzd Complex.I v
  change 0 ≤ a.coeff d (coordinateMap f e d z) (L ∘ ![v, Complex.I • v])
  rw [hvec]
  exact ha d _ (coordinateMap_mem_target hzd) (L v)

/-- Exterior differentiation commutes geometrically with global pullback. -/
theorem exteriorDerivative_pullback {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (a : SmoothRealForm n M p) :
    (pullback hf a).exteriorDerivative.GeometricallyEq (pullback hf a.exteriorDerivative) := by
  intro e z hz
  let d := complexChartAt (n := n) (f (e.val.symm z))
  have hzd : z ∈ coordinateDomain f e d := ⟨hz, mem_complexChartAt_source _⟩
  rw [exteriorDerivative_coeff, extDeriv_pullback_coeff hf a e d hzd,
    pullback_coeff hf a.exteriorDerivative e d hzd, exteriorDerivative_coeff]

/-- An injective holomorphic differential preserves strict positivity and
therefore pulls a Hermitian form back to a Hermitian form. -/
theorem IsHermitian.pullback_of_injective {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hdf : ∀ (e : ComplexChart k V) (d : ComplexChart n M) (z : ComplexModel k),
      z ∈ coordinateDomain f e d → Function.Injective (fderiv ℝ (coordinateMap f e d) z))
    {a : SmoothRealForm n M 2} (ha : a.IsHermitian) :
    (pullback hf a).IsHermitian := by
  intro e z hz
  have htype : a.IsTypeOneOne := fun d w hw => (ha d w hw).1
  refine ⟨htype.pullback hf e z hz, ?_⟩
  intro v hv
  let d := complexChartAt (n := n) (f (e.val.symm z))
  have hzd : z ∈ coordinateDomain f e d := ⟨hz, mem_complexChartAt_source _⟩
  rw [pullback_coeff hf a e d hzd]
  let L := fderiv ℝ (coordinateMap f e d) z
  have hLv : L v ≠ 0 := by
    intro h
    exact hv (hdf e d z hzd (h.trans L.map_zero.symm))
  have hvec : L ∘ ![v, Complex.I • v] = ![L v, Complex.I • L v] := by
    funext i
    fin_cases i
    · rfl
    · exact coordinateMap_fderiv_map_smul_complex hf e d hzd Complex.I v
  change 0 < a.coeff d (coordinateMap f e d z) (L ∘ ![v, Complex.I • v])
  rw [hvec]
  exact (ha d _ (coordinateMap_mem_target hzd)).2 (L v) hLv

/-- A holomorphic immersion pulls a Kähler form back to a Kähler form. -/
theorem IsKahler.pullback_of_injective {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hdf : ∀ (e : ComplexChart k V) (d : ComplexChart n M) (z : ComplexModel k),
      z ∈ coordinateDomain f e d → Function.Injective (fderiv ℝ (coordinateMap f e d) z))
    {a : SmoothRealForm n M 2} (ha : a.IsKahler) : (pullback hf a).IsKahler :=
  ⟨IsHermitian.pullback_of_injective hf hdf ha.1, IsClosed.pullback hf ha.2⟩

end SmoothRealForm

end

end SGPT.Foundations.Analysis.FirstPass
