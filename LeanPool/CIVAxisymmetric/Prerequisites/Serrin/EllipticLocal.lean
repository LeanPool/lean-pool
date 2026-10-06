/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.AnnularKernelBound
public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.SingularIBP
public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.EllipticKernelBounds
public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.MultiIndexCases
public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.LevelSums
public import LeanPool.CIVAxisymmetric.Statements.IsClassicalSolutionOn
public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Equation
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Local elliptic bounds on a time slice

For a divergence-free velocity `u` smooth near the closed Euclidean ball `|y - x| ≤ ρ` of one time
slice, the velocity gradient and Hessian at the centre are controlled by the vorticity gradient
and Hessian on the ball and by the velocity itself:
`∑ᵢⱼ |∂ⱼuᵢ(x)| ≤ C (ρ Λ₁ + M / ρ)` (`EL1_local`) and
`∑ᵢⱼₗ |∂ₗ∂ⱼuᵢ(x)| ≤ C (ρ Λ₂ + M / ρ²)` (`EL2_local`), with an absolute constant `C`.

The proof applies the Newtonian representation `∂ₗv(x) = -∫ ∂ₗN(x - y) Δv(y) dy` to
`v = χ uᵢ` (respectively `v = χ ∂ⱼuᵢ`), where `χ` is the ball cutoff, after replacing `u` by a
globally smooth field that agrees with it near the ball. The Leibniz rule splits `Δv` into
`χ Δh`, which is bounded through `Δuᵢ = ∑ₖ ∂ₖ(∂ₖuᵢ - ∂ᵢuₖ)` (divergence free) and the signed
vorticity form of the antisymmetric gradient, against `∫_{B_ρ} |∂ₗN| ≤ Cρ`; and the cutoff
terms `∂ₖχ ∂ₖh` and `∂ₖ∂ₖχ h`, which are bounded by the annular kernel bound using only
`|u| ≤ M`. The level bounds `EV1_velocity_gradient` and `EV2_velocity_hessian` apply these at the
fixed radius `min (a' - a, b - b', 1) / 2` on an annulus times a backward time interval. These are
the elliptic steps of the interior estimates in the proof of `lem:aniso:annulus`.
-/

public section

open MeasureTheory Set Filter Topology
open CKN.Foundation.Parabolic CKN CKN.Foundation.Heat

noncomputable section
namespace CIV



/-! ## Part 1: a smooth extension of one time slice -/

private theorem isCompact_closedEuclideanBall (x : Vec3) {ρ : ℝ} (hρ : 0 < ρ) :
    IsCompact {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} := by
  rw [← closure_vec3Ball hρ]
  exact isCompact_closure_vec3Ball hρ

private theorem continuous_euclideanDist (x : Vec3) :
    Continuous (fun y : Vec3 => vec3EuclideanNorm (y - x)) :=
  continuous_vec3EuclideanNorm.comp (continuous_id.sub continuous_const)

private theorem exists_smooth_slice_extension {u : ParabolicPoint → Vec3}
    {O : Set ParabolicPoint} {x : Vec3} {t ρ : ℝ} (hO : IsOpen (X := Vec3 × ℝ) O) (hρ : 0 < ρ)
    (hball : ∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ → (y, t) ∈ O)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) O) :
    ∃ G : Vec3 → Vec3, ContDiff ℝ (⊤ : ℕ∞) G ∧ ∃ V : Set Vec3, IsOpen V ∧
      {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ⊆ V ∧
      ∀ y ∈ V, (y, t) ∈ O ∧ G y = u (y, t) := by
  set Ot : Set Vec3 := {y | ((y, t) : Vec3 × ℝ) ∈ O} with hOt
  have hslice : Continuous (fun y : Vec3 => ((y, t) : Vec3 × ℝ)) := by fun_prop
  have hOtopen : IsOpen Ot := hO.preimage hslice
  obtain ⟨L₁, hL₁c, hKL₁, hL₁O⟩ :=
    exists_compact_between (isCompact_closedEuclideanBall x hρ) hOtopen hball
  obtain ⟨L₂, hL₂c, hL₁L₂, hL₂O⟩ := exists_compact_between hL₁c hOtopen hL₁O
  obtain ⟨ψ, hψ, -, hψsupp, hψone⟩ : ∃ f : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧
      range f ⊆ Icc 0 1 ∧ Function.support f = interior L₂ ∧ (∀ y, y ∈ L₁ ↔ f y = 1) :=
    exists_contDiff_support_eq_eq_one_iff isOpen_interior hL₁c.isClosed hL₁L₂
  have hts : tsupport ψ ⊆ Ot := by
    unfold tsupport
    rw [hψsupp]
    exact (closure_minimal interior_subset hL₂c.isClosed).trans hL₂O
  have huOt : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Vec3 => u (y, t)) Ot :=
    hu.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun y hy => hy)
  refine ⟨fun y => ψ y • u (y, t), ?_, interior L₁, isOpen_interior, hKL₁,
    fun y hy => ⟨hL₁O (interior_subset hy), ?_⟩⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ Ot
    · exact hψ.contDiffAt.smul (huOt.contDiffAt (hOtopen.mem_nhds hy))
    · have hz : ψ =ᶠ[𝓝 y] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun h => hy (hts h))
      refine (contDiffAt_const (c := (0 : Vec3))).congr_of_eventuallyEq ?_
      filter_upwards [hz] with y' hy'
      simp [hy']
  · have h1 : ψ y = 1 := (hψone y).mp (interior_subset hy)
    simp [h1]

/-- Equality of two functions on an open subset of one time slice passes to their spatial
partials there. -/
private theorem spatialPartial_eq_of_eqOn_slice {F H : ParabolicPoint → ℝ} {V : Set Vec3}
    (hV : IsOpen V) {t : ℝ} (hFH : ∀ y ∈ V, F (y, t) = H (y, t)) (j : Fin 3) :
    ∀ y ∈ V, spatialPartial F j (y, t) = spatialPartial H j (y, t) := by
  intro y hy
  have hev : (fun y' : Vec3 => F (y', t)) =ᶠ[𝓝 y] fun y' => H (y', t) :=
    Filter.eventuallyEq_of_mem (hV.mem_nhds hy) (fun y' hy' => hFH y' hy')
  show (fderiv ℝ (fun y' : Vec3 => F (y', t)) y) (basisVec j) =
    (fderiv ℝ (fun y' : Vec3 => H (y', t)) y) (basisVec j)
  rw [hev.fderiv_eq]


/-! ## Part 2: calculus of `spatialDeriv` for smooth functions -/

private theorem differentiable_of_smooth {f : Vec3 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Differentiable ℝ f :=
  hf.differentiable (by simp)

private theorem spatialDeriv_fun_sub {f g : Vec3 → ℝ} {y : Vec3} (hf : DifferentiableAt ℝ f y)
    (hg : DifferentiableAt ℝ g y) (i : Fin 3) :
    spatialDeriv (fun y' => f y' - g y') i y = spatialDeriv f i y - spatialDeriv g i y := by
  simp only [spatialDeriv, fderiv_fun_sub hf hg, sub_apply]

private theorem spatialDeriv_fun_sum {f : Fin 3 → Vec3 → ℝ} {y : Vec3}
    (hf : ∀ k, DifferentiableAt ℝ (f k) y) (i : Fin 3) :
    spatialDeriv (fun y' => ∑ k, f k y') i y = ∑ k, spatialDeriv (f k) i y := by
  simp only [spatialDeriv]
  rw [fderiv_fun_sum (fun k _ => hf k)]
  simp

private theorem spatialDeriv_const_mul' {f : Vec3 → ℝ} {y : Vec3} (hf : DifferentiableAt ℝ f y)
    (c : ℝ) (i : Fin 3) :
    spatialDeriv (fun y' => c * f y') i y = c * spatialDeriv f i y := by
  simp only [spatialDeriv, fderiv_const_mul hf c, smul_apply, smul_eq_mul]

private theorem spatialDeriv_eq_zero_of_eventuallyEq_zero {f : Vec3 → ℝ} {y : Vec3}
    (hf : f =ᶠ[𝓝 y] fun _ => (0 : ℝ)) (i : Fin 3) : spatialDeriv f i y = 0 := by
  simp [spatialDeriv, hf.fderiv_eq]

/-- A function vanishing outside a closed Euclidean ball has spatial derivatives vanishing
outside it. -/
private theorem spatialDeriv_eq_zero_outside {F : Vec3 → ℝ} {x : Vec3} {ρ : ℝ}
    (hF : ∀ y, ρ < vec3EuclideanNorm (y - x) → F y = 0) (k : Fin 3) :
    ∀ y, ρ < vec3EuclideanNorm (y - x) → spatialDeriv F k y = 0 := by
  intro y hy
  refine spatialDeriv_eq_zero_of_eventuallyEq_zero ?_ k
  exact Filter.eventuallyEq_of_mem
    ((isOpen_lt continuous_const (continuous_euclideanDist x)).mem_nhds hy)
    (fun y' hy' => hF y' hy')

/-- The Laplacian commutes with a spatial derivative of a smooth function. -/
private theorem spatialLaplacian_spatialDeriv_comm {g : Vec3 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (j : Fin 3) (y : Vec3) :
    spatialLaplacian (spatialDeriv g j) y = spatialDeriv (spatialLaplacian g) j y := by
  have hswap : ∀ k : Fin 3, spatialDeriv (spatialDeriv g j) k = spatialDeriv (spatialDeriv g k) j :=
    fun k => funext fun y' => mixedSecond_swap hg k j y'
  have hdiff : ∀ k : Fin 3, DifferentiableAt ℝ (spatialDeriv (spatialDeriv g k) k) y := fun k =>
    differentiable_of_smooth (contDiff_spatialDeriv_smooth (contDiff_spatialDeriv_smooth hg k) k) y
  show ∑ k : Fin 3, spatialDeriv (spatialDeriv (spatialDeriv g j) k) k y =
    spatialDeriv (fun y' => ∑ k : Fin 3, spatialDeriv (spatialDeriv g k) k y') j y
  rw [spatialDeriv_fun_sum hdiff j]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [hswap k]
  exact mixedSecond_swap (contDiff_spatialDeriv_smooth hg k) k j y

/-! ## Part 3: the Newtonian representation split along the cutoff -/

/-- Kernel integrability against a continuous function supported in the closed ball. -/
private theorem integrable_newtonKernelGrad_mul {x : Vec3} {ρ : ℝ} (hρ : 0 < ρ) {l : Fin 3}
    (hK : IntegrableOn (fun y => spatialDeriv newtonianKernel l (x - y))
      {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ})
    {F : Vec3 → ℝ} (hF : Continuous F) (hout : ∀ y, ρ < vec3EuclideanNorm (y - x) → F y = 0) :
    Integrable (fun y => spatialDeriv newtonianKernel l (x - y) * F y) := by
  refine (hK.mul_continuousOn hF.continuousOn
    (isCompact_closedEuclideanBall x hρ)).integrable_of_forall_notMem_eq_zero ?_
  intro y hy
  rw [hout y (lt_of_not_ge hy), mul_zero]

/-- The kernel term against a function bounded by `A` on the ball is at most `Cb ρ A`. -/
private theorem abs_integral_newtonKernelGrad_mul_le {x : Vec3} {ρ : ℝ} {l : Fin 3} {Cb A : ℝ}
    (hρ : 0 < ρ) (hA : 0 ≤ A)
    (hK : IntegrableOn (fun y => spatialDeriv newtonianKernel l (x - y))
      {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ})
    (hKb : ∫ y in {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ},
      |spatialDeriv newtonianKernel l (x - y)| ≤ Cb * ρ)
    {F : Vec3 → ℝ} (hout : ∀ y, ρ < vec3EuclideanNorm (y - x) → F y = 0)
    (hFA : ∀ y, vec3EuclideanNorm (y - x) ≤ ρ → |F y| ≤ A) :
    |∫ y, spatialDeriv newtonianKernel l (x - y) * F y| ≤ Cb * ρ * A := by
  have hB : MeasurableSet {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} :=
    (isCompact_closedEuclideanBall x hρ).isClosed.measurableSet
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ})
    (fun y hy => by rw [hout y (lt_of_not_ge hy), mul_zero])]
  have h1 : ‖∫ y in {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ},
      spatialDeriv newtonianKernel l (x - y) * F y‖ ≤
      ∫ y in {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ},
        |spatialDeriv newtonianKernel l (x - y)| * A := by
    refine norm_integral_le_of_norm_le (hK.abs.mul_const A) ?_
    refine ae_restrict_of_forall_mem hB (fun y hy => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hFA y hy) (abs_nonneg _)
  rw [Real.norm_eq_abs, integral_mul_const] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right hKb hA)

/-- For a smooth `h`, the Newtonian representation of `∂ₗ(χ h)` at the centre `x` of the cutoff
`χ = serrinBallCutoff x ρ`, with `Δ(χ h)` expanded by the Leibniz rule. -/
private theorem spatialDeriv_eq_neg_integral_split {h : Vec3 → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) {x : Vec3} {ρ : ℝ} (hρ : 0 < ρ) (l : Fin 3)
    (hK : IntegrableOn (fun y => spatialDeriv newtonianKernel l (x - y))
      {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ}) :
    spatialDeriv h l x =
      -((∫ y, spatialDeriv newtonianKernel l (x - y) *
          (serrinBallCutoff x ρ y * spatialLaplacian h y)) +
        ((2 * ∑ k, ∫ y, spatialDeriv newtonianKernel l (x - y) *
            (spatialDeriv (serrinBallCutoff x ρ) k y * spatialDeriv h k y)) +
          ∑ k, ∫ y, spatialDeriv newtonianKernel l (x - y) *
            (spatialDeriv (spatialDeriv (serrinBallCutoff x ρ) k) k y * h y))) := by
  set χ : Vec3 → ℝ := serrinBallCutoff x ρ with hχdef
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := (serrinBallCutoff_support x hρ x).2.2
  have hχout : ∀ y, ρ < vec3EuclideanNorm (y - x) → χ y = 0 := fun y hy =>
    (serrinBallCutoff_support x hρ y).2.1 hy.le
  have hχc : HasCompactSupport χ := HasCompactSupport.intro
    (isCompact_closedEuclideanBall x hρ) (fun y hy => hχout y (lt_of_not_ge hy))
  have hv : ContDiff ℝ (⊤ : ℕ∞) (fun y => χ y * h y) := hχ.mul hh
  have hvc : HasCompactSupport (fun y => χ y * h y) := hχc.mul_right
  have hloc : (fun y => χ y * h y) =ᶠ[𝓝 x] h := by
    have hopen : IsOpen {y : Vec3 | vec3EuclideanNorm (y - x) < ρ / 2} :=
      isOpen_lt (continuous_euclideanDist x) continuous_const
    have hx : x ∈ {y : Vec3 | vec3EuclideanNorm (y - x) < ρ / 2} := by
      show vec3EuclideanNorm (x - x) < ρ / 2
      simp only [sub_self, vec3EuclideanNorm, Pi.zero_apply]
      norm_num
      exact hρ
    refine Filter.eventuallyEq_of_mem (hopen.mem_nhds hx) (fun y hy => ?_)
    show χ y * h y = h y
    rw [hχdef, (serrinBallCutoff_support x hρ y).1 (le_of_lt hy), one_mul]
  have hcentre : spatialDeriv (fun y => χ y * h y) l x = spatialDeriv h l x := by
    simp only [spatialDeriv, hloc.fderiv_eq]
  have hχ1 : ∀ k : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv χ k) := fun k =>
    contDiff_spatialDeriv_smooth hχ k
  have hχ1out : ∀ k : Fin 3, ∀ y, ρ < vec3EuclideanNorm (y - x) → spatialDeriv χ k y = 0 :=
    fun k => spatialDeriv_eq_zero_outside hχout k
  have hχ2out : ∀ k : Fin 3, ∀ y, ρ < vec3EuclideanNorm (y - x) →
      spatialDeriv (spatialDeriv χ k) k y = 0 :=
    fun k => spatialDeriv_eq_zero_outside (hχ1out k) k
  have hI1 : Integrable (fun y => spatialDeriv newtonianKernel l (x - y) *
      (χ y * spatialLaplacian h y)) :=
    integrable_newtonKernelGrad_mul hρ hK (hχ.continuous.mul (contDiff_spatialLaplacian_smooth
      hh).continuous)
      (fun y hy => by rw [hχout y hy, zero_mul])
  have hI2 : ∀ k : Fin 3, Integrable (fun y => spatialDeriv newtonianKernel l (x - y) *
      (spatialDeriv χ k y * spatialDeriv h k y)) := fun k =>
    integrable_newtonKernelGrad_mul hρ hK ((hχ1 k).continuous.mul
      (contDiff_spatialDeriv_smooth hh k).continuous)
      (fun y hy => by rw [hχ1out k y hy, zero_mul])
  have hI3 : ∀ k : Fin 3, Integrable (fun y => spatialDeriv newtonianKernel l (x - y) *
      (spatialDeriv (spatialDeriv χ k) k y * h y)) := fun k =>
    integrable_newtonKernelGrad_mul hρ hK
      ((contDiff_spatialDeriv_smooth (hχ1 k) k).continuous.mul hh.continuous)
      (fun y hy => by rw [hχ2out k y hy, zero_mul])
  rw [← hcentre, ELa_gradient_newton_representation hv hvc x l, spatialLaplacian_mul_smooth hχ hh]
  congr 1
  have hpt : (fun y => spatialDeriv newtonianKernel l (x - y) *
      (χ y * spatialLaplacian h y + 2 * spatialGradDot χ h y + h y * spatialLaplacian χ y)) =
      fun y => spatialDeriv newtonianKernel l (x - y) * (χ y * spatialLaplacian h y) +
        ((2 * ∑ k, spatialDeriv newtonianKernel l (x - y) *
            (spatialDeriv χ k y * spatialDeriv h k y)) +
          ∑ k, spatialDeriv newtonianKernel l (x - y) *
            (spatialDeriv (spatialDeriv χ k) k y * h y)) := by
    funext y
    simp only [spatialGradDot, spatialLaplacian, Fin.sum_univ_three]
    ring
  have hS2 : Integrable (fun y => 2 * ∑ k, spatialDeriv newtonianKernel l (x - y) *
      (spatialDeriv χ k y * spatialDeriv h k y)) :=
    (integrable_finsetSum _ (fun k _ => hI2 k)).const_mul 2
  have hS3 : Integrable (fun y => ∑ k, spatialDeriv newtonianKernel l (x - y) *
      (spatialDeriv (spatialDeriv χ k) k y * h y)) :=
    integrable_finsetSum _ (fun k _ => hI3 k)
  have hS23 : Integrable (fun y => (2 * ∑ k, spatialDeriv newtonianKernel l (x - y) *
      (spatialDeriv χ k y * spatialDeriv h k y)) + ∑ k, spatialDeriv newtonianKernel l (x - y) *
      (spatialDeriv (spatialDeriv χ k) k y * h y)) := hS2.add hS3
  rw [hpt, integral_add hI1 hS23, integral_add hS2 hS3, integral_const_mul,
    integral_finsetSum _ (fun k _ => hI2 k), integral_finsetSum _ (fun k _ => hI3 k)]

/-- The split representation bounds `|∂ₗh(x)|` by the ball term and the six cutoff terms. -/
private theorem abs_spatialDeriv_le_of_split {h : Vec3 → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {x : Vec3} {ρ Cb A E : ℝ} (hρ : 0 < ρ) (hA : 0 ≤ A) (l : Fin 3)
    (hK : IntegrableOn (fun y => spatialDeriv newtonianKernel l (x - y))
      {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ})
    (hKb : ∫ y in {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ},
      |spatialDeriv newtonianKernel l (x - y)| ≤ Cb * ρ)
    (hΔ : ∀ y, vec3EuclideanNorm (y - x) ≤ ρ → |spatialLaplacian h y| ≤ A)
    (h2 : ∀ k : Fin 3, |∫ y, spatialDeriv newtonianKernel l (x - y) *
      spatialDeriv (serrinBallCutoff x ρ) k y * spatialDeriv h k y| ≤ E)
    (h3 : ∀ k : Fin 3, |∫ y, spatialDeriv newtonianKernel l (x - y) *
      spatialDeriv (spatialDeriv (serrinBallCutoff x ρ) k) k y * h y| ≤ E) :
    |spatialDeriv h l x| ≤ Cb * ρ * A + 9 * E := by
  have hmain : |∫ y, spatialDeriv newtonianKernel l (x - y) *
      (serrinBallCutoff x ρ y * spatialLaplacian h y)| ≤ Cb * ρ * A := by
    refine abs_integral_newtonKernelGrad_mul_le hρ hA hK hKb
      (fun y hy => by rw [(serrinBallCutoff_support x hρ y).2.1 hy.le, zero_mul]) ?_
    intro y hy
    have hχ1 : |serrinBallCutoff x ρ y| ≤ 1 := by
      obtain ⟨h0, h1⟩ := serrinBallCutoff_mem_Icc x ρ y
      rw [abs_of_nonneg h0]
      exact h1
    rw [abs_mul]
    calc |serrinBallCutoff x ρ y| * |spatialLaplacian h y| ≤ 1 * A :=
          mul_le_mul hχ1 (hΔ y hy) (abs_nonneg _) zero_le_one
      _ = A := one_mul A
  have h2' : ∀ k : Fin 3, |∫ y, spatialDeriv newtonianKernel l (x - y) *
      (spatialDeriv (serrinBallCutoff x ρ) k y * spatialDeriv h k y)| ≤ E := fun k => by
    simpa only [mul_assoc] using h2 k
  have h3' : ∀ k : Fin 3, |∫ y, spatialDeriv newtonianKernel l (x - y) *
      (spatialDeriv (spatialDeriv (serrinBallCutoff x ρ) k) k y * h y)| ≤ E := fun k => by
    simpa only [mul_assoc] using h3 k
  rw [spatialDeriv_eq_neg_integral_split hh hρ l hK, abs_neg]
  simp only [Fin.sum_univ_three]
  have hm := abs_le.mp hmain
  have a0 := abs_le.mp (h2' 0)
  have a1 := abs_le.mp (h2' 1)
  have a2 := abs_le.mp (h2' 2)
  have b0 := abs_le.mp (h3' 0)
  have b1 := abs_le.mp (h3' 1)
  have b2 := abs_le.mp (h3' 2)
  refine abs_le.mpr ⟨?_, ?_⟩
  · linarith only [hm.1, a0.1, a1.1, a2.1, b0.1, b1.1, b2.1]
  · linarith only [hm.2, a0.2, a1.2, a2.2, b0.2, b1.2, b2.2]

/-! ## Part 4: the annular cutoff terms, through the annular kernel bound -/

private theorem multiPartialVec3_zero' (k : Vec3 → ℝ) : multiPartialVec3 k 0 = k := by
  simp [multiPartialVec3]

private theorem multiPartialVec3_single_one (k : Vec3 → ℝ) (a : Fin 3) :
    multiPartialVec3 k (Pi.single a 1) = spatialDeriv k a := by
  fin_cases a <;> simp [multiPartialVec3]

private theorem multiPartialVec3_single_two (k : Vec3 → ℝ) (a : Fin 3) :
    multiPartialVec3 k (Pi.single a 2) = spatialDeriv (spatialDeriv k a) a := by
  fin_cases a <;> simp [multiPartialVec3]

private theorem multiPartialVec3_pair {k : Vec3 → ℝ} (hk : ContDiff ℝ (⊤ : ℕ∞) k) (a b : Fin 3) :
    multiPartialVec3 k (Pi.single a 1 + Pi.single b 1) = spatialDeriv (spatialDeriv k b) a := by
  fin_cases a <;> fin_cases b <;> simp [multiPartialVec3] <;>
    exact funext fun y => mixedSecond_swap hk _ _ y

private theorem order_single_one (a : Fin 3) :
    (Pi.single a 1 : Fin 3 → ℕ) 0 + (Pi.single a 1 : Fin 3 → ℕ) 1 +
      (Pi.single a 1 : Fin 3 → ℕ) 2 = 1 := by
  fin_cases a <;> rfl

private theorem order_single_two (a : Fin 3) :
    (Pi.single a 2 : Fin 3 → ℕ) 0 + (Pi.single a 2 : Fin 3 → ℕ) 1 +
      (Pi.single a 2 : Fin 3 → ℕ) 2 = 2 := by
  fin_cases a <;> rfl

private theorem order_pair (a b : Fin 3) :
    (Pi.single a 1 + Pi.single b 1 : Fin 3 → ℕ) 0 + (Pi.single a 1 + Pi.single b 1 : Fin 3 → ℕ) 1 +
      (Pi.single a 1 + Pi.single b 1 : Fin 3 → ℕ) 2 = 2 := by
  fin_cases a <;> fin_cases b <;> rfl

private theorem single_ne_zero' (a : Fin 3) (n : ℕ) (hn : n ≠ 0) :
    (Pi.single a n : Fin 3 → ℕ) ≠ 0 := by
  intro h
  have := congrFun h a
  simp only [Pi.single_eq_same, Pi.zero_apply] at this
  exact hn this

/-- The annular kernel bound in `Vec3` form, for a smooth time-independent function. -/
private theorem annular_kernel_bound_vec3 : ∃ C : ℝ, 0 < C ∧ ∀ (k : Vec3 → ℝ) (x : Vec3)
    (ρ M : ℝ) (γ₁ γ₂ : Fin 3 → ℕ) (l : Fin 3), ContDiff ℝ (⊤ : ℕ∞) k → 0 < ρ → ρ ≤ 1 →
    (∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ → |k y| ≤ M) →
    γ₁ ≠ 0 → γ₁ 0 + γ₁ 1 + γ₁ 2 + (γ₂ 0 + γ₂ 1 + γ₂ 2) ≤ 3 →
    |∫ y : Vec3, spatialDeriv newtonianKernel l (x - y) *
        multiPartialVec3 (serrinBallCutoff x ρ) γ₁ y * multiPartialVec3 k γ₂ y| ≤
      C * M * ρ / ρ ^ (γ₁ 0 + γ₁ 1 + γ₁ 2 + (γ₂ 0 + γ₂ 1 + γ₂ 2)) := by
  obtain ⟨C, hC, hELc⟩ := ELc_annular_kernel_ibp
  refine ⟨C, hC, fun k x ρ M γ₁ γ₂ l hk hρ hρ1 hM hγ hord => ?_⟩
  have hkO : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => k z.1) univ :=
    (hk.comp contDiff_fst).contDiffOn
  have h := hELc (fun z => k z.1) univ x 0 ρ M γ₁ γ₂ l isOpen_univ hρ hρ1
    (fun _ _ => mem_univ _) hkO hM hγ hord
  have e1 : ∀ y : Vec3, multiPartial (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1) γ₁ (y,
    0) =
      multiPartialVec3 (serrinBallCutoff x ρ) γ₁ y := fun y => multiPartial_lift_eq _ γ₁ (y, 0)
  have e2 : ∀ y : Vec3, multiPartial (fun z : ParabolicPoint => k z.1) γ₂ (y, 0) =
      multiPartialVec3 k γ₂ y := fun y => multiPartial_lift_eq k γ₂ (y, 0)
  simp only [e1, e2] at h
  exact h

/-! ## Part 5: the Laplacian of a divergence-free field through its curl -/

private theorem contDiff_component {G : Vec3 → Vec3} (hG : ContDiff ℝ (⊤ : ℕ∞) G) (k : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => G y k) :=
  contDiff_pi.mp hG k

private theorem contDiff_curlComp_lift {G : Vec3 → Vec3} (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (m : Fin 3) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => curlComp (fun z : ParabolicPoint => G z.1) m (y, t)) := by
  show ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => spatialDeriv (fun y' => G y' (m + 2)) (m + 1) y -
    spatialDeriv (fun y' => G y' (m + 1)) (m + 2) y)
  exact (contDiff_spatialDeriv_smooth (contDiff_component hG _) _).sub
    (contDiff_spatialDeriv_smooth (contDiff_component hG _) _)

/-- On an open set where the smooth field `G` is divergence free, `Δ Gᵢ = ∑ₖ σₖ ∂ₖ ω_{mₖ}` with
`|σₖ| ≤ 1`, where `ω` is the vorticity of the time-independent lift of `G`. -/
private theorem laplacian_eq_curl_sum {G : Vec3 → Vec3} (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    {V : Set Vec3} (hV : IsOpen V)
    (hdiv : ∀ y ∈ V, ∑ k, spatialDeriv (fun y' => G y' k) k y = 0) (t : ℝ) (i : Fin 3) :
    ∃ m : Fin 3 → Fin 3, ∃ σ : Fin 3 → ℝ, (∀ k, |σ k| ≤ 1) ∧ ∀ y ∈ V,
      spatialLaplacian (fun y' => G y' i) y =
        ∑ k, σ k * spatialDeriv
          (fun y' => curlComp (fun z : ParabolicPoint => G z.1) (m k) (y', t)) k y := by
  have hE := fun k => spatialPartial_antisymm_eq_smul_curlComp
    (fun z : ParabolicPoint => G z.1) i k
  choose m σ hσ hid using hE
  refine ⟨m, σ, hσ, fun y hy => ?_⟩
  have hGc := contDiff_component hG
  have hd1 : ∀ a b : Fin 3, Differentiable ℝ (spatialDeriv (fun y' => G y' a) b) := fun a b =>
    differentiable_of_smooth (contDiff_spatialDeriv_smooth (hGc a) b)
  have hfun : ∀ k : Fin 3, (fun y' => spatialDeriv (fun y'' => G y'' i) k y' -
      spatialDeriv (fun y'' => G y'' k) i y') =
      fun y' => σ k * curlComp (fun z : ParabolicPoint => G z.1) (m k) (y', t) :=
    fun k => funext fun y' => hid k (y', t)
  have hdivloc : (fun y' => ∑ k, spatialDeriv (fun y'' => G y'' k) k y') =ᶠ[𝓝 y]
      fun _ => (0 : ℝ) :=
    Filter.eventuallyEq_of_mem (hV.mem_nhds hy) (fun y' hy' => hdiv y' hy')
  have hdivderiv : spatialDeriv (fun y' => ∑ k, spatialDeriv (fun y'' => G y'' k) k y') i y = 0 :=
    spatialDeriv_eq_zero_of_eventuallyEq_zero hdivloc i
  rw [spatialDeriv_fun_sum (fun k => hd1 k k y) i] at hdivderiv
  have hswap : ∀ k : Fin 3, spatialDeriv (spatialDeriv (fun y'' => G y'' k) i) k y =
      spatialDeriv (spatialDeriv (fun y'' => G y'' k) k) i y := fun k =>
    mixedSecond_swap (hGc k) k i y
  calc spatialLaplacian (fun y' => G y' i) y
      = ∑ k, spatialDeriv (spatialDeriv (fun y'' => G y'' i) k) k y -
          ∑ k, spatialDeriv (spatialDeriv (fun y'' => G y'' k) k) i y := by
        rw [hdivderiv, sub_zero]
        rfl
    _ = ∑ k, (spatialDeriv (spatialDeriv (fun y'' => G y'' i) k) k y -
          spatialDeriv (spatialDeriv (fun y'' => G y'' k) i) k y) := by
        rw [Finset.sum_sub_distrib]
        simp only [hswap]
    _ = ∑ k, spatialDeriv (fun y' => spatialDeriv (fun y'' => G y'' i) k y' -
          spatialDeriv (fun y'' => G y'' k) i y') k y := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [spatialDeriv_fun_sub (hd1 i k y) (hd1 k i y)]
    _ = ∑ k, σ k * spatialDeriv
          (fun y' => curlComp (fun z : ParabolicPoint => G z.1) (m k) (y', t)) k y := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [hfun k, spatialDeriv_const_mul'
          (differentiable_of_smooth (contDiff_curlComp_lift hG (m k) t) y)]

private theorem abs_le_vortSum1 (U : ParabolicPoint → Vec3) (z : ParabolicPoint) (m k : Fin 3) :
    |spatialPartial (curlComp U m) k z| ≤ vortSum1 U z := by
  unfold vortSum1
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, |spatialPartial (curlComp U i) j z|)
    (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)) (Finset.mem_univ m))
  exact Finset.single_le_sum (f := fun j => |spatialPartial (curlComp U m) j z|)
    (fun j _ => abs_nonneg _) (Finset.mem_univ k)

private theorem abs_le_vortSum2 (U : ParabolicPoint → Vec3) (z : ParabolicPoint) (m k j : Fin 3) :
    |spatialPartial (fun w => spatialPartial (curlComp U m) k w) j z| ≤ vortSum2 U z := by
  unfold vortSum2
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun i => ∑ k', ∑ j', |spatialPartial (fun w => spatialPartial (curlComp U i) k' w) j' z|)
    (fun i _ => Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)))
    (Finset.mem_univ m))
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun k' => ∑ j', |spatialPartial (fun w => spatialPartial (curlComp U m) k' w) j' z|)
    (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ k))
  exact Finset.single_le_sum (f := fun j' => |spatialPartial
    (fun w => spatialPartial (curlComp U m) k w) j' z|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)

/-! ## Part 6: the pointwise bounds for a smooth divergence-free field -/

/-- The first-order bound at the centre for a globally smooth field that is divergence free
near the closed ball. -/
private theorem abs_spatialDeriv_component_le {Cb Cc : ℝ}
    (hELb : ∀ (x : Vec3) (ρ : ℝ), 0 < ρ → ∀ l : Fin 3,
      IntegrableOn (fun y => spatialDeriv newtonianKernel l (x - y))
        {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ∧
      ∫ y in {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ},
        |spatialDeriv newtonianKernel l (x - y)| ≤ Cb * ρ)
    (hELc : ∀ (k : Vec3 → ℝ) (x : Vec3) (ρ M : ℝ) (γ₁ γ₂ : Fin 3 → ℕ) (l : Fin 3),
      ContDiff ℝ (⊤ : ℕ∞) k → 0 < ρ → ρ ≤ 1 →
      (∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ → |k y| ≤ M) →
      γ₁ ≠ 0 → γ₁ 0 + γ₁ 1 + γ₁ 2 + (γ₂ 0 + γ₂ 1 + γ₂ 2) ≤ 3 →
      |∫ y : Vec3, spatialDeriv newtonianKernel l (x - y) *
          multiPartialVec3 (serrinBallCutoff x ρ) γ₁ y * multiPartialVec3 k γ₂ y| ≤
        Cc * M * ρ / ρ ^ (γ₁ 0 + γ₁ 1 + γ₁ 2 + (γ₂ 0 + γ₂ 1 + γ₂ 2)))
    {G : Vec3 → Vec3} (hG : ContDiff ℝ (⊤ : ℕ∞) G) {V : Set Vec3} (hV : IsOpen V)
    (hdiv : ∀ y ∈ V, ∑ k, spatialDeriv (fun y' => G y' k) k y = 0)
    {x : Vec3} {t ρ M Λ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hΛ0 : 0 ≤ Λ)
    (hBV : {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ⊆ V)
    (hM : ∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ → ∀ i, |G y i| ≤ M)
    (hΛ : ∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ →
      vortSum1 (fun z : ParabolicPoint => G z.1) (y, t) ≤ Λ)
    (i l : Fin 3) :
    |spatialDeriv (fun y => G y i) l x| ≤ Cb * ρ * (3 * Λ) + 9 * (Cc * M * ρ / ρ ^ 2) := by
  obtain ⟨hK, hKb⟩ := hELb x ρ hρ l
  obtain ⟨m, σ, hσ, hlap⟩ := laplacian_eq_curl_sum hG hV hdiv t i
  have hGi := contDiff_component hG i
  refine abs_spatialDeriv_le_of_split hGi hρ (by positivity) l hK hKb ?_ ?_ ?_
  · intro y hy
    rw [hlap y (hBV hy)]
    have hb : ∀ k : Fin 3, |σ k * spatialDeriv
        (fun y' => curlComp (fun z : ParabolicPoint => G z.1) (m k) (y', t)) k y| ≤ Λ := by
      intro k
      have h1 : |spatialDeriv
          (fun y' => curlComp (fun z : ParabolicPoint => G z.1) (m k) (y', t)) k y| ≤ Λ :=
        (abs_le_vortSum1 (fun z : ParabolicPoint => G z.1) (y, t) (m k) k).trans (hΛ y hy)
      rw [abs_mul]
      calc |σ k| * |spatialDeriv
            (fun y' => curlComp (fun z : ParabolicPoint => G z.1) (m k) (y', t)) k y|
          ≤ 1 * Λ := mul_le_mul (hσ k) h1 (abs_nonneg _) zero_le_one
        _ = Λ := one_mul Λ
    simp only [Fin.sum_univ_three]
    exact (abs_add_three _ _ _).trans (by linarith only [hb 0, hb 1, hb 2])
  · intro k
    have h := hELc (fun y => G y i) x ρ M (Pi.single k 1) (Pi.single k 1) l hGi hρ hρ1
      (fun y hy => hM y hy i) (single_ne_zero' k 1 one_ne_zero)
      (by rw [order_single_one]; norm_num)
    rw [multiPartialVec3_single_one, multiPartialVec3_single_one, order_single_one] at h
    exact h.trans_eq (by norm_num)
  · intro k
    have h := hELc (fun y => G y i) x ρ M (Pi.single k 2) 0 l hGi hρ hρ1
      (fun y hy => hM y hy i) (single_ne_zero' k 2 two_ne_zero)
      (by rw [order_single_two]; norm_num)
    rw [multiPartialVec3_single_two, multiPartialVec3_zero', order_single_two] at h
    refine le_trans (le_of_eq ?_) (h.trans (le_of_eq ?_))
    · rfl
    · norm_num

/-- The second-order bound at the centre for a globally smooth field that is divergence free
near the closed ball. -/
private theorem abs_spatialDeriv_spatialDeriv_component_le {Cb Cc : ℝ}
    (hELb : ∀ (x : Vec3) (ρ : ℝ), 0 < ρ → ∀ l : Fin 3,
      IntegrableOn (fun y => spatialDeriv newtonianKernel l (x - y))
        {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ∧
      ∫ y in {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ},
        |spatialDeriv newtonianKernel l (x - y)| ≤ Cb * ρ)
    (hELc : ∀ (k : Vec3 → ℝ) (x : Vec3) (ρ M : ℝ) (γ₁ γ₂ : Fin 3 → ℕ) (l : Fin 3),
      ContDiff ℝ (⊤ : ℕ∞) k → 0 < ρ → ρ ≤ 1 →
      (∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ → |k y| ≤ M) →
      γ₁ ≠ 0 → γ₁ 0 + γ₁ 1 + γ₁ 2 + (γ₂ 0 + γ₂ 1 + γ₂ 2) ≤ 3 →
      |∫ y : Vec3, spatialDeriv newtonianKernel l (x - y) *
          multiPartialVec3 (serrinBallCutoff x ρ) γ₁ y * multiPartialVec3 k γ₂ y| ≤
        Cc * M * ρ / ρ ^ (γ₁ 0 + γ₁ 1 + γ₁ 2 + (γ₂ 0 + γ₂ 1 + γ₂ 2)))
    {G : Vec3 → Vec3} (hG : ContDiff ℝ (⊤ : ℕ∞) G) {V : Set Vec3} (hV : IsOpen V)
    (hdiv : ∀ y ∈ V, ∑ k, spatialDeriv (fun y' => G y' k) k y = 0)
    {x : Vec3} {t ρ M Λ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hΛ0 : 0 ≤ Λ)
    (hBV : {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ⊆ V)
    (hM : ∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ → ∀ i, |G y i| ≤ M)
    (hΛ : ∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ →
      vortSum2 (fun z : ParabolicPoint => G z.1) (y, t) ≤ Λ)
    (i j l : Fin 3) :
    |spatialDeriv (spatialDeriv (fun y => G y i) j) l x| ≤
      Cb * ρ * (3 * Λ) + 9 * (Cc * M * ρ / ρ ^ 3) := by
  obtain ⟨hK, hKb⟩ := hELb x ρ hρ l
  obtain ⟨m, σ, hσ, hlap⟩ := laplacian_eq_curl_sum hG hV hdiv t i
  have hGi := contDiff_component hG i
  have hΩ : ∀ k : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv
      (fun y' => curlComp (fun z : ParabolicPoint => G z.1) (m k) (y', t)) k) := fun k =>
    contDiff_spatialDeriv_smooth (contDiff_curlComp_lift hG (m k) t) k
  refine abs_spatialDeriv_le_of_split (contDiff_spatialDeriv_smooth hGi j) hρ (by positivity) l
    hK hKb ?_ ?_ ?_
  · intro y hy
    have hyV : y ∈ V := hBV hy
    have hev : spatialLaplacian (fun y' => G y' i) =ᶠ[𝓝 y] fun y' => ∑ k, σ k * spatialDeriv
        (fun y'' => curlComp (fun z : ParabolicPoint => G z.1) (m k) (y'', t)) k y' :=
      Filter.eventuallyEq_of_mem (hV.mem_nhds hyV) (fun y' hy' => hlap y' hy')
    have hstep : spatialLaplacian (spatialDeriv (fun y' => G y' i) j) y =
        ∑ k, σ k * spatialDeriv (spatialDeriv
          (fun y'' => curlComp (fun z : ParabolicPoint => G z.1) (m k) (y'', t)) k) j y := by
      rw [spatialLaplacian_spatialDeriv_comm hGi j y]
      have e1 : spatialDeriv (spatialLaplacian (fun y' => G y' i)) j y =
          spatialDeriv (fun y' => ∑ k, σ k * spatialDeriv
            (fun y'' => curlComp (fun z : ParabolicPoint => G z.1) (m k) (y'', t)) k y') j y := by
        simp only [spatialDeriv, hev.fderiv_eq]
      rw [e1, spatialDeriv_fun_sum (fun k => ((differentiable_of_smooth (hΩ k)).const_mul
        (σ k)) y) j]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      exact spatialDeriv_const_mul' (differentiable_of_smooth (hΩ k) y) (σ k) j
    rw [hstep]
    have hb : ∀ k : Fin 3, |σ k * spatialDeriv (spatialDeriv
        (fun y'' => curlComp (fun z : ParabolicPoint => G z.1) (m k) (y'', t)) k) j y| ≤ Λ := by
      intro k
      have h1 : |spatialDeriv (spatialDeriv
          (fun y'' => curlComp (fun z : ParabolicPoint => G z.1) (m k) (y'', t)) k) j y| ≤ Λ :=
        (abs_le_vortSum2 (fun z : ParabolicPoint => G z.1) (y, t) (m k) k j).trans (hΛ y hy)
      rw [abs_mul]
      calc |σ k| * |spatialDeriv (spatialDeriv
            (fun y'' => curlComp (fun z : ParabolicPoint => G z.1) (m k) (y'', t)) k) j y|
          ≤ 1 * Λ := mul_le_mul (hσ k) h1 (abs_nonneg _) zero_le_one
        _ = Λ := one_mul Λ
    simp only [Fin.sum_univ_three]
    exact (abs_add_three _ _ _).trans (by linarith only [hb 0, hb 1, hb 2])
  · intro k
    have h := hELc (fun y => G y i) x ρ M (Pi.single k 1) (Pi.single k 1 + Pi.single j 1) l hGi
      hρ hρ1 (fun y hy => hM y hy i) (single_ne_zero' k 1 one_ne_zero)
      (by rw [order_single_one, order_pair])
    rw [multiPartialVec3_single_one, multiPartialVec3_pair hGi, order_single_one, order_pair] at h
    exact h.trans_eq (by norm_num)
  · intro k
    have h := hELc (fun y => G y i) x ρ M (Pi.single k 2) (Pi.single j 1) l hGi hρ hρ1
      (fun y hy => hM y hy i) (single_ne_zero' k 2 two_ne_zero)
      (by rw [order_single_two, order_single_one])
    rw [multiPartialVec3_single_two, multiPartialVec3_single_one, order_single_two,
      order_single_one] at h
    exact h.trans_eq (by norm_num)

/-! ## Part 7: transfer from the velocity to its smooth extension -/

/-- The data of a velocity on one time slice, transferred to a globally smooth field that
agrees with it near the closed ball. -/
private theorem slice_transfer {u : ParabolicPoint → Vec3} {O : Set ParabolicPoint} {x : Vec3}
    {t ρ : ℝ} (hO : IsOpen (X := Vec3 × ℝ) O) (hρ : 0 < ρ)
    (hball : ∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ → (y, t) ∈ O)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) O)
    (hdiv : ∀ z ∈ O, ∑ j, spatialPartial (fun w => u w j) j z = 0) :
    ∃ G : Vec3 → Vec3, ContDiff ℝ (⊤ : ℕ∞) G ∧ ∃ V : Set Vec3, IsOpen V ∧
      {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ⊆ V ∧
      (∀ y ∈ V, ∑ k, spatialDeriv (fun y' => G y' k) k y = 0) ∧
      (∀ y ∈ V, ∀ i, G y i = u (y, t) i) ∧
      (∀ y ∈ V, vortSum1 (fun z : ParabolicPoint => G z.1) (y, t) = vortSum1 u (y, t)) ∧
      (∀ y ∈ V, vortSum2 (fun z : ParabolicPoint => G z.1) (y, t) = vortSum2 u (y, t)) ∧
      (∀ y ∈ V, velSum1 u (y, t) = ∑ i, ∑ j, |spatialDeriv (fun y' => G y' i) j y|) ∧
      (∀ y ∈ V, velSum2 u (y, t) =
        ∑ i, ∑ j, ∑ l, |spatialDeriv (spatialDeriv (fun y' => G y' i) j) l y|) := by
  obtain ⟨G, hG, V, hV, hBV, hVG⟩ := exists_smooth_slice_extension hO hρ hball hu
  set U : ParabolicPoint → Vec3 := fun z => G z.1 with hU
  have h0 : ∀ k : Fin 3, ∀ y ∈ V, (fun w => u w k) (y, t) = (fun w => U w k) (y, t) :=
    fun k y hy => by
      show u (y, t) k = G y k
      rw [(hVG y hy).2]
  have h1 : ∀ k j : Fin 3, ∀ y ∈ V,
      spatialPartial (fun w => u w k) j (y, t) = spatialPartial (fun w => U w k) j (y, t) :=
    fun k j => spatialPartial_eq_of_eqOn_slice hV (h0 k) j
  have h2 : ∀ k j l : Fin 3, ∀ y ∈ V,
      spatialPartial (fun w => spatialPartial (fun w' => u w' k) j w) l (y, t) =
        spatialPartial (fun w => spatialPartial (fun w' => U w' k) j w) l (y, t) :=
    fun k j l => spatialPartial_eq_of_eqOn_slice hV (h1 k j) l
  have hc : ∀ m : Fin 3, ∀ y ∈ V, curlComp u m (y, t) = curlComp U m (y, t) := fun m y hy => by
    unfold curlComp
    rw [h1 _ _ y hy, h1 _ _ y hy]
  have hc1 : ∀ m j : Fin 3, ∀ y ∈ V,
      spatialPartial (curlComp u m) j (y, t) = spatialPartial (curlComp U m) j (y, t) :=
    fun m j => spatialPartial_eq_of_eqOn_slice hV (hc m) j
  have hc2 : ∀ m j l : Fin 3, ∀ y ∈ V,
      spatialPartial (fun w => spatialPartial (curlComp u m) j w) l (y, t) =
        spatialPartial (fun w => spatialPartial (curlComp U m) j w) l (y, t) :=
    fun m j l => spatialPartial_eq_of_eqOn_slice hV (hc1 m j) l
  refine ⟨G, hG, V, hV, hBV, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    rw [← hdiv (y, t) (hVG y hy).1]
    exact Finset.sum_congr rfl (fun k _ => (h1 k k y hy).symm)
  · intro y hy i
    rw [(hVG y hy).2]
  · intro y hy
    unfold vortSum1
    exact Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun j _ => by
      rw [hc1 m j y hy]))
  · intro y hy
    unfold vortSum2
    exact Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun l _ => by rw [hc2 m j l y hy])))
  · intro y hy
    unfold velSum1
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by
      rw [h1 i j y hy]
      rfl))
  · intro y hy
    unfold velSum2
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun l _ => by
        rw [h2 i j l y hy]
        rfl)))

private theorem centre_mem_closedBall (x : Vec3) {ρ : ℝ} (hρ : 0 < ρ) :
    vec3EuclideanNorm (x - x) ≤ ρ := by
  simp only [sub_self, vec3EuclideanNorm, Pi.zero_apply]
  norm_num
  exact hρ.le

/-! ## Part 8: the local elliptic bounds EL1 and EL2 -/

/-- First-order local elliptic bound on a time slice: for a divergence-free velocity smooth near
the closed ball `|y - x| ≤ ρ` of the slice `t`, the velocity gradient at the centre is bounded by
`C (ρ Λ + M / ρ)`, where `M` bounds the velocity and `Λ` the vorticity gradient on the ball. -/
theorem EL1_local : ∃ C : ℝ, 0 < C ∧ ∀ (u : ParabolicPoint → Vec3) (O : Set ParabolicPoint)
    (x : Vec3) (t ρ M Λ : ℝ), IsOpen (X := Vec3 × ℝ) O → 0 < ρ → ρ ≤ 1 →
    (∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ → (y, t) ∈ O) →
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) O →
    (∀ z ∈ O, ∑ j, spatialPartial (fun w => u w j) j z = 0) →
    (∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ → ∀ i, |u (y, t) i| ≤ M) →
    (∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ → vortSum1 u (y, t) ≤ Λ) →
    velSum1 u (x, t) ≤ C * (ρ * Λ + M / ρ) := by
  obtain ⟨Cb, hCb, hELb⟩ := ELb_kernel_ball_integral
  obtain ⟨Cc, hCc, hELc⟩ := annular_kernel_bound_vec3
  refine ⟨27 * Cb + 81 * Cc, by positivity, ?_⟩
  intro u O x t ρ M Λ hO hρ hρ1 hball hu hdiv hM hΛ
  obtain ⟨G, hG, V, hV, hBV, hdivG, hGu, hv1, -, hvel1, -⟩ :=
    slice_transfer hO hρ hball hu hdiv
  have hxB := centre_mem_closedBall x hρ
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x hxB 0)
  have hΛ0 : 0 ≤ Λ := (levelSums_nonneg u (x, t)).2.1.trans (hΛ x hxB)
  have hMG : ∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ → ∀ i, |G y i| ≤ M := fun y hy i => by
    rw [hGu y (hBV hy) i]
    exact hM y hy i
  have hΛG : ∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ →
      vortSum1 (fun z : ParabolicPoint => G z.1) (y, t) ≤ Λ := fun y hy => by
    rw [hv1 y (hBV hy)]
    exact hΛ y hy
  have hcore := abs_spatialDeriv_component_le hELb hELc hG hV hdivG hρ hρ1 hΛ0 hBV hMG hΛG
  rw [hvel1 x (hBV hxB)]
  have hρΛ : 0 ≤ ρ * Λ := mul_nonneg hρ.le hΛ0
  have hMρ : 0 ≤ M / ρ := div_nonneg hM0 hρ.le
  have e : Cc * M * ρ / ρ ^ 2 = Cc * (M / ρ) := by
    field_simp
  calc ∑ i, ∑ j, |spatialDeriv (fun y' => G y' i) j x|
      ≤ ∑ i : Fin 3, ∑ j : Fin 3, (Cb * ρ * (3 * Λ) + 9 * (Cc * M * ρ / ρ ^ 2)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hcore i j
    _ = 27 * Cb * (ρ * Λ) + 81 * Cc * (M / ρ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, e]
        ring
    _ ≤ (27 * Cb + 81 * Cc) * (ρ * Λ + M / ρ) := by
        nlinarith only [mul_nonneg hCc.le hρΛ, mul_nonneg hCb.le hMρ]

/-- Second-order local elliptic bound on a time slice: for a divergence-free velocity smooth near
the closed ball `|y - x| ≤ ρ` of the slice `t`, the velocity Hessian at the centre is bounded by
`C (ρ Λ + M / ρ²)`, where `M` bounds the velocity and `Λ` the vorticity Hessian on the ball. -/
theorem EL2_local : ∃ C : ℝ, 0 < C ∧ ∀ (u : ParabolicPoint → Vec3) (O : Set ParabolicPoint)
    (x : Vec3) (t ρ M Λ : ℝ), IsOpen (X := Vec3 × ℝ) O → 0 < ρ → ρ ≤ 1 →
    (∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ → (y, t) ∈ O) →
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) O →
    (∀ z ∈ O, ∑ j, spatialPartial (fun w => u w j) j z = 0) →
    (∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ → ∀ i, |u (y, t) i| ≤ M) →
    (∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ → vortSum2 u (y, t) ≤ Λ) →
    velSum2 u (x, t) ≤ C * (ρ * Λ + M / ρ ^ 2) := by
  obtain ⟨Cb, hCb, hELb⟩ := ELb_kernel_ball_integral
  obtain ⟨Cc, hCc, hELc⟩ := annular_kernel_bound_vec3
  refine ⟨81 * Cb + 243 * Cc, by positivity, ?_⟩
  intro u O x t ρ M Λ hO hρ hρ1 hball hu hdiv hM hΛ
  obtain ⟨G, hG, V, hV, hBV, hdivG, hGu, -, hv2, -, hvel2⟩ :=
    slice_transfer hO hρ hball hu hdiv
  have hxB := centre_mem_closedBall x hρ
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x hxB 0)
  have hΛ0 : 0 ≤ Λ := (levelSums_nonneg u (x, t)).2.2.1.trans (hΛ x hxB)
  have hMG : ∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ → ∀ i, |G y i| ≤ M := fun y hy i => by
    rw [hGu y (hBV hy) i]
    exact hM y hy i
  have hΛG : ∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ →
      vortSum2 (fun z : ParabolicPoint => G z.1) (y, t) ≤ Λ := fun y hy => by
    rw [hv2 y (hBV hy)]
    exact hΛ y hy
  have hcore := abs_spatialDeriv_spatialDeriv_component_le hELb hELc hG hV hdivG hρ hρ1 hΛ0 hBV
    hMG hΛG
  rw [hvel2 x (hBV hxB)]
  have hρΛ : 0 ≤ ρ * Λ := mul_nonneg hρ.le hΛ0
  have hMρ : 0 ≤ M / ρ ^ 2 := div_nonneg hM0 (by positivity)
  have e : Cc * M * ρ / ρ ^ 3 = Cc * (M / ρ ^ 2) := by
    field_simp
  calc ∑ i, ∑ j, ∑ l, |spatialDeriv (spatialDeriv (fun y' => G y' i) j) l x|
      ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
          (Cb * ρ * (3 * Λ) + 9 * (Cc * M * ρ / ρ ^ 3)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          Finset.sum_le_sum fun l _ => hcore i j l
    _ = 81 * Cb * (ρ * Λ) + 243 * Cc * (M / ρ ^ 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, e]
        ring
    _ ≤ (81 * Cb + 243 * Cc) * (ρ * Λ + M / ρ ^ 2) := by
        nlinarith only [mul_nonneg hCc.le hρΛ, mul_nonneg hCb.le hMρ]

/-! ## Part 9: the velocity level bounds EV1 and EV2 -/

private theorem isOpen_unitCylinder' : IsOpen (X := Vec3 × ℝ) unitCylinder :=
  (isOpen_vec3Ball 0 1).prod isOpen_Ioo

/-- The fixed radius `ρ = min (a' - a, b - b', 1) / 2` keeps the closed ball of every point of the
inner annulus inside the outer annulus. -/
private theorem annulus_ball_geometry {a b a' b' : ℝ} (ha' : a < a') (hb' : b' < b) :
    0 < min (min (a' - a) (b - b')) 1 / 2 ∧ min (min (a' - a) (b - b')) 1 / 2 ≤ 1 ∧
      ∀ x y : Vec3, a' < vec3EuclideanNorm x → vec3EuclideanNorm x < b' →
        vec3EuclideanNorm (y - x) ≤ min (min (a' - a) (b - b')) 1 / 2 →
        a < vec3EuclideanNorm y ∧ vec3EuclideanNorm y < b := by
  have hm1 : min (min (a' - a) (b - b')) 1 ≤ a' - a :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hm2 : min (min (a' - a) (b - b')) 1 ≤ b - b' :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hm3 : min (min (a' - a) (b - b')) 1 ≤ 1 := min_le_right _ _
  have hmpos : 0 < min (min (a' - a) (b - b')) 1 :=
    lt_min (lt_min (sub_pos.mpr ha') (sub_pos.mpr hb')) one_pos
  refine ⟨by positivity, by linarith only [hm3], ?_⟩
  intro x y hx1 hx2 hy
  have hup : vec3EuclideanNorm y ≤ vec3EuclideanNorm (y - x) + vec3EuclideanNorm x := by
    have h := vec3EuclideanNorm_add_le (y - x) x
    rwa [sub_add_cancel] at h
  have hlow : vec3EuclideanNorm x ≤ vec3EuclideanNorm (y - x) + vec3EuclideanNorm y := by
    have h := vec3EuclideanNorm_add_le (-(y - x)) y
    rwa [vec3EuclideanNorm_neg, neg_sub, sub_add_cancel] at h
  constructor
  · linarith only [hlow, hy, hx1, hm1, hmpos]
  · linarith only [hup, hy, hx2, hm2, hmpos]

/-- Velocity-gradient level bound: a bound on the vorticity gradient over an annulus times a
backward time interval gives a bound on the velocity gradient over any inner annulus. -/
theorem EV1_velocity_gradient {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} (hcl : IsClassicalSolutionOn u p f unitCylinder)
    {a b t₁ Mu Ω₁ : ℝ} (hab : 0 ≤ a ∧ a < b ∧ b < 1) (ht₁ : -1 < t₁ ∧ t₁ < 0)
    (hu : ∀ x : Vec3, a < vec3EuclideanNorm x → vec3EuclideanNorm x < b →
      ∀ s ∈ Ioo t₁ 0, ∀ i, |u (x, s) i| ≤ Mu)
    (hω₁ : ∀ x : Vec3, a < vec3EuclideanNorm x → vec3EuclideanNorm x < b →
      ∀ s ∈ Ioo t₁ 0, vortSum1 u (x, s) ≤ Ω₁)
    {a' b' : ℝ} (hab' : a < a' ∧ a' < b' ∧ b' < b) :
    ∃ K : ℝ, ∀ x : Vec3, a' < vec3EuclideanNorm x → vec3EuclideanNorm x < b' →
      ∀ s ∈ Ioo t₁ 0, velSum1 u (x, s) ≤ K := by
  obtain ⟨C, -, hEL⟩ := EL1_local
  obtain ⟨hρ, hρ1, hgeom⟩ := annulus_ball_geometry (a := a) (b := b) hab'.1 hab'.2.2
  refine ⟨C * (min (min (a' - a) (b - b')) 1 / 2 * Ω₁ +
    Mu / (min (min (a' - a) (b - b')) 1 / 2)), fun x hx1 hx2 s hs => ?_⟩
  refine hEL u unitCylinder x s _ Mu Ω₁ isOpen_unitCylinder' hρ hρ1 (fun y hy => ?_) hcl.1
    hcl.2.2.2.2 (fun y hy i => hu y (hgeom x y hx1 hx2 hy).1 (hgeom x y hx1 hx2 hy).2 s hs i)
    (fun y hy => hω₁ y (hgeom x y hx1 hx2 hy).1 (hgeom x y hx1 hx2 hy).2 s hs)
  refine ⟨?_, ?_, ?_⟩
  · show vec3EuclideanNorm (y - 0) < 1
    rw [sub_zero]
    exact (hgeom x y hx1 hx2 hy).2.trans hab.2.2
  · exact ht₁.1.trans hs.1
  · exact hs.2

/-- Velocity-Hessian level bound: a bound on the vorticity Hessian over an annulus times a
backward time interval gives a bound on the velocity Hessian over any inner annulus. -/
theorem EV2_velocity_hessian {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} (hcl : IsClassicalSolutionOn u p f unitCylinder)
    {a b t₁ Mu Ω₂ : ℝ} (hab : 0 ≤ a ∧ a < b ∧ b < 1) (ht₁ : -1 < t₁ ∧ t₁ < 0)
    (hu : ∀ x : Vec3, a < vec3EuclideanNorm x → vec3EuclideanNorm x < b →
      ∀ s ∈ Ioo t₁ 0, ∀ i, |u (x, s) i| ≤ Mu)
    (hω₂ : ∀ x : Vec3, a < vec3EuclideanNorm x → vec3EuclideanNorm x < b →
      ∀ s ∈ Ioo t₁ 0, vortSum2 u (x, s) ≤ Ω₂)
    {a' b' : ℝ} (hab' : a < a' ∧ a' < b' ∧ b' < b) :
    ∃ K : ℝ, ∀ x : Vec3, a' < vec3EuclideanNorm x → vec3EuclideanNorm x < b' →
      ∀ s ∈ Ioo t₁ 0, velSum2 u (x, s) ≤ K := by
  obtain ⟨C, -, hEL⟩ := EL2_local
  obtain ⟨hρ, hρ1, hgeom⟩ := annulus_ball_geometry (a := a) (b := b) hab'.1 hab'.2.2
  refine ⟨C * (min (min (a' - a) (b - b')) 1 / 2 * Ω₂ +
    Mu / (min (min (a' - a) (b - b')) 1 / 2) ^ 2), fun x hx1 hx2 s hs => ?_⟩
  refine hEL u unitCylinder x s _ Mu Ω₂ isOpen_unitCylinder' hρ hρ1 (fun y hy => ?_) hcl.1
    hcl.2.2.2.2 (fun y hy i => hu y (hgeom x y hx1 hx2 hy).1 (hgeom x y hx1 hx2 hy).2 s hs i)
    (fun y hy => hω₂ y (hgeom x y hx1 hx2 hy).1 (hgeom x y hx1 hx2 hy).2 s hs)
  refine ⟨?_, ?_, ?_⟩
  · show vec3EuclideanNorm (y - 0) < 1
    rw [sub_zero]
    exact (hgeom x y hx1 hx2 hy).2.trans hab.2.2
  · exact ht₁.1.trans hs.1
  · exact hs.2

end CIV
