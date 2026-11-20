/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticDbarL2.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticWeakSolvability
public import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Concrete weighted ∂bar test maps in L²
Multiplication by exp(-nV/2) represents the actual weighted Hilbert space
isometrically inside Lebesgue L². -/

@[expose] public section
open MeasureTheory
open scoped ContDiff InnerProductSpace
namespace GinibrePoincare
noncomputable section

/-- The algebraic space of all compact C² complex planar tests. -/
def planarCompactTestSpace : Submodule ℝ (ℂ → ℂ) where
  carrier := {f | ContDiff ℝ 2 f ∧ HasCompactSupport f}
  zero_mem' := ⟨contDiff_const, by simp [HasCompactSupport]⟩
  add_mem' := fun hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := fun c f hf => ⟨contDiff_const.smul hf.1, hf.2.smul_left⟩

/-- Compactly supported `C²` planar test functions `ℂ → ℂ`, as a real vector space. -/
abbrev PlanarCompactTest := ↥planarCompactTestSpace
instance : CoeFun PlanarCompactTest (fun _ => ℂ → ℂ) := ⟨fun f => f.val⟩
/-- The Hilbert space `L²(ℂ)` of complex square-integrable functions for Lebesgue measure. -/
abbrev PlanarLebesgueL2 := Lp ℂ 2 (volume : Measure ℂ)

/-- Real-linear concrete adjoint on the full compact C² test space. -/
def planarAdjointTestMap (W : ℂ → ℝ) : PlanarCompactTest →ₗ[ℝ] (ℂ → ℂ) where
  toFun f := planarDbarAdjoint W f
  map_add' f g := by
    funext z
    have hf := f.property.1.differentiable (by norm_num) z
    have hg := g.property.1.differentiable (by norm_num) z
    unfold planarDbarAdjoint
    simp only [Submodule.coe_add]
    rw [fderiv_add hf hg]
    simp only [add_apply, Pi.add_apply]
    ring
  map_smul' c f := by
    funext z
    have hf := f.property.1.differentiable (by norm_num) z
    unfold planarDbarAdjoint
    simp only [Submodule.coe_smul]
    rw [fderiv_const_smul hf]
    simp only [smul_apply, Pi.smul_apply, Complex.real_smul, RingHom.id_apply]
    ring

/-- The density's positive square root. -/
def planarPotentialHalfWeight (n : ℕ) (V : ℂ → ℝ) (z : ℂ) : ℂ :=
  (Real.exp (-(n : ℝ) * V z / 2) : ℂ)

/-- Actual weighted value functions before taking L² equivalence classes. -/
def planarWeightedTestMap (n : ℕ) (V : ℂ → ℝ) : PlanarCompactTest →ₗ[ℝ] (ℂ → ℂ) where
  toFun f z := f z * planarPotentialHalfWeight n V z
  map_add' f g := by funext z; simp [add_mul]
  map_smul' c f := by funext z; simp [mul_assoc]

/-- Actual weighted adjoint functions before taking L² equivalence classes. -/
def planarWeightedAdjointTestMap (n : ℕ) (V : ℂ → ℝ) : PlanarCompactTest →ₗ[ℝ] (ℂ → ℂ) :=
  { toFun := fun f z => planarAdjointTestMap (fun z => (n : ℝ) * V z) f z *
      planarPotentialHalfWeight n V z
    map_add' := by intros f g; funext z; simp [add_mul]
    map_smul' := by intros c f; funext z; simp [mul_assoc] }

private theorem planar_half_weight_continuous (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) :
    Continuous (planarPotentialHalfWeight n V) := by
  unfold planarPotentialHalfWeight
  exact Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp ((continuous_const.mul hV).div_const 2))

private theorem planar_adjoint_continuous (W : ℂ → ℝ) (hW : ContDiff ℝ 1 W)
    (f : PlanarCompactTest) : Continuous (planarAdjointTestMap W f) := by
  have hd := f.property.1.continuous_fderiv (by norm_num)
  have hdx := hd.clm_apply (continuous_const (y := (1 : ℂ)))
  have hdy := hd.clm_apply (continuous_const (y := Complex.I))
  have hDW := hW.continuous_fderiv (by norm_num)
  have hWx := hDW.clm_apply (continuous_const (y := (1 : ℂ)))
  have hWy := hDW.clm_apply (continuous_const (y := Complex.I))
  exact (continuous_const.mul (hdx.sub (continuous_const.mul hdy))).add
    (((continuous_const.mul ((Complex.continuous_ofReal.comp hWx).sub
      (continuous_const.mul (Complex.continuous_ofReal.comp hWy)))).mul f.property.1.continuous))

private theorem planar_adjoint_compact (W : ℂ → ℝ) (f : PlanarCompactTest) :
    HasCompactSupport (planarAdjointTestMap W f) := by
  have hc := f.property.2
  have hx := hc.fderiv_apply ℝ (1 : ℂ)
  have hy := hc.fderiv_apply ℝ Complex.I
  have hfirst : HasCompactSupport (fun z => -(1 / 2 : ℂ) *
      (fderiv ℝ (f : ℂ → ℂ) z 1 - Complex.I * fderiv ℝ (f : ℂ → ℂ) z Complex.I)) :=
    (hx.sub hy.mul_left).mul_left
  exact hfirst.add hc.mul_left

/-- Compact tests belong to actual weighted L² without a global partition hypothesis. -/
theorem planarWeightedTestMap_memLp (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (f : PlanarCompactTest) : MemLp (planarWeightedTestMap n V f) 2 volume := by
  convert (f.property.1.continuous.mul (planar_half_weight_continuous n V
      hV)).memLp_of_hasCompactSupport (μ := volume) (p := 2)
    f.property.2.mul_right using 1; rfl

/-- The concrete weighted adjoints are in L² without a global partition hypothesis. -/
theorem planarWeightedAdjointTestMap_memLp (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 1 V)
    (f : PlanarCompactTest) : MemLp (planarWeightedAdjointTestMap n V f) 2 volume :=
  ((planar_adjoint_continuous (fun z => (n : ℝ) * V z) (contDiff_const.mul hV) f).mul
    (planar_half_weight_continuous n V hV.continuous)).memLp_of_hasCompactSupport
    (planar_adjoint_compact _ f).mul_right

/-- A real-linear map from tests to square-integrable functions, lifted to a map into
`PlanarLebesgueL2` by taking `L²` classes. -/
def planarTestLpLift (P : PlanarCompactTest →ₗ[ℝ] (ℂ → ℂ))
    (hP : ∀ f, MemLp (P f) 2 volume) : PlanarCompactTest →ₗ[ℝ] PlanarLebesgueL2 where
  toFun f := (hP f).toLp (P f)
  map_add' f g := by
    rw [← MemLp.toLp_add (hP f) (hP g)]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall (fun z => congrFun (P.map_add f g) z)
  map_smul' c f := by
    simp only [RingHom.id_apply]
    rw [← MemLp.toLp_const_smul c (hP f)]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall (fun z => congrFun (P.map_smul c f) z)

/-- Actual weighted values embedded in Lebesgue L² by the square-root density. -/
def planarWeightedTestL2 (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) :
    PlanarCompactTest →ₗ[ℝ] PlanarLebesgueL2 :=
  planarTestLpLift (planarWeightedTestMap n V) (planarWeightedTestMap_memLp n V hV)

/-- Actual weighted adjoints embedded in Lebesgue L² by the square-root density. -/
def planarWeightedAdjointTestL2 (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 1 V) :
    PlanarCompactTest →ₗ[ℝ] PlanarLebesgueL2 :=
  planarTestLpLift (planarWeightedAdjointTestMap n V) (planarWeightedAdjointTestMap_memLp n V hV)

private theorem planar_half_weight_norm (n : ℕ) (V : ℂ → ℝ) (z w : ℂ) :
    ‖w * planarPotentialHalfWeight n V z‖ ^ 2 =
      Complex.normSq w * Real.exp (-(n : ℝ) * V z) := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_mul]
  simp only [planarPotentialHalfWeight, Complex.normSq_ofReal]
  rw [← Real.exp_add]
  congr 2
  ring

/-- Exact L² norm identification for weighted value tests. -/
theorem planarWeightedTestL2_norm_sq (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (f : PlanarCompactTest) :
    ‖planarWeightedTestL2 n V hV f‖ ^ 2 =
      ∫ z, Complex.normSq (f z) * Real.exp (-(n : ℝ) * V z) := by
  rw [← integral_norm_sq_eq_L2_norm_sq volume]
  apply integral_congr_ae
  filter_upwards [(planarWeightedTestMap_memLp n V hV f).coeFn_toLp] with z hz
  change ‖((planarWeightedTestMap_memLp n V hV f).toLp _) z‖ ^ 2 = _
  rw [hz]
  exact planar_half_weight_norm n V z (f z)

/-- Exact L² norm identification for the concrete weighted adjoint tests. -/
theorem planarWeightedAdjointTestL2_norm_sq (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 1 V)
    (f : PlanarCompactTest) :
    ‖planarWeightedAdjointTestL2 n V hV f‖ ^ 2 =
      ∫ z, Complex.normSq (planarDbarAdjoint (fun z => (n : ℝ) * V z) f z) *
        Real.exp (-(n : ℝ) * V z) := by
  rw [← integral_norm_sq_eq_L2_norm_sq volume]
  apply integral_congr_ae
  filter_upwards [(planarWeightedAdjointTestMap_memLp n V hV f).coeFn_toLp] with z hz
  change ‖((planarWeightedAdjointTestMap_memLp n V hV f).toLp _) z‖ ^ 2 = _
  rw [hz]
  exact planar_half_weight_norm n V z (planarDbarAdjoint (fun z => (n : ℝ) * V z) f z)

/-- The actual adjoint map is coercive under the exact subharmonic assumption. -/
theorem rhoSubharmonicPotential_testL2_coercivity (n : ℕ) (V : ℂ → ℝ) (ρ : ℝ)
    (hV : ContDiff ℝ 2 V) (hρ : IsRhoSubharmonicPotential ρ V) (f : PlanarCompactTest) :
    ((n : ℝ) * ρ / 2) * ‖planarWeightedTestL2 n V hV.continuous f‖ ^ 2 ≤
      ‖planarWeightedAdjointTestL2 n V (hV.of_le (by norm_num)) f‖ ^ 2 := by
  rw [planarWeightedTestL2_norm_sq, planarWeightedAdjointTestL2_norm_sq]
  exact rhoSubharmonicPotential_complex_adjoint_coercivity n V f ρ hV f.property.1 f.property.2 hρ

/-- Exact coercive norm bound needed in the Hahn–Banach construction. -/
theorem rhoSubharmonicPotential_testL2_norm_bound (n : ℕ) (hn : 0 < n)
    (V : ℂ → ℝ) (ρ : ℝ) (hρpos : 0 < ρ) (hV : ContDiff ℝ 2 V)
    (hρ : IsRhoSubharmonicPotential ρ V) (f : PlanarCompactTest) :
    ‖planarWeightedTestL2 n V hV.continuous f‖ ≤
      (Real.sqrt ((n : ℝ) * ρ / 2))⁻¹ *
      ‖planarWeightedAdjointTestL2 n V (hV.of_le (by norm_num)) f‖ := by
  have hp : 0 < (n : ℝ) * ρ / 2 := by positivity
  have hs := rhoSubharmonicPotential_testL2_coercivity n V ρ hV hρ f
  have hk : 0 < Real.sqrt ((n : ℝ) * ρ / 2) := Real.sqrt_pos.mpr hp
  have hmul : Real.sqrt ((n : ℝ) * ρ / 2) * ‖planarWeightedTestL2 n V hV.continuous f‖ ≤
      ‖planarWeightedAdjointTestL2 n V (hV.of_le (by norm_num)) f‖ := by
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (norm_nonneg _)).mp
    rwa [mul_pow, Real.sq_sqrt hp.le]
  have hdiv : ‖planarWeightedTestL2 n V hV.continuous f‖ ≤
      ‖planarWeightedAdjointTestL2 n V (hV.of_le (by norm_num)) f‖ /
      Real.sqrt ((n : ℝ) * ρ / 2) :=
    (le_div_iff₀ hk).mpr (by simpa only [mul_comm] using hmul)
  simpa only [div_eq_mul_inv, mul_comm] using hdiv

/-- Full weak solvability of the actual planar ∂bar equation under the
paper's subharmonic curvature bound. Both unknown and source are represented
in Lebesgue L² through the square-root density exp(-nV/2). The pairing is
against every compact C² complex test, with no solution hypothesis. -/
theorem rhoSubharmonicPotential_exists_weak_dbar_solution
    (n : ℕ) (hn : 0 < n) (V : ℂ → ℝ) (ρ : ℝ) (hρpos : 0 < ρ)
    (hV : ContDiff ℝ 2 V) (hρ : IsRhoSubharmonicPotential ρ V)
    (h : PlanarLebesgueL2) :
    ∃ u : PlanarLebesgueL2,
      ‖u‖ ^ 2 ≤ (2 / ((n : ℝ) * ρ)) * ‖h‖ ^ 2 ∧
      ∀ f : PlanarCompactTest,
        ⟪u, planarWeightedAdjointTestL2 n V (hV.of_le (by norm_num)) f⟫_ℝ =
          ⟪h, planarWeightedTestL2 n V hV.continuous f⟫_ℝ := by
  have hp : 0 < (n : ℝ) * ρ / 2 := by positivity
  have hb := rhoSubharmonicPotential_testL2_norm_bound n hn V ρ hρpos hV hρ
  obtain ⟨u, hu, hpair⟩ := exists_weak_solution_of_adjoint_bound
    (planarWeightedAdjointTestL2 n V (hV.of_le (by norm_num)))
    (planarWeightedTestL2 n V hV.continuous)
    (Real.sqrt ((n : ℝ) * ρ / 2))⁻¹ (inv_nonneg.mpr (Real.sqrt_nonneg _)) hb h
  refine ⟨u, ?_, hpair⟩
  have hsq := (sq_le_sq₀ (norm_nonneg u)
    (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (norm_nonneg h))).mpr hu
  rw [mul_pow, inv_pow, Real.sq_sqrt hp.le] at hsq
  have he : ((n : ℝ) * ρ / 2)⁻¹ = 2 / ((n : ℝ) * ρ) := by
    field_simp
  rwa [he] at hsq

/-- The actual distributional ∂bar kernel in square-root-density coordinates:
all weighted L² functions whose pairing with every weighted compact-test
adjoint vanishes. -/
def planarWeakDbarKernel (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 1 V) :
    Submodule ℝ PlanarLebesgueL2 := (planarWeightedAdjointTestL2 n V hV).rangeᗮ

/-- Membership in the kernel is the concrete distributional zero equation. -/
theorem mem_planarWeakDbarKernel_iff (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 1 V)
    (u : PlanarLebesgueL2) :
    u ∈ planarWeakDbarKernel n V hV ↔
      ∀ f : PlanarCompactTest, ⟪u, planarWeightedAdjointTestL2 n V hV f⟫_ℝ = 0 := by
  rw [planarWeakDbarKernel, Submodule.mem_orthogonal]
  constructor
  · intro h f
    simpa only [real_inner_comm] using h _ ⟨f, rfl⟩
  · intro h y hy
    obtain ⟨f, rfl⟩ := hy
    simpa only [real_inner_comm] using h f

/-- The full weak Hörmander gap for the concrete weighted ∂bar operator,
on the orthogonal complement of its actual distributional kernel. -/
theorem rhoSubharmonicPotential_weak_dbar_gap
    (n : ℕ) (hn : 0 < n) (V : ℂ → ℝ) (ρ : ℝ) (hρpos : 0 < ρ)
    (hV : ContDiff ℝ 2 V) (hρ : IsRhoSubharmonicPotential ρ V)
    (f h : PlanarLebesgueL2)
    (horth : f ∈ (planarWeakDbarKernel n V (hV.of_le (by norm_num)))ᗮ)
    (hpair : ∀ φ : PlanarCompactTest,
      ⟪f, planarWeightedAdjointTestL2 n V (hV.of_le (by norm_num)) φ⟫_ℝ =
        ⟪h, planarWeightedTestL2 n V hV.continuous φ⟫_ℝ) :
    ‖f‖ ^ 2 ≤ (2 / ((n : ℝ) * ρ)) * ‖h‖ ^ 2 := by
  have hp : 0 < (n : ℝ) * ρ / 2 := by positivity
  have hb := rhoSubharmonicPotential_testL2_norm_bound n hn V ρ hρpos hV hρ
  have hh := norm_le_of_weak_pairing_and_kernel_orthogonal
    (planarWeightedAdjointTestL2 n V (hV.of_le (by norm_num)))
    (planarWeightedTestL2 n V hV.continuous)
    (Real.sqrt ((n : ℝ) * ρ / 2))⁻¹ (inv_nonneg.mpr (Real.sqrt_nonneg _)) hb f h horth hpair
  have hs := (sq_le_sq₀ (norm_nonneg f)
    (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (norm_nonneg h))).mpr hh
  rw [mul_pow, inv_pow, Real.sq_sqrt hp.le] at hs
  have he : ((n : ℝ) * ρ / 2)⁻¹ = 2 / ((n : ℝ) * ρ) := by field_simp
  rwa [he] at hs

/-- The distributional ∂bar kernel is a closed Hilbert subspace. -/
def planarWeakDbarKernelClosed (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 1 V) :
    ClosedSubmodule ℝ PlanarLebesgueL2 :=
  ⟨planarWeakDbarKernel n V hV,
    Submodule.isClosed_orthogonal (planarWeightedAdjointTestL2 n V hV).range⟩

/-- The actual Hilbert projection onto the distributional ∂bar kernel. -/
def planarWeakDbarProjection (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 1 V) :
    PlanarLebesgueL2 →L[ℝ] PlanarLebesgueL2 :=
  (planarWeakDbarKernelClosed n V hV).starProjection

/-- General weak-domain Hörmander estimate: distance from the actual
∂bar kernel is controlled by the actual weak derivative at exact constant. -/
theorem rhoSubharmonicPotential_weak_dbar_projection_gap
    (n : ℕ) (hn : 0 < n) (V : ℂ → ℝ) (ρ : ℝ) (hρpos : 0 < ρ)
    (hV : ContDiff ℝ 2 V) (hρ : IsRhoSubharmonicPotential ρ V)
    (f h : PlanarLebesgueL2)
    (hpair : ∀ φ : PlanarCompactTest,
      ⟪f, planarWeightedAdjointTestL2 n V (hV.of_le (by norm_num)) φ⟫_ℝ =
        ⟪h, planarWeightedTestL2 n V hV.continuous φ⟫_ℝ) :
    ‖f - planarWeakDbarProjection n V (hV.of_le (by norm_num)) f‖ ^ 2 ≤
      (2 / ((n : ℝ) * ρ)) * ‖h‖ ^ 2 := by
  let K := planarWeakDbarKernelClosed n V (hV.of_le (by norm_num))
  have horth : f - K.starProjection f ∈
      (planarWeakDbarKernel n V (hV.of_le (by norm_num)))ᗮ :=
    Submodule.sub_starProjection_mem_orthogonal (K := K.toSubmodule) f
  apply rhoSubharmonicPotential_weak_dbar_gap n hn V ρ hρpos hV hρ _ h horth
  intro φ
  rw [inner_sub_left, hpair]
  have hp : K.starProjection f ∈ planarWeakDbarKernel n V (hV.of_le (by norm_num)) :=
    (K.orthogonalProjectionOnto f).property
  have hz := (mem_planarWeakDbarKernel_iff n V (hV.of_le (by norm_num)) _).mp hp φ
  rw [hz, sub_zero]

/-- Actual weighted ∂bar derivative of a compact C² test. -/
def planarWeightedDbarTestFunction (n : ℕ) (V : ℂ → ℝ) (f : PlanarCompactTest) (z : ℂ) : ℂ :=
  planarDbar f z * planarPotentialHalfWeight n V z

/-- The concrete weighted derivatives are genuinely square integrable. -/
theorem planarWeightedDbarTestFunction_memLp (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (f : PlanarCompactTest) : MemLp (planarWeightedDbarTestFunction n V f) 2 volume := by
  have hd := f.property.1.continuous_fderiv (by norm_num)
  have hdx := hd.clm_apply (continuous_const (y := (1 : ℂ)))
  have hdy := hd.clm_apply (continuous_const (y := Complex.I))
  have hdc : Continuous (planarDbar f) :=
    continuous_const.mul (hdx.add (continuous_const.mul hdy))
  have hc : HasCompactSupport (planarDbar f) :=
    ((f.property.2.fderiv_apply ℝ 1).add
      (f.property.2.fderiv_apply ℝ Complex.I).mul_left).mul_left
  exact (hdc.mul (planar_half_weight_continuous n V hV)).memLp_of_hasCompactSupport hc.mul_right

/-- Actual ∂bar derivative in the weighted L² representation. -/
def planarWeightedDbarTestL2 (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (f : PlanarCompactTest) : PlanarLebesgueL2 :=
  (planarWeightedDbarTestFunction_memLp n V hV f).toLp (planarWeightedDbarTestFunction n V f)

private theorem planar_half_weight_inner (n : ℕ) (V : ℂ → ℝ) (z a b : ℂ) :
    ⟪a * planarPotentialHalfWeight n V z, b * planarPotentialHalfWeight n V z⟫_ℝ =
      (star a * b).re * Real.exp (-(n : ℝ) * V z) := by
  have he : Real.exp (-(n : ℝ) * V z / 2) * Real.exp (-(n : ℝ) * V z / 2) =
      Real.exp (-(n : ℝ) * V z) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (star a * b).re *
        (Real.exp (-(n : ℝ) * V z / 2) * Real.exp (-(n : ℝ) * V z / 2)) := by
      simp only [Complex.inner, planarPotentialHalfWeight, Complex.mul_re,
        Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero, Complex.star_def]
      ring
    _ = _ := by rw [he]

private theorem planar_weighted_toLp_inner (n : ℕ) (V : ℂ → ℝ) (F G : ℂ → ℂ)
    (hF : MemLp (fun z => F z * planarPotentialHalfWeight n V z) 2 volume)
    (hG : MemLp (fun z => G z * planarPotentialHalfWeight n V z) 2 volume) :
    ⟪hF.toLp _, hG.toLp _⟫_ℝ = ∫ z, (star (F z) * G z).re * Real.exp (-(n : ℝ) * V z) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with z hzF hzG
  rw [hzF, hzG]
  exact planar_half_weight_inner n V z (F z) (G z)

/-- Integration by parts identifies the actual smooth weighted derivative
with the distributional derivative against all compact C² tests. -/
theorem planarWeightedTestL2_weak_derivative (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 1 V)
    (f φ : PlanarCompactTest) :
    ⟪planarWeightedTestL2 n V hV.continuous f, planarWeightedAdjointTestL2 n V hV φ⟫_ℝ =
      ⟪planarWeightedDbarTestL2 n V hV.continuous f, planarWeightedTestL2 n V hV.continuous φ⟫_ℝ :=
          by
  rw [real_inner_comm (planarWeightedAdjointTestL2 n V hV φ) (planarWeightedTestL2 n V hV.continuous
      f),
    real_inner_comm (planarWeightedTestL2 n V hV.continuous φ) (planarWeightedDbarTestL2 n V
        hV.continuous f)]
  change ⟪(planarWeightedAdjointTestMap_memLp n V hV φ).toLp _,
      (planarWeightedTestMap_memLp n V hV.continuous f).toLp _⟫_ℝ =
    ⟪(planarWeightedTestMap_memLp n V hV.continuous φ).toLp _,
      (planarWeightedDbarTestFunction_memLp n V hV.continuous f).toLp _⟫_ℝ
  calc
    _ = ∫ z, (star (planarDbarAdjoint (fun z => (n : ℝ) * V z) φ z) * f z).re *
        Real.exp (-(n : ℝ) * V z) :=
      planar_weighted_toLp_inner n V (planarDbarAdjoint (fun z => (n : ℝ) * V z) φ) f
        (planarWeightedAdjointTestMap_memLp n V hV φ) (planarWeightedTestMap_memLp n V hV.continuous
            f)
    _ = ∫ z, (star (φ z) * planarDbar f z).re * Real.exp (-(n : ℝ) * V z) := by
      simpa only [neg_mul] using planarDbar_real_adjoint_pairing (fun z => (n : ℝ) * V z) φ f
        (contDiff_const.mul hV) (φ.property.1.of_le (by norm_num)) (f.property.1.of_le (by
            norm_num))
        φ.property.2
    _ = _ := (planar_weighted_toLp_inner n V φ (planarDbar f)
      (planarWeightedTestMap_memLp n V hV.continuous φ)
      (planarWeightedDbarTestFunction_memLp n V hV.continuous f)).symm

/-- Exact identification of the actual weak derivative norm and ∂bar energy. -/
theorem planarWeightedDbarTestL2_norm_sq (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (f : PlanarCompactTest) :
    ‖planarWeightedDbarTestL2 n V hV f‖ ^ 2 =
      ∫ z, Complex.normSq (planarDbar f z) * Real.exp (-(n : ℝ) * V z) := by
  rw [← integral_norm_sq_eq_L2_norm_sq volume]
  apply integral_congr_ae
  filter_upwards [(planarWeightedDbarTestFunction_memLp n V hV f).coeFn_toLp] with z hz
  change ‖((planarWeightedDbarTestFunction_memLp n V hV f).toLp _) z‖ ^ 2 = _
  rw [hz]
  exact planar_half_weight_norm n V z (planarDbar f z)

/-- Unconditional compact C² core Hörmander projection gap for the actual
nonquadratic weighted measure, with exact constant 2/(nρ). -/
theorem rhoSubharmonicPotential_compact_dbar_projection_gap
    (n : ℕ) (hn : 0 < n) (V : ℂ → ℝ) (ρ : ℝ) (hρpos : 0 < ρ)
    (hV : ContDiff ℝ 2 V) (hρ : IsRhoSubharmonicPotential ρ V) (f : PlanarCompactTest) :
    ‖planarWeightedTestL2 n V hV.continuous f -
      planarWeakDbarProjection n V (hV.of_le (by norm_num)) (planarWeightedTestL2 n V hV.continuous
          f)‖ ^ 2 ≤
      (2 / ((n : ℝ) * ρ)) *
        ∫ z, Complex.normSq (planarDbar f z) * Real.exp (-(n : ℝ) * V z) := by
  rw [← planarWeightedDbarTestL2_norm_sq n V hV.continuous f]
  exact rhoSubharmonicPotential_weak_dbar_projection_gap n hn V ρ hρpos hV hρ _ _
    (planarWeightedTestL2_weak_derivative n V (hV.of_le (by norm_num)) f)

/-- The concrete Wirtinger derivative of every entire function vanishes. -/
theorem planarDbar_eq_zero_of_holomorphic (g : ℂ → ℂ) (hg : Differentiable ℂ g) (z : ℂ) :
    planarDbar g z = 0 := by
  unfold planarDbar
  rw [(hg z).fderiv_restrictScalars ℝ]
  change (1 / 2 : ℂ) * ((fderiv ℂ g z) 1 + Complex.I * (fderiv ℂ g z) Complex.I) = 0
  have he : Complex.I = Complex.I • (1 : ℂ) := by simp
  conv_lhs => arg 2; arg 2; arg 2; rw [he]
  rw [(fderiv ℂ g z).map_smul]
  simp only [smul_eq_mul]
  rw [← mul_assoc, Complex.I_mul_I]
  simp

/-- Every genuinely entire function in the actual weighted L² space belongs
to the concrete distributional ∂bar kernel. -/
theorem weighted_holomorphic_mem_weak_dbar_kernel
    (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 1 V) (g : ℂ → ℂ)
    (hg : Differentiable ℂ g)
    (hG : MemLp (fun z => g z * planarPotentialHalfWeight n V z) 2 volume) :
    hG.toLp _ ∈ planarWeakDbarKernel n V hV := by
  rw [mem_planarWeakDbarKernel_iff]
  intro φ
  rw [real_inner_comm (planarWeightedAdjointTestL2 n V hV φ)]
  change ⟪(planarWeightedAdjointTestMap_memLp n V hV φ).toLp _, hG.toLp _⟫_ℝ = 0
  calc
    _ = ∫ z, (star (planarDbarAdjoint (fun z => (n : ℝ) * V z) φ z) * g z).re *
        Real.exp (-(n : ℝ) * V z) :=
      planar_weighted_toLp_inner n V (planarDbarAdjoint (fun z => (n : ℝ) * V z) φ) g
        (planarWeightedAdjointTestMap_memLp n V hV φ) hG
    _ = ∫ z, (star (φ z) * planarDbar g z).re * Real.exp (-(n : ℝ) * V z) := by
      simpa only [neg_mul] using planarDbar_real_adjoint_pairing (fun z => (n : ℝ) * V z) φ g
        (contDiff_const.mul hV) (φ.property.1.of_le (by norm_num))
        ((hg.contDiff : ContDiff ℂ 1 g).restrict_scalars ℝ) φ.property.2
    _ = 0 := by simp only [planarDbar_eq_zero_of_holomorphic g hg, mul_zero, Complex.zero_re,
                  zero_mul, integral_zero]

end
end GinibrePoincare
