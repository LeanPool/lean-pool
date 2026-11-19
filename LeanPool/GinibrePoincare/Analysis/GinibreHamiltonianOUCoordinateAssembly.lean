/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianOUCoordinateAssembly.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianOUJointPath
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianConfigurationOUReference

/-!
# Ginibre Hamiltonian OU coordinate assembly

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreHamiltonianOUReference_horizon_scalar_assembly`.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- The continuous linear map sending real coordinates `x` to the configuration whose
coordinate `j` is `(x (j, 0) + I * x (j, 1)) / √n`. -/
def ginibreHamiltonianOUCoordinateAssembly (n : ℕ) :
    ((Fin n × Fin 2) → ℝ) →L[ℝ] Configuration n :=
  { toLinearMap :=
      { toFun := fun x j => ((x (j, 0) : ℂ) + Complex.I*(x (j, 1) : ℂ))/Real.sqrt n
        map_add' := by intro x y; ext j; simp only [Pi.add_apply, Complex.ofReal_add]; ring
        map_smul' := by
          intro c x
          ext j
          simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul,
              RingHom.id_apply]
          ring }
    cont := by apply continuous_pi; intro j; fun_prop }

/-- Coordinate assembly of the actual OU convolution is the configuration OU
convolution of the assembled initial state and cumulative noise. -/
theorem ginibreHamiltonianOUCoordinateAssembly_driven
    (n : ℕ) (κ : ℝ) (z : (Fin n × Fin 2) → ℝ)
    (N : ℝ → (Fin n × Fin 2) → ℝ) (hN : Continuous N) (t : ℝ) :
    ginibreHamiltonianOUCoordinateAssembly n (drivenOUPath κ z N t) =
      drivenOUPath κ (ginibreHamiltonianOUCoordinateAssembly n z)
        (fun s => ginibreHamiltonianOUCoordinateAssembly n (N s)) t :=
  ginibreHamiltonian_drivenOUPath_map _ κ z N hN t

theorem ginibreHamiltonian_drivenOUPath_pi {ι : Type*} [Fintype ι]
    (κ : ℝ) (z : ι → ℝ) (N : ℝ → ι → ℝ) (hN : Continuous N) (t : ℝ) :
    drivenOUPath κ z N t = fun i => drivenOUPath κ (z i) (fun s => N s i) t := by
  ext i
  exact ginibreHamiltonian_drivenOUPath_map
    (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ) κ z N hN t

/-- Literal independent scalar OU paths assemble into the genuine
configuration convolution, without invoking a law certificate. -/
theorem ginibreHamiltonianOUCoordinateAssembly_scalar_paths
    (n : ℕ) (κ : ℝ) (z : (Fin n × Fin 2) → ℝ)
    (N : ℝ → (Fin n × Fin 2) → ℝ) (hN : Continuous N) (t : ℝ) :
    ginibreHamiltonianOUCoordinateAssembly n
      (fun i => drivenOUPath κ (z i) (fun s => N s i) t) =
      drivenOUPath κ (ginibreHamiltonianOUCoordinateAssembly n z)
        (fun s => ginibreHamiltonianOUCoordinateAssembly n (N s)) t := by
  rw [← ginibreHamiltonian_drivenOUPath_pi κ z N hN t]
  exact ginibreHamiltonianOUCoordinateAssembly_driven n κ z N hN t

theorem ginibreHamiltonianOU_noise_coefficient {n : ℕ} (hn : 0 < n)
    (α : ℝ) (hα : 0 ≤ α) :
    Real.sqrt (2*α/(n : ℝ)) / Real.sqrt (n : ℝ) = Real.sqrt (2*α/(n : ℝ)^2) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  apply (sq_eq_sq₀ (div_nonneg (Real.sqrt_nonneg _) hs.le) (Real.sqrt_nonneg _)).mp
  rw [div_pow, Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) hα) hnR.le),
    Real.sq_sqrt hnR.le, Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) hα) (sq_nonneg _))]
  field_simp

theorem ginibreHamiltonianOUCoordinateAssembly_noise {Ω : Type*}
    {n : ℕ} (hn : 0 < n) (α : ℝ) (hα : 0 ≤ α)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (ω : Ω) (s : ℝ) :
    ginibreHamiltonianOUCoordinateAssembly n
      (fun i => ginibreBrownianNoise (B i) (Real.sqrt (2*α/(n : ℝ))) ω s) =
      ginibreConfigurationBrownianNoise n B α ω s := by
  ext j
  have he := ginibreHamiltonianOU_noise_coefficient hn α hα
  simp only [ginibreHamiltonianOUCoordinateAssembly, ContinuousLinearMap.coe_mk',
    LinearMap.coe_mk, AddHom.coe_mk, ginibreBrownianNoise, ginibreConfigurationBrownianNoise,
    Complex.ofReal_mul, Complex.real_smul]
  rw [← he, Complex.ofReal_div]
  ring

/-- The genuine original-Brownian configuration reference equals the assembled
scalar OU processes at the same rate, simultaneously at every time. -/
theorem ginibreHamiltonianOUReferenceProcess_scalar_assembly {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ) (hα : 0 ≤ α)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsBrownianReal (B i) P) (Z : Ω → (Fin n × Fin 2) → ℝ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ginibreHamiltonianOUReferenceProcess n α (ginibreHamiltonianOUCoordinateAssembly n (Z ω)) B t
          ω =
      ginibreHamiltonianOUCoordinateAssembly n
        (fun i => ginibreBrownianOU (B i) (2*α/(n : ℝ))
          (Real.sqrt (2*α/(n : ℝ))) (Z ω i) (t : ℝ) ω) := by
  have hCont : ∀ᵐ ω ∂P, ∀ i, Continuous (fun t => B i t ω) :=
    ae_all_iff.mpr (fun i => (hB i).cont)
  filter_upwards [ginibreBrownianFullContinuousNoise_ae n B P hB α, hCont] with ω hω hc
  intro t
  let N : ℝ → (Fin n × Fin 2) → ℝ :=
    fun s i => ginibreBrownianNoise (B i) (Real.sqrt (2*α/(n : ℝ))) ω s
  have hN : Continuous N := continuous_pi (fun i =>
    continuous_const.mul ((hc i).comp continuous_real_toNNReal))
  have he : (ginibreBrownianFullContinuousNoise n B α ω).val =
      (fun s => ginibreHamiltonianOUCoordinateAssembly n (N s)) := by
    funext s
    rw [hω s]
    exact (ginibreHamiltonianOUCoordinateAssembly_noise hn α hα B ω s).symm
  unfold ginibreHamiltonianOUReferenceProcess ginibreHamiltonianOUValue
  rw [he]
  exact (ginibreHamiltonianOUCoordinateAssembly_scalar_paths n (2*α/(n : ℝ)) (Z ω) N hN t).symm

theorem ginibreHamiltonianOUReference_horizon_scalar_assembly {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ) (hα : 0 ≤ α)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsBrownianReal (B i) P) (Z : Ω → (Fin n × Fin 2) → ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂P,
      ginibreHamiltonianOUJointHorizonPath n α T
        (ginibreHamiltonianOUCoordinateAssembly n (Z ω), ginibreBrownianFullContinuousNoise n B α ω)
            =
      ginibreConfigurationOUAssemble n T
        (fun i => ginibreBrownianOUHorizonPath (B i) (fun ω => Z ω i) (2*α/(n : ℝ)).toNNReal T ω) :=
            by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hr : 0 ≤ 2*α/(n : ℝ) := div_nonneg (mul_nonneg (by norm_num) hα) hnR.le
  have hs : ∀ᵐ ω ∂P, ∀ i, ∀ t : Icc (0 : ℝ≥0) T,
      ginibreBrownianOUHorizonPath (B i) (fun ω => Z ω i) (2*α/(n : ℝ)).toNNReal T ω t =
      ginibreBrownianOU (B i) (2*α/(n : ℝ)).toNNReal
        (Real.sqrt ((2*α/(n : ℝ)).toNNReal : ℝ)) (Z ω i) t.val ω :=
    ae_all_iff.mpr (fun i => ginibreBrownianOUHorizonPath_ae (B i) P (hB i)
      (fun ω => Z ω i) _ T)
  filter_upwards [ginibreHamiltonianOUReferenceProcess_scalar_assembly hn α hα B P hB Z, hs] with ω
      hω hsω
  apply DFunLike.ext
  intro t
  have hh := hω t.val.toNNReal
  change ginibreHamiltonianOUReferenceProcess n α
    (ginibreHamiltonianOUCoordinateAssembly n (Z ω)) B t.val.toNNReal ω = _
  rw [hh]
  ext j
  simp only [ginibreConfigurationOUAssemble, ContinuousMap.coe_mk, hsω,
    Real.coe_toNNReal _ hr, ginibreOURealHorizonToNNReal,
    ginibreHamiltonianOUCoordinateAssembly, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
        AddHom.coe_mk]

end
end GinibrePoincare
