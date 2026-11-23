/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Affine description of the first eigenfunctions through the splitting

Abstract algebra/measure part of Lemma `lem_rig` of the paper: if `g₁,…,g_k` is an
`L²(μ)`-orthonormal family of eigenfunctions spanning all eigenfunctions of eigenvalue `ρ`, and the
Euclidean coordinate of the splitting is `p = ρ^{-1/2} (g₁,…,g_k)`, then every eigenfunction is
`⟨a, p⟩` with `‖a‖² = ρ ‖f‖²`, and orthogonal eigenfunctions have orthogonal vectors `a`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace CutoffRigidity.Riemann

section Algebra

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {k : ℕ} {ρ : ℝ}

/-- Orthonormal functions in `L²` : the coefficient of a combination. -/
theorem integral_sum_mul_orthonormal (g : Fin k → Ω → ℝ) (hg : ∀ i, MemLp (g i) 2 μ)
    (horth : ∀ i j, ∫ x, g i x * g j x ∂μ = if i = j then 1 else 0) (c : Fin k → ℝ) (j : Fin k) :
    ∫ x, (∑ i, c i * g i x) * g j x ∂μ = c j := by
  have hint : ∀ i j, Integrable (fun x => g i x * g j x) μ := fun i j =>
    (hg i).integrable_mul (hg j)
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => ?_)]
  · simp_rw [mul_assoc, integral_const_mul, horth]
    simp
  · simpa [mul_assoc] using (hint i j).const_mul (c i)

/-- `∫ (Σ cᵢ gᵢ)(Σ dᵢ gᵢ) = Σ cᵢ dᵢ`. -/
theorem integral_sum_mul_sum_orthonormal (g : Fin k → Ω → ℝ) (hg : ∀ i, MemLp (g i) 2 μ)
    (horth : ∀ i j, ∫ x, g i x * g j x ∂μ = if i = j then 1 else 0) (c d : Fin k → ℝ) :
    ∫ x, (∑ i, c i * g i x) * (∑ j, d j * g j x) ∂μ = ∑ i, c i * d i := by
  have hint : ∀ i j, Integrable (fun x => g i x * g j x) μ := fun i j =>
    (hg i).integrable_mul (hg j)
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun j _ => ?_)]
  · refine Finset.sum_congr rfl fun j _ => ?_
    have := integral_sum_mul_orthonormal g hg horth c j
    calc ∫ x, (∑ i, c i * g i x) * (d j * g j x) ∂μ
        = d j * ∫ x, (∑ i, c i * g i x) * g j x ∂μ := by
          rw [← integral_const_mul]; congr 1; ext x; ring
      _ = c j * d j := by rw [this]; ring
  · have : Integrable (fun x => ∑ i, c i * (g i x * g j x)) μ :=
      integrable_finsetSum _ fun i _ => (hint i j).const_mul (c i)
    refine (this.const_mul (d j)).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring

omit [MeasurableSpace Ω] in
private theorem inner_eq_scaled_sum (g : Fin k → Ω → ℝ) (p : Ω → EuclideanSpace ℝ (Fin k))
    (hp : ∀ x i, p x i = g i x / Real.sqrt ρ)
    (a : EuclideanSpace ℝ (Fin k)) (x : Ω) :
    inner ℝ a (p x) = ∑ i, (a i / Real.sqrt ρ) * g i x := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [hp, dotProduct, star_trivial]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The pairing of two coefficient vectors is the curvature times the corresponding L² pairing. -/
theorem coefficient_inner_eq_integral_mul (hρ : 0 < ρ) (g : Fin k → Ω → ℝ)
    (hg : ∀ i, MemLp (g i) 2 μ)
    (horth : ∀ i j, ∫ x, g i x * g j x ∂μ = if i = j then 1 else 0)
    (p : Ω → EuclideanSpace ℝ (Fin k)) (hp : ∀ x i, p x i = g i x / Real.sqrt ρ)
    (a b : EuclideanSpace ℝ (Fin k)) (f h : Ω → ℝ)
    (haf : ∀ x, f x = inner ℝ a (p x)) (hbh : ∀ x, h x = inner ℝ b (p x)) :
    inner ℝ a b = ρ * ∫ x, f x * h x ∂μ := by
  have hpair : (∫ x, f x * h x ∂μ) =
      ∑ i, (a i / Real.sqrt ρ) * (b i / Real.sqrt ρ) := by
    simpa only [haf, hbh, inner_eq_scaled_sum g p hp] using
      (integral_sum_mul_sum_orthonormal g hg horth
        (fun i => a i / Real.sqrt ρ) (fun i => b i / Real.sqrt ρ))
  rw [hpair, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  calc b i * a i = (Real.sqrt ρ) ^ 2 * ((a i / Real.sqrt ρ) * (b i / Real.sqrt ρ)) := by
        field_simp [(Real.sqrt_pos.mpr hρ).ne']
    _ = _ := by rw [Real.sq_sqrt hρ.le]

/-- The affine description: if every eigenfunction is a combination of the orthonormal `gᵢ`, then
it is `⟨a, p⟩` with `‖a‖² = ρ ‖f‖²`, where `p = ρ^{-1/2} g`. -/
theorem exists_vector_of_combination (hρ : 0 < ρ) (g : Fin k → Ω → ℝ) (hg : ∀ i, MemLp (g i) 2 μ)
    (horth : ∀ i j, ∫ x, g i x * g j x ∂μ = if i = j then 1 else 0)
    (p : Ω → EuclideanSpace ℝ (Fin k)) (hp : ∀ x i, p x i = g i x / Real.sqrt ρ)
    (f : Ω → ℝ) (c : Fin k → ℝ) (hc : ∀ x, f x = ∑ i, c i * g i x) :
    ∃ a : EuclideanSpace ℝ (Fin k), (∀ x, f x = inner ℝ a (p x)) ∧
      ‖a‖ ^ 2 = ρ * ∫ x, f x ^ 2 ∂μ ∧ ∀ i, a i = Real.sqrt ρ * c i := by
  let a : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 fun i => Real.sqrt ρ * c i
  have hrepr (x : Ω) : f x = inner ℝ a (p x) := by
    rw [hc x, inner_eq_scaled_sum g p hp]
    refine Finset.sum_congr rfl fun i _ => ?_
    change c i * g i x = ((Real.sqrt ρ * c i) / Real.sqrt ρ) * g i x
    rw [mul_comm (Real.sqrt ρ), mul_div_cancel_right₀ _ ((Real.sqrt_pos.mpr hρ).ne')]
  refine ⟨a, hrepr, ?_, fun i => rfl⟩
  simpa only [real_inner_self_eq_norm_sq, pow_two] using
    (coefficient_inner_eq_integral_mul hρ g hg horth p hp a a f f hrepr hrepr)

/-- The vector `a` is unique: `⟨a, p⟩ = ⟨a', p⟩` forces `a = a'`. -/
theorem vector_unique (hρ : 0 < ρ) (g : Fin k → Ω → ℝ) (hg : ∀ i, MemLp (g i) 2 μ)
    (horth : ∀ i j, ∫ x, g i x * g j x ∂μ = if i = j then 1 else 0)
    (p : Ω → EuclideanSpace ℝ (Fin k)) (hp : ∀ x i, p x i = g i x / Real.sqrt ρ)
    (a b : EuclideanSpace ℝ (Fin k)) (h : ∀ x, inner ℝ a (p x) = inner ℝ b (p x)) : a = b := by
  have hs : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  ext j
  have h1 := integral_sum_mul_orthonormal g hg horth (fun i => a i / Real.sqrt ρ) j
  have h2 := integral_sum_mul_orthonormal g hg horth (fun i => b i / Real.sqrt ρ) j
  have : ∫ x, (∑ i, (a i / Real.sqrt ρ) * g i x) * g j x ∂μ =
      ∫ x, (∑ i, (b i / Real.sqrt ρ) * g i x) * g j x ∂μ := by
    congr 1
    ext x
    rw [← inner_eq_scaled_sum g p hp a, ← inner_eq_scaled_sum g p hp b, h x]
  rw [h1, h2] at this
  exact (div_left_inj₀ hs.ne').mp this

/-- The norm and orthogonality conclusions for the split eigenfunctions. -/
theorem affine_items (hρ : 0 < ρ) (g : Fin k → Ω → ℝ) (hg : ∀ i, MemLp (g i) 2 μ)
    (horth : ∀ i j, ∫ x, g i x * g j x ∂μ = if i = j then 1 else 0)
    (p : Ω → EuclideanSpace ℝ (Fin k)) (hp : ∀ x i, p x i = g i x / Real.sqrt ρ)
    (E : (Ω → ℝ) → Prop) (hE : ∀ f, E f → ∃ c : Fin k → ℝ, ∀ x, f x = ∑ i, c i * g i x) :
    (∀ f, E f → ∃ a : EuclideanSpace ℝ (Fin k), (∀ x, f x = inner ℝ a (p x)) ∧
        ‖a‖ ^ 2 = ρ * ∫ x, f x ^ 2 ∂μ) ∧
      ∀ f h (a b : EuclideanSpace ℝ (Fin k)), E f → E h →
        (∀ x, f x = inner ℝ a (p x)) → (∀ x, h x = inner ℝ b (p x)) →
        ∫ x, f x * h x ∂μ = 0 → inner ℝ a b = 0 := by
  refine ⟨fun f hf => ?_, fun f h a b _ _ haf hbh hint => ?_⟩
  · obtain ⟨c, hc⟩ := hE f hf
    obtain ⟨a, h1, h2, -⟩ := exists_vector_of_combination hρ g hg horth p hp f c hc
    exact ⟨a, h1, h2⟩
  · rw [coefficient_inner_eq_integral_mul hρ g hg horth p hp a b f h haf hbh, hint, mul_zero]

end Algebra

end CutoffRigidity.Riemann
