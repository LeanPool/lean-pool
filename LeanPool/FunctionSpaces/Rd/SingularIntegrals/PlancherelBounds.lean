/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.SingularIntegrals.DilationFamilies

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Plancherel bounds for families of convolution operators

Let `V` be a finite-dimensional real inner product space with Lebesgue measure, and let
`(θ_j)_{j ∈ ℕ}` be integrable kernels with **Fourier overlap** `B`:
`∑_j |𝓕θ_j(ξ)|² ≤ B` for almost every `ξ`. This file proves the `L_2` bounds of the analysis
operator `f ↦ (θ_j ⋆ f)_j` and of the synthesis operators `(g_j)_j ↦ ∑_{j ∈ s} θ_j ⋆ g_j` for
finite sets `s`, by Plancherel's theorem for one convolution, `‖K ⋆ f‖_2² = ∫ |𝓕K|² |𝓕f|²`
(`Rd.enorm_convLp_sq`), and the convolution theorem on `L_2` (`Rd.fourier_convLp`).

* **The analysis bound** (`Rd.tsum_enorm_convLp_sq_le`, `Rd.lintegral_lqNorm_conv_sq_le`):
  `∑_j ‖θ_j ⋆ f‖_2² ≤ B ‖f‖_2²`, that is, `∫ ‖((θ_j ⋆ f)(x))_j‖_{ℓ_2}² dx ≤ B ∫ |f|²`.
* **The synthesis bound** (`Rd.enorm_sum_convLp_sq_le`, `Rd.lintegral_enorm_sum_conv_sq_le`):
  for every finite set `s` of indices, `‖∑_{j ∈ s} θ_j ⋆ g_j‖_2² ≤ B ∑_{j ∈ s} ‖g_j‖_2²`,
  hence `∫ |∑_{j ∈ s} θ_j ⋆ g_j|² ≤ B ∫ ‖(g_j(x))_j‖_{ℓ_2}² dx`, by the Cauchy–Schwarz
  inequality at each frequency (`enorm_sum_mul_sq_le`).
* **Calderón–Zygmund families** satisfy both bounds with their overlap `B`
  (`Rd.IsCZFamily.lintegral_lqNorm_conv_sq_le`, `Rd.IsCZFamily.lintegral_enorm_sum_conv_sq_le`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal FourierTransform

/-! ### Cauchy–Schwarz and squares of `L_2` norms -/

/-- **The Cauchy–Schwarz inequality for finite sums of products**:
`|∑_{j ∈ s} a_j b_j|² ≤ (∑_{j ∈ s} |a_j|²) (∑_{j ∈ s} |b_j|²)` in every seminormed ring, such
as `ℂ`, with values in `[0, ∞]` (Mathlib's `Finset.sum_mul_sq_le_sq_mul_sq` for the norms, after
the triangle inequality and `‖a b‖ ≤ ‖a‖ ‖b‖`). -/
theorem enorm_sum_mul_sq_le {R ι : Type*} [SeminormedRing R] (s : Finset ι) (a b : ι → R) :
    ‖∑ j ∈ s, a j * b j‖ₑ ^ 2 ≤ (∑ j ∈ s, ‖a j‖ₑ ^ 2) * ∑ j ∈ s, ‖b j‖ₑ ^ 2 := by
  have h1 : ‖∑ j ∈ s, a j * b j‖₊ ≤ ∑ j ∈ s, ‖a j‖₊ * ‖b j‖₊ :=
    (nnNorm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => nnNorm_mul_le _ _)
  have h2 : ‖∑ j ∈ s, a j * b j‖₊ ^ 2 ≤ (∑ j ∈ s, ‖a j‖₊ ^ 2) * ∑ j ∈ s, ‖b j‖₊ ^ 2 :=
    (pow_le_pow_left₀ zero_le h1 2).trans
      (Finset.sum_mul_sq_le_sq_mul_sq s (fun j => ‖a j‖₊) fun j => ‖b j‖₊)
  simp only [eNorm_eq_nnNorm]
  exact_mod_cast h2

namespace Rd

open ENNReal (lqNorm)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **The `L_2` norm of a convolution through its class**: for integrable `K` and `f ∈ L_2(V)`,
`∫ |K ⋆ f|² = ‖K ⋆ f‖_2²` with the convolution operator `Rd.convLp` on `L_2(V)`. -/
theorem lintegral_enorm_conv_sq_eq {K f : V → ℂ} (hK : Integrable K) (hf : MemLp f 2) :
    ∫⁻ x, ‖conv K f volume x‖ₑ ^ 2 = ‖convLp two_ne_top hK (hf.toLp f)‖ₑ ^ 2 := by
  rw [enorm_sq_eq_lintegral]
  refine lintegral_congr_ae ?_
  filter_upwards [convLp_apply_ae two_ne_top hK (hf.toLp f)] with x hx
  rw [hx, conv_congr_ae hf.coeFn_toLp]

/-! ### The analysis bound -/

/-- **The analysis bound on `L_2`**: for integrable kernels `θ_j` with Fourier overlap `B`,
`∑_j |𝓕θ_j(ξ)|² ≤ B` for almost every `ξ`, and every `f ∈ L_2(V)`,
`∑_j ‖θ_j ⋆ f‖_2² ≤ B ‖f‖_2²`. By `Rd.enorm_convLp_sq` the left side is
`∫ (∑_j |𝓕θ_j|²) |𝓕f|²` (Mathlib's `lintegral_tsum`), and Plancherel's theorem gives
`∫ |𝓕f|² = ‖f‖_2²`. -/
theorem tsum_enorm_convLp_sq_le {θ : ℕ → V → ℂ} (hθ : ∀ j, Integrable (θ j)) {B : ℝ≥0∞}
    (hB : ∀ᵐ ξ ∂volume, ∑' j, ‖𝓕 (θ j) ξ‖ₑ ^ 2 ≤ B) (f : Lp ℂ 2 (volume : Measure V)) :
    ∑' j, ‖convLp two_ne_top (hθ j) f‖ₑ ^ 2 ≤ B * ‖f‖ₑ ^ 2 := by
  have hF : AEMeasurable (fun ξ => ‖(𝓕 f : Lp ℂ 2 (volume : Measure V)) ξ‖ₑ ^ 2) volume :=
    (Lp.aestronglyMeasurable _).eNorm.pow_const 2
  have hm : ∀ j, AEMeasurable (fun ξ => ‖𝓕 (θ j) ξ‖ₑ ^ 2 *
      ‖(𝓕 f : Lp ℂ 2 (volume : Measure V)) ξ‖ₑ ^ 2) volume := fun j =>
    ((memLp_top_fourier (hθ j)).aestronglyMeasurable.eNorm.pow_const 2).mul hF
  rw [tsum_congr fun j => enorm_convLp_sq (hθ j) f, ← lintegral_tsum hm]
  calc ∫⁻ ξ, ∑' j, ‖𝓕 (θ j) ξ‖ₑ ^ 2 * ‖(𝓕 f : Lp ℂ 2 (volume : Measure V)) ξ‖ₑ ^ 2
      = ∫⁻ ξ, (∑' j, ‖𝓕 (θ j) ξ‖ₑ ^ 2) * ‖(𝓕 f : Lp ℂ 2 (volume : Measure V)) ξ‖ₑ ^ 2 := by
        simp_rw [ENNReal.tsum_mul_right]
    _ ≤ ∫⁻ ξ, B * ‖(𝓕 f : Lp ℂ 2 (volume : Measure V)) ξ‖ₑ ^ 2 := by
        refine lintegral_mono_ae ?_
        filter_upwards [hB] with ξ hξ
        gcongr
    _ = B * ‖f‖ₑ ^ 2 := by
        rw [lintegral_const_mul'' _ hF, ← enorm_sq_eq_lintegral, enorm_fourier_Lp_two]

/-- **The analysis bound on `L_2`, for functions**: for integrable kernels `θ_j` with Fourier
overlap `B` (almost everywhere) and every `f ∈ L_2(V)`,
`∫ ‖((θ_j ⋆ f)(x))_j‖_{ℓ_2}² dx ≤ B ∫ |f|²` (`Rd.tsum_enorm_convLp_sq_le` for the class of `f`,
and Mathlib's `lintegral_tsum`). -/
theorem lintegral_lqNorm_conv_sq_le {θ : ℕ → V → ℂ} (hθ : ∀ j, Integrable (θ j)) {B : ℝ≥0∞}
    (hB : ∀ᵐ ξ ∂volume, ∑' j, ‖𝓕 (θ j) ξ‖ₑ ^ 2 ≤ B) {f : V → ℂ} (hf : MemLp f 2) :
    ∫⁻ x, lqNorm 2 (fun j => ‖conv (θ j) f volume x‖ₑ) ^ 2 ≤ B * ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  simp_rw [ENNReal.lqNorm_two_sq]
  rw [lintegral_tsum fun j => (aestronglyMeasurable_conv (hθ j).aestronglyMeasurable
      hf.aestronglyMeasurable).eNorm.pow_const 2, lintegral_enorm_sq_eq_enorm_toLp hf]
  calc ∑' j, ∫⁻ x, ‖conv (θ j) f volume x‖ₑ ^ 2
      = ∑' j, ‖convLp two_ne_top (hθ j) (hf.toLp f)‖ₑ ^ 2 :=
        tsum_congr fun j => lintegral_enorm_conv_sq_eq (hθ j) hf
    _ ≤ B * ‖hf.toLp f‖ₑ ^ 2 := tsum_enorm_convLp_sq_le hθ hB _

/-! ### The synthesis bound -/

/-- **The Fourier transform of a finite sum of convolutions**: for integrable kernels `θ_j`,
functions `g_j ∈ L_2(V)` and a finite set `s`,
`𝓕(∑_{j ∈ s} θ_j ⋆ g_j) = ∑_{j ∈ s} 𝓕θ_j 𝓕g_j` almost everywhere (Mathlib's
`FourierTransform.fourier_sum` and `Rd.fourier_convLp`). -/
theorem fourier_sum_convLp {θ : ℕ → V → ℂ} (hθ : ∀ j, Integrable (θ j)) (s : Finset ℕ)
    (g : ℕ → Lp ℂ 2 (volume : Measure V)) :
    ((𝓕 (∑ j ∈ s, convLp two_ne_top (hθ j) (g j)) : Lp ℂ 2 (volume : Measure V)) : V → ℂ)
      =ᵐ[volume] fun ξ => ∑ j ∈ s, 𝓕 (θ j) ξ * (𝓕 (g j) : Lp ℂ 2 (volume : Measure V)) ξ := by
  rw [FourierTransform.fourier_sum]
  filter_upwards [Lp.coeFn_fun_finsetSum s fun j => 𝓕 (convLp two_ne_top (hθ j) (g j)),
    ae_all_iff.2 fun j => fourier_convLp (hθ j) (g j)] with ξ h1 h2
  rw [h1]
  exact Finset.sum_congr rfl fun j _ => h2 j

/-- **The synthesis bound on `L_2`**: for integrable kernels `θ_j` with Fourier overlap `B`
(almost everywhere), functions `g_j ∈ L_2(V)` and every finite set `s` of indices,
`‖∑_{j ∈ s} θ_j ⋆ g_j‖_2² ≤ B ∑_{j ∈ s} ‖g_j‖_2²`. At each frequency `ξ`, the Fourier transform
of the sum is `∑_{j ∈ s} 𝓕θ_j(ξ) 𝓕g_j(ξ)` (`Rd.fourier_sum_convLp`), whose square is at most
`(∑_j |𝓕θ_j(ξ)|²) ∑_{j ∈ s} |𝓕g_j(ξ)|² ≤ B ∑_{j ∈ s} |𝓕g_j(ξ)|²` by the Cauchy–Schwarz
inequality (`enorm_sum_mul_sq_le`); Plancherel's theorem finishes. -/
theorem enorm_sum_convLp_sq_le {θ : ℕ → V → ℂ} (hθ : ∀ j, Integrable (θ j)) {B : ℝ≥0∞}
    (hB : ∀ᵐ ξ ∂volume, ∑' j, ‖𝓕 (θ j) ξ‖ₑ ^ 2 ≤ B) (s : Finset ℕ)
    (g : ℕ → Lp ℂ 2 (volume : Measure V)) :
    ‖∑ j ∈ s, convLp two_ne_top (hθ j) (g j)‖ₑ ^ 2 ≤ B * ∑ j ∈ s, ‖g j‖ₑ ^ 2 := by
  have hG : ∀ j ∈ s, AEMeasurable
      (fun ξ => ‖(𝓕 (g j) : Lp ℂ 2 (volume : Measure V)) ξ‖ₑ ^ 2) volume := fun j _ =>
    (Lp.aestronglyMeasurable _).eNorm.pow_const 2
  rw [← enorm_fourier_Lp_two, enorm_sq_eq_lintegral]
  calc ∫⁻ ξ, ‖((𝓕 (∑ j ∈ s, convLp two_ne_top (hθ j) (g j)) :
        Lp ℂ 2 (volume : Measure V)) : V → ℂ) ξ‖ₑ ^ 2
      ≤ ∫⁻ ξ, B * ∑ j ∈ s, ‖(𝓕 (g j) : Lp ℂ 2 (volume : Measure V)) ξ‖ₑ ^ 2 := by
        refine lintegral_mono_ae ?_
        filter_upwards [fourier_sum_convLp hθ s g, hB] with ξ h1 h2
        rw [h1]
        refine (enorm_sum_mul_sq_le s _ _).trans ?_
        gcongr
        exact (sum_le_tsum s).trans h2
    _ = B * ∑ j ∈ s, ‖g j‖ₑ ^ 2 := by
        rw [lintegral_const_mul'' _ (Finset.aemeasurable_fun_sum s hG), lintegral_finsetSum' s hG]
        congr 1
        exact Finset.sum_congr rfl fun j _ => by rw [← enorm_sq_eq_lintegral, enorm_fourier_Lp_two]

/-- **The synthesis bound on `L_2`, for functions**: for integrable kernels `θ_j` with Fourier
overlap `B` (almost everywhere), functions `g_j ∈ L_2(V)` and every finite set `s` of indices,
`∫ |∑_{j ∈ s} θ_j ⋆ g_j|² ≤ B ∫ ‖(g_j(x))_j‖_{ℓ_2}² dx` (`Rd.enorm_sum_convLp_sq_le` for the
classes of the `g_j`). -/
theorem lintegral_enorm_sum_conv_sq_le {θ : ℕ → V → ℂ} (hθ : ∀ j, Integrable (θ j))
    {B : ℝ≥0∞} (hB : ∀ᵐ ξ ∂volume, ∑' j, ‖𝓕 (θ j) ξ‖ₑ ^ 2 ≤ B) (s : Finset ℕ)
    {g : ℕ → V → ℂ} (hg : ∀ j, MemLp (g j) 2) :
    ∫⁻ x, ‖∑ j ∈ s, conv (θ j) (g j) volume x‖ₑ ^ 2 ≤
      B * ∫⁻ x, lqNorm 2 (fun j => ‖g j x‖ₑ) ^ 2 := by
  have hv : ⇑(∑ j ∈ s, convLp two_ne_top (hθ j) ((hg j).toLp (g j))) =ᵐ[volume]
      fun x => ∑ j ∈ s, conv (θ j) (g j) volume x := by
    filter_upwards [Lp.coeFn_fun_finsetSum s fun j =>
      convLp two_ne_top (hθ j) ((hg j).toLp (g j)), ae_all_iff.2 fun j =>
      convLp_apply_ae two_ne_top (hθ j) ((hg j).toLp (g j))] with x h1 h2
    rw [h1]
    exact Finset.sum_congr rfl fun j _ => by rw [h2 j, conv_congr_ae (hg j).coeFn_toLp]
  have hG : ∀ j ∈ s, AEMeasurable (fun x => ‖g j x‖ₑ ^ 2) volume := fun j _ =>
    (hg j).aestronglyMeasurable.eNorm.pow_const 2
  calc ∫⁻ x, ‖∑ j ∈ s, conv (θ j) (g j) volume x‖ₑ ^ 2
      = ‖∑ j ∈ s, convLp two_ne_top (hθ j) ((hg j).toLp (g j))‖ₑ ^ 2 := by
        rw [enorm_sq_eq_lintegral]
        exact lintegral_congr_ae (hv.mono fun x hx => by dsimp only at hx ⊢; rw [hx])
    _ ≤ B * ∑ j ∈ s, ‖(hg j).toLp (g j)‖ₑ ^ 2 := enorm_sum_convLp_sq_le hθ hB s _
    _ = B * ∫⁻ x, ∑ j ∈ s, ‖g j x‖ₑ ^ 2 := by
        rw [lintegral_finsetSum' s hG]
        congr 1
        exact Finset.sum_congr rfl fun j _ => (lintegral_enorm_sq_eq_enorm_toLp (hg j)).symm
    _ ≤ B * ∫⁻ x, lqNorm 2 (fun j => ‖g j x‖ₑ) ^ 2 := by
        gcongr with x
        rw [ENNReal.lqNorm_two_sq]
        exact sum_le_tsum s

/-! ### Calderón–Zygmund families -/

/-- **The analysis bound for a Calderón–Zygmund family** with overlap `B`:
`∑_j ‖θ_j ⋆ f‖_2² ≤ B ‖f‖_2²` for every `f ∈ L_2(V)` (`Rd.tsum_enorm_convLp_sq_le`). -/
theorem IsCZFamily.tsum_enorm_convLp_sq_le {θ : ℕ → V → ℂ} {B H : ℝ≥0∞}
    (h : IsCZFamily θ B H) (f : Lp ℂ 2 (volume : Measure V)) :
    ∑' j, ‖convLp two_ne_top (h.integrable j) f‖ₑ ^ 2 ≤ B * ‖f‖ₑ ^ 2 :=
  Rd.tsum_enorm_convLp_sq_le h.integrable (ae_of_all _ h.overlap) f

/-- **The analysis bound for a Calderón–Zygmund family, for functions**: with overlap `B`,
`∫ ‖((θ_j ⋆ f)(x))_j‖_{ℓ_2}² dx ≤ B ∫ |f|²` for every `f ∈ L_2(V)`
(`Rd.lintegral_lqNorm_conv_sq_le`). -/
theorem IsCZFamily.lintegral_lqNorm_conv_sq_le {θ : ℕ → V → ℂ} {B H : ℝ≥0∞}
    (h : IsCZFamily θ B H) {f : V → ℂ} (hf : MemLp f 2) :
    ∫⁻ x, lqNorm 2 (fun j => ‖conv (θ j) f volume x‖ₑ) ^ 2 ≤ B * ∫⁻ x, ‖f x‖ₑ ^ 2 :=
  Rd.lintegral_lqNorm_conv_sq_le h.integrable (ae_of_all _ h.overlap) hf

/-- **The synthesis bound for a Calderón–Zygmund family** with overlap `B`:
`‖∑_{j ∈ s} θ_j ⋆ g_j‖_2² ≤ B ∑_{j ∈ s} ‖g_j‖_2²` for all `g_j ∈ L_2(V)` and every finite set
`s` (`Rd.enorm_sum_convLp_sq_le`). -/
theorem IsCZFamily.enorm_sum_convLp_sq_le {θ : ℕ → V → ℂ} {B H : ℝ≥0∞}
    (h : IsCZFamily θ B H) (s : Finset ℕ) (g : ℕ → Lp ℂ 2 (volume : Measure V)) :
    ‖∑ j ∈ s, convLp two_ne_top (h.integrable j) (g j)‖ₑ ^ 2 ≤ B * ∑ j ∈ s, ‖g j‖ₑ ^ 2 :=
  Rd.enorm_sum_convLp_sq_le h.integrable (ae_of_all _ h.overlap) s g

/-- **The synthesis bound for a Calderón–Zygmund family, for functions**: with overlap `B`,
`∫ |∑_{j ∈ s} θ_j ⋆ g_j|² ≤ B ∫ ‖(g_j(x))_j‖_{ℓ_2}² dx` for all `g_j ∈ L_2(V)` and every finite
set `s` (`Rd.lintegral_enorm_sum_conv_sq_le`). -/
theorem IsCZFamily.lintegral_enorm_sum_conv_sq_le {θ : ℕ → V → ℂ} {B H : ℝ≥0∞}
    (h : IsCZFamily θ B H) (s : Finset ℕ) {g : ℕ → V → ℂ} (hg : ∀ j, MemLp (g j) 2) :
    ∫⁻ x, ‖∑ j ∈ s, conv (θ j) (g j) volume x‖ₑ ^ 2 ≤
      B * ∫⁻ x, lqNorm 2 (fun j => ‖g j x‖ₑ) ^ 2 :=
  Rd.lintegral_enorm_sum_conv_sq_le h.integrable (ae_of_all _ h.overlap) s hg

end Rd
