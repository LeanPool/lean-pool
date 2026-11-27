/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.Reproducing
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Data.Finsupp.Pointwise
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Linter.Style
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.TypeStar
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Existence of a Weyl system with a Gaussian vacuum (construction, part 1)

Given an additive map `u : X → K` into a complex inner product space, the Gaussian kernel
`𝒦(F, G) = exp(-‖u F‖²/2 - ‖u G‖²/2 + ⟪u F, u G⟫)` is positive semidefinite.  This is the
input for the construction of the (exponential Fock / GNS) Hilbert space carrying the Weyl
operators.

## Main results

* `VacuumBellSeparation.posSemidef_gram_complex`: Gram matrices of arbitrary (possibly infinite)
  families of vectors are positive semidefinite.
* `VacuumBellSeparation.posSemidef_pow_entrywise`: entrywise powers of a positive semidefinite
  complex matrix are positive semidefinite (Schur product theorem).
* `VacuumBellSeparation.posSemidef_exp_entrywise`: the entrywise exponential of a positive
  semidefinite complex matrix is positive semidefinite.
* `VacuumBellSeparation.posSemidef_weylKernel`, `VacuumBellSeparation.weylKernel_sum_nonneg`:
  positive semidefiniteness of the Gaussian kernel.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped InnerProductSpace ComplexConjugate ComplexOrder
open Matrix

section PSD

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The Gram matrix of an arbitrary (possibly infinite) family of vectors is positive
semidefinite. -/
theorem posSemidef_gram_complex (v : ι → E) : (gram ℂ v).PosSemidef := by
  refine ⟨isHermitian_gram ℂ v, fun x => ?_⟩
  have h : (x.sum fun i xi => x.sum fun j xj => star xi * gram ℂ v i j * xj) =
      ⟪x.sum fun i xi => xi • v i, x.sum fun j xj => xj • v j⟫_ℂ := by
    rw [Finsupp.sum_inner]
    refine Finsupp.sum_congr fun i _ => ?_
    rw [Finsupp.inner_sum]
    refine Finsupp.sum_congr fun j _ => ?_
    rw [gram_apply, inner_smul_left, inner_smul_right, show star (x i) = conj (x i) from rfl]
    ring
  rw [h, inner_self_eq_norm_sq_to_K]
  have h0 : (0 : ℝ) ≤ ‖x.sum fun i xi => xi • v i‖ ^ 2 := sq_nonneg _
  exact_mod_cast (RCLike.ofReal_nonneg (K := ℂ)).mpr h0

/-- Entrywise powers of a positive semidefinite complex matrix are positive semidefinite
(Schur product theorem). -/
theorem posSemidef_pow_entrywise {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (n : ℕ) :
    (Matrix.of fun i j => A i j ^ n).PosSemidef := by
  induction n with
  | zero =>
    have h1 : (Matrix.of fun i j => A i j ^ 0) = gram ℂ (fun _ : ι => (1 : ℂ)) := by
      ext i j
      simp [gram_apply]
    rw [h1]
    exact posSemidef_gram_complex _
  | succ n ih =>
    have h1 : (Matrix.of fun i j => A i j ^ (n + 1)) = (Matrix.of fun i j => A i j ^ n) ⊙ A := by
      ext i j
      simp [hadamard_apply, pow_succ]
    rw [h1]
    exact ih.hadamard hA

/-- The entrywise exponential of a positive semidefinite complex matrix is positive
semidefinite. -/
theorem posSemidef_exp_entrywise {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    (Matrix.of fun i j => Complex.exp (A i j)).PosSemidef := by
  refine ⟨?_, fun x => ?_⟩
  · ext i j
    simp only [conjTranspose_apply, of_apply]
    rw [← hA.isHermitian.apply i j]
    exact (Complex.exp_conj (A j i)).symm
  · have hser : ∀ z : ℂ, HasSum (fun n : ℕ => z ^ n / (n.factorial : ℂ)) (Complex.exp z) := by
      intro z
      rw [Complex.exp_eq_exp_ℂ]
      exact NormedSpace.expSeries_div_hasSum_exp z
    have key : HasSum (fun n : ℕ => x.sum fun i xi => x.sum fun j xj =>
          star xi * (A i j ^ n / (n.factorial : ℂ)) * xj)
        (x.sum fun i xi => x.sum fun j xj => star xi * Complex.exp (A i j) * xj) := by
      simp only [Finsupp.sum]
      refine hasSum_sum fun i _ => hasSum_sum fun j _ => ?_
      exact ((hser (A i j)).mul_left (star (x i))).mul_right (x j)
    refine key.nonneg fun n => ?_
    have hn := (posSemidef_pow_entrywise hA n).2 x
    have hfac : (0 : ℂ) ≤ ((n.factorial : ℝ)⁻¹ : ℝ) := Complex.zero_le_real.mpr (by positivity)
    have heq : (x.sum fun i xi => x.sum fun j xj => star xi * (A i j ^ n / (n.factorial : ℂ)) * xj)
        = ((n.factorial : ℝ)⁻¹ : ℝ) * (x.sum fun i xi => x.sum fun j xj =>
          star xi * (Matrix.of fun i j => A i j ^ n) i j * xj) := by
      simp only [Finsupp.mul_sum, of_apply]
      refine Finsupp.sum_congr fun i _ => Finsupp.sum_congr fun j _ => ?_
      push_cast
      ring
    rw [heq]
    exact mul_nonneg hfac hn

end PSD

/-- The Gaussian kernel `𝒦(F, G) = exp(-‖uF‖²/2 - ‖uG‖²/2 + ⟪uF, uG⟫)`. -/
noncomputable def weylKernel {X K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (u : X → K) (F G : X) : ℂ :=
  Complex.exp (((-(‖u F‖ ^ 2) / 2 - ‖u G‖ ^ 2 / 2 : ℝ) : ℂ) + ⟪u F, u G⟫_ℂ)

section Kernel

variable {X K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (u : X → K)

theorem weylKernel_conj (F G : X) : conj (weylKernel u F G) = weylKernel u G F := by
  unfold weylKernel
  rw [← Complex.exp_conj, map_add, Complex.conj_ofReal, inner_conj_symm,
    show (-(‖u F‖ ^ 2) / 2 - ‖u G‖ ^ 2 / 2 : ℝ) = -(‖u G‖ ^ 2) / 2 - ‖u F‖ ^ 2 / 2 by ring]

/-- Factorization `𝒦(F, G) = exp ⟪uF, uG⟫ · conj (a F) · a G` with `a F = exp(-‖uF‖²/2)`. -/
theorem weylKernel_eq (F G : X) :
    weylKernel u F G = Complex.exp ⟪u F, u G⟫_ℂ *
      (conj (Complex.exp ((-(‖u F‖ ^ 2 / 2) : ℝ) : ℂ)) *
        Complex.exp ((-(‖u G‖ ^ 2 / 2) : ℝ) : ℂ)) := by
  unfold weylKernel
  rw [← Complex.exp_conj, Complex.conj_ofReal, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The Gaussian kernel is a positive semidefinite matrix. -/
theorem posSemidef_weylKernel : (Matrix.of fun F G => weylKernel u F G).PosSemidef := by
  have h1 := posSemidef_exp_entrywise (posSemidef_gram_complex u)
  have h2 := posSemidef_gram_complex (fun F : X => Complex.exp ((-(‖u F‖ ^ 2 / 2) : ℝ) : ℂ))
  have h3 := h1.hadamard h2
  convert h3 using 1
  ext F G
  simp only [of_apply, hadamard_apply, gram_apply, RCLike.inner_apply']
  exact weylKernel_eq u F G

/-- Positive semidefiniteness of the Gaussian kernel, in `Finsupp` form. -/
theorem weylKernel_sum_nonneg (c : X →₀ ℂ) :
    0 ≤ (c.sum fun F a => c.sum fun G b => conj a * b * weylKernel u F G).re := by
  have h := (posSemidef_weylKernel u).2 c
  have h' : (c.sum fun F a => c.sum fun G b => conj a * b * weylKernel u F G) =
      (c.sum fun F a => c.sum fun G b =>
        star a * (Matrix.of fun F G => weylKernel u F G) F G * b) := by
    refine Finsupp.sum_congr fun F _ => Finsupp.sum_congr fun G _ => ?_
    rw [of_apply, show star (c F) = conj (c F) from rfl]
    ring
  rw [h']
  exact (Complex.nonneg_iff.mp h).1

/-! ### The Gaussian kernel as a reproducing kernel -/

/-- The Gaussian kernel as an operator-valued kernel (with fibre `ℂ`), in the form used by
Mathlib's reproducing-kernel-Hilbert-space API, so that `⟪k_F, k_G⟫ = ⟪K G F 1, 1⟫ = 𝒦(F, G)`. -/
noncomputable def weylRKHSKernel : Matrix X X (ℂ →L[ℂ] ℂ) :=
  Matrix.of fun F G => weylKernel u F G • (1 : ℂ →L[ℂ] ℂ)

theorem posSemidef_weylRKHSKernel : (weylRKHSKernel u).PosSemidef := by
  rw [RKHS.posSemidef_iff_re_sum_kernel']
  refine ⟨?_, fun vv => ?_⟩
  · change (weylRKHSKernel u)ᴴ = weylRKHSKernel u
    refine Matrix.ext fun F G => ?_
    simp only [weylRKHSKernel, conjTranspose_apply, of_apply, star_smul, star_one]
    rw [show star (weylKernel u G F) = conj (weylKernel u G F) from rfl, weylKernel_conj]
  · have h := weylKernel_sum_nonneg u vv
    rw [RCLike.re_to_complex]
    convert h using 2
    refine Finsupp.sum_congr fun F _ => Finsupp.sum_congr fun G _ => ?_
    simp only [weylRKHSKernel, of_apply, smul_apply,
      one_apply_eq_self, smul_eq_mul, RCLike.inner_apply, map_mul, weylKernel_conj]
    ring

instance : Fact (weylRKHSKernel u).PosSemidef := ⟨posSemidef_weylRKHSKernel u⟩

/-- The Hilbert space of the Weyl system: the reproducing kernel Hilbert space of the Gaussian
kernel (the completion of the pre-Hilbert space `X × ℂ →₀ ℂ` with the kernel inner product). -/
abbrev WeylSpace : Type _ := RKHS.OfKernel (weylRKHSKernel u)

example : CompleteSpace (WeylSpace u) := inferInstance

/-- The kernel vectors `k_F` of the Weyl space (later: `k_F = W(F) Ω`). -/
noncomputable def weylKerVec (F : X) : WeylSpace u := RKHS.kerFun (WeylSpace u) F 1

/-- The reproducing property: `⟪k_F, k_G⟫ = 𝒦(F, G)`. -/
theorem inner_weylKerVec (F G : X) :
    ⟪weylKerVec u F, weylKerVec u G⟫_ℂ = weylKernel u F G := by
  unfold weylKerVec
  rw [← RKHS.kernel_inner, RKHS.OfKernel.kernel_ofKernel]
  simp only [weylRKHSKernel, of_apply, smul_apply,
    one_apply_eq_self, smul_eq_mul, mul_one, one_mul, RCLike.inner_apply,
    weylKernel_conj]

/-- The kernel vectors span a dense subspace of the Weyl space. -/
theorem weylKerVec_dense :
    (Submodule.span ℂ (Set.range (weylKerVec u))).topologicalClosure = ⊤ := by
  rw [eq_top_iff, ← RKHS.kerFun_dense (WeylSpace u)]
  refine Submodule.topologicalClosure_mono (Submodule.span_le.mpr ?_)
  rintro _ ⟨F, v, rfl⟩
  have hv : RKHS.kerFun (WeylSpace u) F v = v • weylKerVec u F := by
    have h1 : v = v • (1 : ℂ) := by simp
    conv_lhs => rw [h1]
    rw [map_smul, weylKerVec]
  rw [hv]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨F, rfl⟩)

/-! ### Weyl operators on the pre-Hilbert space -/

/-- The Weyl phase `exp(-i Im⟪uF, uG⟫)`. -/
noncomputable def weylPhase (F G : X) : ℂ :=
  Complex.exp (-(Complex.I * ((⟪u F, u G⟫_ℂ).im : ℂ)))

/-- Translation covariance of the Gaussian kernel:
`conj φ(F,G) · φ(F,G') · 𝒦(F+G, F+G') = 𝒦(G, G')`. -/
theorem weylKernel_add_add [Add X] (hu : ∀ F G, u (F + G) = u F + u G) (F G G' : X) :
    conj (weylPhase u F G) * weylPhase u F G' * weylKernel u (F + G) (F + G') =
      weylKernel u G G' := by
  simp only [weylPhase, weylKernel, hu, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  have ha_re : (⟪u F, u F⟫_ℂ).re = ‖u F‖ ^ 2 := by
    have := inner_self_eq_norm_sq (𝕜 := ℂ) (u F)
    rwa [RCLike.re_to_complex] at this
  have ha_im : (⟪u F, u F⟫_ℂ).im = 0 := by
    have := inner_self_im (𝕜 := ℂ) (u F)
    rwa [RCLike.im_to_complex] at this
  have h1 := norm_add_sq (𝕜 := ℂ) (u F) (u G)
  have h2 := norm_add_sq (𝕜 := ℂ) (u F) (u G')
  rw [RCLike.re_to_complex] at h1 h2
  have hc : ⟪u G, u F⟫_ℂ = conj ⟪u F, u G⟫_ℂ := (inner_conj_symm (u G) (u F)).symm
  rw [h1, h2, inner_add_left, inner_add_right, inner_add_right, hc]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, map_neg, map_mul,
      Complex.conj_I, Complex.conj_ofReal, ha_re]
    ring
  · simp only [Complex.add_im, Complex.neg_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_im, map_neg, map_mul,
      Complex.conj_I, Complex.conj_ofReal, ha_im]
    ring

/-- The kernel inner product of two point masses in the pre-Hilbert space `X × ℂ →₀ ℂ`. -/
theorem inner_H₀_single (y x : X) (v w a b : ℂ) :
    @inner ℂ (RKHS.H₀ (weylRKHSKernel u)) _ (Finsupp.single (y, v) a) (Finsupp.single (x, w) b) =
      conj a * b * conj v * w * weylKernel u y x := by
  have : @inner ℂ (RKHS.H₀ (weylRKHSKernel u)) _ (Finsupp.single (y, v) a)
      (Finsupp.single (x, w) b) =
      (Finsupp.single (y, v) a).sum fun ⟨y', v'⟩ z => (Finsupp.single (x, w) b).sum
        fun ⟨x', w'⟩ c => star z * c * ⟪weylRKHSKernel u x' y' v', w'⟫_ℂ := rfl
  rw [this]
  first
    | (simp only [weylRKHSKernel, of_apply, smul_apply,
        one_apply_eq_self, smul_eq_mul, RCLike.inner_apply, map_mul, weylKernel_conj,
        star_zero, zero_mul, mul_zero, Finsupp.sum_single_index]
       rw [show star a = conj a from rfl]
       ring)



/-- The Weyl operator on the pre-Hilbert space: `δ_(G,v) ↦ φ(F,G) δ_(F+G,v)`. -/
noncomputable def weylOp₀ [Add X] (F : X) :
    RKHS.H₀ (weylRKHSKernel u) →ₗ[ℂ] RKHS.H₀ (weylRKHSKernel u) :=
  Finsupp.lsum ℂ fun p : X × ℂ => weylPhase u F p.1 • Finsupp.lsingle (F + p.1, p.2)

theorem weylOp₀_single [Add X] (F G : X) (v a : ℂ) :
    weylOp₀ u F (Finsupp.single (G, v) a) = weylPhase u F G • Finsupp.single (F + G, v) a := by
  simp [weylOp₀]

/-- The Weyl operators preserve the (pre-)inner product. -/
theorem inner_weylOp₀ [Add X] (hu : ∀ F G, u (F + G) = u F + u G) (F : X)
    (f g : RKHS.H₀ (weylRKHSKernel u)) :
    ⟪weylOp₀ u F f, weylOp₀ u F g⟫_ℂ = ⟪f, g⟫_ℂ := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, inner_zero_left]
  | add f₁ f₂ h₁ h₂ => simp only [map_add, inner_add_left, h₁, h₂]
  | single p a =>
    induction g using Finsupp.induction_linear with
    | zero => simp only [map_zero, inner_zero_right]
    | add g₁ g₂ h₁ h₂ => simp only [map_add, inner_add_right, h₁, h₂]
    | single q b =>
      obtain ⟨G, v⟩ := p
      obtain ⟨G', w⟩ := q
      rw [weylOp₀_single, weylOp₀_single, inner_smul_left, inner_smul_right, inner_H₀_single,
        inner_H₀_single, ← weylKernel_add_add u hu F G G']
      ring

/-! ### Extension to the completion -/

/-- The Weyl operator as a linear isometry of the pre-Hilbert space. -/
noncomputable def weylIso₀ [Add X] (hu : ∀ F G, u (F + G) = u F + u G) (F : X) :
    RKHS.H₀ (weylRKHSKernel u) →ₗᵢ[ℂ] RKHS.H₀ (weylRKHSKernel u) :=
  (weylOp₀ u F).isometryOfInner (inner_weylOp₀ u hu F)

/-- The Weyl operator on the Weyl space, extended by continuity from the pre-Hilbert space. -/
noncomputable def weylOp [Add X] (hu : ∀ F G, u (F + G) = u F + u G) (F : X) :
    WeylSpace u →ₗᵢ[ℂ] WeylSpace u :=
  (UniformSpace.Completion.toComplₗᵢ.comp (weylIso₀ u hu F)).fromCompletion

theorem weylOp_coe [Add X] (hu : ∀ F G, u (F + G) = u F + u G) (F : X)
    (f : RKHS.H₀ (weylRKHSKernel u)) :
    weylOp u hu F (f : WeylSpace u) = (weylOp₀ u F f : WeylSpace u) := by
  rw [weylOp, LinearIsometry.fromCompletion_apply_coe]
  rfl

/-- Weyl relation on the pre-Hilbert space: `W(F) W(F') = φ(F,F') W(F + F')`. -/
theorem weylOp₀_comp [AddSemigroup X] (hu : ∀ F G, u (F + G) = u F + u G) (F F' : X)
    (f : RKHS.H₀ (weylRKHSKernel u)) :
    weylOp₀ u F (weylOp₀ u F' f) = weylPhase u F F' • weylOp₀ u (F + F') f := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, smul_zero]
  | add f g hf hg => simp only [map_add, smul_add, hf, hg]
  | single p a =>
    obtain ⟨G, v⟩ := p
    rw [weylOp₀_single, map_smul, weylOp₀_single, weylOp₀_single, smul_smul, smul_smul,
      add_assoc]
    congr 1
    simp only [weylPhase, hu, ← Complex.exp_add]
    congr 1
    simp only [inner_add_left, inner_add_right, Complex.add_im]
    push_cast
    ring

/-! ### The vacuum -/

omit [InnerProductSpace ℂ K] in
theorem map_zero_of_additive [AddZeroClass X] (hu : ∀ F G, u (F + G) = u F + u G) : u 0 = 0 := by
  have h := hu 0 0
  rw [add_zero] at h
  simpa using (congrArg (fun z => z - u 0) h).symm

/-- `⟪Ω, Ω⟫ = 1` for the vacuum `Ω = k_0`. -/
theorem inner_weylKerVec_zero_zero [AddZeroClass X] (hu : ∀ F G, u (F + G) = u F + u G) :
    ⟪weylKerVec u 0, weylKerVec u 0⟫_ℂ = 1 := by
  rw [inner_weylKerVec, weylKernel, map_zero_of_additive u hu]
  simp

/-- The vacuum `Ω = k_0` is a unit vector. -/
theorem norm_weylKerVec_zero [AddZeroClass X] (hu : ∀ F G, u (F + G) = u F + u G) :
    ‖weylKerVec u 0‖ = 1 := by
  have h := inner_weylKerVec_zero_zero u hu
  have h2 : ‖weylKerVec u 0‖ ^ 2 = 1 := by
    have h' := inner_self_eq_norm_sq (𝕜 := ℂ) (weylKerVec u 0)
    rw [h] at h'
    simpa using h'.symm
  rw [← Real.sqrt_sq (norm_nonneg (weylKerVec u 0)), h2, Real.sqrt_one]

/-- Vacuum expectation values of the kernel vectors: `⟪Ω, k_F⟫ = exp(-‖uF‖²/2)`. -/
theorem inner_weylKerVec_zero [AddZeroClass X] (hu : ∀ F G, u (F + G) = u F + u G) (F : X) :
    ⟪weylKerVec u 0, weylKerVec u F⟫_ℂ = ((Real.exp (-(‖u F‖ ^ 2 / 2)) : ℝ) : ℂ) := by
  rw [inner_weylKerVec, weylKernel, map_zero_of_additive u hu, inner_zero_left, add_zero,
    Complex.ofReal_exp, norm_zero]
  congr 1
  push_cast
  ring

/-! ### Point masses in the Weyl space -/

/-- The point masses `e_F = [δ_(F,1)]` of the Weyl space (`e_F = W(F) Ω` for `Ω = e_0`). -/
noncomputable def weylVec (F : X) : WeylSpace u :=
  ((Finsupp.single (F, (1 : ℂ)) (1 : ℂ) : RKHS.H₀ (weylRKHSKernel u)) : WeylSpace u)

theorem weylVec_def (F : X) :
    weylVec u F =
      ((Finsupp.single (F, (1 : ℂ)) (1 : ℂ) : RKHS.H₀ (weylRKHSKernel u)) : WeylSpace u) :=
  rfl

/-- `⟪e_F, e_G⟫ = 𝒦(F, G)`. -/
theorem inner_weylVec (F G : X) :
    ⟪weylVec u F, weylVec u G⟫_ℂ = weylKernel u F G := by
  have h := inner_H₀_single u F G 1 1 1 1
  simp only [map_one, one_mul, mul_one] at h
  exact (UniformSpace.Completion.inner_coe (𝕜 := ℂ) (E := RKHS.H₀ (weylRKHSKernel u))
    (Finsupp.single (F, (1 : ℂ)) (1 : ℂ)) (Finsupp.single (G, (1 : ℂ)) (1 : ℂ))).trans h

/-- `W(F) e_G = φ(F, G) e_(F+G)`. -/
theorem weylOp_weylVec [Add X] (hu : ∀ F G, u (F + G) = u F + u G) (F G : X) :
    weylOp u hu F (weylVec u G) = weylPhase u F G • weylVec u (F + G) := by
  simp only [weylVec_def]
  rw [weylOp_coe, weylOp₀_single, UniformSpace.Completion.coe_smul]

/-- Weyl relation on the Weyl space: `W(F) W(F') = φ(F,F') W(F + F')`. -/
theorem weylOp_comp [AddSemigroup X] (hu : ∀ F G, u (F + G) = u F + u G) (F F' : X)
    (x : WeylSpace u) :
    weylOp u hu F (weylOp u hu F' x) = weylPhase u F F' • weylOp u hu (F + F') x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    have h1 : Continuous fun a : WeylSpace u => weylOp u hu F (weylOp u hu F' a) :=
      (weylOp u hu F).continuous.comp (weylOp u hu F').continuous
    have h2 : Continuous fun a : WeylSpace u => weylPhase u F F' • weylOp u hu (F + F') a :=
      (weylOp u hu (F + F')).continuous.const_smul (weylPhase u F F')
    exact isClosed_eq h1 h2
  | ih f =>
    rw [weylOp_coe, weylOp_coe, weylOp_coe, weylOp₀_comp u hu, UniformSpace.Completion.coe_smul]

/-! ### Unitarity -/

theorem weylPhase_zero_left [AddZeroClass X] (hu : ∀ F G, u (F + G) = u F + u G) (G : X) :
    weylPhase u 0 G = 1 := by
  simp [weylPhase, map_zero_of_additive u hu]

theorem weylPhase_zero_right [AddZeroClass X] (hu : ∀ F G, u (F + G) = u F + u G) (F : X) :
    weylPhase u F 0 = 1 := by
  simp [weylPhase, map_zero_of_additive u hu]

omit [InnerProductSpace ℂ K] in
theorem map_neg_of_additive [AddGroup X] (hu : ∀ F G, u (F + G) = u F + u G) (F : X) :
    u (-F) = -u F := by
  have h := hu (-F) F
  rw [neg_add_cancel, map_zero_of_additive u hu] at h
  rw [← sub_eq_zero, sub_neg_eq_add, ← h]

/-- `φ(F, -F) = 1`, since `⟪uF, -uF⟫` is real. -/
theorem weylPhase_neg_right [AddGroup X] (hu : ∀ F G, u (F + G) = u F + u G) (F : X) :
    weylPhase u F (-F) = 1 := by
  have h : (⟪u F, u F⟫_ℂ).im = 0 := by
    have := inner_self_im (𝕜 := ℂ) (u F)
    rwa [RCLike.im_to_complex] at this
  rw [weylPhase, map_neg_of_additive u hu, inner_neg_right, Complex.neg_im, h]
  simp

theorem weylOp₀_zero [AddMonoid X] (hu : ∀ F G, u (F + G) = u F + u G)
    (f : RKHS.H₀ (weylRKHSKernel u)) : weylOp₀ u 0 f = f := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single p a =>
    obtain ⟨G, v⟩ := p
    rw [weylOp₀_single, weylPhase_zero_left u hu, one_smul, zero_add]

/-- `W(0) = 1`. -/
theorem weylOp_zero [AddMonoid X] (hu : ∀ F G, u (F + G) = u F + u G) (x : WeylSpace u) :
    weylOp u hu 0 x = x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (weylOp u hu 0).continuous continuous_id
  | ih f => rw [weylOp_coe, weylOp₀_zero u hu]

/-- `W(F) W(-F) = 1`. -/
theorem weylOp_neg_right [AddGroup X] (hu : ∀ F G, u (F + G) = u F + u G) (F : X)
    (x : WeylSpace u) : weylOp u hu F (weylOp u hu (-F) x) = x := by
  rw [weylOp_comp u hu, weylPhase_neg_right u hu, one_smul, add_neg_cancel, weylOp_zero u hu]

/-- The Weyl operator as a linear isometric equivalence of the Weyl space. -/
noncomputable def weylEquiv [AddGroup X] (hu : ∀ F G, u (F + G) = u F + u G) (F : X) :
    WeylSpace u ≃ₗᵢ[ℂ] WeylSpace u :=
  LinearIsometryEquiv.ofSurjective (weylOp u hu F) fun x =>
    ⟨weylOp u hu (-F) x, weylOp_neg_right u hu F x⟩

/-- The Weyl operator as a bounded operator on the Weyl space. -/
noncomputable def weylCLM [AddGroup X] (hu : ∀ F G, u (F + G) = u F + u G) (F : X) :
    WeylSpace u →L[ℂ] WeylSpace u :=
  (weylOp u hu F).toContinuousLinearMap

theorem weylCLM_apply [AddGroup X] (hu : ∀ F G, u (F + G) = u F + u G) (F : X)
    (x : WeylSpace u) : weylCLM u hu F x = weylOp u hu F x :=
  rfl

/-- The Weyl operators are unitary. -/
theorem weylCLM_mem_unitary [AddGroup X] (hu : ∀ F G, u (F + G) = u F + u G) (F : X) :
    weylCLM u hu F ∈ unitary (WeylSpace u →L[ℂ] WeylSpace u) := by
  have e : weylCLM u hu F =
      ((weylEquiv u hu F : WeylSpace u ≃ₗᵢ[ℂ] WeylSpace u) : WeylSpace u →L[ℂ] WeylSpace u) := by
    ext x
    rfl
  rw [e]
  have h := ((Unitary.linearIsometryEquiv :
    unitary (WeylSpace u →L[ℂ] WeylSpace u) ≃* (WeylSpace u ≃ₗᵢ[ℂ] WeylSpace u)).symm
      (weylEquiv u hu F)).property
  exact h

/-- The Weyl relation for the bounded Weyl operators. -/
theorem weylCLM_mul [AddGroup X] (hu : ∀ F G, u (F + G) = u F + u G) (F G : X) :
    weylCLM u hu F * weylCLM u hu G = weylPhase u F G • weylCLM u hu (F + G) := by
  refine ContinuousLinearMap.ext fun x => ?_
  exact weylOp_comp u hu F G x

/-! ### Vacuum and cyclicity -/

theorem weylOp_weylVec_zero [AddMonoid X] (hu : ∀ F G, u (F + G) = u F + u G) (F : X) :
    weylOp u hu F (weylVec u 0) = weylVec u F := by
  rw [weylOp_weylVec, weylPhase_zero_right u hu, one_smul, add_zero]

theorem inner_weylVec_zero_left [AddZeroClass X] (hu : ∀ F G, u (F + G) = u F + u G) (F : X) :
    ⟪weylVec u 0, weylVec u F⟫_ℂ = ((Real.exp (-(‖u F‖ ^ 2 / 2)) : ℝ) : ℂ) := by
  rw [inner_weylVec, ← inner_weylKerVec, inner_weylKerVec_zero u hu]

/-- The vacuum `Ω = e_0` is a unit vector. -/
theorem norm_weylVec_zero [AddZeroClass X] (hu : ∀ F G, u (F + G) = u F + u G) :
    ‖weylVec u 0‖ = 1 := by
  have h : ⟪weylVec u 0, weylVec u 0⟫_ℂ = 1 := by
    rw [inner_weylVec, ← inner_weylKerVec, inner_weylKerVec_zero_zero u hu]
  have h2 : ‖weylVec u 0‖ ^ 2 = 1 := by
    have h' := inner_self_eq_norm_sq (𝕜 := ℂ) (weylVec u 0)
    rw [h] at h'
    simpa using h'.symm
  rw [← Real.sqrt_sq (norm_nonneg (weylVec u 0)), h2, Real.sqrt_one]

/-- Vacuum expectation values: `⟪Ω, W(F) Ω⟫ = exp(-‖uF‖²/2)`. -/
theorem weyl_vacuum [AddGroup X] (hu : ∀ F G, u (F + G) = u F + u G) (F : X) :
    ⟪weylVec u 0, weylCLM u hu F (weylVec u 0)⟫_ℂ =
      ((Real.exp (-(‖u F‖ ^ 2 / 2)) : ℝ) : ℂ) := by
  rw [weylCLM_apply, weylOp_weylVec_zero u hu, inner_weylVec_zero_left u hu]

/-- In the pre-Hilbert space, `δ_(G,v) a` acts like `(v a) δ_(G,1)` on the left. -/
theorem inner_H₀_single_left (G : X) (v a : ℂ) (f : RKHS.H₀ (weylRKHSKernel u)) :
    @inner ℂ (RKHS.H₀ (weylRKHSKernel u)) _ (Finsupp.single (G, v) a) f =
      conj (v * a) * @inner ℂ (RKHS.H₀ (weylRKHSKernel u)) _ (Finsupp.single (G, 1) 1) f := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [inner_zero_right, mul_zero]
  | add f g hf hg => rw [inner_add_right, inner_add_right, hf, hg, mul_add]
  | single p b =>
    obtain ⟨y, w⟩ := p
    rw [inner_H₀_single, inner_H₀_single]
    simp only [map_mul, map_one]
    ring

/-- In the Weyl space, `[δ_(G,v) a] = (v a) e_G`. -/
theorem coe_single_eq_smul_weylVec (G : X) (v a : ℂ) :
    ((Finsupp.single (G, v) a : RKHS.H₀ (weylRKHSKernel u)) : WeylSpace u) =
      (v * a) • weylVec u G := by
  refine (UniformSpace.Completion.denseRange_coe
    (α := RKHS.H₀ (weylRKHSKernel u))).eq_of_inner_left ℂ fun f => ?_
  rw [weylVec_def, inner_smul_left,
    UniformSpace.Completion.inner_coe (𝕜 := ℂ) (E := RKHS.H₀ (weylRKHSKernel u)),
    UniformSpace.Completion.inner_coe (𝕜 := ℂ) (E := RKHS.H₀ (weylRKHSKernel u))]
  exact inner_H₀_single_left u G v a f

theorem coe_mem_span_weylVec (f : RKHS.H₀ (weylRKHSKernel u)) :
    (f : WeylSpace u) ∈ Submodule.span ℂ (Set.range (weylVec u)) := by
  induction f using Finsupp.induction_linear with
  | zero => exact zero_mem _
  | add f g hf hg =>
    rw [UniformSpace.Completion.coe_add]
    exact add_mem hf hg
  | single p a =>
    obtain ⟨G, v⟩ := p
    rw [coe_single_eq_smul_weylVec]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨G, rfl⟩)

/-- The point masses span a dense subspace of the Weyl space. -/
theorem weylVec_dense :
    (Submodule.span ℂ (Set.range (weylVec u))).topologicalClosure = ⊤ := by
  refine Submodule.dense_iff_topologicalClosure_eq_top.mp ?_
  refine Dense.mono ?_ UniformSpace.Completion.denseRange_coe
  rintro _ ⟨f, rfl⟩
  exact coe_mem_span_weylVec u f

/-- The vacuum is cyclic for the Weyl operators. -/
theorem weyl_cyclic [AddGroup X] (hu : ∀ F G, u (F + G) = u F + u G) :
    (Submodule.span ℂ (Set.range fun F => weylCLM u hu F (weylVec u 0))).topologicalClosure =
      ⊤ := by
  have h : (fun F => weylCLM u hu F (weylVec u 0)) = weylVec u := by
    funext F
    rw [weylCLM_apply, weylOp_weylVec_zero u hu]
  rw [h]
  exact weylVec_dense u

end Kernel

/-- **Existence of a Weyl system with a Gaussian vacuum.** For every additive map `u : X → K`
into a complex inner product space there are a Hilbert space `H`, unitary operators `W F`
satisfying the Weyl relations `W F * W G = exp(-i Im⟪uF, uG⟫) W (F + G)`, and a cyclic unit
vector `Ω` with `⟪Ω, W F Ω⟫ = exp(-‖uF‖²/2)`. -/
theorem exists_weyl_system {X K : Type} [AddCommGroup X] [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] (u : X → K) (hu : ∀ F G, u (F + G) = u F + u G) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (W : X → (H →L[ℂ] H)) (Ω : H),
      (∀ F, W F ∈ unitary (H →L[ℂ] H)) ∧
      (∀ F G, W F * W G = Complex.exp (-(Complex.I * ((⟪u F, u G⟫_ℂ).im : ℂ))) • W (F + G)) ∧
      ‖Ω‖ = 1 ∧
      (∀ F, ⟪Ω, W F Ω⟫_ℂ = ((Real.exp (-(‖u F‖ ^ 2 / 2)) : ℝ) : ℂ)) ∧
      (Submodule.span ℂ (Set.range fun F => W F Ω)).topologicalClosure = ⊤ :=
  ⟨WeylSpace u, inferInstance, inferInstance, inferInstance, weylCLM u hu, weylVec u 0,
    weylCLM_mem_unitary u hu, weylCLM_mul u hu, norm_weylVec_zero u hu, weyl_vacuum u hu,
    weyl_cyclic u hu⟩

end VacuumBellSeparation
