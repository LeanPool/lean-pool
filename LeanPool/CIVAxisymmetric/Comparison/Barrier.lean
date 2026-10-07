/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.GradPair
public import LeanPool.CIVAxisymmetric.Statements.PartialLaplacian
public import LeanPool.CIVAxisymmetric.Statements.TimeDeriv
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The linearly growing barrier of `lem:aniso:comparison`

The comparison argument for `eq:aniso:comparison:equation` is run against the barrier
`eq:aniso:comparison:barrier`

`Ψ_σ(x, τ) = M + σ (⟨x⟩ + K (τ - τ₀))`,   `⟨x⟩ = (1 + |x|²)^{1/2}`,

which grows linearly at infinity and is a supersolution of the drift-diffusion operator
`∂_τ + B·∇ - Δ_X` once the rate `K` dominates the drift bound and the number `d` of
diffusive directions.

The Japanese bracket `⟨x⟩` is smooth on `Vec m`, bounds every coordinate, has gradient of
length at most one, and has partial Laplacian at most `d`. Its derivatives are computed with
the explicit iterated `fderiv … (basisVec i)`, and the barrier facts are then restated with
`timeDeriv`, `gradPair`, and `partialLaplacian`, so that they can be substituted into the
distributional formulation of `eq:aniso:comparison:equation` directly.

The carrier of `Vec m` is the sup norm, for which the Cauchy-Schwarz bound on `B·∇⟨x⟩`
carries the dimensional factor `√m`; the rate is therefore `K = √m Λ + d` instead of the
`Λ + d` of the printed proof, which measures the drift in the Euclidean norm. The inequality
of `eq:aniso:comparison:barrier` is unaffected: only the size of `K` changes, and the
comparison argument uses no upper bound on `K`.
-/

public section

open CKN

noncomputable section

namespace CIV

variable {m : ℕ}

/-! ### The Japanese bracket -/

/-- The Japanese bracket `⟨x⟩ = (1 + |x|²)^{1/2}` on `Vec m`, with `|x|` the Euclidean
length of the coordinate vector `x`. -/
@[expose] def japaneseBracket (m : ℕ) (x : Vec m) : ℝ := Real.sqrt (1 + ∑ i, x i ^ 2)

theorem one_le_japaneseBracket (x : Vec m) : 1 ≤ japaneseBracket m x := by
  have h : (0 : ℝ) ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (1 + ∑ i, x i ^ 2) := Real.sqrt_le_sqrt (by linarith only [h])

theorem japaneseBracket_pos (x : Vec m) : 0 < japaneseBracket m x :=
  lt_of_lt_of_le zero_lt_one (one_le_japaneseBracket x)

theorem japaneseBracket_ne_zero (x : Vec m) : japaneseBracket m x ≠ 0 :=
  ne_of_gt (japaneseBracket_pos x)

theorem sq_japaneseBracket (x : Vec m) : japaneseBracket m x ^ 2 = 1 + ∑ i, x i ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- The Euclidean length of `x` is at most `⟨x⟩`. -/
theorem sqrt_sum_sq_le_japaneseBracket (x : Vec m) :
    Real.sqrt (∑ i, x i ^ 2) ≤ japaneseBracket m x :=
  Real.sqrt_le_sqrt (by linarith only [le_refl (∑ i, x i ^ 2)])

/-- Every coordinate of `x` is bounded by `⟨x⟩`. -/
theorem abs_le_japaneseBracket (x : Vec m) (i : Fin m) : |x i| ≤ japaneseBracket m x := by
  have hle : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
    Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  calc |x i| = Real.sqrt (x i ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ j, x j ^ 2) := Real.sqrt_le_sqrt hle
    _ ≤ japaneseBracket m x := sqrt_sum_sq_le_japaneseBracket x

/-- The sup norm of `x` is bounded by `⟨x⟩`. -/
theorem norm_le_japaneseBracket (x : Vec m) : ‖x‖ ≤ japaneseBracket m x := by
  refine (pi_norm_le_iff_of_nonneg (le_of_lt (japaneseBracket_pos x))).2 fun i => ?_
  simpa [Real.norm_eq_abs] using abs_le_japaneseBracket x i

theorem contDiff_japaneseBracket : ContDiff ℝ (⊤ : ℕ∞) (japaneseBracket m) := by
  refine ContDiff.sqrt ?_ (fun x => by positivity)
  exact contDiff_const.add (ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).pow 2)

theorem differentiable_japaneseBracket : Differentiable ℝ (japaneseBracket m) :=
  (contDiff_japaneseBracket (m := m)).differentiable (by simp)

/-! ### First derivatives -/

/-- The gradient of `⟨x⟩` paired with a vector: `∇⟨x⟩ · v = (x · v) / ⟨x⟩`. -/
theorem fderiv_japaneseBracket_apply (x v : Vec m) :
    fderiv ℝ (japaneseBracket m) x v = (∑ i, x i * v i) / japaneseBracket m x := by
  have hne : (1 : ℝ) + ∑ i, x i ^ 2 ≠ 0 := by positivity
  have hsq := (HasFDerivAt.sum (fun (i : Fin m) (_ : i ∈ Finset.univ) =>
      (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin m => ℝ) i x).pow 2)).const_add (1 : ℝ)
  have hfun : (fun y : Vec m => 1 + (∑ i : Fin m, fun z : Vec m => z i ^ 2) y)
      = fun y : Vec m => 1 + ∑ i, y i ^ 2 := by
    funext y; simp
  rw [hfun] at hsq
  have h : HasFDerivAt (japaneseBracket m) _ x := hsq.sqrt hne
  rw [h.fderiv]
  simp only [smul_apply, sum_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, nsmul_eq_mul]
  rw [show Real.sqrt (1 + ∑ i, x i ^ 2) = japaneseBracket m x from rfl]
  have hsum : ∑ i, ((2 : ℕ) : ℝ) * x i ^ (2 - 1) * v i = 2 * ∑ i, x i * v i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  rw [hsum]
  field_simp

/-- The coordinate partial derivative `∂_i⟨x⟩ = x_i / ⟨x⟩`. -/
theorem fderiv_japaneseBracket_basisVec (x : Vec m) (i : Fin m) :
    fderiv ℝ (japaneseBracket m) x (basisVec i) = x i / japaneseBracket m x := by
  rw [fderiv_japaneseBracket_apply]
  congr 1
  simp [basisVec_apply]

/-- The gradient of `⟨x⟩` has Euclidean length at most one: `∑_i (∂_i⟨x⟩)² ≤ 1`. -/
theorem sum_sq_fderiv_japaneseBracket_le_one (x : Vec m) :
    ∑ i, fderiv ℝ (japaneseBracket m) x (basisVec i) ^ 2 ≤ 1 := by
  have hpos : 0 < japaneseBracket m x := japaneseBracket_pos x
  have hrw : ∑ i, fderiv ℝ (japaneseBracket m) x (basisVec i) ^ 2
      = (∑ i, x i ^ 2) / japaneseBracket m x ^ 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by
      rw [fderiv_japaneseBracket_basisVec, div_pow]
  rw [hrw, div_le_one (by positivity), sq_japaneseBracket]
  linarith only [le_refl (∑ i, x i ^ 2)]

/-- Cauchy-Schwarz against the sup norm: `|∇⟨x⟩ · v| ≤ √m ‖v‖`. -/
theorem abs_fderiv_japaneseBracket_apply_le (x v : Vec m) :
    |fderiv ℝ (japaneseBracket m) x v| ≤ Real.sqrt m * ‖v‖ := by
  have hpos : 0 < japaneseBracket m x := japaneseBracket_pos x
  have hv : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
  have h1 : |∑ i, x i * v i| ≤ (∑ i, |x i|) * ‖v‖ := by
    calc |∑ i, x i * v i| ≤ ∑ i, |x i * v i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |x i| * ‖v‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          have : |v i| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm v i
          exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = (∑ i, |x i|) * ‖v‖ := by rw [Finset.sum_mul]
  have h2 : ∑ i, |x i| ≤ Real.sqrt m * japaneseBracket m x := by
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin m))
      (fun _ => (1 : ℝ)) (fun i => |x i|)
    have hone : Real.sqrt (∑ _i : Fin m, (1 : ℝ) ^ 2) = Real.sqrt m := by
      simp
    have habs : Real.sqrt (∑ i, |x i| ^ 2) = Real.sqrt (∑ i, x i ^ 2) := by
      simp [sq_abs]
    have := hcs
    rw [hone, habs] at this
    simp only [one_mul] at this
    exact this.trans (mul_le_mul_of_nonneg_left (sqrt_sum_sq_le_japaneseBracket x)
      (Real.sqrt_nonneg _))
  rw [fderiv_japaneseBracket_apply, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  calc |∑ i, x i * v i| ≤ (∑ i, |x i|) * ‖v‖ := h1
    _ ≤ (Real.sqrt m * japaneseBracket m x) * ‖v‖ := mul_le_mul_of_nonneg_right h2 hv
    _ = Real.sqrt m * ‖v‖ * japaneseBracket m x := by ring

/-! ### Second derivatives -/

theorem differentiableAt_fderiv_japaneseBracket (x : Vec m) (i : Fin m) :
    DifferentiableAt ℝ (fun y : Vec m => fderiv ℝ (japaneseBracket m) y (basisVec i)) x := by
  have hfun : (fun y : Vec m => fderiv ℝ (japaneseBracket m) y (basisVec i))
      = fun y : Vec m => y i * (japaneseBracket m y)⁻¹ := by
    funext y
    rw [fderiv_japaneseBracket_basisVec, div_eq_mul_inv]
  rw [hfun]
  have hinv : HasFDerivAt (fun y : Vec m => (japaneseBracket m y)⁻¹) _ x :=
    (hasDerivAt_inv (japaneseBracket_ne_zero x)).comp_hasFDerivAt x
      (differentiable_japaneseBracket x).hasFDerivAt
  exact ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin m => ℝ) i x).mul hinv).differentiableAt

/-- The second coordinate derivative `∂_i∂_i⟨x⟩ = (⟨x⟩² - x_i²) / ⟨x⟩³`. -/
theorem fderiv_fderiv_japaneseBracket (x : Vec m) (i : Fin m) :
    fderiv ℝ (fun y : Vec m => fderiv ℝ (japaneseBracket m) y (basisVec i)) x (basisVec i)
      = (japaneseBracket m x ^ 2 - x i ^ 2) / japaneseBracket m x ^ 3 := by
  have hfun : (fun y : Vec m => fderiv ℝ (japaneseBracket m) y (basisVec i))
      = fun y : Vec m => y i * (japaneseBracket m y)⁻¹ := by
    funext y
    rw [fderiv_japaneseBracket_basisVec, div_eq_mul_inv]
  rw [hfun]
  have hinv : HasFDerivAt (fun y : Vec m => (japaneseBracket m y)⁻¹) _ x :=
    (hasDerivAt_inv (japaneseBracket_ne_zero x)).comp_hasFDerivAt x
      (differentiable_japaneseBracket x).hasFDerivAt
  have happ := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin m => ℝ) i x
  rw [fderiv_fun_mul happ.differentiableAt hinv.differentiableAt, hinv.fderiv, happ.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    basisVec_apply, ite_true]
  rw [fderiv_japaneseBracket_basisVec]
  have hne := japaneseBracket_ne_zero x
  field_simp
  ring

/-- The second coordinate derivatives of `⟨x⟩` are bounded by one. -/
theorem fderiv_fderiv_japaneseBracket_le_one (x : Vec m) (i : Fin m) :
    fderiv ℝ (fun y : Vec m => fderiv ℝ (japaneseBracket m) y (basisVec i)) x (basisVec i)
      ≤ 1 := by
  rw [fderiv_fderiv_japaneseBracket]
  have h1 : 1 ≤ japaneseBracket m x := one_le_japaneseBracket x
  have hpos : (0 : ℝ) < japaneseBracket m x ^ 3 := by positivity
  rw [div_le_one hpos]
  nlinarith only [h1, sq_nonneg (x i), sq_nonneg (japaneseBracket m x)]

/-- The partial Laplacian of `⟨x⟩` in the first `d` coordinates is at most `d`. -/
theorem sum_ite_fderiv_fderiv_japaneseBracket_le (d : ℕ) (x : Vec m) :
    ∑ i : Fin m, (if (i : ℕ) < d then
        fderiv ℝ (fun y : Vec m => fderiv ℝ (japaneseBracket m) y (basisVec i)) x (basisVec i)
      else 0) ≤ (d : ℝ) := by
  classical
  have hcard : (Finset.univ.filter fun i : Fin m => (i : ℕ) < d).card ≤ d := by
    have hmap : ∀ i ∈ Finset.univ.filter fun i : Fin m => (i : ℕ) < d,
        (i : ℕ) ∈ Finset.range d := by
      intro i hi
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
    have hinj : Set.InjOn (fun i : Fin m => (i : ℕ))
        (Finset.univ.filter fun i : Fin m => (i : ℕ) < d) := fun a _ b _ h => Fin.ext h
    simpa using Finset.card_le_card_of_injOn (fun i : Fin m => (i : ℕ)) hmap hinj
  calc ∑ i : Fin m, (if (i : ℕ) < d then
          fderiv ℝ (fun y : Vec m => fderiv ℝ (japaneseBracket m) y (basisVec i)) x (basisVec i)
        else 0)
      ≤ ∑ i : Fin m, (if (i : ℕ) < d then (1 : ℝ) else 0) := by
        refine Finset.sum_le_sum fun i _ => ?_
        by_cases hi : (i : ℕ) < d
        · simpa [hi] using fderiv_fderiv_japaneseBracket_le_one x i
        · simp [hi]
    _ = ((Finset.univ.filter fun i : Fin m => (i : ℕ) < d).card : ℝ) := by
        simp
    _ ≤ (d : ℝ) := by exact_mod_cast hcard

/-- The second coordinate derivatives of `⟨x⟩` are nonnegative: `⟨x⟩² - x_i² = 1 + ∑_{j ≠ i} x_j²
≥ 0`, so the whole quotient by `⟨x⟩³ > 0` is nonnegative. -/
theorem fderiv_fderiv_japaneseBracket_nonneg (x : Vec m) (i : Fin m) :
    0 ≤ fderiv ℝ (fun y : Vec m => fderiv ℝ (japaneseBracket m) y (basisVec i)) x (basisVec i) := by
  rw [fderiv_fderiv_japaneseBracket]
  have hnum : (0 : ℝ) ≤ japaneseBracket m x ^ 2 - x i ^ 2 := by
    rw [sq_japaneseBracket]
    have hsum : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
      Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    linarith only [hsum]
  have hpos : (0 : ℝ) < japaneseBracket m x ^ 3 := pow_pos (japaneseBracket_pos x) 3
  exact div_nonneg hnum hpos.le

/-- The partial Laplacian of `⟨x⟩` in the first `d` coordinates is nonnegative: a sum of
nonnegative terms. -/
theorem sum_ite_fderiv_fderiv_japaneseBracket_nonneg (d : ℕ) (x : Vec m) :
    0 ≤ ∑ i : Fin m, (if (i : ℕ) < d then
        fderiv ℝ (fun y : Vec m => fderiv ℝ (japaneseBracket m) y (basisVec i)) x (basisVec i)
      else 0) := by
  refine Finset.sum_nonneg fun i _ => ?_
  split_ifs with hi
  · exact fderiv_fderiv_japaneseBracket_nonneg x i
  · exact le_refl (0 : ℝ)

/-! ### The barrier `Ψ_σ` -/

/-- The barrier `eq:aniso:comparison:barrier`:
`Ψ_σ(x, τ) = M + σ (⟨x⟩ + K (τ - τ₀))`. -/
@[expose] def barrier (m : ℕ) (M σ K τ₀ : ℝ) (z : Vec m × ℝ) : ℝ :=
  M + σ * (japaneseBracket m z.1 + K * (z.2 - τ₀))

/-- The rate `K = √m Λ + d` of `eq:aniso:comparison:barrier`, for a drift bounded by `Λ`
in the sup norm of `Vec m` and diffusion in the first `d` coordinates. -/
@[expose] def barrierRate (m d : ℕ) (Λ : ℝ) : ℝ := Real.sqrt m * Λ + d

theorem barrierRate_nonneg (m d : ℕ) {Λ : ℝ} (hΛ : 0 ≤ Λ) : 0 ≤ barrierRate m d Λ :=
  add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hΛ) (Nat.cast_nonneg d)

theorem contDiff_barrier (M σ K τ₀ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (barrier m M σ K τ₀) := by
  unfold barrier
  exact contDiff_const.add (contDiff_const.mul
    ((contDiff_japaneseBracket.comp contDiff_fst).add
      (contDiff_const.mul (contDiff_snd.sub contDiff_const))))

/-- The time derivative of the barrier: `∂_τΨ_σ = σK`. -/
theorem fderiv_barrier_time (M σ K τ₀ : ℝ) (x : Vec m) (t : ℝ) :
    fderiv ℝ (fun τ : ℝ => barrier m M σ K τ₀ (x, τ)) t 1 = σ * K := by
  have hid : HasDerivAt (fun τ : ℝ => τ - τ₀) 1 t := by
    simpa using HasDerivAt.sub_const τ₀ (hasDerivAt_id t)
  have h0 : HasDerivAt (fun τ : ℝ => K * (τ - τ₀)) K t := by
    simpa using HasDerivAt.const_mul K hid
  have h1 : HasDerivAt (fun τ : ℝ => japaneseBracket m x + K * (τ - τ₀)) K t := by
    simpa using HasDerivAt.const_add (japaneseBracket m x) h0
  have h2 : HasDerivAt (fun τ : ℝ => σ * (japaneseBracket m x + K * (τ - τ₀))) (σ * K) t :=
    HasDerivAt.const_mul σ h1
  have h : HasDerivAt (fun τ : ℝ => barrier m M σ K τ₀ (x, τ)) (σ * K) t := by
    simpa [barrier] using HasDerivAt.const_add M h2
  rw [show fderiv ℝ (fun τ : ℝ => barrier m M σ K τ₀ (x, τ)) t 1
      = deriv (fun τ : ℝ => barrier m M σ K τ₀ (x, τ)) t from rfl]
  exact h.deriv

/-- The spatial gradient of the barrier paired with a vector:
`∇Ψ_σ · v = σ (x · v) / ⟨x⟩`. -/
theorem fderiv_barrier_spatial_apply (M σ K τ₀ τ : ℝ) (x v : Vec m) :
    fderiv ℝ (fun y : Vec m => barrier m M σ K τ₀ (y, τ)) x v
      = σ * ((∑ i, x i * v i) / japaneseBracket m x) := by
  have ha : HasFDerivAt (fun y : Vec m => japaneseBracket m y + K * (τ - τ₀))
      (fderiv ℝ (japaneseBracket m) x) x :=
    (differentiable_japaneseBracket x).hasFDerivAt.add_const (K * (τ - τ₀))
  have hb : HasFDerivAt (fun y : Vec m => σ * (japaneseBracket m y + K * (τ - τ₀)))
      (σ • fderiv ℝ (japaneseBracket m) x) x := ha.const_mul σ
  have h : HasFDerivAt (fun y : Vec m => barrier m M σ K τ₀ (y, τ))
      (σ • fderiv ℝ (japaneseBracket m) x) x := hb.const_add M
  rw [h.fderiv]
  simp only [smul_apply, smul_eq_mul]
  rw [fderiv_japaneseBracket_apply]

/-- The drift term of the barrier is controlled by the sup norm of the drift:
`|B · ∇Ψ_σ| ≤ σ √m ‖B‖`. -/
theorem abs_fderiv_barrier_spatial_apply_le (M K τ₀ τ : ℝ) {σ : ℝ} (hσ : 0 ≤ σ) (x v : Vec m) :
    |fderiv ℝ (fun y : Vec m => barrier m M σ K τ₀ (y, τ)) x v| ≤ σ * (Real.sqrt m * ‖v‖) := by
  rw [fderiv_barrier_spatial_apply, ← fderiv_japaneseBracket_apply, abs_mul, abs_of_nonneg hσ]
  exact mul_le_mul_of_nonneg_left (abs_fderiv_japaneseBracket_apply_le x v) hσ

/-- The second spatial derivatives of the barrier:
`∂_i∂_iΨ_σ = σ (⟨x⟩² - x_i²) / ⟨x⟩³`. -/
theorem fderiv_fderiv_barrier_spatial (M σ K τ₀ τ : ℝ) (x : Vec m) (i : Fin m) :
    fderiv ℝ (fun y : Vec m =>
        fderiv ℝ (fun w : Vec m => barrier m M σ K τ₀ (w, τ)) y (basisVec i)) x (basisVec i)
      = σ * ((japaneseBracket m x ^ 2 - x i ^ 2) / japaneseBracket m x ^ 3) := by
  have hfun : (fun y : Vec m =>
        fderiv ℝ (fun w : Vec m => barrier m M σ K τ₀ (w, τ)) y (basisVec i))
      = fun y : Vec m => σ * fderiv ℝ (japaneseBracket m) y (basisVec i) := by
    funext y
    rw [fderiv_barrier_spatial_apply, fderiv_japaneseBracket_apply]
  rw [hfun, fderiv_const_mul (differentiableAt_fderiv_japaneseBracket x i) σ]
  simp only [smul_apply, smul_eq_mul]
  rw [fderiv_fderiv_japaneseBracket]

/-- The partial Laplacian of the barrier in the first `d` coordinates is at most `σd`. -/
theorem sum_ite_fderiv_fderiv_barrier_le (d : ℕ) (M K τ₀ τ : ℝ) {σ : ℝ} (hσ : 0 ≤ σ)
    (x : Vec m) :
    ∑ i : Fin m, (if (i : ℕ) < d then
        fderiv ℝ (fun y : Vec m =>
          fderiv ℝ (fun w : Vec m => barrier m M σ K τ₀ (w, τ)) y (basisVec i)) x (basisVec i)
      else 0) ≤ σ * d := by
  have hrw : ∀ i : Fin m, (if (i : ℕ) < d then
        fderiv ℝ (fun y : Vec m =>
          fderiv ℝ (fun w : Vec m => barrier m M σ K τ₀ (w, τ)) y (basisVec i)) x (basisVec i)
      else 0)
      = σ * (if (i : ℕ) < d then
          fderiv ℝ (fun y : Vec m => fderiv ℝ (japaneseBracket m) y (basisVec i)) x (basisVec i)
        else 0) := by
    intro i
    split_ifs with hi
    · rw [fderiv_fderiv_barrier_spatial, fderiv_fderiv_japaneseBracket]
    · rw [mul_zero]
  rw [Finset.sum_congr rfl fun i _ => hrw i, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_ite_fderiv_fderiv_japaneseBracket_le d x) hσ

/-- The partial Laplacian of the barrier in the first `d` coordinates is nonnegative: the same
term-by-term rescaling as `sum_ite_fderiv_fderiv_barrier_le`, against
`sum_ite_fderiv_fderiv_japaneseBracket_nonneg` instead of the upper bound. -/
theorem sum_ite_fderiv_fderiv_barrier_nonneg (d : ℕ) (M K τ₀ τ : ℝ) {σ : ℝ} (hσ : 0 ≤ σ)
    (x : Vec m) :
    0 ≤ ∑ i : Fin m, (if (i : ℕ) < d then
        fderiv ℝ (fun y : Vec m =>
          fderiv ℝ (fun w : Vec m => barrier m M σ K τ₀ (w, τ)) y (basisVec i)) x (basisVec i)
      else 0) := by
  have hrw : ∀ i : Fin m, (if (i : ℕ) < d then
        fderiv ℝ (fun y : Vec m =>
          fderiv ℝ (fun w : Vec m => barrier m M σ K τ₀ (w, τ)) y (basisVec i)) x (basisVec i)
      else 0)
      = σ * (if (i : ℕ) < d then
          fderiv ℝ (fun y : Vec m => fderiv ℝ (japaneseBracket m) y (basisVec i)) x (basisVec i)
        else 0) := by
    intro i
    split_ifs with hi
    · rw [fderiv_fderiv_barrier_spatial, fderiv_fderiv_japaneseBracket]
    · rw [mul_zero]
  rw [Finset.sum_congr rfl fun i _ => hrw i, ← Finset.mul_sum]
  exact mul_nonneg hσ (sum_ite_fderiv_fderiv_japaneseBracket_nonneg d x)

/-! ### The barrier against the drift-diffusion operator -/

/-- `∂_τΨ_σ = σK`. -/
theorem timeDeriv_barrier (M σ K τ₀ : ℝ) (z : Vec m × ℝ) :
    timeDeriv m (barrier m M σ K τ₀) z = σ * K :=
  fderiv_barrier_time M σ K τ₀ z.1 z.2

/-- `∇Ψ_σ · v = σ (x · v) / ⟨x⟩`. -/
theorem gradPair_barrier (M σ K τ₀ : ℝ) (z : Vec m × ℝ) (v : Vec m) :
    gradPair m (barrier m M σ K τ₀) z v
      = σ * ((∑ i, z.1 i * v i) / japaneseBracket m z.1) :=
  fderiv_barrier_spatial_apply M σ K τ₀ z.2 z.1 v

/-- `|∇Ψ_σ · v| ≤ σ √m ‖v‖` for the sup norm of `Vec m`. -/
theorem abs_gradPair_barrier_le (M K τ₀ : ℝ) {σ : ℝ} (hσ : 0 ≤ σ) (z : Vec m × ℝ) (v : Vec m) :
    |gradPair m (barrier m M σ K τ₀) z v| ≤ σ * (Real.sqrt m * ‖v‖) :=
  abs_fderiv_barrier_spatial_apply_le M K τ₀ z.2 hσ z.1 v

/-- `Δ_XΨ_σ ≤ σd`. -/
theorem partialLaplacian_barrier_le (d : ℕ) (M K τ₀ : ℝ) {σ : ℝ} (hσ : 0 ≤ σ)
    (z : Vec m × ℝ) :
    partialLaplacian m d (barrier m M σ K τ₀) z ≤ σ * d :=
  sum_ite_fderiv_fderiv_barrier_le d M K τ₀ z.2 hσ z.1

/-- `Δ_XΨ_σ ≥ 0`. -/
theorem partialLaplacian_barrier_nonneg (d : ℕ) (M K τ₀ : ℝ) {σ : ℝ} (hσ : 0 ≤ σ)
    (z : Vec m × ℝ) :
    0 ≤ partialLaplacian m d (barrier m M σ K τ₀) z :=
  sum_ite_fderiv_fderiv_barrier_nonneg d M K τ₀ z.2 hσ z.1

/-- The supersolution inequality of `eq:aniso:comparison:barrier`: with the rate
`K = √m Λ + d` the barrier satisfies `∂_τΨ_σ + B·∇Ψ_σ - Δ_XΨ_σ ≥ 0` at every point where
the drift is bounded by `Λ`. -/
theorem barrier_supersolution (d : ℕ) (M τ₀ Λ : ℝ) {σ : ℝ} (hσ : 0 ≤ σ)
    (B : Vec m × ℝ → Vec m) (z : Vec m × ℝ) (hB : ‖B z‖ ≤ Λ) :
    0 ≤ timeDeriv m (barrier m M σ (barrierRate m d Λ) τ₀) z
      + gradPair m (barrier m M σ (barrierRate m d Λ) τ₀) z (B z)
      - partialLaplacian m d (barrier m M σ (barrierRate m d Λ) τ₀) z := by
  have hΛ : 0 ≤ Λ := le_trans (norm_nonneg _) hB
  have htime := timeDeriv_barrier (m := m) M σ (barrierRate m d Λ) τ₀ z
  have hlap := partialLaplacian_barrier_le (m := m) d M (barrierRate m d Λ) τ₀ hσ z
  have hdrift := abs_gradPair_barrier_le (m := m) M (barrierRate m d Λ) τ₀ hσ z (B z)
  have hmono : σ * (Real.sqrt m * ‖B z‖) ≤ σ * (Real.sqrt m * Λ) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB (Real.sqrt_nonneg _)) hσ
  have hlow := (abs_le.mp hdrift).1
  have hrate : σ * barrierRate m d Λ = σ * (Real.sqrt m * Λ) + σ * d := by
    rw [barrierRate]
    ring
  rw [htime, hrate]
  linarith only [hlap, hlow, hmono]

/-- **An upper bound on the barrier's supersolution slack.** `barrier_supersolution` bounds
`∂_τΨ_σ + B·∇Ψ_σ - Δ_XΨ_σ` from below by `0`; this bounds the same quantity from above, by
`σ (2 √m Λ + d)`, from the exact value of `∂_τΨ_σ`, the Cauchy–Schwarz bound on `∇Ψ_σ·B`, and
`partialLaplacian_barrier_nonneg` (dropping the Laplacian term, which can only decrease the
slack). -/
theorem barrier_supersolution_slack_le (d : ℕ) (M τ₀ Λ : ℝ) {σ : ℝ} (hσ : 0 ≤ σ)
    (B : Vec m × ℝ → Vec m) (z : Vec m × ℝ) (hB : ‖B z‖ ≤ Λ) :
    timeDeriv m (barrier m M σ (barrierRate m d Λ) τ₀) z
        + gradPair m (barrier m M σ (barrierRate m d Λ) τ₀) z (B z)
        - partialLaplacian m d (barrier m M σ (barrierRate m d Λ) τ₀) z
      ≤ σ * (2 * Real.sqrt m * Λ + d) := by
  have htime := timeDeriv_barrier (m := m) M σ (barrierRate m d Λ) τ₀ z
  have hlapnn := partialLaplacian_barrier_nonneg (m := m) d M (barrierRate m d Λ) τ₀ hσ z
  have hdrift := abs_gradPair_barrier_le (m := m) M (barrierRate m d Λ) τ₀ hσ z (B z)
  have hup := (abs_le.mp hdrift).2
  have hmono : σ * (Real.sqrt m * ‖B z‖) ≤ σ * (Real.sqrt m * Λ) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB (Real.sqrt_nonneg _)) hσ
  have hrate : σ * barrierRate m d Λ = σ * (Real.sqrt m * Λ) + σ * d := by
    rw [barrierRate]
    ring
  have hRHS : σ * (2 * Real.sqrt m * Λ + d)
      = σ * (Real.sqrt m * Λ) + σ * d + σ * (Real.sqrt m * Λ) := by ring
  rw [htime, hrate, hRHS]
  linarith only [hlapnn, hup, hmono]

/-- The barrier dominates `M + σ‖x‖` after the initial time `τ₀`. -/
theorem le_barrier (M K τ₀ τ : ℝ) {σ : ℝ} (x : Vec m) (hσ : 0 ≤ σ) (hK : 0 ≤ K)
    (hτ : τ₀ ≤ τ) : M + σ * ‖x‖ ≤ barrier m M σ K τ₀ (x, τ) := by
  have h1 : ‖x‖ ≤ japaneseBracket m x := norm_le_japaneseBracket x
  have h2 : 0 ≤ K * (τ - τ₀) := mul_nonneg hK (by linarith only [hτ])
  have h3 : σ * ‖x‖ ≤ σ * (japaneseBracket m x + K * (τ - τ₀)) :=
    mul_le_mul_of_nonneg_left (by linarith only [h1, h2]) hσ
  simp only [barrier]
  linarith only [h3]

end CIV
