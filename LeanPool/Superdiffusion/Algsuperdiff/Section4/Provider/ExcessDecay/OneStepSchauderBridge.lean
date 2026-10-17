/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.Cutoff.Euclidean
public import LeanPool.HighContrastHomogenization.Support.Sobolev.WeakDerivatives
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# OneStepSchauderBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The coordinate identification `Vec d ≃L EuclideanSpace ℝ (Fin d)`

The interior Schauder estimate for the harmonic competitor of
the Schauder gradient-Hölder estimate is proved against Mathlib's
`InnerProductSpace.HarmonicOnNhd`, which lives on `EuclideanSpace ℝ (Fin d)`
with `Metric.ball` and the coordinate-free Laplacian `Δ`.  Every §4 carrier
(`Vec d`, `truncatedWindow`, `HolderSeminormBoundOn`, `affineExcess`) lives on
the CoarseGraining coordinate carrier `Vec d = Fin d → ℝ` with the **sup**
norm.

This module is the definitional dictionary between the two, through the
canonical identification `toEuc : Vec d ≃L[ℝ] EuclideanSpace ℝ (Fin d)`
(the identity on underlying data; only the ambient norm differs):

* `toEuc`, `toEuc_apply`, `toEuc_basisVec`;
* `mem_euclideanBall_toEuc_iff` — the ball dictionary
  `toEuc a ∈ Metric.ball (toEuc b) r ↔ a ∈ euclideanBall b r`;
* `norm_toEuc_le`, `norm_le_norm_toEuc` — the two-sided
  comparison of the sup and `ℓ²` norms with the sharp constants `√d` and `1`,
  the source of every dimensional factor in the Schauder constant;
* `norm_fderiv_vec_sub_le` — the resulting transfer of gradient Hölder
  differences;
* `harmonicOnNhd_sub_vec_affine` — subtracting a `Vec d` affine competitor
  preserves harmonicity of the Euclidean avatar.  This is what turns a
  *constant*-deviation interior estimate into a genuine **excess** estimate.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open InnerProductSpace
open scoped Laplacian
open HCPolySupport (Vec basisVec basisVec_apply euclideanBall euclideanSqDist vecNormSq vecDot)

noncomputable section

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-! ## 1. The coordinate identification -/

/-- The canonical identification of the CoarseGraining coordinate carrier `Vec d =
Fin d → ℝ` with the Mathlib inner-product space `EuclideanSpace ℝ (Fin d)`.  It
is the identity on underlying data; only the ambient norm (sup vs.  `ℓ²`)
differs. -/
def toEuc : Vec d ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm

@[simp] theorem toEuc_apply (y : Vec d) (i : Fin d) : (toEuc y) i = y i := rfl

@[simp] theorem toEuc_symm_apply (x : 𝔼) (i : Fin d) :
    (toEuc.symm x) i = x i := rfl

/-- The coordinate basis vector `basisVec i` maps to the orthonormal basis vector
`EuclideanSpace.single i 1`. -/
@[simp] theorem toEuc_basisVec (i : Fin d) :
    toEuc (basisVec i) = EuclideanSpace.single i 1 := by
  ext j
  simp [toEuc_apply, basisVec_apply]

@[simp] theorem toEuc_symm_single (i : Fin d) :
    toEuc.symm (EuclideanSpace.single i (1 : ℝ)) = (basisVec i : Vec d) := by
  rw [← toEuc_basisVec i, ContinuousLinearEquiv.symm_apply_apply]

/-- The round trip: a function on the `Vec d` carrier, pushed to the Euclidean
carrier and pulled back, is itself. -/
theorem comp_toEuc_symm_toEuc (v : Vec d → ℝ) :
    (v ∘ (toEuc.symm : 𝔼 → Vec d)) ∘ (toEuc : Vec d → 𝔼) = v := by
  funext y
  simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]

/-! ## 2. The ball dictionary -/

/-- The `ℓ²` distance of two coordinate vectors, transported to `EuclideanSpace`,
is the CoarseGraining Euclidean squared distance. -/
theorem norm_sq_toEuc_sub (a b : Vec d) :
    ‖toEuc a - toEuc b‖ ^ 2 = euclideanSqDist a b := by
  rw [← map_sub, EuclideanSpace.norm_sq_eq]
  simp only [toEuc_apply, Real.norm_eq_abs, sq_abs]
  simp only [euclideanSqDist, vecNormSq, vecDot, Pi.sub_apply, pow_two]

/-- **Ball dictionary.**  Under the coordinate identification the Mathlib metric
ball corresponds to the CoarseGraining explicit Euclidean ball. -/
theorem mem_euclideanBall_toEuc_iff (a b : Vec d) {r : ℝ} (hr : 0 < r) :
    toEuc a ∈ Metric.ball (toEuc b) r ↔ a ∈ euclideanBall b r := by
  rw [Metric.mem_ball, dist_eq_norm]
  have hN : ‖toEuc a - toEuc b‖ = Real.sqrt (euclideanSqDist a b) := by
    rw [← norm_sq_toEuc_sub a b, Real.sqrt_sq (norm_nonneg _)]
  rw [hN]
  rw [show (euclideanBall b r : Set (Vec d)) = {x | euclideanSqDist x b < r ^ 2} from rfl,
    Set.mem_ofPred_eq, Real.sqrt_lt' hr]

/-! ## 3. The two-sided norm comparison -/

/-- The `ℓ²` norm of a coordinate vector is at most `√d` times its sup norm. -/
theorem norm_toEuc_le (y : Vec d) :
    ‖(toEuc y : 𝔼)‖ ≤ Real.sqrt d * ‖y‖ := by
  rw [EuclideanSpace.norm_eq]
  have hstep : ∑ i, ‖(toEuc y : 𝔼) i‖ ^ 2 ≤ (d : ℝ) * ‖y‖ ^ 2 := by
    have hcoord : ∀ i : Fin d, ‖(toEuc y : 𝔼) i‖ ^ 2 ≤ ‖y‖ ^ 2 := by
      intro i
      have h : ‖y i‖ ≤ ‖y‖ := norm_le_pi_norm y i
      have hrfl : ‖(toEuc y : 𝔼) i‖ = ‖y i‖ := rfl
      rw [hrfl]
      exact pow_le_pow_left₀ (norm_nonneg _) h 2
    calc ∑ i, ‖(toEuc y : 𝔼) i‖ ^ 2 ≤ ∑ _i : Fin d, ‖y‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => hcoord i
      _ = (d : ℝ) * ‖y‖ ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc Real.sqrt (∑ i, ‖(toEuc y : 𝔼) i‖ ^ 2) ≤ Real.sqrt ((d : ℝ) * ‖y‖ ^ 2) :=
        Real.sqrt_le_sqrt hstep
    _ = Real.sqrt d * ‖y‖ := by
        rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq (norm_nonneg _)]

/-- The sup norm of a coordinate vector is at most its `ℓ²` norm. -/
theorem norm_le_norm_toEuc (y : Vec d) : ‖y‖ ≤ ‖(toEuc y : 𝔼)‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  rw [EuclideanSpace.norm_eq]
  have hmem : i ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ i
  have hsingle : ‖(toEuc y : 𝔼) i‖ ^ 2
      ≤ ∑ j, ‖(toEuc y : 𝔼) j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖(toEuc y : 𝔼) j‖ ^ 2)
      (fun j _ => sq_nonneg _) hmem
  have hrfl : ‖(toEuc y : 𝔼) i‖ = ‖y i‖ := rfl
  rw [hrfl] at hsingle
  have hle := Real.sqrt_le_sqrt hsingle
  rwa [Real.sqrt_sq (norm_nonneg _)] at hle

/-- The operator norm of the coordinate identification, viewed as a continuous
linear map from the sup-normed carrier to the `ℓ²`-normed one, is at most `√d`. -/
theorem opNorm_toEuc_le :
    ‖(toEuc : Vec d ≃L[ℝ] 𝔼).toContinuousLinearMap‖ ≤ Real.sqrt d :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun y => norm_toEuc_le y

/-! ## 4. `fderiv` transfer -/

/-- **Chain rule across the coordinate identification.**  No differentiability
hypothesis is needed: if `V` is not differentiable at `toEuc y` then
neither side is, and both are `0`. -/
theorem fderiv_comp_toEuc (V : 𝔼 → ℝ) (y : Vec d) :
    fderiv ℝ (V ∘ toEuc) y
      = (fderiv ℝ V (toEuc y)).comp
          (toEuc : Vec d ≃L[ℝ] 𝔼).toContinuousLinearMap :=
  ContinuousLinearEquiv.comp_right_fderiv _

/-- **Hölder/Lipschitz seminorm transfer for `fderiv`.**  Differences of the
derivative of `V ∘ toEuc` at the `Vec d` carrier are bounded by `√d`
times the corresponding differences of `fderiv V` at the Euclidean carrier. -/
theorem norm_fderiv_comp_toEuc_sub_le (V : 𝔼 → ℝ) (y z : Vec d) :
    ‖fderiv ℝ (V ∘ toEuc) y - fderiv ℝ (V ∘ toEuc) z‖
      ≤ Real.sqrt d * ‖fderiv ℝ V (toEuc y) - fderiv ℝ V (toEuc z)‖ := by
  rw [fderiv_comp_toEuc, fderiv_comp_toEuc, ← ContinuousLinearMap.sub_comp]
  calc ‖(fderiv ℝ V (toEuc y) - fderiv ℝ V (toEuc z)).comp
          (toEuc : Vec d ≃L[ℝ] 𝔼).toContinuousLinearMap‖
      ≤ ‖fderiv ℝ V (toEuc y) - fderiv ℝ V (toEuc z)‖ *
          ‖(toEuc : Vec d ≃L[ℝ] 𝔼).toContinuousLinearMap‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ V (toEuc y) - fderiv ℝ V (toEuc z)‖ * Real.sqrt d :=
        mul_le_mul_of_nonneg_left opNorm_toEuc_le (norm_nonneg _)
    _ = Real.sqrt d * ‖fderiv ℝ V (toEuc y) - fderiv ℝ V (toEuc z)‖ :=
        mul_comm _ _

/-- **Hölder/Lipschitz seminorm transfer, `Vec d` shape.** -/
theorem norm_fderiv_vec_sub_le (v : Vec d → ℝ) (y z : Vec d) :
    ‖fderiv ℝ v y - fderiv ℝ v z‖
      ≤ Real.sqrt d * ‖fderiv ℝ (v ∘ toEuc.symm) (toEuc y)
          - fderiv ℝ (v ∘ toEuc.symm) (toEuc z)‖ := by
  have h := norm_fderiv_comp_toEuc_sub_le (v ∘ toEuc.symm) y z
  rwa [comp_toEuc_symm_toEuc] at h

/-! ## 5. Affine functions are harmonic -/

/-- The second iterated derivative of an affine function vanishes. -/
theorem iteratedFDeriv_two_affine (c : ℝ) (L : 𝔼 →L[ℝ] ℝ) (x : 𝔼) :
    iteratedFDeriv ℝ 2 (fun z => c + L z) x = 0 := by
  have hfd : (fun y => fderiv ℝ (fun z : 𝔼 => c + L z) y) = fun _ : 𝔼 => (L : 𝔼 →L[ℝ] ℝ) := by
    funext y
    exact (L.hasFDerivAt.const_add c).fderiv
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, hfd,
    iteratedFDeriv_const_of_ne one_ne_zero, Pi.zero_apply]
  exact LinearIsometryEquiv.map_zero _

/-- The Laplacian of an affine function vanishes identically. -/
theorem laplacian_affine (c : ℝ) (L : 𝔼 →L[ℝ] ℝ) : Δ (fun z : 𝔼 => c + L z) = 0 := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  funext z
  simp only [iteratedFDeriv_two_affine c L z, zero_apply,
    Finset.sum_const_zero, Pi.zero_apply]

/-- **Affine functions are harmonic.**  (Mathlib has no such lemma.) -/
theorem harmonicOnNhd_affine (c : ℝ) (L : 𝔼 →L[ℝ] ℝ) (s : Set 𝔼) :
    HarmonicOnNhd (fun x => c + L x) s := by
  intro x _
  refine ⟨(contDiff_const.add L.contDiff).contDiffAt, ?_⟩
  rw [laplacian_affine c L]

/-- **Subtracting an affine competitor preserves harmonicity.** -/
theorem harmonicOnNhd_sub_affine {V : 𝔼 → ℝ} {s : Set 𝔼} (hV : HarmonicOnNhd V s)
    (c : ℝ) (L : 𝔼 →L[ℝ] ℝ) :
    HarmonicOnNhd (fun x => V x - (c + L x)) s := by
  intro x hx
  have hsum := (hV x hx).add (harmonicOnNhd_affine (-c) (-L) s x hx)
  have heq : (V + fun z : 𝔼 => (-c) + (-L) z) = fun z => V z - (c + L z) := by
    funext z
    simp only [Pi.add_apply, neg_apply]
    ring
  rwa [heq] at hsum

/-! ## 6. The `Vec d` affine competitor as a Euclidean continuous linear map -/

/-- The CoarseGraining coordinate dot product `vecDot g` realized as a continuous
linear functional on `EuclideanSpace ℝ (Fin d)`: the inner product against
`toEuc g`. -/
def dotCLM (g : Vec d) : 𝔼 →L[ℝ] ℝ := innerSL ℝ (toEuc g)

@[simp] theorem dotCLM_apply (g : Vec d) (x : 𝔼) :
    dotCLM g x = vecDot g (toEuc.symm x) := by
  simp only [dotCLM, innerSL_apply_apply, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, vecDot, toEuc_apply, toEuc_symm_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **Subtracting a `Vec d` affine competitor preserves harmonicity.**  If the
Euclidean avatar of `v : Vec d → ℝ` is harmonic, so is the avatar of
`y ↦ v y - (c + vecDot g y)`.  This is the step that upgrades a
constant-deviation interior estimate to an **excess** estimate. -/
theorem harmonicOnNhd_sub_vec_affine {v : Vec d → ℝ} {s : Set 𝔼}
    (hv : HarmonicOnNhd (v ∘ toEuc.symm) s) (c : ℝ) (g : Vec d) :
    HarmonicOnNhd ((fun y => v y - (c + vecDot g y)) ∘ toEuc.symm) s := by
  have h := harmonicOnNhd_sub_affine hv c (dotCLM g)
  have heq : ((fun y : Vec d => v y - (c + vecDot g y)) ∘ toEuc.symm)
      = fun x : 𝔼 => (v ∘ toEuc.symm) x - (c + dotCLM g x) := by
    funext x
    simp only [Function.comp_apply, dotCLM_apply]
  rw [heq]
  exact h

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
