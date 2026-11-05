/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderInteriorHess
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.AffineSplitLift

/-!
# OneStepSchauderExcess

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The interior Schauder atom in the §4 excess vocabulary

`OneStepSchauderInteriorHess` bounds the Lipschitz seminorm of `∇u` on the
half-radius ball by `C(d) r⁻²` times the `L²` deviation of `u` from **one**
constant, at the Euclidean carrier.  Three moves turn that into the atom
`[∇v]_{Lip(B_{r/2})} ≤ C(d) r⁻² E_raw(v, B_r)` the §4 excess machinery needs:

1. **affine competitors.**  `v − ℓ` is harmonic for every affine `ℓ`
   (`Schauder.harmonicOnNhd_sub_vec_affine`), and
   `∇(v−ℓ)(y) − ∇(v−ℓ)(z) = ∇v(y) − ∇v(z)`.  So the estimate holds against
   every competitor and passes to the infimum by
   `le_mul_affineExcessRaw_of_forall` — a *constant*-deviation bound becomes a
   genuine **excess** bound.
2. **carrier transfer.**  `Schauder.norm_fderiv_vec_sub_le` and
   `Schauder.norm_toEuc_le` move the estimate from `EuclideanSpace ℝ (Fin d)`
   (`ℓ²` norm) to `Vec d` (sup norm) at the cost of `√d · √d = d`.
3. **gradient field.**  `HasGradientOn`/`HolderSeminormBoundOn` of
   `AffineSplitLift`/`Support` are phrased through a gradient *field* `G : Vec
   d → Vec d`; `gradField v y i := (fderiv ℝ v y) (basisVec i)` is that field,
   `slopeCLM_gradField` identifies `slope (gradField v y)` with `fderiv ℝ v y`, and
   `norm_gradField_sub_le` bounds the sup-norm difference of the field by the
   operator-norm difference of the derivatives.

## The excess carrier

The §4 excess carrier is `Support.affineExcessRaw W v = sInf {‖v −
ℓ‖_{L²(W)}}` with `Support.affineDistOn W v c g = Support.normalizedL2On W (v
− affineEval c g)`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open HCPolySupport (Vec basisVec vecDot euclideanBall)
open HCPolySupport.Book.Ch01 (meanSquareDeviationOn)
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. Taking the infimum over affine competitors -/

/-- **The infimum-taking step.**  If a quantity `A` is bounded by `K` times the
`L²(W)` distance of `v` to *every* affine competitor `(c, g)`, then it is bounded
by `K` times the excess minimum `affineExcessRaw W v`.

This is the bridge from the harmonic interior estimates — which bound
derivatives of `v` by the deviation of `v` from a *fixed* competitor, and which
apply to `v − ℓ` for every affine `ℓ` because affine functions are harmonic — to
the **excess** the §4 contraction is stated in. -/
theorem le_mul_affineExcessRaw_of_forall {W : Set (Vec d)} {v : Vec d → ℝ} {A K : ℝ}
    (hK : 0 ≤ K) (h : ∀ (c : ℝ) (g : Vec d), A ≤ K * affineDistOn W v c g) :
    A ≤ K * affineExcessRaw W v := by
  rcases eq_or_lt_of_le hK with hK0 | hKpos
  · have h00 := h 0 0
    rw [← hK0, zero_mul] at h00 ⊢
    exact h00
  · have hne : (affineDistSet W v).Nonempty := affineDistSet_nonempty W v
    have hdiv : A / K ≤ affineExcessRaw W v := by
      refine le_csInf hne ?_
      rintro t ⟨p, rfl⟩
      rw [div_le_iff₀ hKpos, mul_comm]
      exact h p.1 p.2
    have hmul := (div_le_iff₀ hKpos).mp hdiv
    linarith only [hmul]

/-! ## 2. The dimensional constant -/

/-- The dimensional constant of the interior Schauder atom: `d` times the
constant of the native interior gradient-Lipschitz estimate
`interiorGradLipschitz_le_l2dev`.  The factor `d` is the round-trip cost
`√d · √d` of the `Vec d ↔ EuclideanSpace ℝ (Fin d)` norm comparison. -/
def schauderConst (d : ℕ) [NeZero d] : ℝ :=
  (d : ℝ) * (interiorGradLipschitz_le_l2dev d).choose

theorem schauderConst_nonneg (d : ℕ) [NeZero d] : 0 ≤ schauderConst d :=
  mul_nonneg (Nat.cast_nonneg d) (interiorGradLipschitz_le_l2dev d).choose_spec.1

/-! ## 3. Differentiability and the affine competitor at the `Vec d` carrier -/

/-- Differentiability at the `Vec d` carrier from harmonicity of the Euclidean
avatar. -/
theorem differentiableAt_of_harmonic_avatar {v : Vec d → ℝ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hv : HarmonicOnNhd (v ∘ toEuc.symm) s)
    {y : Vec d} (hy : toEuc y ∈ s) : DifferentiableAt ℝ v y := by
  have h1 : DifferentiableAt ℝ (v ∘ toEuc.symm) (toEuc y) :=
    ((hv _ hy).1).differentiableAt (by norm_num)
  have h2 : DifferentiableAt ℝ ((v ∘ toEuc.symm) ∘ toEuc) y :=
    h1.comp y (toEuc : Vec d ≃L[ℝ] EuclideanSpace ℝ (Fin d)).differentiableAt
  rwa [comp_toEuc_symm_toEuc] at h2

/-- The `Vec d` affine slope `x ↦ g · x` as a continuous linear functional. -/
def vecDotCLM (g : Vec d) : Vec d →L[ℝ] ℝ :=
  (dotCLM g).comp (toEuc : Vec d ≃L[ℝ] EuclideanSpace ℝ (Fin d)).toContinuousLinearMap

@[simp] theorem vecDotCLM_apply (g x : Vec d) : vecDotCLM g x = vecDot g x := by
  simp only [vecDotCLM, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, dotCLM_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- The affine function `affineEval c g` has derivative `vecDot g` everywhere. -/
theorem hasFDerivAt_affineEval (c : ℝ) (g y : Vec d) :
    HasFDerivAt (affineEval c g) (vecDotCLM g) y := by
  have h : HasFDerivAt (fun x : Vec d => c + vecDotCLM g x) (vecDotCLM g) y := by
    simpa using (vecDotCLM g).hasFDerivAt.const_add c
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  simp [affineEval]

/-! ## 4. The interior Schauder atom in the excess vocabulary -/

/-- **The interior Schauder atom, `Vec d` carrier.**  For `v` whose Euclidean
avatar is harmonic on `B(toEuc a, R)` and any `0 < r < R`, the gradient of `v`
is Lipschitz on `euclideanBall a (r/2)` with constant

`schauderConst d · r⁻¹ · r⁻¹ · affineExcessRaw (euclideanBall a r) v`. -/
theorem gradLipschitz_le_affineExcessRaw_of_harmonic [NeZero d] {v : Vec d → ℝ} {a : Vec d}
    {r R : ℝ} (hr : 0 < r) (hR : r < R)
    (hharm : HarmonicOnNhd (v ∘ toEuc.symm) (Metric.ball (toEuc a) R))
    {y z : Vec d} (hy : y ∈ euclideanBall a (r / 2)) (hz : z ∈ euclideanBall a (r / 2)) :
    ‖fderiv ℝ v y - fderiv ℝ v z‖
      ≤ (schauderConst d * r⁻¹ * r⁻¹ * affineExcessRaw (euclideanBall a r) v) * ‖y - z‖ := by
  obtain ⟨hC0, hC⟩ := (interiorGradLipschitz_le_l2dev d).choose_spec
  set C : ℝ := (interiorGradLipschitz_le_l2dev d).choose with hCdef
  have hr2 : (0 : ℝ) < r / 2 := by linarith only [hr]
  have hy' : toEuc y ∈ Metric.ball (toEuc a) (r / 2) :=
    (mem_euclideanBall_toEuc_iff y a hr2).mpr hy
  have hz' : toEuc z ∈ Metric.ball (toEuc a) (r / 2) :=
    (mem_euclideanBall_toEuc_iff z a hr2).mpr hz
  have hballR : Metric.ball (toEuc a) (r / 2) ⊆ Metric.ball (toEuc a) R :=
    Metric.ball_subset_ball (by linarith only [hr, hR])
  have hvy : DifferentiableAt ℝ v y := differentiableAt_of_harmonic_avatar hharm (hballR hy')
  have hvz : DifferentiableAt ℝ v z := differentiableAt_of_harmonic_avatar hharm (hballR hz')
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hsqd : Real.sqrt d * Real.sqrt d = (d : ℝ) := Real.mul_self_sqrt hd0
  have key : ∀ (c : ℝ) (g : Vec d),
      ‖fderiv ℝ v y - fderiv ℝ v z‖
        ≤ (schauderConst d * r⁻¹ * r⁻¹ * ‖y - z‖) *
            affineDistOn (euclideanBall a r) v c g := by
    intro c g
    set w : Vec d → ℝ := fun x => v x - affineEval c g x with hwdef
    have hwharm : HarmonicOnNhd (w ∘ toEuc.symm) (Metric.ball (toEuc a) R) :=
      harmonicOnNhd_sub_vec_affine hharm c g
    have hA := hC (w ∘ toEuc.symm) (toEuc a) (R := R) (r := r) (0 : ℝ) hr hR hwharm
      (toEuc y) hy' (toEuc z) hz'
    have hmsd : Real.sqrt (meanSquareDeviationOn (euclideanBall (toEuc.symm (toEuc a)) r)
        ((w ∘ toEuc.symm) ∘ toEuc) 0) = affineDistOn (euclideanBall a r) v c g := by
      rw [ContinuousLinearEquiv.symm_apply_apply, comp_toEuc_symm_toEuc]
      have h2 : meanSquareDeviationOn (euclideanBall a r) w 0
          = HCPolySupport.volumeAverage (euclideanBall a r) (fun x => (w x) ^ 2) := by
        simp only [meanSquareDeviationOn, sub_zero]
      rw [h2]
      rfl
    rw [hmsd] at hA
    have hfw : ∀ p : Vec d, DifferentiableAt ℝ v p →
        fderiv ℝ w p = fderiv ℝ v p - vecDotCLM g := fun p hp =>
      (hp.hasFDerivAt.sub (hasFDerivAt_affineEval c g p)).fderiv
    have hsub : fderiv ℝ w y - fderiv ℝ w z = fderiv ℝ v y - fderiv ℝ v z := by
      rw [hfw y hvy, hfw z hvz]; abel
    have htrans := norm_fderiv_vec_sub_le w y z
    rw [hsub] at htrans
    have hyz : ‖(toEuc y : EuclideanSpace ℝ (Fin d)) - toEuc z‖ ≤ Real.sqrt d * ‖y - z‖ := by
      have hmap := norm_toEuc_le (y - z)
      rwa [map_sub] at hmap
    have hrhs0 : (0 : ℝ) ≤ C * r⁻¹ * r⁻¹ * affineDistOn (euclideanBall a r) v c g :=
      mul_nonneg (by positivity) (affineDistOn_nonneg _ _ _ _)
    calc ‖fderiv ℝ v y - fderiv ℝ v z‖
        ≤ Real.sqrt d * ‖fderiv ℝ (w ∘ toEuc.symm) (toEuc y)
            - fderiv ℝ (w ∘ toEuc.symm) (toEuc z)‖ := htrans
      _ ≤ Real.sqrt d * ((C * r⁻¹ * r⁻¹ * affineDistOn (euclideanBall a r) v c g)
            * ‖(toEuc y : EuclideanSpace ℝ (Fin d)) - toEuc z‖) :=
          mul_le_mul_of_nonneg_left hA (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt d * ((C * r⁻¹ * r⁻¹ * affineDistOn (euclideanBall a r) v c g)
            * (Real.sqrt d * ‖y - z‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hyz hrhs0) (Real.sqrt_nonneg _)
      _ = ((Real.sqrt d * Real.sqrt d) * C * r⁻¹ * r⁻¹ * ‖y - z‖)
            * affineDistOn (euclideanBall a r) v c g := by ring
      _ = (schauderConst d * r⁻¹ * r⁻¹ * ‖y - z‖)
            * affineDistOn (euclideanBall a r) v c g := by
          rw [hsqd, schauderConst, hCdef]
  have hK0 : (0 : ℝ) ≤ schauderConst d * r⁻¹ * r⁻¹ * ‖y - z‖ :=
    mul_nonneg (mul_nonneg (mul_nonneg (schauderConst_nonneg d) (inv_nonneg.2 hr.le))
      (inv_nonneg.2 hr.le)) (norm_nonneg _)
  have hfinal := le_mul_affineExcessRaw_of_forall hK0 key
  refine hfinal.trans_eq ?_
  ring

/-! ## 5. The gradient field -/

/-- The gradient field of `v` in the `Vec d` carrier: the coordinate values of
`fderiv ℝ v`. -/
def gradField (v : Vec d → ℝ) (y : Vec d) : Vec d := fun i => (fderiv ℝ v y) (basisVec i)

theorem gradField_apply (v : Vec d → ℝ) (y : Vec d) (i : Fin d) :
    gradField v y i = (fderiv ℝ v y) (basisVec i) := rfl

/-- A coordinate vector is the sum of its coordinates against the basis. -/
theorem sum_smul_basisVec (w : Vec d) : ∑ i : Fin d, w i • (basisVec i : Vec d) = w := by
  funext j
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, HCPolySupport.basisVec_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ j (fun i => w i)]
  simp

/-- **The gradient field realizes the derivative.**  `slope (gradField v y)` is
`fderiv ℝ v y`. -/
theorem slopeCLM_gradField (v : Vec d → ℝ) (y : Vec d) :
    slopeCLM (gradField v y) = fderiv ℝ v y := by
  ext w
  rw [slopeCLM_apply, vecDot]
  calc ∑ i : Fin d, gradField v y i * w i
      = ∑ i : Fin d, (fderiv ℝ v y) (w i • (basisVec i : Vec d)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, smul_eq_mul, gradField_apply]
        ring
    _ = (fderiv ℝ v y) (∑ i : Fin d, w i • (basisVec i : Vec d)) := (map_sum _ _ _).symm
    _ = (fderiv ℝ v y) w := by rw [sum_smul_basisVec]

theorem norm_basisVec_eq_one (i : Fin d) : ‖basisVec (d := d) i‖ = 1 := by
  refine le_antisymm ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)).2 fun j => ?_
    by_cases h : j = i
    · subst h
      simp [HCPolySupport.basisVec_apply]
    · simp [HCPolySupport.basisVec_apply, h]
  · have hi : ‖basisVec (d := d) i i‖ ≤ ‖basisVec (d := d) i‖ := norm_le_pi_norm _ _
    simpa [HCPolySupport.basisVec_apply] using hi

/-- **From operator norms to gradient-field sup norms.**  The sup norm of the
difference of the gradient fields is at most the operator norm of the difference
of the derivatives. -/
theorem norm_gradField_sub_le (v : Vec d → ℝ) (x y : Vec d) :
    ‖gradField v x - gradField v y‖ ≤ ‖fderiv ℝ v x - fderiv ℝ v y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  have hcomp : (gradField v x - gradField v y) i
      = (fderiv ℝ v x - fderiv ℝ v y) (basisVec i) := by
    simp only [Pi.sub_apply, gradField_apply, sub_apply]
  rw [hcomp]
  calc ‖(fderiv ℝ v x - fderiv ℝ v y) (basisVec i)‖
      ≤ ‖fderiv ℝ v x - fderiv ℝ v y‖ * ‖basisVec (d := d) i‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ v x - fderiv ℝ v y‖ := by rw [norm_basisVec_eq_one i, mul_one]

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
