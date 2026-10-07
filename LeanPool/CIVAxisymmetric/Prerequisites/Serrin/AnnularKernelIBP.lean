/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.CutoffAnnulusSupport
public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.CutoffDerivs
public import LeanPool.CIVAxisymmetric.Identities.VorticityEquation
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SpatialDerivSupport
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.KernelAllOrdersBounds
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.KernelAllOrders

/-!
# Building blocks for the annular kernel integration-by-parts bound

Prerequisites for a kernel estimate of the interior estimates of `lem:aniso:annulus` (`∫
∂ₗN(x-y) D^{γ₁}χ(y) D^{γ₂}g(y,t) dy`,
bounded using only `|g| ≤ M`, no derivative bound on `g`): a Vec3-level mirror of
`CIV.multiPartial` built from `CKN.spatialDeriv` (`multiPartialVec3`), its deterministic peel
(shared with `CIV.multiPartial` via the same `peelDir`/`peelRest`, so the two peel in lockstep),
the ρ-scaling bound on `multiPartial` of the ball cutoff at any order, the Euclidean-norm bound
on the Newtonian kernel gradient differentiated up to two further times, and the fact that
`CIV.multiPartial g γ` is smooth on any open set on which `g` is smooth (generalizing
`CIV.contDiffOn_spatialPartial` from the unit cylinder to an arbitrary open set). The
integration-by-parts argument that moves the `γ₂` derivatives off `g` is in
`CIV/Prerequisites/Serrin/AnnularKernelBound.lean`.
-/

public section

open Set Filter
open CKN.Foundation.Parabolic CKN CKN.Foundation.Heat



noncomputable section

namespace CIV

/-! ## Part 0: a Vec3-level mirror of `multiPartial`, and its scaling bound -/

/-- The Vec3-level mirror of `multiPartial`, built from `CKN.spatialDeriv` instead of
`CIV.spatialPartial`. -/
@[expose] def multiPartialVec3 (k : Vec3 → ℝ) (γ : Fin 3 → ℕ) : Vec3 → ℝ :=
  (fun h => spatialDeriv h 0)^[γ 0]
    ((fun h => spatialDeriv h 1)^[γ 1] ((fun h => spatialDeriv h 2)^[γ 2] k))

private theorem multiPartialVec3_peel0 {γ : Fin 3 → ℕ} (h : 0 < γ 0) (k : Vec3 → ℝ) :
    multiPartialVec3 k γ = spatialDeriv (multiPartialVec3 k (Function.update γ 0 (γ 0 - 1))) 0 := by
  have hγ0 : γ 0 = (γ 0 - 1) + 1 := by omega
  have hu1 : Function.update γ 0 (γ 0 - 1) 1 = γ 1 := Function.update_of_ne (by decide) _ _
  have hu2 : Function.update γ 0 (γ 0 - 1) 2 = γ 2 := Function.update_of_ne (by decide) _ _
  have hu0 : Function.update γ 0 (γ 0 - 1) 0 = γ 0 - 1 := Function.update_self 0 _ γ
  unfold multiPartialVec3
  rw [hu0, hu1, hu2]
  conv_lhs => rw [hγ0]
  rw [Function.iterate_succ_apply']

private theorem multiPartialVec3_peel1 {γ : Fin 3 → ℕ} (h0 : γ 0 = 0) (h1 : 0 < γ 1)
    (k : Vec3 → ℝ) :
    multiPartialVec3 k γ = spatialDeriv (multiPartialVec3 k (Function.update γ 1 (γ 1 - 1))) 1 := by
  have hγ1 : γ 1 = (γ 1 - 1) + 1 := by omega
  have hu0 : Function.update γ 1 (γ 1 - 1) 0 = γ 0 := Function.update_of_ne (by decide) _ _
  have hu1 : Function.update γ 1 (γ 1 - 1) 1 = γ 1 - 1 := Function.update_self 1 _ γ
  have hu2 : Function.update γ 1 (γ 1 - 1) 2 = γ 2 := Function.update_of_ne (by decide) _ _
  unfold multiPartialVec3
  rw [hu0, hu1, hu2, h0]
  conv_lhs => rw [hγ1]
  rw [Function.iterate_succ_apply']
  simp

private theorem multiPartialVec3_peel2 {γ : Fin 3 → ℕ} (h0 : γ 0 = 0) (h1 : γ 1 = 0)
    (h2 : 0 < γ 2) (k : Vec3 → ℝ) :
    multiPartialVec3 k γ = spatialDeriv (multiPartialVec3 k (Function.update γ 2 (γ 2 - 1))) 2 := by
  have hγ2 : γ 2 = (γ 2 - 1) + 1 := by omega
  have hu0 : Function.update γ 2 (γ 2 - 1) 0 = γ 0 := Function.update_of_ne (by decide) _ _
  have hu1 : Function.update γ 2 (γ 2 - 1) 1 = γ 1 := Function.update_of_ne (by decide) _ _
  have hu2 : Function.update γ 2 (γ 2 - 1) 2 = γ 2 - 1 := Function.update_self 2 _ γ
  unfold multiPartialVec3
  rw [hu0, hu1, hu2, h0, h1]
  conv_lhs => rw [hγ2]
  rw [Function.iterate_succ_apply']
  simp

/-- The direction peeled off `γ` by the deterministic outermost-nonzero-exponent rule. -/
@[expose] def peelDir (γ : Fin 3 → ℕ) : Fin 3 := if γ 0 ≠ 0 then 0 else if γ 1 ≠ 0 then 1 else 2

/-- The multi-index left after peeling `peelDir γ` off `γ`. -/
@[expose] def peelRest (γ : Fin 3 → ℕ) : Fin 3 → ℕ := Function.update γ (peelDir γ) (γ (peelDir
  γ) - 1)

/-- The deterministic peel: the same direction and remainder work for every function `k`. -/
theorem multiPartialVec3_peel_det {γ : Fin 3 → ℕ} (hγ : γ 0 + γ 1 + γ 2 ≠ 0) (k : Vec3 → ℝ) :
    multiPartialVec3 k γ = spatialDeriv (multiPartialVec3 k (peelRest γ)) (peelDir γ) := by
  simp only [peelDir, peelRest]
  split_ifs with h0 h1
  · exact multiPartialVec3_peel0 (Nat.pos_of_ne_zero h0) k
  · exact multiPartialVec3_peel1 (by omega) (Nat.pos_of_ne_zero h1) k
  · exact multiPartialVec3_peel2 (by omega) (by omega) (by omega) k

theorem peelRest_order {γ : Fin 3 → ℕ} (hγ : γ 0 + γ 1 + γ 2 ≠ 0) :
    peelRest γ 0 + peelRest γ 1 + peelRest γ 2 + 1 = γ 0 + γ 1 + γ 2 := by
  unfold peelRest peelDir
  split_ifs with h0 h1
  · have e0 : Function.update γ 0 (γ 0 - 1) 0 = γ 0 - 1 := Function.update_self 0 _ γ
    have e1 : Function.update γ 0 (γ 0 - 1) 1 = γ 1 := Function.update_of_ne (by decide) _ _
    have e2 : Function.update γ 0 (γ 0 - 1) 2 = γ 2 := Function.update_of_ne (by decide) _ _
    rw [e0, e1, e2]; omega
  · have e0 : Function.update γ 1 (γ 1 - 1) 0 = γ 0 := Function.update_of_ne (by decide) _ _
    have e1 : Function.update γ 1 (γ 1 - 1) 1 = γ 1 - 1 := Function.update_self 1 _ γ
    have e2 : Function.update γ 1 (γ 1 - 1) 2 = γ 2 := Function.update_of_ne (by decide) _ _
    rw [e0, e1, e2]; omega
  · have e0 : Function.update γ 2 (γ 2 - 1) 0 = γ 0 := Function.update_of_ne (by decide) _ _
    have e1 : Function.update γ 2 (γ 2 - 1) 1 = γ 1 := Function.update_of_ne (by decide) _ _
    have e2 : Function.update γ 2 (γ 2 - 1) 2 = γ 2 - 1 := Function.update_self 2 _ γ
    rw [e0, e1, e2]; omega

/-- A nonzero spatial multi-index derivative of a Vec3 function peels one derivative off the
outermost nonvanishing exponent. -/
theorem multiPartialVec3_peel {γ : Fin 3 → ℕ} (hγ : γ 0 + γ 1 + γ 2 ≠ 0) (k : Vec3 → ℝ) :
    ∃ (j : Fin 3) (γ' : Fin 3 → ℕ), γ' 0 + γ' 1 + γ' 2 + 1 = γ 0 + γ 1 + γ 2 ∧
      multiPartialVec3 k γ = spatialDeriv (multiPartialVec3 k γ') j := by
  by_cases h0 : γ 0 = 0
  · by_cases h1 : γ 1 = 0
    · have h2 : 0 < γ 2 := by omega
      exact ⟨2, Function.update γ 2 (γ 2 - 1), by
        simp [Function.update_of_ne, Function.update_self, h0, h1]; omega,
        multiPartialVec3_peel2 h0 h1 h2 k⟩
    · have h1' : 0 < γ 1 := Nat.pos_of_ne_zero h1
      exact ⟨1, Function.update γ 1 (γ 1 - 1), by
        simp [Function.update_of_ne, Function.update_self, h0]; omega,
        multiPartialVec3_peel1 h0 h1' k⟩
  · have h0' : 0 < γ 0 := Nat.pos_of_ne_zero h0
    exact ⟨0, Function.update γ 0 (γ 0 - 1), by
      simp [Function.update_of_ne, Function.update_self]; omega,
      multiPartialVec3_peel0 h0' k⟩

/-! ## Part 0b: smoothness and the scale-shift identity for `multiPartialVec3` -/

private theorem contDiff_multiPartialVec3_aux :
    ∀ n : ℕ, ∀ γ : Fin 3 → ℕ, γ 0 + γ 1 + γ 2 = n → ∀ {k : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) k → ContDiff ℝ (⊤ : ℕ∞) (multiPartialVec3 k γ) := by
  intro n
  induction n with
  | zero =>
    intro γ hγ k hk
    have h0 : γ 0 = 0 := by omega
    have h1 : γ 1 = 0 := by omega
    have h2 : γ 2 = 0 := by omega
    simp only [multiPartialVec3, h0, h1, h2, Function.iterate_zero, id_eq]
    exact hk
  | succ n ih =>
    intro γ hγ k hk
    obtain ⟨j, γ', hγ'ord, hpeel⟩ := multiPartialVec3_peel (γ := γ) (by omega) k
    have hγ'n : γ' 0 + γ' 1 + γ' 2 = n := by omega
    rw [hpeel]
    exact contDiff_spatialDeriv_smooth (ih γ' hγ'n hk) j

theorem contDiff_multiPartialVec3 {k : Vec3 → ℝ} (hk : ContDiff ℝ (⊤ : ℕ∞) k) (γ : Fin 3 → ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (multiPartialVec3 k γ) :=
  contDiff_multiPartialVec3_aux (γ 0 + γ 1 + γ 2) γ rfl hk

private theorem spatialDeriv_const_smul (c : ℝ) {f : Vec3 → ℝ} (hf : Differentiable ℝ f)
    (i : Fin 3) (y : Vec3) :
    spatialDeriv (fun w => c * f w) i y = c * spatialDeriv f i y := by
  rw [spatialDeriv, show (fun w => c * f w) = fun w => c • f w from rfl,
    fderiv_fun_const_smul (hf y) c]
  simp [spatialDeriv, smul_eq_mul]

private theorem spatialDeriv_scale_shift {k : Vec3 → ℝ} (hk : Differentiable ℝ k) (c : ℝ)
    (x y : Vec3) (i : Fin 3) :
    spatialDeriv (fun w : Vec3 => k (c • (w - x))) i y =
      c * spatialDeriv k i (c • (y - x)) := by
  have h1 : HasFDerivAt (fun w : Vec3 => c • (w - x)) (c • (ContinuousLinearMap.id ℝ Vec3)) y := by
    have hsub : HasFDerivAt (fun w : Vec3 => w - x) (ContinuousLinearMap.id ℝ Vec3) y :=
      (hasFDerivAt_id y).sub_const x
    simpa using hsub.const_smul c
  have hcomp : HasFDerivAt (fun w : Vec3 => k (c • (w - x)))
      ((fderiv ℝ k (c • (y - x))).comp (c • (ContinuousLinearMap.id ℝ Vec3))) y :=
    (hk (c • (y - x))).hasFDerivAt.comp y h1
  rw [spatialDeriv, hcomp.fderiv]
  simp [spatialDeriv, smul_eq_mul]

private theorem multiPartialVec3_scale_shift_aux (c : ℝ) (x : Vec3) :
    ∀ n : ℕ, ∀ γ : Fin 3 → ℕ, γ 0 + γ 1 + γ 2 = n → ∀ {k : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) k → ∀ y : Vec3,
        multiPartialVec3 (fun w : Vec3 => k (c • (w - x))) γ y =
          c ^ n * multiPartialVec3 k γ (c • (y - x)) := by
  intro n
  induction n with
  | zero =>
    intro γ hγ k hk y
    have h0 : γ 0 = 0 := by omega
    have h1 : γ 1 = 0 := by omega
    have h2 : γ 2 = 0 := by omega
    simp only [multiPartialVec3, h0, h1, h2, Function.iterate_zero, id_eq, pow_zero, one_mul]
  | succ n ih =>
    intro γ hγ k hk y
    set j := peelDir γ with hjdef
    set γ' := peelRest γ with hγ'def
    have hγne : γ 0 + γ 1 + γ 2 ≠ 0 := by omega
    have hpeel : multiPartialVec3 (fun w : Vec3 => k (c • (w - x))) γ =
        spatialDeriv (multiPartialVec3 (fun w : Vec3 => k (c • (w - x))) γ') j :=
      multiPartialVec3_peel_det hγne (fun w : Vec3 => k (c • (w - x)))
    have hpeelk : multiPartialVec3 k γ = spatialDeriv (multiPartialVec3 k γ') j :=
      multiPartialVec3_peel_det hγne k
    have hγ'n : γ' 0 + γ' 1 + γ' 2 = n := by
      have hord := peelRest_order (γ := γ) hγne
      rw [← hγ'def] at hord
      omega
    have hIH : multiPartialVec3 (fun w : Vec3 => k (c • (w - x))) γ' =
        fun w : Vec3 => c ^ n * multiPartialVec3 k γ' (c • (w - x)) :=
      funext (ih γ' hγ'n hk)
    have hdiffγ' : Differentiable ℝ (multiPartialVec3 k γ') :=
      (contDiff_multiPartialVec3 hk γ').differentiable (by simp)
    have hdiffshift : Differentiable ℝ (fun w : Vec3 => multiPartialVec3 k γ' (c • (w - x))) :=
      hdiffγ'.comp ((differentiable_id.sub_const x).const_smul c)
    rw [show multiPartialVec3 (fun w : Vec3 => k (c • (w - x))) γ y =
        spatialDeriv (multiPartialVec3 (fun w : Vec3 => k (c • (w - x))) γ') j y from
        congrFun hpeel y,
      hIH,
      spatialDeriv_const_smul (c ^ n) hdiffshift j y,
      spatialDeriv_scale_shift hdiffγ' c x y j,
      show multiPartialVec3 k γ (c • (y - x)) = spatialDeriv (multiPartialVec3 k γ') j
        (c • (y - x)) from congrFun hpeelk (c • (y - x))]
    ring

/-! ## Part 0c: the deterministic peel for `CIV.multiPartial`, and the lift bridge -/

private theorem multiPartial_peelP0 {γ : Fin 3 → ℕ} (h : 0 < γ 0) (g : ParabolicPoint → ℝ) :
    multiPartial g γ = spatialPartial (multiPartial g (Function.update γ 0 (γ 0 - 1))) 0 := by
  have hγ0 : γ 0 = (γ 0 - 1) + 1 := by omega
  have hu1 : Function.update γ 0 (γ 0 - 1) 1 = γ 1 := Function.update_of_ne (by decide) _ _
  have hu2 : Function.update γ 0 (γ 0 - 1) 2 = γ 2 := Function.update_of_ne (by decide) _ _
  have hu0 : Function.update γ 0 (γ 0 - 1) 0 = γ 0 - 1 := Function.update_self 0 _ γ
  unfold multiPartial
  rw [hu0, hu1, hu2]
  conv_lhs => rw [hγ0]
  rw [Function.iterate_succ']
  rfl

private theorem multiPartial_peelP1 {γ : Fin 3 → ℕ} (h0 : γ 0 = 0) (h1 : 0 < γ 1)
    (g : ParabolicPoint → ℝ) :
    multiPartial g γ = spatialPartial (multiPartial g (Function.update γ 1 (γ 1 - 1))) 1 := by
  have hγ1 : γ 1 = (γ 1 - 1) + 1 := by omega
  have hu0 : Function.update γ 1 (γ 1 - 1) 0 = γ 0 := Function.update_of_ne (by decide) _ _
  have hu1 : Function.update γ 1 (γ 1 - 1) 1 = γ 1 - 1 := Function.update_self 1 _ γ
  have hu2 : Function.update γ 1 (γ 1 - 1) 2 = γ 2 := Function.update_of_ne (by decide) _ _
  unfold multiPartial
  rw [hu0, hu1, hu2, h0]
  conv_lhs => rw [hγ1]
  rw [Function.iterate_succ']
  simp

private theorem multiPartial_peelP2 {γ : Fin 3 → ℕ} (h0 : γ 0 = 0) (h1 : γ 1 = 0) (h2 : 0 < γ 2)
    (g : ParabolicPoint → ℝ) :
    multiPartial g γ = spatialPartial (multiPartial g (Function.update γ 2 (γ 2 - 1))) 2 := by
  have hγ2 : γ 2 = (γ 2 - 1) + 1 := by omega
  have hu0 : Function.update γ 2 (γ 2 - 1) 0 = γ 0 := Function.update_of_ne (by decide) _ _
  have hu1 : Function.update γ 2 (γ 2 - 1) 1 = γ 1 := Function.update_of_ne (by decide) _ _
  have hu2 : Function.update γ 2 (γ 2 - 1) 2 = γ 2 - 1 := Function.update_self 2 _ γ
  unfold multiPartial
  rw [hu0, hu1, hu2, h0, h1]
  conv_lhs => rw [hγ2]
  rw [Function.iterate_succ']
  simp

/-- The deterministic peel for `CIV.multiPartial`, using the same `peelDir`/`peelRest` as
`multiPartialVec3`, so the two peel in lockstep. -/
theorem multiPartial_peel_det {γ : Fin 3 → ℕ} (hγ : γ 0 + γ 1 + γ 2 ≠ 0) (g : ParabolicPoint → ℝ) :
    multiPartial g γ = spatialPartial (multiPartial g (peelRest γ)) (peelDir γ) := by
  simp only [peelDir, peelRest]
  split_ifs with h0 h1
  · exact multiPartial_peelP0 (Nat.pos_of_ne_zero h0) g
  · exact multiPartial_peelP1 (by omega) (Nat.pos_of_ne_zero h1) g
  · exact multiPartial_peelP2 (by omega) (by omega) (by omega) g

private theorem spatialPartial_lift_eq (k : Vec3 → ℝ) (i : Fin 3) (z : ParabolicPoint) :
    spatialPartial (fun w : ParabolicPoint => k w.1) i z = spatialDeriv k i z.1 := rfl

/-- `CIV.multiPartial` of a lifted, time-independent `Vec3` function is the lift of its
Vec3-level mirror `multiPartialVec3`. -/
theorem multiPartial_lift_eq_aux :
    ∀ n : ℕ, ∀ γ : Fin 3 → ℕ, γ 0 + γ 1 + γ 2 = n → ∀ (k : Vec3 → ℝ) (z : ParabolicPoint),
      multiPartial (fun w : ParabolicPoint => k w.1) γ z = multiPartialVec3 k γ z.1 := by
  intro n
  induction n with
  | zero =>
    intro γ hγ k z
    have h0 : γ 0 = 0 := by omega
    have h1 : γ 1 = 0 := by omega
    have h2 : γ 2 = 0 := by omega
    simp only [multiPartial, multiPartialVec3, h0, h1, h2, Function.iterate_zero, id_eq]
  | succ n ih =>
    intro γ hγ k z
    have hγne : γ 0 + γ 1 + γ 2 ≠ 0 := by omega
    have hγ'n : peelRest γ 0 + peelRest γ 1 + peelRest γ 2 = n := by
      have := peelRest_order (γ := γ) hγne; omega
    rw [multiPartial_peel_det hγne, multiPartialVec3_peel_det hγne]
    have heq : (fun w : ParabolicPoint => multiPartial (fun w' : ParabolicPoint => k w'.1)
        (peelRest γ) w) = fun w : ParabolicPoint => multiPartialVec3 k (peelRest γ) w.1 :=
      funext (ih (peelRest γ) hγ'n k)
    rw [show multiPartial (fun w' : ParabolicPoint => k w'.1) (peelRest γ) =
        fun w : ParabolicPoint => multiPartialVec3 k (peelRest γ) w.1 from heq]
    exact spatialPartial_lift_eq (multiPartialVec3 k (peelRest γ)) (peelDir γ) z

theorem multiPartial_lift_eq (k : Vec3 → ℝ) (γ : Fin 3 → ℕ) (z : ParabolicPoint) :
    multiPartial (fun w : ParabolicPoint => k w.1) γ z = multiPartialVec3 k γ z.1 :=
  multiPartial_lift_eq_aux (γ 0 + γ 1 + γ 2) γ rfl k z

/-! ## Part 0d: the ρ-scaling bound on `multiPartial` of the cutoff, at any order -/

private theorem hasCompactSupport_multiPartialVec3_aux :
    ∀ n : ℕ, ∀ γ : Fin 3 → ℕ, γ 0 + γ 1 + γ 2 = n → ∀ {k : Vec3 → ℝ},
      HasCompactSupport k → HasCompactSupport (multiPartialVec3 k γ) := by
  intro n
  induction n with
  | zero =>
    intro γ hγ k hk
    have h0 : γ 0 = 0 := by omega
    have h1 : γ 1 = 0 := by omega
    have h2 : γ 2 = 0 := by omega
    simp only [multiPartialVec3, h0, h1, h2, Function.iterate_zero, id_eq]
    exact hk
  | succ n ih =>
    intro γ hγ k hk
    have hγne : γ 0 + γ 1 + γ 2 ≠ 0 := by omega
    have hγ'n : peelRest γ 0 + peelRest γ 1 + peelRest γ 2 = n := by
      have := peelRest_order (γ := γ) hγne; omega
    rw [multiPartialVec3_peel_det hγne]
    exact hasCompactSupport_spatialDeriv (ih (peelRest γ) hγ'n hk) (peelDir γ)

theorem hasCompactSupport_multiPartialVec3 {k : Vec3 → ℝ} (hk : HasCompactSupport k)
    (γ : Fin 3 → ℕ) : HasCompactSupport (multiPartialVec3 k γ) :=
  hasCompactSupport_multiPartialVec3_aux (γ 0 + γ 1 + γ 2) γ rfl hk

/-- Every `multiPartialVec3` derivative of the fixed unit cutoff is bounded, uniformly in the
point (a fixed, `x`- and `ρ`-independent constant). -/
theorem exists_bound_multiPartialVec3_serrinBallCutoff (γ : Fin 3 → ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Vec3, |multiPartialVec3 (serrinBallCutoff 0 1) γ z| ≤ C := by
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (serrinBallCutoff (0 : Vec3) 1) :=
    (serrinBallCutoff_support (0 : Vec3) one_pos 0).2.2
  have hcont : Continuous (multiPartialVec3 (serrinBallCutoff 0 1) γ) :=
    (contDiff_multiPartialVec3 hsmooth γ).continuous
  have hcs : HasCompactSupport (multiPartialVec3 (serrinBallCutoff 0 1) γ) :=
    hasCompactSupport_multiPartialVec3 hasCompactSupport_serrinBallCutoff_unit γ
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hcs
  exact ⟨C, (norm_nonneg _).trans (hC 0), fun z => by
    simpa [Real.norm_eq_abs] using hC z⟩

/-- The ρ-scaling bound: every nonzero-or-zero order `multiPartial` derivative of the ball
cutoff `serrinBallCutoff x ρ` is bounded by an absolute constant (depending only on the order)
times `ρ^{-n}`. -/
theorem exists_bound_multiPartial_serrinBallCutoff_scaled (x : Vec3) {ρ : ℝ} (hρ : 0 < ρ)
    (γ : Fin 3 → ℕ) (t : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Vec3,
      |multiPartial (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1) γ (y, t)| ≤
        C / ρ ^ (γ 0 + γ 1 + γ 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_multiPartialVec3_serrinBallCutoff γ
  refine ⟨C, hC0, fun y => ?_⟩
  rw [show multiPartial (fun z : ParabolicPoint => serrinBallCutoff x ρ z.1) γ (y, t) =
      multiPartialVec3 (serrinBallCutoff x ρ) γ y from
      multiPartial_lift_eq (serrinBallCutoff x ρ) γ (y, t)]
  have heq : serrinBallCutoff x ρ = fun w : Vec3 => serrinBallCutoff 0 1 (ρ⁻¹ • (w - x)) := by
    funext w; exact serrinBallCutoff_eq_unit x hρ w
  rw [heq]
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (serrinBallCutoff (0 : Vec3) 1) :=
    (serrinBallCutoff_support (0 : Vec3) one_pos 0).2.2
  have hscaled := multiPartialVec3_scale_shift_aux ρ⁻¹ x (γ 0 + γ 1 + γ 2) γ rfl hsmooth y
  rw [hscaled, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ρ⁻¹ ^ (γ 0 + γ 1 + γ 2))]
  calc ρ⁻¹ ^ (γ 0 + γ 1 + γ 2) * |multiPartialVec3 (serrinBallCutoff 0 1) γ (ρ⁻¹ • (y - x))| ≤
      ρ⁻¹ ^ (γ 0 + γ 1 + γ 2) * C :=
        mul_le_mul_of_nonneg_left (hC _) (by positivity)
    _ = C / ρ ^ (γ 0 + γ 1 + γ 2) := by rw [inv_pow]; ring

/-! ## Part 0e: Euclidean-norm bounds on the Newtonian kernel gradient, orders 1-3 -/

private theorem norm_fderiv_apply_le {G : Vec3 → (Vec3 →L[ℝ] ℝ)} {z : Vec3}
    (hG : DifferentiableAt ℝ G z) (v : Vec3) :
    ‖fderiv ℝ (fun w => G w v) z‖ ≤ ‖fderiv ℝ G z‖ * ‖v‖ := by
  have hc : HasFDerivAt G (fderiv ℝ G z) z := hG.hasFDerivAt
  have hu : HasFDerivAt (fun _ : Vec3 => v) (0 : Vec3 →L[ℝ] Vec3) z := hasFDerivAt_const v z
  have h := hc.clm_apply hu
  simp only [ContinuousLinearMap.comp_zero, zero_add] at h
  rw [h.fderiv]
  calc ‖(fderiv ℝ G z).flip v‖ ≤ ‖(fderiv ℝ G z).flip‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ G z‖ * ‖v‖ := by rw [ContinuousLinearMap.opNorm_flip]

private theorem multiPartialVec3_order_zero_eq {k : Vec3 → ℝ} {β' : Fin 3 → ℕ}
    (hβ' : β' 0 + β' 1 + β' 2 = 0) : multiPartialVec3 k β' = k := by
  have e0 : β' 0 = 0 := by omega
  have e1 : β' 1 = 0 := by omega
  have e2 : β' 2 = 0 := by omega
  simp only [multiPartialVec3, e0, e1, e2, Function.iterate_zero, id_eq]

/-- The Newtonian kernel gradient, differentiated up to two further times, is bounded in terms
of the Euclidean distance to the origin. -/
theorem abs_multiPartialVec3_spatialDeriv_newtonianKernel_le (l : Fin 3) (β : Fin 3 → ℕ)
    (hβ : β 0 + β 1 + β 2 ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Vec3, z ≠ 0 →
      |multiPartialVec3 (spatialDeriv newtonianKernel l) β z| ≤
        C * (vec3EuclideanNorm z ^ (2 + (β 0 + β 1 + β 2)))⁻¹ := by
  set K := spatialDeriv newtonianKernel l with hKdef
  have hcases : β 0 + β 1 + β 2 = 0 ∨ β 0 + β 1 + β 2 = 1 ∨ β 0 + β 1 + β 2 = 2 := by omega
  rcases hcases with h | h | h
  · obtain ⟨c, hc0, hc⟩ := exists_norm_iteratedFDeriv_newtonianKernel_spatialDeriv_le l 0
    refine ⟨c, hc0, fun z hz => ?_⟩
    rw [multiPartialVec3_order_zero_eq h, h]
    calc |K z| ≤ ‖iteratedFDeriv ℝ 0 K z‖ := by
          rw [norm_iteratedFDeriv_zero]; exact le_of_eq (Real.norm_eq_abs _)
      _ ≤ c * (vec3EuclideanNorm z ^ (2 + 0))⁻¹ := hc z hz
  · obtain ⟨c, hc0, hc⟩ := exists_norm_iteratedFDeriv_newtonianKernel_spatialDeriv_le l 1
    refine ⟨c, hc0, fun z hz => ?_⟩
    rw [h]
    have hβ0 : β 0 + β 1 + β 2 ≠ 0 := by omega
    have hpeel := multiPartialVec3_peel_det hβ0 K
    have hrest0 : peelRest β 0 + peelRest β 1 + peelRest β 2 = 0 := by
      have := peelRest_order (γ := β) hβ0; omega
    rw [show multiPartialVec3 K β = spatialDeriv K (peelDir β) from
      hpeel.trans (by rw [multiPartialVec3_order_zero_eq hrest0])]
    calc |spatialDeriv K (peelDir β) z| = ‖(fderiv ℝ K z) (basisVec (peelDir β))‖ :=
          Real.norm_eq_abs _
      _ ≤ ‖fderiv ℝ K z‖ * ‖basisVec (peelDir β)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ K z‖ * 1 :=
          mul_le_mul_of_nonneg_left (norm_basisVec_le_one _) (norm_nonneg _)
      _ = ‖iteratedFDeriv ℝ 1 K z‖ := by rw [mul_one]; exact (norm_iteratedFDeriv_one K).symm
      _ ≤ c * (vec3EuclideanNorm z ^ (2 + 1))⁻¹ := hc z hz
  · obtain ⟨c, hc0, hc⟩ := exists_norm_iteratedFDeriv_newtonianKernel_spatialDeriv_le l 2
    refine ⟨c, hc0, fun z hz => ?_⟩
    rw [h]
    have hβ0 : β 0 + β 1 + β 2 ≠ 0 := by omega
    have hpeel := multiPartialVec3_peel_det hβ0 K
    have hrest1 : peelRest β 0 + peelRest β 1 + peelRest β 2 = 1 := by
      have := peelRest_order (γ := β) hβ0; omega
    have hrest0 : peelRest β 0 + peelRest β 1 + peelRest β 2 ≠ 0 := by omega
    have hpeel2 := multiPartialVec3_peel_det hrest0 K
    have hrestrest0 : peelRest (peelRest β) 0 + peelRest (peelRest β) 1 +
        peelRest (peelRest β) 2 = 0 := by
      have := peelRest_order (γ := peelRest β) hrest0; omega
    set j' := peelDir (peelRest β)
    set j := peelDir β
    have hval : multiPartialVec3 K β = spatialDeriv (spatialDeriv K j') j := by
      rw [hpeel, hpeel2, multiPartialVec3_order_zero_eq hrestrest0]
    rw [hval]
    have hdiffK : DifferentiableAt ℝ (fderiv ℝ K) z := by
      have hcd : ContDiffAt ℝ (2 : ℕ) K z := contDiffAt_newtonianKernel_spatialDeriv l 2 z hz
      exact (hcd.fderiv_right (m := (1 : ℕ)) (by norm_num)).differentiableAt (by norm_num)
    calc |spatialDeriv (spatialDeriv K j') j z| =
        ‖(fderiv ℝ (fun w => (fderiv ℝ K w) (basisVec j')) z) (basisVec j)‖ :=
          Real.norm_eq_abs _
      _ ≤ ‖fderiv ℝ (fun w => (fderiv ℝ K w) (basisVec j')) z‖ * ‖basisVec j‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ (fun w => (fderiv ℝ K w) (basisVec j')) z‖ * 1 :=
          mul_le_mul_of_nonneg_left (norm_basisVec_le_one _) (norm_nonneg _)
      _ ≤ (‖fderiv ℝ (fderiv ℝ K) z‖ * ‖basisVec j'‖) * 1 := by
          apply mul_le_mul_of_nonneg_right _ (by norm_num)
          exact norm_fderiv_apply_le hdiffK _
      _ ≤ (‖fderiv ℝ (fderiv ℝ K) z‖ * 1) * 1 := by
          apply mul_le_mul_of_nonneg_right _ (by norm_num)
          exact mul_le_mul_of_nonneg_left (norm_basisVec_le_one j')
            (norm_nonneg (fderiv ℝ (fderiv ℝ K) z))
      _ = ‖iteratedFDeriv ℝ 1 (fderiv ℝ K) z‖ := by
          rw [mul_one, mul_one]; exact (norm_iteratedFDeriv_one (fderiv ℝ K)).symm
      _ = ‖iteratedFDeriv ℝ 2 K z‖ := norm_iteratedFDeriv_fderiv
      _ ≤ c * (vec3EuclideanNorm z ^ (2 + 2))⁻¹ := hc z hz

/-! ## Part 1: smoothness of `multiPartial g β` on an open set, for general `O` -/

theorem contDiffOn_spatialPartial_openSet {g : ParabolicPoint → ℝ} {O : Set (Vec3 × ℝ)}
    (hO : IsOpen O) (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) O) (i : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => spatialPartial g i z) O := by
  have hD : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (fun z : Vec3 × ℝ => g z)) O :=
    hg.fderiv_of_isOpen hO (by norm_num)
  have hE : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => (fderiv ℝ (fun w : Vec3 × ℝ => g w) z) (basisVec i, (0 : ℝ))) O :=
    hD.clm_apply contDiffOn_const
  refine hE.congr fun z hz => ?_
  exact spatialPartial_eq_jointFDeriv
    ((hg.differentiableOn (by norm_num) z hz).differentiableAt (hO.mem_nhds hz)) i

private theorem contDiffOn_multiPartial_open_aux :
    ∀ n : ℕ, ∀ γ : Fin 3 → ℕ, γ 0 + γ 1 + γ 2 = n → ∀ {g : ParabolicPoint → ℝ} {O : Set (Vec3 × ℝ)},
      IsOpen O → ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) O →
        ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => multiPartial g γ z) O := by
  intro n
  induction n with
  | zero =>
    intro γ hγ g O hO hg
    have h0 : γ 0 = 0 := by omega
    have h1 : γ 1 = 0 := by omega
    have h2 : γ 2 = 0 := by omega
    simpa only [multiPartial, h0, h1, h2, Function.iterate_zero, id_eq] using hg
  | succ n ih =>
    intro γ hγ g O hO hg
    have hγne : γ 0 + γ 1 + γ 2 ≠ 0 := by omega
    have hγ'n : peelRest γ 0 + peelRest γ 1 + peelRest γ 2 = n := by
      have := peelRest_order (γ := γ) hγne; omega
    rw [multiPartial_peel_det hγne]
    exact contDiffOn_spatialPartial_openSet hO (ih (peelRest γ) hγ'n hO hg) (peelDir γ)

/-- `CIV.multiPartial g γ`, jointly in `z`, is smooth on any open set on which `g` is smooth. -/
theorem contDiffOn_multiPartial_open {g : ParabolicPoint → ℝ} {O : Set (Vec3 × ℝ)}
    (hO : IsOpen O) (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) O) (γ : Fin 3 → ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => multiPartial g γ z) O :=
  contDiffOn_multiPartial_open_aux (γ 0 + γ 1 + γ 2) γ rfl hO hg

/-- The time slice of `CIV.multiPartial g γ` is smooth on the spatial slice of `O`. -/
theorem contDiffOn_multiPartial_openSlice {g : ParabolicPoint → ℝ} {O : Set (Vec3 × ℝ)}
    (hO : IsOpen O) (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) O) (γ : Fin 3 → ℕ)
    (t : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Vec3 => multiPartial g γ (y, t)) {y : Vec3 | (y, t) ∈ O} := by
  have hjoint := contDiffOn_multiPartial_open hO hg γ
  have hemb : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => (y, t)) :=
    contDiff_id.prodMk contDiff_const
  exact hjoint.comp hemb.contDiffOn (fun y hy => hy)

end CIV
