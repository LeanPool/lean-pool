/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import LeanPool.KLS.FunctionalInequalities.Analysis.Tensor.SlotAction

/-!
# The energy form of a coordinate tensor

`energyForm A T = ⟨T, (A⁻¹)^{⊗r} T⟩` for an operator `A` and an order-`r` coordinate tensor `T` (BKL
arXiv:2610.05474v1, p. 22,
`F(A, T)`), the standard matrix of an operator, `energyForm 1 T = |T|²`, and smoothness near
invertible `A`.
-/

@[expose] public section

noncomputable section

open Matrix
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis.CoordinateTensor

variable {n r : ℕ}

/--
The matrix of an operator on `ℝⁿ` in the standard basis: `(stdMatrix H) i k = ⟪e_i, H e_k⟫`. -/
def stdMatrix (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i k =>
    ⟪EuclideanSpace.basisFun (Fin n) ℝ i, H (EuclideanSpace.basisFun (Fin n) ℝ k)⟫

/--
The energy form `F(A, T) = ⟨T, (A⁻¹)^{⊗r} T⟩ = Σ_{J,J'} T_J T_{J'} Π_s ⟪e_{J_s}, A⁻¹ e_{J'_s}⟫` of
BKL
arXiv:2610.05474v1, p. 22 (`A⁻¹ = Ring.inverse A`, the canonical inverse of the operator algebra).
-/
def energyForm (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (T : (Fin r → Fin n) → ℝ) : ℝ :=
  ∑ J : Fin r → Fin n,
    ∑ J' : Fin r → Fin n,
      T J * T J' *
        ∏ s,
          ⟪EuclideanSpace.basisFun (Fin n) ℝ (J s),
            Ring.inverse A (EuclideanSpace.basisFun (Fin n) ℝ (J' s))⟫

private lemma delta_product (J K : Fin r → Fin n) :
    (∏ s, if J s = K s then (1 : ℝ) else 0) =
      if J = K then 1 else 0 := by
  classical
  by_cases h : J = K
  · subst K
    simp
  · rw [ite_eq_right h]
    have hex : ∃ s, J s ≠ K s := by
      by_contra hnone
      apply h
      funext s
      by_contra hs
      exact hnone ⟨s, hs⟩
    obtain ⟨s, hs⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ s) (ite_eq_right hs)

/-- At `A = Id` the energy form is the Euclidean norm squared. -/
theorem energyForm_one (T : (Fin r → Fin n) → ℝ) : energyForm 1 T = inner T T := by
  classical
  simp only [energyForm, Ring.inverse_one, one_apply_eq_self,
    OrthonormalBasis.inner_eq_ite]
  simp_rw [delta_product]
  simp [inner, mul_ite]

/-- The energy form is `C²` near every `(A, T)` with `A` a unit. -/
theorem contDiffAt_energyForm (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : IsUnit A) (T : (Fin r → Fin n) → ℝ) :
    ContDiffAt ℝ 2
      (fun q :
          (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) × ((Fin r → Fin n) → ℝ) =>
        energyForm q.1 q.2)
      (A, T) := by
  classical
  have hinv : ContDiffAt ℝ 2 Ring.inverse A := by
    simpa only [hA.unit_spec] using contDiffAt_ringInverse ℝ hA.unit
  have hcoord (J : Fin r → Fin n) :
    ContDiffAt ℝ 2
      (fun q :
          (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) × ((Fin r → Fin n) → ℝ) =>
        q.2 J)
      (A, T) :=
    (ContinuousLinearMap.proj J : ((Fin r → Fin n) → ℝ) →L[ℝ] ℝ).contDiff.contDiffAt.comp (A, T)
      contDiffAt_snd
  unfold energyForm
  apply ContDiffAt.sum
  intro J _
  apply ContDiffAt.sum
  intro K _
  apply ContDiffAt.mul ((hcoord J).mul (hcoord K))
  apply contDiffAt_prod
  intro s _
  exact
    ContDiffAt.inner ℝ contDiffAt_const
      ((hinv.comp (A, T) contDiffAt_fst).clm_apply contDiffAt_const)

end FunctionalInequalities.Analysis.CoordinateTensor

section EnergyFormFirstDerivative

open Matrix
open scoped RealInnerProductSpace

/-! First derivative of the energy form at `A = Id` (BKL (88), first order). -/

namespace FunctionalInequalities.Analysis.CoordinateTensor

variable {n r : ℕ}

/--
**Delta collapse on all slots but one**: `Σ_{J'} f(J') Π_{s' ≠ s} δ_{J_{s'} J'_{s'}} = Σ_k f(J[s ↦
k])`. -/
theorem sum_mul_prod_delta_erase (J : Fin r → Fin n) (s : Fin r) (f : (Fin r → Fin n) → ℝ) :
    ∑ J' : Fin r → Fin n,
        f J' * ∏ s' ∈ Finset.univ.erase s, (if J s' = J' s' then (1 : ℝ) else 0) =
      ∑ k, f (Function.update J s k) := by
  classical
  let p : (Fin r → Fin n) → Prop := fun J' => ∀ s' ∈ Finset.univ.erase s, J s' = J' s'
  have hprod (J' : Fin r → Fin n) :
    (∏ s' ∈ Finset.univ.erase s, (if J s' = J' s' then (1 : ℝ) else 0)) =
      if p J' then 1 else 0 := by
    by_cases hp : p J'
    · simp only [p, ite_eq_left hp]
      apply Finset.prod_eq_one
      intro s' hs'
      exact ite_eq_left (hp s' hs')
    · rw [ite_eq_right hp]
      obtain ⟨s', hs', hne⟩ : ∃ s', s' ∈ Finset.univ.erase s ∧ J s' ≠ J' s' := by
        by_contra h
        apply hp
        intro s' hs'
        by_contra h'
        exact h ⟨s', hs', h'⟩
      exact Finset.prod_eq_zero hs' (ite_eq_right hne)
  have hfilter : Finset.univ.filter p = Finset.univ.image (Function.update J s) := by
    ext J'
    constructor
    · intro hJ'
      have hp : p J' := (Finset.mem_filter.mp hJ').2
      have heq : Function.update J s (J' s) = J' := by
        funext s'
        by_cases hss' : s' = s
        · subst s'
          simp
        · have hmem : s' ∈ Finset.univ.erase s := by simp [hss']
          simp [Function.update, hss', hp s' hmem]
      exact Finset.mem_image.mpr ⟨J' s, Finset.mem_univ _, heq⟩
    · intro hJ'
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hJ'
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · intro s' hs'
        have hne : s' ≠ s := by simpa using hs'
        simp [Function.update, hne]
  calc
    ∑ J' : Fin r → Fin n,
          f J' * ∏ s' ∈ Finset.univ.erase s, (if J s' = J' s' then (1 : ℝ) else 0) =
        ∑ J', if p J' then f J' else 0 := by
      apply Finset.sum_congr rfl
      intro J' hJ'
      rw [hprod]
      by_cases hp : p J' <;> simp [hp]
    _ = ∑ J' ∈ Finset.univ.filter p, f J' := by rw [← Finset.sum_filter]
    _ = ∑ J' ∈ Finset.univ.image (Function.update J s), f J' := by rw [hfilter]
    _ = ∑ k, f (Function.update J s k) := by
      rw [Finset.sum_image]
      intro k hk l hl hkl
      exact (Function.update_injective J s) hkl

private lemma inverse_line {R : Type*} [NormedRing R]
    [NormedAlgebra ℝ R] [HasSummableGeomSeries R] (H : R) :
    HasDerivAt (fun t : ℝ => Ring.inverse (1 + t • H)) (-H) 0 := by
  have hl : HasDerivAt (fun t : ℝ => (1 : R) + t • H) H 0 := by
    simpa only [id_eq, one_smul] using
      (((hasDerivAt_id (0 : ℝ)).smul_const H).const_add (1 : R))
  have hi :
      HasFDerivAt Ring.inverse
        (-((ContinuousLinearMap.mulLeftRight ℝ R) (1 : R)) (1 : R))
        ((1 : R) + (0 : ℝ) • H) := by
    simpa only [zero_smul, add_zero, inv_one, Units.val_one] using
      (hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : Rˣ))
  have hc := hi.comp_hasDerivAt 0 hl
  have heq :
      (-((ContinuousLinearMap.mulLeftRight ℝ R) (1 : R)) (1 : R)) H = -H := by
    change -((1 : R) * H * 1) = -H
    rw [one_mul, mul_one]
  simpa only [Function.comp_def] using hc.congr_deriv heq

/-- The entries of `(1 + εH)⁻¹` have derivative `−⟪e_i, H e_k⟫` at `ε = 0`. -/
theorem hasDerivAt_inner_ringInverse_one_add
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (i k : Fin n) :
    HasDerivAt
      (fun ε : ℝ =>
        ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
          Ring.inverse (1 + ε • H) (EuclideanSpace.basisFun (Fin n) ℝ k)⟫)
      (-⟪EuclideanSpace.basisFun (Fin n) ℝ i, H (EuclideanSpace.basisFun (Fin n) ℝ k)⟫) 0 := by
  have hi : HasDerivAt (fun t : ℝ => Ring.inverse (1 + t • H)) (-H) 0 := by
    convert inverse_line H using 1
  have hv := hi.clm_apply (hasDerivAt_const (0 : ℝ) (EuclideanSpace.basisFun (Fin n) ℝ k))
  have h := (hasDerivAt_const (0 : ℝ) (EuclideanSpace.basisFun (Fin n) ℝ i)).inner ℝ hv
  simpa using h

/-- The directional derivative is the derivative along the line. -/
theorem fderiv_apply_eq_deriv_line {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {Φ : W → ℝ} {y : W} (hΦ : DifferentiableAt ℝ Φ y) (v : W) :
    fderiv ℝ Φ y v = deriv (fun ε : ℝ => Φ (y + ε • v)) 0 := by
  let line : ℝ → W := fun ε => y + ε • v
  have hl : HasDerivAt line v 0 := by
    simpa only [line, id_eq, one_smul] using
      (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y)
  have hp : HasFDerivAt Φ (fderiv ℝ Φ y) (line 0) := by simpa [line] using hΦ.hasFDerivAt
  have hd := (hp.comp_hasDerivAt 0 hl).deriv.symm
  change fderiv ℝ Φ y v = deriv (fun ε : ℝ => Φ (y + ε • v)) 0 at hd
  exact hd

private lemma real_deriv_mul {f g : ℝ → ℝ} {df dg x : ℝ} (hf : HasDerivAt f df x)
    (hg : HasDerivAt g dg x) : HasDerivAt (fun t => f t * g t) (df * g x + f x * dg) x := by
  convert hf.mul hg using 1

private lemma real_deriv_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → ℝ) (df : ι → ℝ) (x : ℝ)
    (hf : ∀ i ∈ s, HasDerivAt (f i) (df i) x) :
    HasDerivAt (fun t => ∑ i ∈ s, f i t) (∑ i ∈ s, df i) x := by
  have h := HasDerivAt.sum hf
  have he : (∑ i ∈ s, f i) = (fun t => ∑ i ∈ s, f i t) := by
    funext t
    simp
  rw [he] at h
  convert h using 1

private lemma real_deriv_prod {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℝ → ℝ) (df : ι → ℝ) (x : ℝ)
    (hf : ∀ i ∈ s, HasDerivAt (f i) (df i) x) :
    HasDerivAt (fun t => ∏ i ∈ s, f i t)
      (∑ i ∈ s, (∏ j ∈ s.erase i, f j x) * df i) x := by
  have h := HasDerivAt.finsetProd hf
  have he : (∏ i ∈ s, f i) = (fun t => ∏ i ∈ s, f i t) := by
    funext t
    simp
  rw [he] at h
  simp only [smul_eq_mul] at h
  convert h using 1

private lemma slot_derivative_sum
    (T : (Fin r → Fin n) → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    (∑ J : Fin r → Fin n, ∑ K : Fin r → Fin n,
      T J * T K * (∑ s : Fin r,
        (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) *
          (-M (J s) (K s)))) =
      -inner T (actSum M T) := by
  classical
  let D (s : Fin r) (J K : Fin r → Fin n) : ℝ :=
    ∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0
  have hc (s : Fin r) (J : Fin r → Fin n) :
      (∑ K, (T K * M (J s) (K s)) * D s J K) =
        ∑ k, T (Function.update J s k) * M (J s) k := by
    simpa only [D, Function.update_self] using
      sum_mul_prod_delta_erase J s (fun K => T K * M (J s) (K s))
  have hs (s : Fin r) (J : Fin r → Fin n) :
      (∑ K, T J * T K * (D s J K * (-M (J s) (K s)))) =
        -(T J * actOn M s T J) := by
    calc
      (∑ K, T J * T K * (D s J K * (-M (J s) (K s)))) =
          ∑ K, -(T J * ((T K * M (J s) (K s)) * D s J K)) := by
        apply Finset.sum_congr rfl
        intro K _
        ring
      _ = -(T J * ∑ K, (T K * M (J s) (K s)) * D s J K) := by
        rw [Finset.sum_neg_distrib, Finset.mul_sum]
      _ = -(T J * actOn M s T J) := by
        rw [hc]
        apply congrArg (fun z : ℝ => -(T J * z))
        unfold actOn
        apply Finset.sum_congr rfl
        intro k _
        exact mul_comm _ _
  have hJ (J : Fin r → Fin n) :
      (∑ K, T J * T K * (∑ s, D s J K * (-M (J s) (K s)))) =
        -(T J * actSum M T J) := by
    calc
      (∑ K, T J * T K * (∑ s, D s J K * (-M (J s) (K s)))) =
          ∑ K, ∑ s, T J * T K * (D s J K * (-M (J s) (K s))) := by
        simp only [Finset.mul_sum]
      _ = ∑ s, ∑ K, T J * T K * (D s J K * (-M (J s) (K s))) := by
        rw [Finset.sum_comm]
      _ = ∑ s, -(T J * actOn M s T J) := by
        apply Finset.sum_congr rfl
        intro s _
        exact hs s J
      _ = -(T J * actSum M T J) := by
        unfold actSum
        rw [Finset.sum_neg_distrib, Finset.mul_sum]
  change (∑ J, ∑ K, T J * T K * (∑ s, D s J K * (-M (J s) (K s)))) =
    -inner T (actSum M T)
  calc
    (∑ J, ∑ K, T J * T K * (∑ s, D s J K * (-M (J s) (K s)))) =
        ∑ J, -(T J * actSum M T J) := by
      apply Finset.sum_congr rfl
      intro J _
      exact hJ J
    _ = -inner T (actSum M T) := by
      simp only [inner, Finset.sum_neg_distrib]

/--
**BKL (88), first order, along the line**: `d/dε F(1 + εH, T + εX)|₀ = 2⟨T, X⟩ − ⟨T, Σ_H T⟩`. -/
theorem hasDerivAt_energyForm_line (T : (Fin r → Fin n) → ℝ)
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (X : (Fin r → Fin n) → ℝ) :
    HasDerivAt (fun ε : ℝ => energyForm (1 + ε • H) (T + ε • X))
      (2 * inner T X - inner T (actSum (stdMatrix H) T)) 0 := by
  classical
  let a (i k : Fin n) (t : ℝ) : ℝ :=
    ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
      Ring.inverse (1 + t • H) (EuclideanSpace.basisFun (Fin n) ℝ k)⟫
  let P (J K : Fin r → Fin n) : ℝ := ∏ s, if J s = K s then (1 : ℝ) else 0
  let Q (J K : Fin r → Fin n) : ℝ :=
    ∑ s,
      (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) * (-stdMatrix H (J s) (K s))
  have a0 (i k : Fin n) : a i k 0 = if i = k then 1 else 0 := by
    have hz : (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) + (0 : ℝ) • H = 1 := by
      apply ContinuousLinearMap.ext
      intro v
      change v + (0 : ℝ) • H v = v
      simp
    unfold a
    rw [hz, Ring.inverse_one]
    exact (EuclideanSpace.basisFun (Fin n) ℝ).inner_eq_ite i k
  have ha (i k : Fin n) : HasDerivAt (a i k) (-stdMatrix H i k) 0 :=
    hasDerivAt_inner_ringInverse_one_add H i k
  have hp (J K : Fin r → Fin n) : HasDerivAt (fun t => ∏ s, a (J s) (K s) t) (Q J K) 0 := by
    have h :=
      real_deriv_prod Finset.univ (fun s t => a (J s) (K s) t)
        (fun s => -stdMatrix H (J s) (K s)) 0 (fun s _ => ha (J s) (K s))
    apply h.congr_deriv
    simp only [a0, Q]
  have hp0 (J K : Fin r → Fin n) : (∏ s, a (J s) (K s) 0) = P J K := by simp only [a0, P]
  have ht (J : Fin r → Fin n) : HasDerivAt (fun t : ℝ => T J + t * X J) (X J) 0 := by
    simpa only [id_eq, one_mul] using
      (((hasDerivAt_id (0 : ℝ)).mul_const (X J)).const_add (T J))
  let d (J K : Fin r → Fin n) : ℝ := (X J * T K + T J * X K) * P J K + T J * T K * Q J K
  have hterm (J K : Fin r → Fin n) :
    HasDerivAt (fun t : ℝ => (T J + t * X J) * (T K + t * X K) * (∏ s, a (J s) (K s) t)) (d J K)
      0 := by
    have h := real_deriv_mul (real_deriv_mul (ht J) (ht K)) (hp J K)
    apply h.congr_deriv
    simp only [zero_mul, add_zero, hp0, d]
  have hraw :
    HasDerivAt
      (fun t : ℝ => ∑ J, ∑ K, (T J + t * X J) * (T K + t * X K) * (∏ s, a (J s) (K s) t))
      (∑ J, ∑ K, d J K) 0 := by
    apply real_deriv_sum
    intro J _
    apply real_deriv_sum
    intro K _
    exact hterm J K
  have hfirst : (∑ J, ∑ K, (X J * T K + T J * X K) * P J K) = 2 * inner T X := by
    calc
      (∑ J, ∑ K, (X J * T K + T J * X K) * P J K) = ∑ J, (X J * T J + T J * X J) := by
        apply Finset.sum_congr rfl
        intro J _
        simp [P, delta_product, mul_ite]
      _ = ∑ J, 2 * (T J * X J) := by
        apply Finset.sum_congr rfl
        intro J _
        ring
      _ = 2 * inner T X := by
        rw [← Finset.mul_sum]
        rfl
  have hsecond : (∑ J, ∑ K, T J * T K * Q J K) = -inner T (actSum (stdMatrix H) T) :=
    slot_derivative_sum T (stdMatrix H)
  have hd : (∑ J, ∑ K, d J K) = 2 * inner T X - inner T (actSum (stdMatrix H) T) := by
    simp only [d, Finset.sum_add_distrib]
    rw [hfirst, hsecond]
    rfl
  have h := hraw.congr_deriv hd
  convert h using 1
  rfl

/-- **BKL (88), first order**: `DF(Id, T)[(H, X)] = 2⟨T, X⟩ − ⟨T, Σ_H T⟩`. -/
theorem fderiv_energyForm_one (T : (Fin r → Fin n) → ℝ)
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (X : (Fin r → Fin n) → ℝ) :
    fderiv ℝ
        (fun q :
            (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) × ((Fin r → Fin n) → ℝ) =>
          energyForm q.1 q.2)
        (1, T) (H, X) =
      2 * inner T X - inner T (actSum (stdMatrix H) T) := by
  have hdiff :=
    (contDiffAt_energyForm (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
          isUnit_one T).differentiableAt
      (by norm_num)
  rw [fderiv_apply_eq_deriv_line hdiff (H, X)]
  change
    deriv (fun t : ℝ => energyForm (1 + t • H) (T + t • X)) 0 =
      2 * inner T X - inner T (actSum (stdMatrix H) T)
  exact (hasDerivAt_energyForm_line T H X).deriv

end FunctionalInequalities.Analysis.CoordinateTensor

end EnergyFormFirstDerivative

section EnergyFormSecondDerivativeCalculus

open Matrix
open scoped RealInnerProductSpace

/-! Helpers for the second-order expansion of the energy form: a double-erasure product sum and line
derivatives of `⟪(1 + tB)⁻¹ ·, ·⟫`. -/

namespace FunctionalInequalities.Analysis.CoordinateTensor

variable {n r : ℕ}

section StructuredSpace

variable {R : Type*}
  [NormedRing R] [NormedAlgebra ℝ R] [HasSummableGeomSeries R]

private lemma inverse_line_at_unit
    (H : R) (t : ℝ) (ht : IsUnit (1 + t • H)) :
    HasDerivAt (fun x : ℝ => Ring.inverse (1 + x • H))
      (-(Ring.inverse (1 + t • H) * H * Ring.inverse (1 + t • H))) t := by
  have hl : HasDerivAt (fun x : ℝ => (1 : R) + x • H) H t := by
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id t).smul_const H).const_add (1 : R)
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) ht.unit
  rw [ht.unit_spec] at hi
  have hc := hi.comp_hasDerivAt t hl
  simpa only [Function.comp_def, _root_.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, ← Ring.inverse_unit, ht.unit_spec] using hc

end StructuredSpace

section NormedSpace

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

private lemma inverse_entry_at_unit
    (H : E →L[ℝ] E) (L : E →L[ℝ] ℝ) (v : E) (t : ℝ)
    (ht : IsUnit (1 + t • H)) :
    HasDerivAt (fun x : ℝ => L (Ring.inverse (1 + x • H) v))
      (-L (Ring.inverse (1 + t • H) (H (Ring.inverse (1 + t • H) v)))) t := by
  have h := inverse_line_at_unit H t ht
  simpa only [Function.comp_def, _root_.neg_apply, mul_apply_eq_comp,
    map_zero, add_zero, map_neg] using
    L.hasFDerivAt.comp_hasDerivAt t (h.clm_apply (hasDerivAt_const t v))

private lemma inverse_entry_second
    (H : E →L[ℝ] E) (L : E →L[ℝ] ℝ) (v : E) :
    HasDerivAt (deriv fun t : ℝ => L (Ring.inverse (1 + t • H) v))
      (2 * L (H (H v))) 0 := by
  have hR := inverse_line H
  have hv := hR.clm_apply (hasDerivAt_const (0 : ℝ) v)
  have hHv := (hasDerivAt_const (0 : ℝ) H).clm_apply hv
  have hboth := hR.clm_apply hHv
  have hh := (-L).hasFDerivAt.comp_hasDerivAt 0 hboth
  have hd :
      HasDerivAt
        (fun t : ℝ =>
          -L (Ring.inverse (1 + t • H) (H (Ring.inverse (1 + t • H) v))))
        (2 * L (H (H v))) 0 := by
    simpa only [Function.comp_def, zero_smul, add_zero, Ring.inverse_one,
      one_apply_eq_self, _root_.neg_apply, _root_.zero_apply, map_zero,
      zero_add, map_neg, map_add, neg_add, neg_neg, two_mul] using hh
  have hopen : {t : ℝ | IsUnit (1 + t • H)} ∈ nhds (0 : ℝ) := by
    have hc : Continuous (fun t : ℝ => (1 : E →L[ℝ] E) + t • H) :=
      continuous_const.add (continuous_id.smul continuous_const)
    apply (Units.isOpen.preimage hc).mem_nhds
    change IsUnit ((1 : E →L[ℝ] E) + (0 : ℝ) • H)
    simpa only [zero_smul, add_zero] using
      (isUnit_one : IsUnit (1 : E →L[ℝ] E))
  have heq :
      (deriv fun t : ℝ => L (Ring.inverse (1 + t • H) v)) =ᶠ[nhds 0]
        (fun t : ℝ =>
          -L (Ring.inverse (1 + t • H) (H (Ring.inverse (1 + t • H) v)))) := by
    filter_upwards [hopen] with t ht
    exact (inverse_entry_at_unit H L v t ht).deriv
  exact hd.congr_of_eventuallyEq heq

end NormedSpace

/-- **Delta collapse on all slots but two**: for `s ≠ t`,
`Σ_{J'} f(J') Π_{s' ∉ {s,t}} δ_{J_{s'} J'_{s'}} = Σ_{k,l} f(J[s ↦ k][t ↦ l])`. -/
theorem sum_mul_prod_delta_erase_erase (J : Fin r → Fin n) {s t : Fin r} (hst : s ≠ t)
    (f : (Fin r → Fin n) → ℝ) :
    ∑ J' : Fin r → Fin n,
        f J' * ∏ s' ∈ (Finset.univ.erase s).erase t, (if J s' = J' s' then (1 : ℝ) else 0) =
      ∑ k, ∑ l, f (Function.update (Function.update J s k) t l) := by
  classical
  let p : (Fin r → Fin n) → Prop := fun J' => ∀ u ∈ (Finset.univ.erase s).erase t, J u = J' u
  let q : (Fin n × Fin n) → (Fin r → Fin n) := fun kl =>
    Function.update (Function.update J s kl.1) t kl.2
  have hprod (J' : Fin r → Fin n) :
    (∏ u ∈ (Finset.univ.erase s).erase t, (if J u = J' u then (1 : ℝ) else 0)) =
      if p J' then 1 else 0 := by
    by_cases hp : p J'
    · simp only [p, ite_eq_left hp]
      apply Finset.prod_eq_one
      intro u hu
      exact ite_eq_left (hp u hu)
    · rw [ite_eq_right hp]
      obtain ⟨u, hu, hne⟩ : ∃ u, u ∈ (Finset.univ.erase s).erase t ∧ J u ≠ J' u := by
        by_contra h
        apply hp
        intro u hu
        by_contra h'
        exact h ⟨u, hu, h'⟩
      exact Finset.prod_eq_zero hu (ite_eq_right hne)
  have hfilter : Finset.univ.filter p = Finset.univ.image q := by
    ext J'
    constructor
    · intro hJ'
      have hp : p J' := (Finset.mem_filter.mp hJ').2
      have heq : q (J' s, J' t) = J' := by
        funext u
        by_cases hus : u = s
        · subst u
          change Function.update (Function.update J s (J' s)) t (J' t) s = J' s
          rw [Function.update_of_ne hst, Function.update_self]
        · by_cases hut : u = t
          · subst u
            change Function.update (Function.update J s (J' s)) t (J' t) t = J' t
            rw [Function.update_self]
          · have hu : u ∈ (Finset.univ.erase s).erase t := by simp [hus, hut]
            change Function.update (Function.update J s (J' s)) t (J' t) u = J' u
            rw [Function.update_of_ne hut, Function.update_of_ne hus]
            exact hp u hu
      exact Finset.mem_image.mpr ⟨(J' s, J' t), Finset.mem_univ _, heq⟩
    · intro hJ'
      obtain ⟨kl, -, rfl⟩ := Finset.mem_image.mp hJ'
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · intro u hu
        have hut : u ≠ t := (Finset.mem_erase.mp hu).1
        have hus : u ≠ s := (Finset.mem_erase.mp (Finset.mem_erase.mp hu).2).1
        change J u = Function.update (Function.update J s kl.1) t kl.2 u
        rw [Function.update_of_ne hut, Function.update_of_ne hus]
  have hq : Function.Injective q := by
    intro kl kl' hkl
    have hs' := congrFun hkl s
    have ht' := congrFun hkl t
    have hk : kl.1 = kl'.1 := by
      simpa only [q, Function.update_of_ne hst, Function.update_self] using hs'
    have hl : kl.2 = kl'.2 := by simpa only [q, Function.update_self] using ht'
    exact Prod.ext hk hl
  calc
    ∑ J' : Fin r → Fin n,
          f J' * ∏ u ∈ (Finset.univ.erase s).erase t, (if J u = J' u then (1 : ℝ) else 0) =
        ∑ J', if p J' then f J' else 0 := by
      apply Finset.sum_congr rfl
      intro J' _
      rw [hprod]
      by_cases hp : p J' <;> simp [hp]
    _ = ∑ J' ∈ Finset.univ.filter p, f J' := by rw [← Finset.sum_filter]
    _ = ∑ J' ∈ Finset.univ.image q, f J' := by rw [hfilter]
    _ = ∑ kl : Fin n × Fin n, f (q kl) := by
      rw [Finset.sum_image]
      intro kl _ kl' _ hEq
      exact hq hEq
    _ = ∑ k, ∑ l, f (Function.update (Function.update J s k) t l) := by
      simpa only [q] using
        (Fintype.sum_prod_type
          (fun kl : Fin n × Fin n => f (Function.update (Function.update J s kl.1) t kl.2)))

/-- The entries of `(1 + εH)⁻¹` are differentiable near `ε = 0` with derivative
`−⟪e_i, (1+εH)⁻¹ H (1+εH)⁻¹ e_k⟫`. -/
theorem hasDerivAt_inner_ringInverse_one_add_of_isUnit
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (i k : Fin n) {ε : ℝ}
    (hε : IsUnit (1 + ε • H)) :
    HasDerivAt
      (fun ε : ℝ =>
        ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
          Ring.inverse (1 + ε • H) (EuclideanSpace.basisFun (Fin n) ℝ k)⟫)
      (-⟪EuclideanSpace.basisFun (Fin n) ℝ i,
          Ring.inverse (1 + ε • H)
            (H (Ring.inverse (1 + ε • H) (EuclideanSpace.basisFun (Fin n) ℝ k)))⟫)
      ε := by
  exact
    inverse_entry_at_unit H (innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ i))
      (EuclideanSpace.basisFun (Fin n) ℝ k) ε hε

/-- The second derivative of the entries of `(1 + εH)⁻¹` at `ε = 0` is `2⟪e_i, H² e_k⟫`. -/
theorem hasDerivAt_deriv_inner_ringInverse_one_add
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (i k : Fin n) :
    HasDerivAt
      (deriv fun ε : ℝ =>
        ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
          Ring.inverse (1 + ε • H) (EuclideanSpace.basisFun (Fin n) ℝ k)⟫)
      (2 * ⟪EuclideanSpace.basisFun (Fin n) ℝ i, H (H (EuclideanSpace.basisFun (Fin n) ℝ k))⟫)
      0 := by
  exact
    inverse_entry_second H (innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ i))
      (EuclideanSpace.basisFun (Fin n) ℝ k)

/-- The second directional derivative is the second derivative along the line. -/
theorem fderiv_fderiv_apply_eq_deriv_deriv_line {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {Φ : W → ℝ} {y : W} (hΦ : ContDiffAt ℝ 2 Φ y) (v : W) :
    fderiv ℝ (fderiv ℝ Φ) y v v = deriv (deriv fun ε : ℝ => Φ (y + ε • v)) 0 := by
  have hc : ContDiffAt ℝ 1 (fderiv ℝ Φ) y :=
    hΦ.fderiv_right (by norm_num)
  have hl (t : ℝ) : HasDerivAt (fun a : ℝ => y + a • v) v t := by
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id t).smul_const v).const_add y
  have hp :
      HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) y)
        (y + (0 : ℝ) • v) := by
    simpa only [zero_smul, add_zero] using
      (hc.differentiableAt (by norm_num)).hasFDerivAt
  have hd :
      HasDerivAt (fun t : ℝ => fderiv ℝ Φ (y + t • v))
        (fderiv ℝ (fderiv ℝ Φ) y v) 0 :=
    hp.comp_hasDerivAt 0 (hl 0)
  have hd' :
      deriv (fun t : ℝ => fderiv ℝ Φ (y + t • v) v) 0 =
        fderiv ℝ (fderiv ℝ Φ) y v v := by
    simpa only [map_zero, add_zero] using
      (hd.clm_apply (hasDerivAt_const (0 : ℝ) v)).deriv
  have ht :
      Filter.Tendsto (fun t : ℝ => y + t • v) (nhds 0) (nhds y) := by
    simpa only [ContinuousAt, zero_smul, add_zero] using (hl 0).continuousAt
  have heq :
      (deriv fun t : ℝ => Φ (y + t • v)) =ᶠ[nhds 0]
        (fun t : ℝ => fderiv ℝ Φ (y + t • v) v) := by
    filter_upwards [ht.eventually (hΦ.eventually (by norm_num))] with t h
    exact
      ((h.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hl t)).deriv
  exact hd'.symm.trans heq.deriv_eq.symm

end FunctionalInequalities.Analysis.CoordinateTensor

end EnergyFormSecondDerivativeCalculus

section EnergyFormSecondDerivative

open Matrix
open scoped RealInnerProductSpace

/-! Second derivative of the energy form along lines and at the identity (BKL (88), second order).
-/

namespace FunctionalInequalities.Analysis.CoordinateTensor

variable {n r : ℕ}

/-! ### Real-valued `HasDerivAt` combinators with beta-reduced function shapes -/

private lemma real_deriv_add {f g : ℝ → ℝ} {df dg x : ℝ}
    (hf : HasDerivAt f df x) (hg : HasDerivAt g dg x) :
    HasDerivAt (fun t => f t + g t) (df + dg) x :=
  hf.add hg

private lemma real_deriv_const_mul {f : ℝ → ℝ} {df x : ℝ} (c : ℝ)
    (hf : HasDerivAt f df x) :
    HasDerivAt (fun t => c * f t) (c * df) x :=
  hf.const_mul c

private lemma real_deriv_mul_const {f : ℝ → ℝ} {df x : ℝ} (c : ℝ)
    (hf : HasDerivAt f df x) :
    HasDerivAt (fun t => f t * c) (df * c) x :=
  hf.mul_const c

/--
One-slot delta collapse with two tensors: `Σ_{J,K} S_J T_K Σ_s Π_{u≠s} δ (−M_{J_s K_s}) = −⟨S, Σ_M
T⟩`. -/
private lemma slot_sum_two (S T : (Fin r → Fin n) → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    (∑ J : Fin r → Fin n,
        ∑ K : Fin r → Fin n,
          S J * T K *
            (∑ s : Fin r,
              (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) *
                (-M (J s) (K s)))) =
      -inner S (actSum M T) := by
  let D (s : Fin r) (J K : Fin r → Fin n) : ℝ :=
    ∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0
  have hc (s : Fin r) (J : Fin r → Fin n) :
    (∑ K, (T K * M (J s) (K s)) * D s J K) = ∑ k, T (Function.update J s k) * M (J s) k := by
    simpa only [D, Function.update_self] using
      sum_mul_prod_delta_erase J s (fun K => T K * M (J s) (K s))
  have hs (s : Fin r) (J : Fin r → Fin n) :
    (∑ K, S J * T K * (D s J K * (-M (J s) (K s)))) = -(S J * actOn M s T J) := by
    calc
      (∑ K, S J * T K * (D s J K * (-M (J s) (K s)))) =
          ∑ K, -(S J * ((T K * M (J s) (K s)) * D s J K)) := by
        apply Finset.sum_congr rfl
        intro K _
        ring
      _ = -(S J * ∑ K, (T K * M (J s) (K s)) * D s J K) := by
        rw [Finset.sum_neg_distrib, Finset.mul_sum]
      _ = -(S J * actOn M s T J) := by
        rw [hc]
        apply congrArg (fun z : ℝ => -(S J * z))
        unfold actOn
        apply Finset.sum_congr rfl
        intro k _
        exact mul_comm _ _
  have hJ (J : Fin r → Fin n) :
    (∑ K, S J * T K * (∑ s, D s J K * (-M (J s) (K s)))) = -(S J * actSum M T J) := by
    calc
      (∑ K, S J * T K * (∑ s, D s J K * (-M (J s) (K s)))) =
          ∑ K, ∑ s, S J * T K * (D s J K * (-M (J s) (K s))) := by
        simp only [Finset.mul_sum]
      _ = ∑ s, ∑ K, S J * T K * (D s J K * (-M (J s) (K s))) := by rw [Finset.sum_comm]
      _ = ∑ s, -(S J * actOn M s T J) := by
        apply Finset.sum_congr rfl
        intro s _
        exact hs s J
      _ = -(S J * actSum M T J) := by
        unfold actSum
        rw [Finset.sum_neg_distrib, Finset.mul_sum]
  change (∑ J, ∑ K, S J * T K * (∑ s, D s J K * (-M (J s) (K s)))) = -inner S (actSum M T)
  calc
    (∑ J, ∑ K, S J * T K * (∑ s, D s J K * (-M (J s) (K s)))) = ∑ J, -(S J * actSum M T J) := by
      apply Finset.sum_congr rfl
      intro J _
      exact hJ J
    _ = -inner S (actSum M T) := by simp only [inner, Finset.sum_neg_distrib]

private lemma inner_comm' (T S : (Fin r → Fin n) → ℝ) : inner T S = inner S T := by
  unfold inner
  apply Finset.sum_congr rfl
  intro J _
  exact mul_comm _ _

private lemma inner_actSum_eq_sum (N : Matrix (Fin n) (Fin n) ℝ) (T S : (Fin r → Fin n) → ℝ) :
    inner T (actSum N S) = ∑ s, inner T (actOn N s S) := by
  unfold inner actSum
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

private lemma inner_actSum_left (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm)
    (T S : (Fin r → Fin n) → ℝ) : inner (actSum M T) S = inner T (actSum M S) := by
  rw [inner_comm', inner_actSum_eq_sum, inner_actSum_eq_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [inner_comm']
  exact inner_actOn_left M hM s T S

/-- Two-slot delta collapse: the mixed second-order term is `Σ_s Σ_{u≠s} ⟨T, M^{(s)} M^{(u)} T⟩`. -/
private lemma two_slot_sum (T : (Fin r → Fin n) → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    (∑ J : Fin r → Fin n, ∑ K : Fin r → Fin n, T J * T K *
      (∑ s : Fin r, (∑ u ∈ Finset.univ.erase s,
        (∏ v ∈ (Finset.univ.erase s).erase u, if J v = K v then (1 : ℝ) else 0) *
          (-M (J u) (K u))) * (-M (J s) (K s)))) =
      ∑ s : Fin r, ∑ u ∈ Finset.univ.erase s, inner T (actOn M s (actOn M u T)) := by
  have key (J : Fin r → Fin n) (s u : Fin r) (hus : u ≠ s) :
      (∑ K : Fin r → Fin n, T J * T K *
        ((∏ v ∈ (Finset.univ.erase s).erase u, if J v = K v then (1 : ℝ) else 0) *
          (-M (J u) (K u)) * (-M (J s) (K s)))) =
        T J * actOn M s (actOn M u T) J := by
    have hsu : s ≠ u := Ne.symm hus
    have hc := sum_mul_prod_delta_erase_erase J hsu
      (fun K => T K * M (J s) (K s) * M (J u) (K u))
    calc
      (∑ K : Fin r → Fin n, T J * T K *
          ((∏ v ∈ (Finset.univ.erase s).erase u, if J v = K v then (1 : ℝ) else 0) *
            (-M (J u) (K u)) * (-M (J s) (K s)))) =
          T J * ∑ K : Fin r → Fin n, (T K * M (J s) (K s) * M (J u) (K u)) *
            ∏ v ∈ (Finset.univ.erase s).erase u, (if J v = K v then (1 : ℝ) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro K _
        ring
      _ = T J * ∑ k, ∑ l, T (Function.update (Function.update J s k) u l) *
            M (J s) k * M (J u) l := by
        rw [hc]
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        simp only [Function.update_self, Function.update_of_ne hsu]
      _ = T J * actOn M s (actOn M u T) J := by
        congr 1
        simp only [actOn, Function.update_of_ne hus]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
  calc
    (∑ J : Fin r → Fin n, ∑ K : Fin r → Fin n, T J * T K *
        (∑ s : Fin r, (∑ u ∈ Finset.univ.erase s,
          (∏ v ∈ (Finset.univ.erase s).erase u, if J v = K v then (1 : ℝ) else 0) *
            (-M (J u) (K u))) * (-M (J s) (K s)))) =
        ∑ J : Fin r → Fin n, ∑ s : Fin r, ∑ u ∈ Finset.univ.erase s,
          ∑ K : Fin r → Fin n, T J * T K *
            ((∏ v ∈ (Finset.univ.erase s).erase u, if J v = K v then (1 : ℝ) else 0) *
              (-M (J u) (K u)) * (-M (J s) (K s))) := by
      apply Finset.sum_congr rfl
      intro J _
      calc
        (∑ K : Fin r → Fin n, T J * T K *
            (∑ s : Fin r, (∑ u ∈ Finset.univ.erase s,
              (∏ v ∈ (Finset.univ.erase s).erase u, if J v = K v then (1 : ℝ) else 0) *
                (-M (J u) (K u))) * (-M (J s) (K s)))) =
            ∑ K : Fin r → Fin n, ∑ s : Fin r, ∑ u ∈ Finset.univ.erase s, T J * T K *
              ((∏ v ∈ (Finset.univ.erase s).erase u, if J v = K v then (1 : ℝ) else 0) *
                (-M (J u) (K u)) * (-M (J s) (K s))) := by
          apply Finset.sum_congr rfl
          intro K _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.sum_mul, Finset.mul_sum]
        _ = ∑ s : Fin r, ∑ u ∈ Finset.univ.erase s, ∑ K : Fin r → Fin n, T J * T K *
              ((∏ v ∈ (Finset.univ.erase s).erase u, if J v = K v then (1 : ℝ) else 0) *
                (-M (J u) (K u)) * (-M (J s) (K s))) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.sum_comm]
    _ = ∑ J : Fin r → Fin n, ∑ s : Fin r, ∑ u ∈ Finset.univ.erase s,
          T J * actOn M s (actOn M u T) J := by
      apply Finset.sum_congr rfl
      intro J _
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro u hu
      exact key J s u (Finset.ne_of_mem_erase hu)
    _ = ∑ s : Fin r, ∑ u ∈ Finset.univ.erase s, inner T (actOn M s (actOn M u T)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
      rfl

/-! ### The standard matrix of a self-adjoint operator -/

private lemma stdMatrix_isSymm (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : IsSelfAdjoint H) : (stdMatrix H).IsSymm := by
  have hsym : ∀ x y : EuclideanSpace ℝ (Fin n), ⟪H x, y⟫ = ⟪x, H y⟫ :=
    fun x y => (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hH) x y
  apply Matrix.IsSymm.ext
  intro i k
  change ⟪EuclideanSpace.basisFun (Fin n) ℝ k, H (EuclideanSpace.basisFun (Fin n) ℝ i)⟫ =
    ⟪EuclideanSpace.basisFun (Fin n) ℝ i, H (EuclideanSpace.basisFun (Fin n) ℝ k)⟫
  rw [← hsym, real_inner_comm]

private lemma inner_H_H (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : IsSelfAdjoint H) (i k : Fin n) :
    ⟪EuclideanSpace.basisFun (Fin n) ℝ i, H (H (EuclideanSpace.basisFun (Fin n) ℝ k))⟫ =
      (stdMatrix H * stdMatrix H) i k := by
  have hsym : ∀ x y : EuclideanSpace ℝ (Fin n), ⟪H x, y⟫ = ⟪x, H y⟫ := fun x y =>
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hH) x y
  rw [Matrix.mul_apply, ←
    hsym (EuclideanSpace.basisFun (Fin n) ℝ i) (H (EuclideanSpace.basisFun (Fin n) ℝ k)), ←
    (EuclideanSpace.basisFun (Fin n) ℝ).sum_inner_mul_inner
      (H (EuclideanSpace.basisFun (Fin n) ℝ i)) (H (EuclideanSpace.basisFun (Fin n) ℝ k))]
  apply Finset.sum_congr rfl
  intro j _
  change
    ⟪H (EuclideanSpace.basisFun (Fin n) ℝ i), EuclideanSpace.basisFun (Fin n) ℝ j⟫ *
        ⟪EuclideanSpace.basisFun (Fin n) ℝ j, H (EuclideanSpace.basisFun (Fin n) ℝ k)⟫ =
      ⟪EuclideanSpace.basisFun (Fin n) ℝ i, H (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ *
        ⟪EuclideanSpace.basisFun (Fin n) ℝ j, H (EuclideanSpace.basisFun (Fin n) ℝ k)⟫
  rw [hsym]

/-! ### The second derivative along the line -/

private theorem diagonalEnergySum (X : (Fin r → Fin n) → ℝ) :
    (∑ J, ∑ K, (X J * X K + X J * X K) *
        (∏ s, if J s = K s then (1 : ℝ) else 0)) = 2 * inner X X := by
  let P (J K : Fin r → Fin n) : ℝ := ∏ s, if J s = K s then (1 : ℝ) else 0
  calc
    (∑ J, ∑ K, (X J * X K + X J * X K) * P J K) =
        ∑ J, (X J * X J + X J * X J) := by
      apply Finset.sum_congr rfl
      intro J _
      simp [P, delta_product, mul_ite]
    _ = 2 * inner X X := by
      unfold inner
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro J _
      ring

private theorem sameSlotEnergySum (T : (Fin r → Fin n) → ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
      (∑ J, ∑ K, T J * T K * (∑ s,
          (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) *
            (2 * (M * M) (J s) (K s)))) =
        2 * ∑ s, inner (actOn M s T) (actOn M s T) := by
    have e := slot_sum_two T T (M * M)
    have hpt (J K : Fin r → Fin n) :
        (∑ s, (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) *
            (2 * (M * M) (J s) (K s))) =
          -2 * ∑ s, (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) *
            (-(M * M) (J s) (K s)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    calc
      (∑ J, ∑ K, T J * T K * (∑ s,
          (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) *
            (2 * (M * M) (J s) (K s)))) =
          ∑ J, ∑ K, -2 * (T J * T K * (∑ s,
            (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) *
              (-(M * M) (J s) (K s)))) := by
        apply Finset.sum_congr rfl
        intro J _
        apply Finset.sum_congr rfl
        intro K _
        rw [hpt]
        ring
      _ = -2 * ∑ J, ∑ K, T J * T K * (∑ s,
            (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) *
              (-(M * M) (J s) (K s))) := by
        simp only [Finset.mul_sum]
      _ = -2 * -inner T (actSum (M * M) T) := by
        rw [e]
      _ = 2 * ∑ s, inner (actOn M s T) (actOn M s T) := by
        rw [inner_actSum_eq_sum,
          Finset.sum_congr rfl (fun s _ => inner_actOn_mul_self M hM s T)]
        ring

/-- **BKL (88), second order, along the line**: for symmetric `H`,
`d²/dε² F(1 + εH, T + εX)|₀ = 2 (|X|² − 2⟨X, Σ_H T⟩ + ½|Σ_H T|² + ½ Σ_s |H^{(s)} T|²)`. -/
theorem deriv_deriv_energyForm_line (T : (Fin r → Fin n) → ℝ)
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hH : IsSelfAdjoint H)
    (X : (Fin r → Fin n) → ℝ) :
    deriv (deriv fun ε : ℝ => energyForm (1 + ε • H) (T + ε • X)) 0 =
      2 * (inner X X - 2 * inner X (actSum (stdMatrix H) T)
        + (1 / 2 : ℝ) * inner (actSum (stdMatrix H) T) (actSum (stdMatrix H) T)
        + (1 / 2 : ℝ) * ∑ s, inner (actOn (stdMatrix H) s T) (actOn (stdMatrix H) s T)) := by
  have hM : (stdMatrix H).IsSymm := stdMatrix_isSymm H hH
  -- Differentiate the inverse-frame coefficients along the line.
  let a (i k : Fin n) (t : ℝ) : ℝ :=
    ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
      Ring.inverse (1 + t • H) (EuclideanSpace.basisFun (Fin n) ℝ k)⟫
  have hz :
      (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) +
        (0 : ℝ) • H = 1 := by
    apply ContinuousLinearMap.ext
    intro v
    change v + (0 : ℝ) • H v = v
    simp
  have a0 (i k : Fin n) : a i k 0 = if i = k then 1 else 0 := by
    unfold a
    rw [hz, Ring.inverse_one]
    exact (EuclideanSpace.basisFun (Fin n) ℝ).inner_eq_ite i k
  have ha0 (i k : Fin n) : HasDerivAt (a i k) (-stdMatrix H i k) 0 :=
    hasDerivAt_inner_ringInverse_one_add H i k
  have da0 (i k : Fin n) : deriv (a i k) 0 = -stdMatrix H i k := (ha0 i k).deriv
  have hda (i k : Fin n) :
      HasDerivAt (deriv (a i k)) (2 * (stdMatrix H * stdMatrix H) i k) 0 := by
    rw [← inner_H_H H hH i k]
    exact hasDerivAt_deriv_inner_ringInverse_one_add H i k
  have hopen : {t : ℝ | IsUnit (1 + t • H)} ∈ nhds (0 : ℝ) := by
    have hc : Continuous (fun t : ℝ =>
        (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) + t • H) :=
      continuous_const.add (continuous_id.smul continuous_const)
    apply (Units.isOpen.preimage hc).mem_nhds
    change IsUnit ((1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) + (0 : ℝ) • H)
    rw [hz]
    exact isUnit_one
  have hT (J : Fin r → Fin n) (t : ℝ) :
      HasDerivAt (fun x : ℝ => T J + x * X J) (X J) t := by
    simpa only [id_eq, one_mul] using
      (((hasDerivAt_id t).mul_const (X J)).const_add (T J))
  -- the two pieces of the first derivative
  let A (J K : Fin r → Fin n) (t : ℝ) : ℝ :=
    (X J * (T K + t * X K) + (T J + t * X J) * X K) * ∏ s, a (J s) (K s) t
  let B (J K : Fin r → Fin n) (t : ℝ) : ℝ :=
    (T J + t * X J) * (T K + t * X K) *
      ∑ s, (∏ u ∈ Finset.univ.erase s, a (J u) (K u) t) * deriv (a (J s) (K s)) t
  -- first derivative at every unit point
  have hD1 (t : ℝ) (ht : IsUnit (1 + t • H)) :
      HasDerivAt (fun ε : ℝ => energyForm (1 + ε • H) (T + ε • X))
        (∑ J, ∑ K, (A J K t + B J K t)) t := by
    have ha (i k : Fin n) : HasDerivAt (a i k) (deriv (a i k) t) t :=
      (hasDerivAt_inner_ringInverse_one_add_of_isUnit H i k ht).differentiableAt.hasDerivAt
    have hp (J K : Fin r → Fin n) :
        HasDerivAt (fun x => ∏ s, a (J s) (K s) x)
          (∑ s, (∏ u ∈ Finset.univ.erase s, a (J u) (K u) t) * deriv (a (J s) (K s)) t) t :=
      real_deriv_prod Finset.univ (fun s x => a (J s) (K s) x)
        (fun s => deriv (a (J s) (K s)) t) t (fun s _ => ha (J s) (K s))
    have hraw :
        HasDerivAt
          (fun x : ℝ => ∑ J, ∑ K,
            (T J + x * X J) * (T K + x * X K) * ∏ s, a (J s) (K s) x)
          (∑ J, ∑ K, (A J K t + B J K t)) t := by
      apply real_deriv_sum
      intro J _
      apply real_deriv_sum
      intro K _
      exact real_deriv_mul (real_deriv_mul (hT J t) (hT K t)) (hp J K)
    convert hraw using 1
    rfl
  have heq :
      (deriv fun ε : ℝ => energyForm (1 + ε • H) (T + ε • X)) =ᶠ[nhds (0 : ℝ)]
        (fun t : ℝ => ∑ J, ∑ K, (A J K t + B J K t)) := by
    filter_upwards [hopen] with t ht
    exact (hD1 t ht).deriv
  -- second derivative at `0`
  let P (J K : Fin r → Fin n) : ℝ :=
    ∏ s, if J s = K s then (1 : ℝ) else 0
  -- Differentiate the products of tensor coefficients.
  let Q (J K : Fin r → Fin n) : ℝ :=
    ∑ s, (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) *
      (-stdMatrix H (J s) (K s))
  let R (J K : Fin r → Fin n) : ℝ :=
    ∑ s, ((∑ u ∈ Finset.univ.erase s,
        (∏ v ∈ (Finset.univ.erase s).erase u, if J v = K v then (1 : ℝ) else 0) *
          (-stdMatrix H (J u) (K u))) * (-stdMatrix H (J s) (K s)) +
      (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) *
        (2 * (stdMatrix H * stdMatrix H) (J s) (K s)))
  let dA (J K : Fin r → Fin n) : ℝ :=
    (X J * X K + X J * X K) * P J K + (X J * T K + T J * X K) * Q J K
  let dB (J K : Fin r → Fin n) : ℝ :=
    (X J * T K + T J * X K) * Q J K + T J * T K * R J K
  have hp0 (J K : Fin r → Fin n) :
      HasDerivAt (fun x => ∏ s, a (J s) (K s) x) (Q J K) 0 := by
    have h := real_deriv_prod Finset.univ (fun s x => a (J s) (K s) x)
      (fun s => -stdMatrix H (J s) (K s)) 0 (fun s _ => ha0 (J s) (K s))
    apply h.congr_deriv
    simp only [a0, Q]
  have hq0 (J K : Fin r → Fin n) :
      HasDerivAt
        (fun x => ∑ s, (∏ u ∈ Finset.univ.erase s, a (J u) (K u) x) * deriv (a (J s) (K s)) x)
        (R J K) 0 := by
    have h := real_deriv_sum Finset.univ
      (fun s x => (∏ u ∈ Finset.univ.erase s, a (J u) (K u) x) * deriv (a (J s) (K s)) x)
      (fun s => (∑ u ∈ Finset.univ.erase s,
          (∏ v ∈ (Finset.univ.erase s).erase u, a (J v) (K v) 0) *
            (-stdMatrix H (J u) (K u))) * deriv (a (J s) (K s)) 0 +
        (∏ u ∈ Finset.univ.erase s, a (J u) (K u) 0) *
          (2 * (stdMatrix H * stdMatrix H) (J s) (K s))) 0
      (fun s _ => real_deriv_mul
        (real_deriv_prod (Finset.univ.erase s) (fun u x => a (J u) (K u) x)
          (fun u => -stdMatrix H (J u) (K u)) 0 (fun u _ => ha0 (J u) (K u)))
        (hda (J s) (K s)))
    apply h.congr_deriv
    simp only [a0, da0, R]
  have hA (J K : Fin r → Fin n) : HasDerivAt (fun t => A J K t) (dA J K) 0 := by
    have h := real_deriv_mul
      (real_deriv_add (real_deriv_const_mul (X J) (hT K 0)) (real_deriv_mul_const (X K) (hT J 0)))
      (hp0 J K)
    apply h.congr_deriv
    simp only [a0, dA, P, zero_mul, add_zero]
  have hB (J K : Fin r → Fin n) : HasDerivAt (fun t => B J K t) (dB J K) 0 := by
    have h := real_deriv_mul (real_deriv_mul (hT J 0) (hT K 0)) (hq0 J K)
    apply h.congr_deriv
    simp only [a0, da0, dB, Q, zero_mul, add_zero]
  have hD2 :
      HasDerivAt (fun t : ℝ => ∑ J, ∑ K, (A J K t + B J K t))
        (∑ J, ∑ K, (dA J K + dB J K)) 0 := by
    apply real_deriv_sum
    intro J _
    apply real_deriv_sum
    intro K _
    exact real_deriv_add (hA J K) (hB J K)
  rw [heq.deriv_eq, hD2.deriv]
  -- the algebra

  -- Sum the contractions and identify the resulting energy terms.
  have h1 := diagonalEnergySum X
  have h2 : (∑ J, ∑ K, (X J * T K + T J * X K) * Q J K) =
      -(2 * inner X (actSum (stdMatrix H) T)) := by
    have e1 : (∑ J, ∑ K, X J * T K * Q J K) = -inner X (actSum (stdMatrix H) T) :=
      slot_sum_two X T (stdMatrix H)
    have e2 : (∑ J, ∑ K, T J * X K * Q J K) = -inner T (actSum (stdMatrix H) X) :=
      slot_sum_two T X (stdMatrix H)
    have e3 : inner T (actSum (stdMatrix H) X) = inner X (actSum (stdMatrix H) T) := by
      rw [← inner_actSum_left _ hM T X, inner_comm']
    calc
      (∑ J, ∑ K, (X J * T K + T J * X K) * Q J K) =
          ∑ J, ∑ K, (X J * T K * Q J K + T J * X K * Q J K) := by
        apply Finset.sum_congr rfl
        intro J _
        apply Finset.sum_congr rfl
        intro K _
        ring
      _ = (∑ J, ∑ K, X J * T K * Q J K) + ∑ J, ∑ K, T J * X K * Q J K := by
        simp only [Finset.sum_add_distrib]
      _ = -(2 * inner X (actSum (stdMatrix H) T)) := by
        rw [e1, e2, e3]
        ring
  have h3a :
      (∑ J, ∑ K, T J * T K * (∑ s, (∑ u ∈ Finset.univ.erase s,
          (∏ v ∈ (Finset.univ.erase s).erase u, if J v = K v then (1 : ℝ) else 0) *
            (-stdMatrix H (J u) (K u))) * (-stdMatrix H (J s) (K s)))) =
        ∑ s, ∑ u ∈ Finset.univ.erase s,
          inner T (actOn (stdMatrix H) s (actOn (stdMatrix H) u T)) :=
    two_slot_sum T (stdMatrix H)
  have h3b := sameSlotEnergySum T (stdMatrix H) hM
  have h3 : (∑ J, ∑ K, T J * T K * R J K) =
      (∑ s, ∑ u ∈ Finset.univ.erase s,
        inner T (actOn (stdMatrix H) s (actOn (stdMatrix H) u T))) +
      2 * ∑ s, inner (actOn (stdMatrix H) s T) (actOn (stdMatrix H) s T) := by
    calc
      (∑ J, ∑ K, T J * T K * R J K) =
          ∑ J, ∑ K, (T J * T K * (∑ s, (∑ u ∈ Finset.univ.erase s,
              (∏ v ∈ (Finset.univ.erase s).erase u, if J v = K v then (1 : ℝ) else 0) *
                (-stdMatrix H (J u) (K u))) * (-stdMatrix H (J s) (K s))) +
            T J * T K * (∑ s,
              (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) *
                (2 * (stdMatrix H * stdMatrix H) (J s) (K s)))) := by
        apply Finset.sum_congr rfl
        intro J _
        apply Finset.sum_congr rfl
        intro K _
        simp only [R, Finset.sum_add_distrib, mul_add]
      _ = (∑ J, ∑ K, T J * T K * (∑ s, (∑ u ∈ Finset.univ.erase s,
              (∏ v ∈ (Finset.univ.erase s).erase u, if J v = K v then (1 : ℝ) else 0) *
                (-stdMatrix H (J u) (K u))) * (-stdMatrix H (J s) (K s)))) +
          ∑ J, ∑ K, T J * T K * (∑ s,
              (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) *
                (2 * (stdMatrix H * stdMatrix H) (J s) (K s))) := by
        simp only [Finset.sum_add_distrib]
      _ = _ := by
        rw [h3a, h3b]
  have hsplit : (∑ J, ∑ K, (dA J K + dB J K)) =
      ((∑ J, ∑ K, (X J * X K + X J * X K) * P J K) +
        ∑ J, ∑ K, (X J * T K + T J * X K) * Q J K) +
      ((∑ J, ∑ K, (X J * T K + T J * X K) * Q J K) +
        ∑ J, ∑ K, T J * T K * R J K) := by
    simp only [dA, dB, Finset.sum_add_distrib]
  rw [hsplit, h1, h2, h3, inner_actSum_actSum (stdMatrix H) hM T]
  ring

/-- **BKL (88), second order**: for symmetric `H`,
`D²F(Id, T)[(H, X), (H, X)] = 2 (|X|² − 2⟨X, Σ_H T⟩ + ½|Σ_H T|² + ½ Σ_s |H^{(s)} T|²)`. -/
theorem fderiv_fderiv_energyForm_one (T : (Fin r → Fin n) → ℝ)
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hH : IsSelfAdjoint H)
    (X : (Fin r → Fin n) → ℝ) :
    fderiv ℝ
        (fderiv ℝ
          (fun q :
              (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ×
                ((Fin r → Fin n) → ℝ) =>
            energyForm q.1 q.2))
        (1, T) (H, X) (H, X) =
      2 *
        (inner X X - 2 * inner X (actSum (stdMatrix H) T) +
            (1 / 2 : ℝ) * inner (actSum (stdMatrix H) T) (actSum (stdMatrix H) T) +
          (1 / 2 : ℝ) * ∑ s, inner (actOn (stdMatrix H) s T) (actOn (stdMatrix H) s T)) := by
  have hdiff :=
    contDiffAt_energyForm (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      isUnit_one T
  rw [fderiv_fderiv_apply_eq_deriv_deriv_line hdiff (H, X)]
  change deriv (deriv fun ε : ℝ => energyForm (1 + ε • H) (T + ε • X)) 0 = _
  exact deriv_deriv_energyForm_line T H hH X

end FunctionalInequalities.Analysis.CoordinateTensor

end EnergyFormSecondDerivative
