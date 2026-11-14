/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.ForMathlib.Resultant
public import LeanPool.HyperellipticCurves.Log.Fold.FoldWitness

import LeanPool.HyperellipticCurves.Log.Ftau.GoodPosition

/-!
# The genus-one fold witness

The cusp engine of `LeanPool.HyperellipticCurves.Log.Fold.CuspInstance` certifies the fold
conditions only
for `g ≥ 2`: at `g = 1` the interior condition value on the cusp is `3t²/4`, which vanishes
identically in characteristic `3` (on the cusp's additive Jacobian every point is
`3`-torsion, so `x(2P) = x(P)` throughout) — and for `f = X³` the conditions genuinely
vanish on all curve points. This file supplies the missing genus-one witness for
**squarefree** `f` by direct computation: at `g = 1` the fold `τ + τ - τ` is the elliptic
tangent-chord construction, the whole honest chain is governed by a single cubic
factorization (`ChabautyColeman.GenusOne.tangent_factorization` — the chord line of the
second step is the negated tangent line, so no second identity is needed), and the two
condition values are `4·f(x₀)·ψ₃(x₀)` and (up to a power of `2y₀`) `f'·ψ₃ - 8·f²` at `x₀`,
where `ψ₃ = 2·f·f'' - f'²` is the `3`-division polynomial. Squarefreeness enters through
separability: `ψ₃` or `f'·ψ₃ - 8·f²` vanishing identically forces `f ∣ f'` and hence
`f' = 0`, contradicting `f` separable of degree `3`.

## Main statements

* `ChabautyColeman.GenusOne.tangent_factorization`: the tangent line meets `y² = f` doubly
  at the point of tangency; the cubic factorization behind both fold steps.
* `ChabautyColeman.GenusOne.foldChain_one`, `ChabautyColeman.GenusOne.foldChain_two`: the
  honest genus-one fold visits `(X - x(2P), y(2P))` and returns to `(X - x₀, y₀)`.
* `ChabautyColeman.GenusOne.psi_ne_zero`, `ChabautyColeman.GenusOne.avoid_ne_zero`: the
  two condition polynomials are nonzero for squarefree `f`.
* `ChabautyColeman.exists_genusOnePoint`: a curve point at which every step-condition
  numerator and every stage resultant of the genus-one fold is nonzero — the input for the
  genus-one case of the centre-fold witness (`LeanPool.HyperellipticCurves.Log.Fold.CenterFold`).
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

namespace GenusOne

/-! ### The tangent factorization -/

section Identity

variable {R : Type*} [CommRing R] {a b c x₀ y₀ l : R}

/-- **The tangent factorization**: the line through `(x₀, y₀)` with the tangent slope
`l = f'(x₀)/(2y₀)` meets `y² = f` doubly at `x₀` and thirdly at
`x₂ = l² - a - 2x₀`. The chord line of the second fold step is the negated tangent line,
so this single identity also governs the return step. -/
theorem tangent_factorization (hcv : y₀ ^ 2 = x₀ ^ 3 + a * x₀ ^ 2 + b * x₀ + c)
    (hl : 2 * y₀ * l = 3 * x₀ ^ 2 + 2 * a * x₀ + b) :
    (C y₀ + C l * (X - C x₀)) ^ 2 - (X ^ 3 + C a * X ^ 2 + C b * X + C c)
      = -((X - C x₀) ^ 2 * (X - C (l ^ 2 - a - 2 * x₀))) := by
  have hcv' := congrArg (C : R →+* R[X]) hcv
  have hl' := congrArg (C : R →+* R[X]) hl
  simp only [map_pow, map_add, map_mul, map_ofNat] at hcv' hl'
  simp only [map_sub, map_pow, map_mul, map_ofNat]
  linear_combination hcv' + (X - C x₀) * hl'

end Identity

/-! ### The cubic identities -/

section Cubic

variable {R : Type*} [CommRing R] {f : R[X]} {x₀ y₀ l x₂ y₂ : R}

/-- A monic cubic is determined by its three lower coefficients. -/
theorem cubic_eq (hf : f.Monic) (h3 : f.natDegree = 3) :
    f = X ^ 3 + C (f.coeff 2) * X ^ 2 + C (f.coeff 1) * X + C (f.coeff 0) := by
  conv_lhs => rw [hf.as_sum, h3]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  ring

theorem cubic_derivative (hf : f.Monic) (h3 : f.natDegree = 3) :
    f.derivative = C 3 * X ^ 2 + C (2 * f.coeff 2) * X + C (f.coeff 1) := by
  nth_rw 1 [cubic_eq hf h3]
  simp only [derivative_add, derivative_pow, derivative_X, derivative_C_mul, derivative_C,
    Nat.cast_ofNat, add_zero, map_mul, map_ofNat]
  ring

theorem cubic_derivative_derivative (hf : f.Monic) (h3 : f.natDegree = 3) :
    f.derivative.derivative = C 6 * X + C (2 * f.coeff 2) := by
  rw [cubic_derivative hf h3, derivative_add, derivative_add, derivative_C_mul,
    derivative_C_mul, derivative_C, derivative_X, derivative_X_pow]
  push_cast
  simp only [map_mul, map_ofNat]
  ring

variable (hf : f.Monic) (h3 : f.natDegree = 3) (hcv : y₀ ^ 2 = f.eval x₀)
  (hl : 2 * y₀ * l = f.derivative.eval x₀) (hx₂ : x₂ = l ^ 2 - f.coeff 2 - 2 * x₀)
  (hy₂ : y₂ = -y₀ - l * (x₂ - x₀))

include hf h3 hcv hl hx₂ in
/-- The tangent factorization, in terms of the abstract cubic. -/
theorem tangent_factorization' :
    (C y₀ + C l * (X - C x₀)) ^ 2 - f = -((X - C x₀) ^ 2 * (X - C x₂)) := by
  have hcv' : y₀ ^ 2 = x₀ ^ 3 + f.coeff 2 * x₀ ^ 2 + f.coeff 1 * x₀ + f.coeff 0 := by
    rw [hcv]
    nth_rw 1 [cubic_eq hf h3]
    simp
  have hl' : 2 * y₀ * l = 3 * x₀ ^ 2 + 2 * f.coeff 2 * x₀ + f.coeff 1 := by
    rw [hl, cubic_derivative hf h3]
    simp
  rw [hx₂]
  nth_rw 1 [cubic_eq hf h3]
  exact tangent_factorization hcv' hl'

include hf h3 hcv hl hx₂ in
/-- **The interior condition value**: the `3`-division polynomial `ψ₃ = 2ff'' - f'²`
measures the `x`-separation of `P` and `2P`. -/
theorem psi_eval_eq :
    (2 * f * f.derivative.derivative - f.derivative ^ 2).eval x₀
      = 4 * y₀ ^ 2 * (x₀ - x₂) := by
  simp only [eval_sub, eval_mul, eval_pow, eval_ofNat, cubic_derivative_derivative hf h3,
    eval_add, eval_C, eval_X]
  rw [hx₂]
  linear_combination (-(4 * (3 * x₀ + f.coeff 2))) * hcv
    + (2 * y₀ * l + f.derivative.eval x₀) * hl

include hf h3 hcv hl hx₂ hy₂ in
/-- **The avoidance value**: `y(2P)`, scaled by `8y₀³`, is the avoidance polynomial
`f'·ψ₃ - 8f²` at `x₀`. -/
theorem avoid_eval_eq :
    8 * y₀ ^ 3 * y₂
      = (f.derivative * (2 * f * f.derivative.derivative - f.derivative ^ 2)
          - 8 * f ^ 2).eval x₀ := by
  simp only [eval_sub, eval_mul, eval_pow, eval_ofNat, psi_eval_eq hf h3 hcv hl hx₂]
  rw [hy₂]
  linear_combination 4 * y₀ ^ 2 * (x₀ - x₂) * hl - 8 * (y₀ ^ 2 + f.eval x₀) * hcv

end Cubic

/-! ### The honest genus-one fold chain -/

section Chain

variable {F : Type*} [Field F] {f : F[X]} {x₀ y₀ l x₂ y₂ : F} {xs ys : ℕ → F}
  (hf : f.Monic) (h3 : f.natDegree = 3) (hcv : y₀ ^ 2 = f.eval x₀)
  (hl : 2 * y₀ * l = f.derivative.eval x₀) (hx₂ : x₂ = l ^ 2 - f.coeff 2 - 2 * x₀)
  (hy₂ : y₂ = -y₀ - l * (x₂ - x₀))
  (hxs0 : xs 0 = x₀) (hxs1 : xs 1 = x₀) (hys0 : ys 0 = y₀) (hys1 : ys 1 = -y₀)
  (hy : y₀ ≠ 0) (h2 : (2 : F) ≠ 0)

include hl hxs0 hys0 hy h2 in
/-- The computed scalar of the initial doubling step is the tangent slope. -/
theorem foldGenH_zero_eq : foldGenH f xs ys (X - C x₀) (C y₀) 0 = l := by
  rw [foldGenH_zero, hxs0, hys0]
  simp only [derivative_C, eval_zero, mul_zero, sub_zero, derivative_X_sub_C, eval_one,
    mul_one]
  rw [div_eq_iff (mul_ne_zero h2 hy)]
  linear_combination -hl

include hf h3 hcv hl hx₂ hy₂ hxs0 hys0 hy h2 in
/-- **The first step of the honest genus-one fold** is the elliptic doubling
`P ↦ 2P`. -/
theorem foldChain_one :
    foldChain f xs (foldGenH f xs ys (X - C x₀) (C y₀)) (X - C x₀) (C y₀) 1
      = (X - C x₂, C y₂) := by
  simp only [foldChain_succ, foldChain_zero]
  rw [foldGenH_zero_eq hl hxs0 hys0 hy h2, hxs0]
  have hcof : cantorCofactor f ((X - C x₀) * (X - C x₀)) (C y₀ + C l * (X - C x₀))
      = -(X - C x₂) :=
    cantorCofactor_eq_of_sq_sub ((monic_X_sub_C x₀).mul (monic_X_sub_C x₀))
      (by rw [tangent_factorization' hf h3 hcv hl hx₂]; ring)
  rw [cantorReduce, hcof]
  have h1 : C (-1 : F) * -(X - C x₂) = X - C x₂ := by
    rw [map_neg, map_one]
    ring
  rw [h1, modByMonic_X_sub_C_eq_C_eval]
  refine Prod.ext rfl ?_
  change C (eval x₂ (-(C y₀ + C l * (X - C x₀)))) = C y₂
  congr 1
  simp only [eval_neg, eval_add, eval_mul, eval_sub, eval_C, eval_X]
  rw [hy₂]
  ring

include hf h3 hcv hl hx₂ hy₂ hxs0 hxs1 hys0 hys1 hy h2 in
/-- The computed scalar of the return step is the negated tangent slope: the chord
through `2P` and `-P` is the reflected tangent line. -/
theorem foldGenH_one_eq (hx₂0 : x₂ ≠ x₀) :
    foldGenH f xs ys (X - C x₀) (C y₀) 1 = -l := by
  rw [foldGenH_succ, foldChain_one hf h3 hcv hl hx₂ hy₂ hxs0 hys0 hy h2, hxs1, hys1]
  simp only [eval_sub, eval_C, eval_X]
  rw [div_eq_iff (sub_ne_zero.mpr fun h ↦ hx₂0 h.symm), hy₂]
  ring

include hf h3 hcv hl hx₂ hy₂ hxs0 hxs1 hys0 hys1 hy h2 in
/-- **The honest genus-one fold returns to its starting pair**: `τ + τ - τ = τ`. -/
theorem foldChain_two (hx₂0 : x₂ ≠ x₀) :
    foldChain f xs (foldGenH f xs ys (X - C x₀) (C y₀)) (X - C x₀) (C y₀) 2
      = (X - C x₀, C y₀) := by
  rw [foldChain_succ, foldChain_one hf h3 hcv hl hx₂ hy₂ hxs0 hys0 hy h2,
    foldGenH_one_eq hf h3 hcv hl hx₂ hy₂ hxs0 hxs1 hys0 hys1 hy h2 hx₂0, hxs1]
  have hVc : C y₂ + C (-l) * (X - C x₂) = -(C y₀ + C l * (X - C x₀)) := by
    rw [hy₂]
    simp only [map_neg, map_sub, map_mul]
    ring
  have hcof : cantorCofactor f ((X - C x₂) * (X - C x₀))
      (C y₂ + C (-l) * (X - C x₂)) = -(X - C x₀) :=
    cantorCofactor_eq_of_sq_sub ((monic_X_sub_C x₂).mul (monic_X_sub_C x₀))
      (by rw [hVc, neg_sq, tangent_factorization' hf h3 hcv hl hx₂]; ring)
  rw [cantorReduce, hcof]
  have h1 : C (-1 : F) * -(X - C x₀) = X - C x₀ := by
    rw [map_neg, map_one]
    ring
  rw [h1, modByMonic_X_sub_C_eq_C_eval]
  refine Prod.ext rfl ?_
  change C (eval x₀ (-(C y₂ + C (-l) * (X - C x₂)))) = C y₀
  congr 1
  rw [hVc]
  simp only [eval_add, eval_mul, eval_sub, eval_C, eval_X, neg_neg, sub_self, mul_zero,
    add_zero]

end Chain

/-! ### Nonvanishing of the condition polynomials for squarefree `f` -/

section Separable

variable {F : Type*} [Field F] {f : F[X]}

/-- Squarefree of positive degree gives `f ∤ f'` — the common core of the two
nonvanishing lemmas: from `f ∣ f'²` conclude `False`. -/
private theorem not_dvd_derivative_sq [PerfectField F] (hsq : Squarefree f)
    (h3 : f.natDegree = 3) (hdvd : f ∣ f.derivative ^ 2) : False := by
  have hcop : IsCoprime f f.derivative := PerfectField.separable_iff_squarefree.mpr hsq
  have hdvd' : f ∣ f.derivative := by
    rw [sq] at hdvd
    exact hcop.dvd_of_dvd_mul_right hdvd
  lia [natDegree_eq_zero_of_isUnit (hcop.isUnit_of_dvd' dvd_rfl hdvd')]

/-- **The `3`-division polynomial of a squarefree cubic is nonzero** — in every
characteristic, including `3` (where `ψ₃` degenerates to degree `≤ 3`). -/
theorem psi_ne_zero [PerfectField F] (hsq : Squarefree f) (h3 : f.natDegree = 3) :
    2 * f * f.derivative.derivative - f.derivative ^ 2 ≠ 0 := fun h0 ↦
  not_dvd_derivative_sq hsq h3 ⟨2 * f.derivative.derivative, by linear_combination -h0⟩

/-- **The avoidance polynomial of a squarefree cubic is nonzero**: `y(2P)` does not
vanish identically. -/
theorem avoid_ne_zero [PerfectField F] (hsq : Squarefree f) (h3 : f.natDegree = 3) :
    f.derivative * (2 * f * f.derivative.derivative - f.derivative ^ 2) - 8 * f ^ 2
      ≠ 0 := by
  intro h0
  have hcop : IsCoprime f f.derivative := PerfectField.separable_iff_squarefree.mpr hsq
  have hpsi : f ∣ 2 * f * f.derivative.derivative - f.derivative ^ 2 := by
    refine hcop.dvd_of_dvd_mul_left ⟨8 * f, ?_⟩
    linear_combination h0
  refine not_dvd_derivative_sq hsq h3 ?_
  obtain ⟨q, hq⟩ := hpsi
  exact ⟨2 * f.derivative.derivative - q, by linear_combination -hq⟩

end Separable

/-! ### Tuple plumbing at a single point -/

section Single

variable {F : Type*} [Field F] (x₀ y₀ : F)

theorem nodeDen_single : nodeDen ![x₀] = 1 := by
  rw [nodeDen, Fin.prod_univ_one, nodeDiff, show ({0}ᶜ : Finset (Fin 1)) = ∅ by decide,
    Finset.prod_empty]

theorem tupleU_single : tupleU ![x₀] = X - C x₀ := by
  rw [tupleU_eq_prod, Fin.prod_univ_one, Matrix.cons_val_zero]

theorem tupleV_single : tupleV ![x₀] ![y₀] = C y₀ := by
  rw [tupleV, nodeDen_single, tupleInterp, Fin.sum_univ_one, nodeCoDen, nodeLag,
    show ({0}ᶜ : Finset (Fin 1)) = ∅ by decide]
  simp

theorem foldXs_single_zero : foldXs ![x₀] 0 = x₀ := foldXs_zero _ one_pos

theorem foldXs_single_one : foldXs ![x₀] 1 = x₀ := by
  rw [foldXs]
  norm_num

theorem foldYs_single_zero : foldYs ![y₀] 0 = y₀ := foldYs_zero _ one_pos

theorem foldYs_single_one : foldYs ![y₀] 1 = -y₀ := by
  rw [foldYs]
  norm_num

end Single

/-! ### The genus-one witness point -/

section Point

variable {κ : Type*} [Field κ] {f : κ[X]}

/-- The formal `(1, 1)`-resultant of a reduced genus-one Mumford pair with nonzero
square root is nonzero. -/
private theorem resultant_X_sub_C_ne_zero {α β : κ} (hβ : β ≠ 0) :
    (X - C α).resultant (C β) 1 1 ≠ 0 := by simp [hβ]

variable [IsAlgClosed κ] [NeZero (2 : κ)]

/-- **The genus-one witness point** (the genus-one case of `thm:fold-witness`): for a
squarefree monic cubic over an algebraically closed field of characteristic `≠ 2`, some
affine curve point has nonzero `y`-coordinate, nonzero step-condition numerators at both
fold steps, and nonzero stage resultants at all three fold stages. The proof runs the
honest tangent-chord chain: the interior condition is `x(2P) ≠ x(P)` — the value of the
`3`-division polynomial `ψ₃` — and the interior resultant is `y(2P)` — the value of
`f'·ψ₃ - 8f²` — up to powers of `2y₀`; both polynomials are nonzero for squarefree `f`
(`ChabautyColeman.GenusOne.psi_ne_zero`/`avoid_ne_zero`), and the point avoids their
roots. -/
theorem _root_.ChabautyColeman.exists_genusOnePoint (hf : f.Monic) (h3 : f.natDegree = 3)
    (hsq : Squarefree f) :
    ∃ x₀ y₀ : κ, y₀ ^ 2 = f.eval x₀ ∧ y₀ ≠ 0
      ∧ (∀ j < 2, foldCondNum f (foldXs ![x₀]) (foldYs ![y₀])
          (foldBase f ![x₀] ![y₀]) j ≠ 0)
      ∧ ∀ j ≤ 2, ((foldNum f (foldXs ![x₀]) (foldYs ![y₀])
            (foldBase f ![x₀] ![y₀]) j).u).resultant
          ((foldNum f (foldXs ![x₀]) (foldYs ![y₀]) (foldBase f ![x₀] ![y₀]) j).v)
          1 1 ≠ 0 := by
  have h2 : (2 : κ) ≠ 0 := NeZero.ne 2
  have hfdeg : f.natDegree = 2 * 1 + 1 := by rw [h3]
  -- the point: `x₀` avoids the roots of `f`, `ψ₃` and the avoidance polynomial
  have hψ : 2 * f * f.derivative.derivative - f.derivative ^ 2 ≠ 0 := psi_ne_zero hsq h3
  have hN : f.derivative * (2 * f * f.derivative.derivative - f.derivative ^ 2)
      - 8 * f ^ 2 ≠ 0 := avoid_ne_zero hsq h3
  obtain ⟨x₀, hx₀⟩ := (infinite_setOf_eval_ne_zero (mul_ne_zero hf.ne_zero
    (mul_ne_zero hψ hN))).nonempty
  simp only [Set.mem_ofPred_eq, eval_mul, mul_ne_zero_iff] at hx₀
  obtain ⟨hf0, hψ0, hN0⟩ := hx₀
  obtain ⟨y₀, hcv⟩ := IsAlgClosed.exists_pow_nat_eq (f.eval x₀) (n := 2) two_pos
  have hy : y₀ ≠ 0 := fun h ↦ hf0 (by rw [← hcv, h]; ring)
  -- the tangent slope and the image point
  obtain ⟨l, hl⟩ : ∃ l, 2 * y₀ * l = f.derivative.eval x₀ :=
    ⟨_, mul_div_cancel₀ _ (mul_ne_zero h2 hy)⟩
  obtain ⟨x₂, hx₂def⟩ : ∃ x₂ : κ, x₂ = l ^ 2 - f.coeff 2 - 2 * x₀ := ⟨_, rfl⟩
  obtain ⟨y₂, hy₂def⟩ : ∃ y₂ : κ, y₂ = -y₀ - l * (x₂ - x₀) := ⟨_, rfl⟩
  -- the two condition values
  have hx₂0 : x₂ ≠ x₀ := fun h ↦ hψ0 (by rw [psi_eval_eq hf h3 hcv hl hx₂def, h]; ring)
  have hy₂0 : y₂ ≠ 0 := fun h ↦
    hN0 (by rw [← avoid_eval_eq hf h3 hcv hl hx₂def hy₂def, h, mul_zero])
  -- the scaled base state at the explicit base pair
  have hxinj : Function.Injective ![x₀] := fun i j _ ↦ Subsingleton.elim i j
  have hcurve : ∀ i, ![y₀] i ^ 2 = f.eval (![x₀] i) := fun i ↦ by fin_cases i; simpa
  have hbase := isScaledState_foldBase (f := f) hxinj hcurve
  rw [tupleU_single, tupleV_single] at hbase
  have hx₀eval : (X - C x₀).eval (foldXs ![x₀] 0) = 0 := by
    rw [foldXs_single_zero]
    simp
  have hV₀eval : (C y₀).eval (foldXs ![x₀] 0) = foldYs ![y₀] 0 := by rw [foldYs_single_zero, eval_C]
  have hcurve2 : ∀ i < 2, foldYs ![y₀] i ^ 2 = f.eval (foldXs ![x₀] i) := fun i hi ↦
    foldYs_sq hcurve (by lia)
  -- the two step-condition numerators
  have hcond0 : foldCondNum f (foldXs ![x₀]) (foldYs ![y₀])
      (foldBase f ![x₀] ![y₀]) 0 ≠ 0 := by
    rw [foldCondNum_zero, foldYs_single_zero, foldXs_single_zero]
    change 2 * y₀ * (C (nodeDen ![x₀] ^ 2) * tupleU ![x₀]).derivative.eval x₀ ≠ 0
    rw [nodeDen_single, tupleU_single]
    simpa using mul_ne_zero h2 hy
  have hchain1 := foldChain_one hf h3 hcv hl hx₂def hy₂def (foldXs_single_zero x₀)
    (foldYs_single_zero y₀) hy h2 (ys := foldYs ![y₀])
  have hclt1 : ∀ i < 1, foldCondNum f (foldXs ![x₀]) (foldYs ![y₀])
      (foldBase f ![x₀] ![y₀]) i ≠ 0 := fun i hi ↦ Nat.lt_one_iff.mp hi ▸ hcond0
  have hcond1 : foldCondNum f (foldXs ![x₀]) (foldYs ![y₀])
      (foldBase f ![x₀] ![y₀]) 1 ≠ 0 := by
    rw [foldCondNum_eq_den_mul hf hfdeg hbase hx₀eval hV₀eval
      (fun i hi ↦ hcurve2 i (by lia)) hclt1]
    refine mul_ne_zero (isScaledState_foldNum hf hfdeg hbase hx₀eval hV₀eval
      (fun i hi ↦ hcurve2 i (by lia)) hclt1).den_ne ?_
    rw [foldCond_succ, hchain1, foldXs_single_one]
    simp only [eval_sub, eval_C, eval_X]
    exact sub_ne_zero.mpr fun h ↦ hx₂0 h.symm
  have hconds : ∀ j < 2, foldCondNum f (foldXs ![x₀]) (foldYs ![y₀])
      (foldBase f ![x₀] ![y₀]) j ≠ 0 := fun j hj ↦ by
    interval_cases j
    exacts [hcond0, hcond1]
  -- the stage resultants, via the honest chain
  refine ⟨x₀, y₀, hcv, hy, hconds, fun j hj ↦ ?_⟩
  have hspec := isScaledState_foldNum hf hfdeg hbase hx₀eval hV₀eval (m := j)
    (fun i hi ↦ hcurve2 i (by lia)) fun i hi ↦ hconds i (by lia)
  rw [hspec.u_eq, hspec.v_eq, Polynomial.resultant_C_mul_left,
    Polynomial.resultant_C_mul_right]
  refine mul_ne_zero (pow_ne_zero _ hspec.den_ne)
    (mul_ne_zero (pow_ne_zero _ hspec.den_ne) ?_)
  interval_cases j
  · rw [foldChain_zero]
    exact resultant_X_sub_C_ne_zero hy
  · rw [hchain1]
    exact resultant_X_sub_C_ne_zero hy₂0
  · rw [foldChain_two hf h3 hcv hl hx₂def hy₂def (foldXs_single_zero x₀)
      (foldXs_single_one x₀) (foldYs_single_zero y₀) (foldYs_single_one y₀) hy h2 hx₂0]
    exact resultant_X_sub_C_ne_zero hy

end Point

end GenusOne

end ChabautyColeman

end
