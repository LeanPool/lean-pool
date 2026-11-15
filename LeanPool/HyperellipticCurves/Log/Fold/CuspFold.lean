/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.ForMathlib.Polynomial

/-!
# The cuspidal fold in the `A`-picture

The general-genus witness for the centre fold is certified on the **cuspidal model**
`y² = X^N` (`N = 2g+1`), where the point-by-point fold `τ + τ - τ` can be tracked through the
substitution `x = z²`, `y = z^N`: each Mumford support `U` factors as
`U(z²) = (-1)^g·A(z)·A(-z)` for a monic degree-`g` polynomial `A`, and the whole fold becomes
a recursion on `A` alone (blueprint `def:cusp-fold`). This file proves the per-step lemmas of
that recursion in certificate form — every constructed quantity enters as a variable
constrained by its defining identity, so no division and no case split between the generic and
the doubling composition is ever needed — and assembles the **master congruence**
`A_j(z)·d_j(-z) ≡ A_j(-z)·d_j(z) mod z^N` along the chain (blueprint `thm:cusp-moment` (1)),
which pins down `A_j` by finitely many moment equations.

The step relates a state `(V, A)` (with `A ∣ z^N - V(z²)`, the `z`-lift of the Mumford
condition) to the next state via the composed square root `V_c`, the `z`-cofactor `C_c` with
`A·(z - t)·C_c = z^N - V_c(z²)`, and the reduced support `A' = (-1)^g·C_c(-z)`.

## Main statements

* `ChabautyColeman.cuspCompose_dvd`: the composed support divides the `z`-lift
  (`lem:cusp-divisibility`, composition half; produces the certificate `C_c` at a
  disjoint step).
* `ChabautyColeman.cuspCofactor_monic`, `ChabautyColeman.cuspNext_monic`: the `z`-cofactor
  and the reduced support are monic of degree `g` (`lem:cusp-reduction`).
* `ChabautyColeman.cuspNext_dvd`: the reduced state satisfies the `z`-lifted Mumford
  condition again (`lem:cusp-divisibility`, reduction half).
* `ChabautyColeman.cuspNext_exact`: the exact defect identity
  `A'(z)·A_c(-z) - A'(-z)·A_c(z) = (-1)^(g+1)·2·z^N` (`lem:cusp-exact`).
* `ChabautyColeman.cuspMoment_congruence`: the master congruence along a certificate chain
  (`thm:cusp-moment` (1)); its base case is the exact identity
  `ChabautyColeman.cuspMoment_base`.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

/-! ### The fold step in certificate form -/

section CommRing

variable {R : Type*} [CommRing R] {g : ℕ} {A Vc Cc A' V' : R[X]} {t : R}

/-- Composing the defining identity of the `z`-cofactor with `-z`: the sign of the odd-degree
term flips, the even-degree block is fixed. -/
theorem cuspCompose_comp_neg_X (hCc : A * (X - C t) * Cc = X ^ (2 * g + 1) - Vc.comp (X ^ 2)) :
    (A * (X - C t)).comp (-X) * Cc.comp (-X) = -X ^ (2 * g + 1) - Vc.comp (X ^ 2) := by
  rw [← mul_comp, hCc]
  simp only [sub_comp, pow_comp, X_comp, comp_assoc]
  rw [Odd.neg_pow ⟨g, by ring⟩ (X : R[X]), neg_sq]

/-- **`lem:cusp-exact`**: the reduced support `A' = (-1)^g·C_c(-z)` against the composed
support `A_c = A·(z - t)` has exact defect `(-1)^(g+1)·2·z^N` — the single identity driving
the master congruence. -/
theorem cuspNext_exact (hCc : A * (X - C t) * Cc = X ^ (2 * g + 1) - Vc.comp (X ^ 2))
    (hA' : A' = (-1) ^ g * Cc.comp (-X)) :
    A' * (A * (X - C t)).comp (-X) - A'.comp (-X) * (A * (X - C t))
      = (-1) ^ (g + 1) * (2 * X ^ (2 * g + 1)) := by
  subst hA'
  have h2 : ((-1 : R[X]) ^ g * Cc.comp (-X)).comp (-X) = (-1) ^ g * Cc := by
    simp only [mul_comp, pow_comp, neg_comp, one_comp, comp_neg_X_comp_neg_X]
  rw [h2]
  linear_combination ((-1 : R[X]) ^ g) * cuspCompose_comp_neg_X hCc
    - ((-1 : R[X]) ^ g) * hCc

/-- The reduced support is monic (`lem:cusp-reduction`, normalization half). -/
theorem cuspNext_monic (hCcm : Cc.Monic) (hCcdeg : Cc.natDegree = g)
    (hA' : A' = (-1) ^ g * Cc.comp (-X)) : A'.Monic := by
  rw [hA', ← hCcdeg]
  exact hCcm.neg_one_pow_natDegree_mul_comp_neg_X

/-- **`lem:cusp-divisibility`, reduction half**: the reduced support divides the `z`-lift of
any `V'` with `V' ≡ -V_c` modulo the reduced support (in `z`-lifted certificate form). -/
theorem cuspNext_dvd (hCc : A * (X - C t) * Cc = X ^ (2 * g + 1) - Vc.comp (X ^ 2))
    (hA' : A' = (-1) ^ g * Cc.comp (-X)) (hV' : A' ∣ (V' + Vc).comp (X ^ 2)) :
    A' ∣ X ^ (2 * g + 1) - V'.comp (X ^ 2) := by
  have h1 : A' ∣ X ^ (2 * g + 1) + Vc.comp (X ^ 2) := by
    refine Dvd.intro ((-1) ^ g * -(A * (X - C t)).comp (-X)) ?_
    subst hA'
    have hsq : ((-1 : R[X]) ^ g) * ((-1) ^ g) = 1 := by
      rw [← pow_add]
      exact Even.neg_one_pow ⟨g, rfl⟩
    linear_combination -((A * (X - C t)).comp (-X) * Cc.comp (-X)) * hsq
      - cuspCompose_comp_neg_X hCc
  have h2 : X ^ (2 * g + 1) - V'.comp (X ^ 2)
      = (X ^ (2 * g + 1) + Vc.comp (X ^ 2)) - (V' + Vc).comp (X ^ 2) := by
    rw [add_comp]
    ring
  rw [h2]
  exact h1.sub hV'

/-- **The base of the master congruence is exact**: at `j = 0` the node polynomial is
`d₀ = (-1)^g·A₀`, and the defect vanishes identically. -/
theorem cuspMoment_base (g : ℕ) (A : R[X]) :
    A * ((-1) ^ g * A : R[X]).comp (-X) - A.comp (-X) * ((-1) ^ g * A) = 0 := by
  simp only [mul_comp, pow_comp, neg_comp, one_comp]
  ring

end CommRing

section Domain

variable {R : Type*} [CommRing R] [IsDomain R] {g : ℕ} {A Vc Cc A' : R[X]} {t : R}

/-- The `z`-lift of a composed square root stays below the curve's degree `N = 2g+1`. -/
private theorem cusp_zLift_degree_lt (hVc : Vc.natDegree ≤ g) :
    (Vc.comp (X ^ 2)).degree < ((2 * g + 1 : ℕ) : WithBot ℕ) := by
  refine degree_le_natDegree.trans_lt ?_
  have h1 : (Vc.comp (X ^ 2)).natDegree < 2 * g + 1 := by
    rw [natDegree_comp, natDegree_X_pow]
    lia
  exact_mod_cast h1

/-- **The `z`-cofactor is monic**: dividing the monic `z`-lift `z^N - V_c(z²)` (of degree
`N = 2g+1` since `deg V_c ≤ g`) by the monic composed support `A_c = A·(z - t)` leaves a
monic quotient. Certificate form of the normalization half of `lem:cusp-reduction`. -/
theorem cuspCofactor_monic (hA : A.Monic)
    (hCc : A * (X - C t) * Cc = X ^ (2 * g + 1) - Vc.comp (X ^ 2)) (hVc : Vc.natDegree ≤ g) :
    Cc.Monic := by
  refine (hA.mul (monic_X_sub_C t)).of_mul_monic_left ?_
  rw [hCc]
  exact monic_X_pow_sub (cusp_zLift_degree_lt hVc)

/-- The `z`-cofactor has degree `g` (`lem:cusp-reduction`, degree half). -/
theorem cuspCofactor_natDegree (hA : A.Monic) (hAdeg : A.natDegree = g)
    (hCc : A * (X - C t) * Cc = X ^ (2 * g + 1) - Vc.comp (X ^ 2)) (hVc : Vc.natDegree ≤ g) :
    Cc.natDegree = g := by
  have h1 := congrArg natDegree hCc
  rw [(hA.mul (monic_X_sub_C t)).natDegree_mul (cuspCofactor_monic hA hCc hVc),
    hA.natDegree_mul (monic_X_sub_C t), natDegree_X_sub_C, hAdeg,
    natDegree_sub_eq_left_of_natDegree_lt (by
      simp only [natDegree_comp, natDegree_X_pow]
      lia), natDegree_X_pow] at h1
  lia

/-- The reduced support has degree `g` (`lem:cusp-reduction`, degree half). -/
theorem cuspNext_natDegree (hCcdeg : Cc.natDegree = g) (hA' : A' = (-1) ^ g * Cc.comp (-X)) :
    A'.natDegree = g := by
  rw [hA', show ((-1 : R[X]) ^ g) = C ((-1) ^ g) by rw [map_pow, map_neg, map_one],
    natDegree_C_mul (pow_ne_zero g (by norm_num)), natDegree_comp, natDegree_neg, natDegree_X,
    mul_one, hCcdeg]

end Domain

/-! ### Producing the certificate, and the master congruence -/

section Field

variable {F : Type*} [Field F] {g : ℕ} {A V Vc Cc A' d : F[X]} {t : F}

/-- **`lem:cusp-divisibility`, composition half**: the composed support `A_c = A·(z - t)`
divides the `z`-lift of the composed square root. The hypotheses are the state's Mumford
divisibility, the congruence `V_c ≡ V mod U` in `z`-lifted certificate form, the interpolation
at the new point, and the disjointness value `A(t) ≠ 0`. (The doubling step, where `A(t) = 0`,
produces its certificate from the second-order interpolation instead; the chain lemmas below
consume the certificate itself either way.) -/
theorem cuspCompose_dvd (hdvd : A ∣ X ^ (2 * g + 1) - V.comp (X ^ 2))
    (hVcV : A ∣ (Vc - V).comp (X ^ 2)) (hint : Vc.eval (t ^ 2) = t ^ (2 * g + 1))
    (hAt : A.eval t ≠ 0) :
    A * (X - C t) ∣ X ^ (2 * g + 1) - Vc.comp (X ^ 2) := by
  refine (isCoprime_X_sub_C_of_eval_ne_zero hAt).mul_dvd ?_ ?_
  · have h1 : X ^ (2 * g + 1) - Vc.comp (X ^ 2)
        = (X ^ (2 * g + 1) - V.comp (X ^ 2)) - (Vc - V).comp (X ^ 2) := by
      rw [sub_comp]
      ring
    rw [h1]
    exact hdvd.sub hVcV
  · refine dvd_iff_isRoot.mpr ?_
    rw [IsRoot, eval_sub, eval_pow, eval_X, eval_comp, eval_pow, eval_X, hint, sub_self]

/-- A power of `X` is coprime to any polynomial with nonzero constant term. -/
theorem isCoprime_X_pow_of_eval_zero_ne_zero {p : F[X]} (hp : p.eval 0 ≠ 0) (n : ℕ) :
    IsCoprime ((X : F[X]) ^ n) p := by
  have h1 := (isCoprime_X_sub_C_of_eval_ne_zero hp).symm
  rw [map_zero, sub_zero] at h1
  exact h1.pow_left

/-- **The master congruence transfers along one fold step** (`thm:cusp-moment` (1), the
induction step): if `A(z)·d(-z) ≡ A(-z)·d(z) mod z^N` and the avoidance values `A(0)`, `t`
are nonzero, then the same congruence holds for the reduced support `A'` and the extended
node polynomial `d·(t - z)`. -/
theorem cuspMoment_step (hCc : A * (X - C t) * Cc = X ^ (2 * g + 1) - Vc.comp (X ^ 2))
    (hA' : A' = (-1) ^ g * Cc.comp (-X))
    (hmc : X ^ (2 * g + 1) ∣ A * d.comp (-X) - A.comp (-X) * d)
    (hA0 : A.eval 0 ≠ 0) (ht : t ≠ 0) :
    X ^ (2 * g + 1) ∣ A' * (d * (C t - X)).comp (-X) - A'.comp (-X) * (d * (C t - X)) := by
  -- the composed defect is the old one times `(z² - t²)`
  have h2 : A * (X - C t) * (d * (C t - X)).comp (-X)
        - (A * (X - C t)).comp (-X) * (d * (C t - X))
      = (X ^ 2 - C t ^ 2) * (A * d.comp (-X) - A.comp (-X) * d) := by
    simp only [mul_comp, sub_comp, C_comp, X_comp]
    ring
  have hdvd1 : X ^ (2 * g + 1)
      ∣ A' * (A * (X - C t)).comp (-X) - A'.comp (-X) * (A * (X - C t)) := by
    rw [cuspNext_exact hCc hA']
    exact (dvd_mul_left _ 2).mul_left _
  have hdvd2 : X ^ (2 * g + 1) ∣ A * (X - C t) * (d * (C t - X)).comp (-X)
      - (A * (X - C t)).comp (-X) * (d * (C t - X)) := by
    rw [h2]
    exact hmc.mul_left _
  -- combine the two defects; the composed support is invertible mod `z^N` by avoidance
  have hkey : (A * (X - C t)).comp (-X)
        * (A' * (d * (C t - X)).comp (-X) - A'.comp (-X) * (d * (C t - X)))
      = (d * (C t - X)).comp (-X)
          * (A' * (A * (X - C t)).comp (-X) - A'.comp (-X) * (A * (X - C t)))
        + A'.comp (-X) * (A * (X - C t) * (d * (C t - X)).comp (-X)
          - (A * (X - C t)).comp (-X) * (d * (C t - X))) := by
    ring
  have hdvd3 := (hdvd1.mul_left ((d * (C t - X)).comp (-X))).add (hdvd2.mul_left (A'.comp (-X)))
  rw [← hkey] at hdvd3
  have heval : ((A * (X - C t)).comp (-X)).eval 0 ≠ 0 := by
    rw [eval_comp]
    simp only [eval_neg, eval_X, neg_zero, eval_mul, eval_sub, eval_C]
    simpa using mul_ne_zero hA0 (neg_ne_zero.mpr ht)
  exact (isCoprime_X_pow_of_eval_zero_ne_zero heval _).dvd_of_dvd_mul_left hdvd3

/-- **The master congruence along a fold chain** (`thm:cusp-moment` (1)): a base congruence
for `(A 0, d₀)` transfers along any certificate chain of fold steps to
`(A m, d₀·∏(tᵢ - z))`, provided the avoidance values `A j |>.eval 0` and the nodes `t j` are
nonzero. The steps enter only through their factorization certificates — the doubling step
needs no special treatment. -/
theorem cuspMoment_congruence {m : ℕ} {A Vc Cc : ℕ → F[X]} {t : ℕ → F} {d₀ : F[X]}
    (hCc : ∀ j < m, A j * (X - C (t j)) * Cc j = X ^ (2 * g + 1) - (Vc j).comp (X ^ 2))
    (hA' : ∀ j < m, A (j + 1) = (-1) ^ g * (Cc j).comp (-X))
    (hA0 : ∀ j < m, (A j).eval 0 ≠ 0) (ht : ∀ j < m, t j ≠ 0)
    (hd0 : X ^ (2 * g + 1) ∣ A 0 * d₀.comp (-X) - (A 0).comp (-X) * d₀) :
    X ^ (2 * g + 1) ∣ A m * (d₀ * ∏ i ∈ Finset.range m, (C (t i) - X)).comp (-X)
      - (A m).comp (-X) * (d₀ * ∏ i ∈ Finset.range m, (C (t i) - X)) := by
  induction m with
  | zero => simpa using hd0
  | succ m ih =>
    have hm := ih (fun j hj ↦ hCc j (by lia)) (fun j hj ↦ hA' j (by lia))
      (fun j hj ↦ hA0 j (by lia)) (fun j hj ↦ ht j (by lia))
    rw [Finset.prod_range_succ, ← mul_assoc]
    exact cuspMoment_step (hCc m (by lia)) (hA' m (by lia)) hm (hA0 m (by lia)) (ht m (by lia))

end Field

end ChabautyColeman

end
