/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Fold.CuspBase
public import LeanPool.HyperellipticCurves.Log.Fold.Moment
public import LeanPool.HyperellipticCurves.Log.Fold.PeelAlphabet

import LeanPool.HyperellipticCurves.Log.Fold.CuspFold
import LeanPool.HyperellipticCurves.Log.Fold.MomentValue

/-!
# Towards the cuspidal witness: alphabets and value atoms

This file begins the assembly of `thm:cusp-witness`, connecting the cuspidal fold chain
(`LeanPool.HyperellipticCurves.Log.Fold.CuspChain`) to the pattern-determinant machinery:

* `ChabautyColeman.cusp_alphabet_comp_neg`: the `z ↦ -z` composition of the stage-`j`
  congruence alphabet `(-1)^g·A₀·∏_(i<j)(tᵢ - X)` — the polynomial whose moment matrix
  governs the stage — is *exactly* the monic doubles-and-singles product
  `ChabautyColeman.doublesPoly` with the first `j` nodes doubled: all signs cancel. The
  node lists come out in descending fold order, matching the peel order of the cascades at
  rates decreasing in the fold index.
* `ChabautyColeman.moment_system_of_congruence`: the master congruence forces the odd
  coefficients of `A·d(-z)`, i.e. the moment system of the stage alphabet.
* `ChabautyColeman.momentDet_value_atom`: consequently every evaluation of the state
  support times `det M` is a single pattern determinant of the once-extended alphabet
  (`thm:cusp-moment` (3) in determinant form) — the step and mirror condition values
  become products of two atom determinants via `ChabautyColeman.IsCuspState.eval_sq`.
* `ChabautyColeman.eval_ne_zero_of_momentDet_ne_zero`: nonvanishing of a value atom forces
  nonvanishing of the state evaluation — the invertibility-free step the chain induction
  consumes. The atoms themselves are certified at the generic nodes
  (`LeanPool.HyperellipticCurves.Log.Fold.GenericAtom`) and consumed through the chain induction of
  `LeanPool.HyperellipticCurves.Log.Fold.CuspGeneric` and
  `LeanPool.HyperellipticCurves.Log.Fold.CuspField`.
-/
@[expose] public section

open Polynomial

namespace ChabautyColeman

section Alphabet

variable {R : Type*} [CommRing R] {g : ℕ}

/-- **The fold's moment-system alphabet is the monic doubles-and-singles product**: the
`z ↦ -z` composition of the stage-`j` congruence alphabet `(-1)^g·A₀·∏_(i<j) (tᵢ - X)`
is exactly the positive-node product with the first `j` nodes doubled — all signs cancel.
The nodes are listed by *descending fold index*, matching the peel order of the cascades
at rates decreasing in the fold index. -/
theorem cusp_alphabet_comp_neg (t : ℕ → R) {j : ℕ} (hj : j ≤ g) :
    ((-1) ^ g * tupleU (fun i : Fin g ↦ t i)
        * ∏ i ∈ Finset.range j, (C (t i) - X)).comp (-X)
      = doublesPoly (fun l ↦ t (j - 1 - l)) (fun i ↦ t (g - 1 - i)) j (g - j) := by
  have hsplit := Finset.prod_range_add (fun i ↦ (C (t i) + X : R[X])) j (g - j)
  rw [show j + (g - j) = g by lia] at hsplit
  -- the three composed factors
  have hneg : ∏ i ∈ Finset.range g, -(C (t i) + X : R[X])
      = (-1) ^ g * ∏ i ∈ Finset.range g, (C (t i) + X) := by
    rw [Finset.prod_neg, Finset.card_range]
  have hA : (tupleU (fun i : Fin g ↦ t i)).comp (-X)
      = (-1) ^ g * ∏ i ∈ Finset.range g, (C (t i) + X) := by
    rw [tupleU_eq_prod, Fin.prod_univ_eq_prod_range (fun i ↦ ((X : R[X]) - C (t i))) g,
      prod_comp, ← hneg]
    exact Finset.prod_congr rfl fun i _ ↦ by
      rw [sub_comp, X_comp, C_comp]
      ring
  have hP : (∏ i ∈ Finset.range j, (C (t i) - X : R[X])).comp (-X)
      = ∏ i ∈ Finset.range j, (C (t i) + X) := by
    rw [prod_comp]
    exact Finset.prod_congr rfl fun i _ ↦ by
      rw [sub_comp, X_comp, C_comp]
      ring
  -- the reversed node lists of the cascade are the fold-ordered products
  have hv : ∏ l ∈ Finset.range j, (C (t (j - 1 - l)) + X : R[X]) ^ 2
      = ∏ l ∈ Finset.range j, (C (t l) + X) ^ 2 :=
    Finset.prod_range_reflect (fun l ↦ (C (t l) + X : R[X]) ^ 2) j
  have hu : singlesPoly (fun i ↦ t (g - 1 - i)) (g - j)
      = ∏ i ∈ Finset.range (g - j), (C (t (j + i)) + X) := by
    rw [singlesPoly,
      ← Finset.prod_range_reflect (fun i ↦ (C (t (j + i)) + X : R[X])) (g - j)]
    refine Finset.prod_congr rfl fun i hi ↦ ?_
    have h1 := Finset.mem_range.mp hi
    rw [show j + (g - j - 1 - i) = g - 1 - i by lia]
  have hsq : (-1 : R[X]) ^ g * (-1) ^ g = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨g, rfl⟩
  rw [mul_comp, mul_comp, hA, hP, pow_comp, neg_comp, one_comp, doublesPoly, hv, hu,
    hsplit, Finset.prod_pow]
  linear_combination (∏ i ∈ Finset.range j, (C (t i) + X : R[X])) ^ 2
    * (∏ i ∈ Finset.range (g - j), (C (t (j + i)) + X)) * hsq

end Alphabet

section ValueAtom

variable {F : Type*} [Field F] {g : ℕ}

/-- **The odd coefficients vanish along the congruence**: the moment system of the stage
alphabet, extracted from the master congruence. -/
theorem moment_system_of_congruence (h2 : (2 : F) ≠ 0) {A dm : F[X]}
    (hcong : X ^ (2 * g + 1) ∣ A * dm.comp (-X) - A.comp (-X) * dm) (i : Fin g) :
    (A * dm.comp (-X)).coeff (2 * (i : ℕ) + 1) = 0 :=
  coeff_mul_comp_neg_X_eq_zero h2 hcong ⟨i, by ring⟩ (by have := i.isLt; lia)

/-- **The value-atom identity**: at any stage of the master congruence, every evaluation
of the state support times `det M` is a single pattern determinant of the extended
alphabet (`thm:cusp-moment` (3), determinant form). -/
theorem momentDet_value_atom (h2 : (2 : F) ≠ 0) {A dm : F[X]} (hg : 0 < g)
    (hA : A.Monic) (hAdeg : A.natDegree = g)
    (hcong : X ^ (2 * g + 1) ∣ A * dm.comp (-X) - A.comp (-X) * dm) (w : F) :
    momentDet g (dm.comp (-X) * (C w + X)) (fun m ↦ (m : ℕ))
      = (-1) ^ g * (A.eval (-w) * (momentMatrix g (dm.comp (-X))).det) := by
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by lia⟩
  exact momentDet_linear hA hAdeg (fun i ↦ moment_system_of_congruence h2 hcong i) w

/-- Composition with `-X` turns the appended fold factor into the extension node. -/
theorem comp_neg_X_mul (dm : F[X]) (t : F) :
    (dm * (C t - X)).comp (-X) = dm.comp (-X) * (C t + X) := by
  rw [mul_comp, sub_comp, C_comp, X_comp]
  ring

/-- **The master congruence descends along even alphabet factors** that do not vanish at
`0` — on the cusp, the factor `∏ᵢ (X² - tᵢ²)` pairing each phase-2 node with one copy of
its double. -/
theorem congruence_of_even_mul {A dm e : F[X]} (h0 : e.eval 0 ≠ 0)
    (he : e.comp (-X) = e)
    (hcong : X ^ (2 * g + 1) ∣ A * (e * dm).comp (-X) - A.comp (-X) * (e * dm)) :
    X ^ (2 * g + 1) ∣ A * dm.comp (-X) - A.comp (-X) * dm := by
  rw [show A * (e * dm).comp (-X) - A.comp (-X) * (e * dm)
      = e * (A * dm.comp (-X) - A.comp (-X) * dm) by rw [mul_comp, he]; ring] at hcong
  exact (isCoprime_X_pow_of_eval_zero_ne_zero h0 _).dvd_of_dvd_mul_left hcong

/-- **Uniqueness of the monic moment solution** (`thm:cusp-moment` (3)): two monic
degree-`g` solutions of the master congruence for the same alphabet coincide when the
moment determinant is nonzero. -/
theorem eq_of_det_momentMatrix_ne_zero (h2 : (2 : F) ≠ 0) {A A' dm : F[X]}
    (hA : A.Monic) (hAdeg : A.natDegree = g) (hA' : A'.Monic) (hA'deg : A'.natDegree = g)
    (hcong : X ^ (2 * g + 1) ∣ A * dm.comp (-X) - A.comp (-X) * dm)
    (hcong' : X ^ (2 * g + 1) ∣ A' * dm.comp (-X) - A'.comp (-X) * dm)
    (hdet : (momentMatrix g (dm.comp (-X))).det ≠ 0) : A = A' := by
  have hv := momentMatrix_mulVec hA hAdeg (moment_system_of_congruence h2 hcong)
  have hv' := momentMatrix_mulVec hA' hA'deg (moment_system_of_congruence h2 hcong')
  have hsub : (momentMatrix g (dm.comp (-X))).mulVec
      ((fun m : Fin g ↦ A.coeff (m : ℕ)) - fun m : Fin g ↦ A'.coeff (m : ℕ)) = 0 := by
    rw [Matrix.mulVec_sub, hv, hv', sub_self]
  have hz := det_smul_eq_cramer_of_mulVec hsub
  rw [map_zero, smul_eq_zero] at hz
  have hzero := hz.resolve_left hdet
  refine Polynomial.ext fun n ↦ ?_
  rcases lt_trichotomy n g with hn | rfl | hn
  · simpa [sub_eq_zero] using congrFun hzero ⟨n, hn⟩
  · rw [← hAdeg, hA.coeff_natDegree, hAdeg, ← hA'deg, hA'.coeff_natDegree]
  · rw [coeff_eq_zero_of_natDegree_lt (by lia), coeff_eq_zero_of_natDegree_lt (by lia)]

/-- Nonvanishing of a value atom forces nonvanishing of the state evaluation. -/
theorem eval_ne_zero_of_momentDet_ne_zero (h2 : (2 : F) ≠ 0) {A dm : F[X]} (hg : 0 < g)
    (hA : A.Monic) (hAdeg : A.natDegree = g)
    (hcong : X ^ (2 * g + 1) ∣ A * dm.comp (-X) - A.comp (-X) * dm) {w : F}
    (hne : momentDet g (dm.comp (-X) * (C w + X)) (fun m ↦ (m : ℕ)) ≠ 0) :
    A.eval (-w) ≠ 0 := by
  intro h0
  rw [momentDet_value_atom h2 hg hA hAdeg hcong w, h0] at hne
  simp at hne

end ValueAtom

end ChabautyColeman

end
