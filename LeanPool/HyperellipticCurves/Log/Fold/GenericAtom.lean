/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Fold.PeelCascade

/-!
# The atom determinants at generic nodes

Every certificate atom of `thm:cusp-witness` is a pattern determinant of a
doubles-and-singles alphabet, possibly extended by a zero node or by one extension group
(signed pair, signed trio, or tripled node) carrying a distinguished node. This file proves
that each atom is **nonzero when the nodes are distinct variables** — i.e. as an element of
`MvPolynomial ℕ K` — which is the function-field form the chain induction of
`thm:cusp-witness` consumes (any concrete index layout follows by an injective
`MvPolynomial.rename`, and nonvanishing over the fraction field by injectivity of the
algebra map).

The proof is the exact leading-coefficient induction of
`LeanPool.HyperellipticCurves.Log.Fold.PeelCascade`:
the doubles-and-singles atoms are the doubles cascade outright (base `1`, resp. `X` for
the avoidance-value atoms), and each extension atom peels its distinguished node first
(`ChabautyColeman.peelHom` at that node, then the lead, identity or tripled stage of
`LeanPool.HyperellipticCurves.Log.Fold.PeelCoeff`) and hands the rest to the cascade. No
specialization and
no valuation enters.

* `ChabautyColeman.momentDet_generic_doubles_ne_zero`: the avoidance/step+ atoms;
* `ChabautyColeman.momentDet_generic_doubles_mul_X_ne_zero`: the avoidance-value atoms
  `NA_j(0)`;
* `ChabautyColeman.momentDet_generic_pair_ne_zero`: the step− atoms;
* `ChabautyColeman.momentDet_generic_trio_ne_zero`,
  `ChabautyColeman.momentDet_generic_tripled_ne_zero`: the mirror atoms for stages
  `j ≥ 2` (the doubled node `j - 1` completed to the signed trio resp. tripled by the
  extension node);
* `ChabautyColeman.momentDet_generic_trio_id_ne_zero`,
  `ChabautyColeman.momentDet_generic_tripled_one_ne_zero`: the mirror atoms for stage
  `j = 1` (the latter with the top single peeled first, matching its peel order).

All seven are stated with the node lists in **descending fold order** — exactly the
lists `ChabautyColeman.cusp_alphabet_comp_neg` produces — so the chain instantiation
consumes them without any relabeling.
-/
@[expose] public section

open Polynomial

namespace ChabautyColeman

section PeelImages

variable {K : Type*} [CommRing K]

/-- The peel image of the stage-`j` alphabet at its extension node `j - 1`: the doubles stay,
the singles shift down. -/
private theorem doublesPoly_map_peelHom {g j : ℕ} (hj2 : 2 ≤ j) :
    (doublesPoly (fun l ↦ (MvPolynomial.X (j - 2 - l) : MvPolynomial ℕ K))
        (fun i ↦ MvPolynomial.X (g - 1 - i)) (j - 1) (g - j)).map (peelHom K (j - 1))
      = (doublesPoly (fun l ↦ (MvPolynomial.X (j - 2 - l) : MvPolynomial ℕ K))
          (fun i ↦ MvPolynomial.X (g - 2 - i)) (j - 1) (g - j)).map C := by
  rw [doublesPoly_map, doublesPoly_map]
  refine doublesPoly_congr (fun l hl ↦ ?_) fun i hi ↦ ?_
  · rw [peelHom_X_of_lt (by lia)]
  · rw [peelHom_X_of_gt (by lia), show g - 1 - i - 1 = g - 2 - i by lia]

/-- The peel image of the stage-`1` singles at node `0`: all singles shift down. -/
private theorem singlesPoly_map_peelHom_zero (k : ℕ) :
    (singlesPoly (fun i ↦ (MvPolynomial.X (k - i) : MvPolynomial ℕ K)) k).map (peelHom K 0)
      = (singlesPoly (fun i ↦ (MvPolynomial.X (k - 1 - i) : MvPolynomial ℕ K)) k).map C := by
  rw [singlesPoly_map, singlesPoly_map]
  exact singlesPoly_congr fun i hi ↦ by
    rw [peelHom_X_of_gt (by lia), show k - i - 1 = k - 1 - i by lia]

end PeelImages

section GenericAtoms

variable {K : Type*} [CommRing K] [IsDomain K] {g : ℕ}

/-- The singles cascade at base `1`: `k` generic singles at the stage-`k` pattern. -/
private theorem momentDet_singles_one_ne_zero {k : ℕ} (hk : k ≤ g) :
    momentDet g (singlesPoly (fun i ↦ (MvPolynomial.X (k - 1 - i) : MvPolynomial ℕ K)) k)
      (peelPattern g k) ≠ 0 := by
  have h := momentDet_singles_ne_zero (g := g) (b := (1 : K[X])) (r₀ := 0) (by simp)
    (by rw [← C_1, momentDet_C_peelPattern_zero, one_pow]; exact one_ne_zero) (k := k) (by lia)
  rwa [Polynomial.map_one, one_mul, zero_add] at h

/-- The doubles cascade at base `1`: the stage-`d` alphabet with `k` singles, at the
pattern `min g (2d + k)`. -/
private theorem momentDet_doubles_one_ne_zero [NeZero (2 : K)] {d k : ℕ} (hk : k ≤ g) :
    momentDet g (doublesPoly (fun l ↦ (MvPolynomial.X (d - 1 - l) : MvPolynomial ℕ K))
        (fun i ↦ MvPolynomial.X (d + k - 1 - i)) d k) (peelPattern g (min g (2 * d + k))) ≠ 0 := by
  have h := momentDet_doubles_ne_zero (g := g) (b := (1 : K[X])) (r₀ := 0) (by simp)
    (by rw [← C_1, momentDet_C_peelPattern_zero, one_pow]; exact one_ne_zero) (d := d) (k := k)
    (by lia)
  rwa [Polynomial.map_one, one_mul, add_zero] at h

/-- **The avoidance/step+ atoms are nonzero at generic nodes**: the stage-`J` fold
alphabet — the first `J` nodes doubled, the rest single, all nodes distinct variables in
descending fold order — has nonzero moment determinant. -/
theorem momentDet_generic_doubles_ne_zero [NeZero (2 : K)] {J : ℕ} (hJ : J ≤ g) :
    momentDet g (doublesPoly (fun l ↦ (MvPolynomial.X (J - 1 - l) : MvPolynomial ℕ K))
        (fun i ↦ MvPolynomial.X (g - 1 - i)) J (g - J)) (fun m ↦ (m : ℕ)) ≠ 0 := by
  have h := momentDet_doubles_one_ne_zero (K := K) (g := g) (d := J) (k := g - J) (by lia)
  rwa [show J + (g - J) - 1 = g - 1 by lia, show min g (2 * J + (g - J)) = g by lia,
    peelPattern_eq_id le_rfl] at h

/-- **The avoidance-value atoms `NA_J(0)` are nonzero at generic nodes**: the zero-node
extension of the stage-`J` fold alphabet has nonzero pattern determinant (`1 ≤ J`; at
`J = 0` the state support is the explicit node product). -/
theorem momentDet_generic_doubles_mul_X_ne_zero [NeZero (2 : K)] {J : ℕ} (hJ1 : 1 ≤ J)
    (hJ : J ≤ g) :
    momentDet g (doublesPoly (fun l ↦ (MvPolynomial.X (J - 1 - l) : MvPolynomial ℕ K))
        (fun i ↦ MvPolynomial.X (g - 1 - i)) J (g - J) * X) (fun m ↦ (m : ℕ)) ≠ 0 := by
  have h := momentDet_doubles_ne_zero (g := g) (b := (X : K[X])) (r₀ := 1) natDegree_X_le
    (by rw [momentDet_X_peelPattern_one]; exact one_ne_zero) (d := J) (k := g - J) (by lia)
  rwa [Polynomial.map_X, mul_comm, show J + (g - J) - 1 = g - 1 by lia,
    show min g (2 * J + (g - J) + 1) = g by lia, peelPattern_eq_id le_rfl] at h

/-- **The step− atoms are nonzero at generic nodes**: the stage-`j` fold alphabet with the
single at the extension node `j` completed to the signed pair has nonzero pattern
determinant (`1 ≤ j < g`; at `j = 0` the stage is the doubling step and has no step−
condition). The extension node is lead-peeled first. -/
theorem momentDet_generic_pair_ne_zero [NeZero (2 : K)] {j : ℕ} (hj1 : 1 ≤ j) (hj : j < g) :
    momentDet g (doublesPoly (fun l ↦ (MvPolynomial.X (j - 1 - l) : MvPolynomial ℕ K))
        (fun i ↦ MvPolynomial.X (g - 1 - i)) j (g - j - 1)
      * (X ^ 2 - Polynomial.C (MvPolynomial.X j ^ 2))) (fun m ↦ (m : ℕ)) ≠ 0 := by
  refine momentDet_ne_zero_of_map (peelHom K j) fun h0 ↦ ?_
  have hmap : (doublesPoly (fun l ↦ (MvPolynomial.X (j - 1 - l) : MvPolynomial ℕ K))
          (fun i ↦ MvPolynomial.X (g - 1 - i)) j (g - j - 1)
        * (X ^ 2 - Polynomial.C (MvPolynomial.X j ^ 2))).map (peelHom K j)
      = (doublesPoly (fun l ↦ (MvPolynomial.X (j - 1 - l) : MvPolynomial ℕ K))
          (fun i ↦ MvPolynomial.X (g - 2 - i)) j (g - j - 1)).map C
        * (X ^ 2 - Polynomial.C (X ^ 2)) := by
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C, map_pow, peelHom_X_self, doublesPoly_map]
    refine congrArg (· * _) (doublesPoly_congr (fun l hl ↦ ?_) fun i hi ↦ ?_)
    · rw [peelHom_X_of_lt (by lia)]
    · rw [peelHom_X_of_gt (by lia), show g - 1 - i - 1 = g - 2 - i by lia]
  have hrest := momentDet_doubles_one_ne_zero (K := K) (g := g) (d := j) (k := g - j - 1)
    (by lia)
  rw [show j + (g - j - 1) - 1 = g - 2 by lia,
    show min g (2 * j + (g - j - 1)) = g by lia, peelPattern_eq_id le_rfl] at hrest
  set q := doublesPoly (fun l ↦ (MvPolynomial.X (j - 1 - l) : MvPolynomial ℕ K))
    (fun i ↦ MvPolynomial.X (g - 2 - i)) j (g - j - 1)
  have hc := coeff_momentDet_lead q (natDegree_X_sq_sub_C_lt _)
    (Nat.lt_add_one_iff.mp (natDegree_X_sq_sub_C_lt _)) natDegree_coeff_X_sq_sub_C_le
    coeff_zero_X_sq_sub_C (fun m : Fin g ↦ (m : ℕ))
  rw [hmap] at h0
  rw [h0, coeff_zero] at hc
  exact hrest (by simpa using hc.symm)

/-- The doubles cascade behind the mirror atoms for `j ≥ 2`: the stage-`j` alphabet with
the extension node peeled off, at the identity pattern. -/
private theorem momentDet_mirror_rest_ne_zero [NeZero (2 : K)] {j : ℕ} (hj2 : 2 ≤ j)
    (hj : j ≤ g) :
    momentDet g (doublesPoly (fun l ↦ (MvPolynomial.X (j - 2 - l) : MvPolynomial ℕ K))
        (fun i ↦ MvPolynomial.X (g - 2 - i)) (j - 1) (g - j)) (fun m ↦ (m : ℕ)) ≠ 0 := by
  have h := momentDet_doubles_one_ne_zero (K := K) (g := g) (d := j - 1) (k := g - j) (by lia)
  rwa [show j - 1 + (g - j) - 1 = g - 2 by lia,
    show min g (2 * (j - 1) + (g - j)) = g by lia, peelPattern_eq_id le_rfl] at h

/-- **The mirror− atoms (`j ≥ 2` shape) are nonzero at generic nodes**: the stage-`j`
fold alphabet with the doubled node `j - 1` completed to the signed trio by the extension
node has nonzero pattern determinant. The extension node is lead-peeled first. -/
theorem momentDet_generic_trio_ne_zero [NeZero (2 : K)] {j : ℕ}
    (hj2 : 2 ≤ j) (hj : j ≤ g) :
    momentDet g (doublesPoly (fun l ↦ (MvPolynomial.X (j - 2 - l) : MvPolynomial ℕ K))
        (fun i ↦ MvPolynomial.X (g - 1 - i)) (j - 1) (g - j)
      * ((Polynomial.C (MvPolynomial.X (j - 1)) + X) ^ 2
        * (X - Polynomial.C (MvPolynomial.X (j - 1))))) (fun m ↦ (m : ℕ)) ≠ 0 := by
  refine momentDet_ne_zero_of_map (peelHom K (j - 1)) fun h0 ↦ ?_
  rw [Polynomial.map_mul, doublesPoly_map_peelHom hj2] at h0
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_C, Polynomial.map_X, peelHom_X_self] at h0
  have hrest := momentDet_mirror_rest_ne_zero (K := K) hj2 hj
  set q := doublesPoly (fun l ↦ (MvPolynomial.X (j - 2 - l) : MvPolynomial ℕ K))
    (fun i ↦ MvPolynomial.X (g - 2 - i)) (j - 1) (g - j)
  have hc := coeff_momentDet_lead q (natDegree_trio_lt _)
    (Nat.lt_add_one_iff.mp (natDegree_trio_lt _)) natDegree_coeff_trio_le coeff_zero_trio
    (fun m : Fin g ↦ (m : ℕ))
  rw [h0, coeff_zero] at hc
  exact hrest (by simpa using hc.symm)

/-- **The mirror+ atoms (`j ≥ 2` shape) are nonzero at generic nodes**: the stage-`j`
fold alphabet with the doubled node `j - 1` tripled by the extension node has nonzero
pattern determinant. The extension node is lead-peeled first. -/
theorem momentDet_generic_tripled_ne_zero [NeZero (2 : K)] {j : ℕ}
    (hj2 : 2 ≤ j) (hj : j ≤ g) :
    momentDet g (doublesPoly (fun l ↦ (MvPolynomial.X (j - 2 - l) : MvPolynomial ℕ K))
        (fun i ↦ MvPolynomial.X (g - 1 - i)) (j - 1) (g - j)
      * (Polynomial.C (MvPolynomial.X (j - 1)) + X) ^ 3) (fun m ↦ (m : ℕ)) ≠ 0 := by
  refine momentDet_ne_zero_of_map (peelHom K (j - 1)) fun h0 ↦ ?_
  rw [Polynomial.map_mul, doublesPoly_map_peelHom hj2] at h0
  simp only [Polynomial.map_pow, Polynomial.map_add, Polynomial.map_C, Polynomial.map_X,
    peelHom_X_self] at h0
  have hrest := momentDet_mirror_rest_ne_zero (K := K) hj2 hj
  set q := doublesPoly (fun l ↦ (MvPolynomial.X (j - 2 - l) : MvPolynomial ℕ K))
    (fun i ↦ MvPolynomial.X (g - 2 - i)) (j - 1) (g - j)
  have hc := coeff_momentDet_lead q (natDegree_tripled_lt _)
    (Nat.lt_add_one_iff.mp (natDegree_tripled_lt _)) natDegree_coeff_tripled_le
    coeff_zero_tripled (fun m : Fin g ↦ (m : ℕ))
  rw [h0, coeff_zero, one_pow, one_mul] at hc
  exact hrest hc.symm

/-- **The mirror− atom (`j = 1` shape) is nonzero at generic nodes**: the stage-`1` fold
alphabet of size `g + 1` — the doubled node `0` completed to the signed trio by the
extension node, over the `g` fold-order singles. The extension node is peeled first, at
the identity stage. -/
theorem momentDet_generic_trio_id_ne_zero :
    momentDet (g + 1) (singlesPoly (fun i ↦ (MvPolynomial.X (g - i) : MvPolynomial ℕ K)) g
      * ((Polynomial.C (MvPolynomial.X 0) + X) ^ 2
        * (X - Polynomial.C (MvPolynomial.X 0)))) (fun m ↦ (m : ℕ)) ≠ 0 := by
  refine momentDet_ne_zero_of_map (peelHom K 0) fun h0 ↦ ?_
  rw [Polynomial.map_mul, singlesPoly_map_peelHom_zero] at h0
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_C, Polynomial.map_X, peelHom_X_self] at h0
  have hrest := momentDet_singles_one_ne_zero (K := K) (g := g + 1) (k := g) (by lia)
  set q := singlesPoly (fun i ↦ (MvPolynomial.X (g - 1 - i) : MvPolynomial ℕ K)) g
  have hc := coeff_momentDet_id (q := q) (by norm_num) (natDegree_trio_lt _)
    (Nat.lt_add_one_iff.mp (natDegree_trio_lt _)) natDegree_coeff_trio_le coeff_zero_trio
    coeff_one_trio (by norm_num) (natDegree_singlesPoly_le _ g)
  rw [h0, coeff_zero] at hc
  exact hrest (by simpa using hc.symm)

/-- The tripled node at the identity pattern of size `g + 2` over `g` fold-order singles:
the `j = 1` mirror+ atom after its top single has been peeled. -/
private theorem momentDet_generic_tripled_id_ne_zero [NeZero (2 : K)] :
    momentDet (g + 2) (singlesPoly (fun i ↦ (MvPolynomial.X (g - i) : MvPolynomial ℕ K)) g
      * (Polynomial.C (MvPolynomial.X 0) + X) ^ 3) (fun m ↦ (m : ℕ)) ≠ 0 := by
  refine momentDet_ne_zero_of_map (peelHom K 0) fun h0 ↦ ?_
  rw [Polynomial.map_mul, singlesPoly_map_peelHom_zero] at h0
  simp only [Polynomial.map_pow, Polynomial.map_add, Polynomial.map_C, Polynomial.map_X,
    peelHom_X_self] at h0
  have hrest := momentDet_singles_one_ne_zero (K := K) (g := g + 2) (k := g) (by lia)
  set q := singlesPoly (fun i ↦ (MvPolynomial.X (g - 1 - i) : MvPolynomial ℕ K)) g
  have hc := coeff_momentDet_triple_id (q := q) (natDegree_singlesPoly_le _ g)
  rw [h0, coeff_zero] at hc
  refine hrest ((mul_eq_zero.mp hc.symm).resolve_left ?_)
  rw [show (8 : MvPolynomial ℕ K) = 2 ^ 3 by norm_num]
  exact pow_ne_zero _ two_ne_zero_mvPolynomial

/-- **The mirror+ atom (`j = 1` shape) is nonzero at generic nodes**: the stage-`1` fold
alphabet of size `g + 2` — the doubled node `0` tripled by the extension node, over the
`g + 1` fold-order singles, with the top single (node `1`) lead-peeled first. -/
theorem momentDet_generic_tripled_one_ne_zero [NeZero (2 : K)] :
    momentDet (g + 2)
      (singlesPoly (fun i ↦ (MvPolynomial.X (g + 1 - i) : MvPolynomial ℕ K)) g
        * (Polynomial.C (MvPolynomial.X 1) + X)
        * (Polynomial.C (MvPolynomial.X 0) + X) ^ 3) (fun m ↦ (m : ℕ)) ≠ 0 := by
  refine momentDet_ne_zero_of_map (peelHom K 1) fun h0 ↦ ?_
  have hmap : (singlesPoly (fun i ↦ (MvPolynomial.X (g + 1 - i) : MvPolynomial ℕ K)) g
        * (Polynomial.C (MvPolynomial.X 1) + X)
        * (Polynomial.C (MvPolynomial.X 0) + X) ^ 3).map (peelHom K 1)
      = (singlesPoly (fun i ↦ (MvPolynomial.X (g - i) : MvPolynomial ℕ K)) g
          * (Polynomial.C (MvPolynomial.X 0) + X) ^ 3).map C * (C X + X) := by
    rw [mul_right_comm]
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_C,
      Polynomial.map_X, peelHom_X_self, peelHom_X_of_lt one_pos, singlesPoly_map]
    refine congrArg (· * _) (congrArg (· * _) (singlesPoly_congr fun i hi ↦ ?_))
    rw [peelHom_X_of_gt (by lia), show g + 1 - i - 1 = g - i by lia]
  have hrest := momentDet_generic_tripled_id_ne_zero (K := K) (g := g)
  rw [hmap] at h0
  set q := singlesPoly (fun i ↦ (MvPolynomial.X (g - i) : MvPolynomial ℕ K)) g
    * (Polynomial.C (MvPolynomial.X 0) + X) ^ 3
  have hc := coeff_momentDet_lead q (natDegree_C_add_X_lt _)
    (Nat.lt_add_one_iff.mp (natDegree_C_add_X_lt _)) natDegree_coeff_C_add_X_le
    coeff_zero_C_add_X (fun m : Fin (g + 2) ↦ (m : ℕ))
  rw [h0, coeff_zero, one_pow, one_mul] at hc
  exact hrest hc.symm

end GenericAtoms

end ChabautyColeman

end
