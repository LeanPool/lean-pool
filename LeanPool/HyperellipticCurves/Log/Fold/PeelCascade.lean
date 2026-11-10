/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Fold.PeelCoeff
public import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# The peel cascades at generic nodes

The atom determinants of `thm:cusp-witness` are pattern determinants of doubles-and-singles
alphabets whose nodes are distinct variables of `MvPolynomial ℕ K`, listed in descending
fold order — so the node to peel first is always the variable `0`. The **peel
homomorphism** `ChabautyColeman.peelHom K m` makes the variable `m` the polynomial
variable of `(MvPolynomial ℕ K)[u]` and shifts the variables above `m` down, turning the
determinant into a polynomial in the peeled node over the remaining generic nodes. Its
top coefficient is computed by the stage identities of
`LeanPool.HyperellipticCurves.Log.Fold.PeelCoeff`, and
is — up to a power of `2` — the determinant of the remaining alphabet, again in descending
fold order; so nonvanishing follows by induction on the number of nodes, with no
specialization, rate or valuation anywhere
(`ChabautyColeman.momentDet_ne_zero_of_map`).

* `ChabautyColeman.momentDet_singles_ne_zero`: the **singles cascade** — a base polynomial
  over `K` of degree `≤ r₀` with nonzero stage-`r₀` determinant, times `k` generic single
  nodes, has nonzero stage-`(r₀ + k)` determinant;
* `ChabautyColeman.momentDet_doubles_ne_zero`: the **doubles cascade** — the same with
  `d` doubled and `k` single nodes, at the pattern index `min g (2d + k + r₀)`, by the
  **three-regime flavor law**: each doubled peel is a doubled stage, an identity stage or a
  lead according to the position of `2(d+1) + k + r₀` relative to `g`.

The base polynomial is `1` (avoidance/step atoms) or `X` (avoidance-value atoms); the
extension atoms peel their distinguished node first
(`LeanPool.HyperellipticCurves.Log.Fold.GenericAtom`).
-/
@[expose] public section

open Polynomial

namespace ChabautyColeman

section PeelHom

variable (K : Type*) [CommRing K]

/-- **The peel homomorphism at node `m`**: the variable `m` becomes the polynomial variable,
the variables below `m` stay, those above shift down by one. Peeling along it turns a
generic-node determinant into a polynomial in the peeled node over the remaining generic
nodes, whose top coefficient the stage identities compute. -/
noncomputable def peelHom (m : ℕ) : MvPolynomial ℕ K →+* (MvPolynomial ℕ K)[X] :=
  (MvPolynomial.aeval fun i ↦ if i = m then (X : (MvPolynomial ℕ K)[X])
    else if i < m then C (MvPolynomial.X i) else C (MvPolynomial.X (i - 1))).toRingHom

variable {K}

@[simp] theorem peelHom_X_self (m : ℕ) : peelHom K m (MvPolynomial.X m) = X := by simp [peelHom]

theorem peelHom_X_of_lt {m i : ℕ} (h : i < m) :
    peelHom K m (MvPolynomial.X i) = C (MvPolynomial.X i) := by
  simp [peelHom, h.ne, h]

theorem peelHom_X_of_gt {m i : ℕ} (h : m < i) :
    peelHom K m (MvPolynomial.X i) = C (MvPolynomial.X (i - 1)) := by
  simp [peelHom, h.ne', h.not_gt]

@[simp] theorem peelHom_C (m : ℕ) (a : K) :
    peelHom K m (MvPolynomial.C a) = C (MvPolynomial.C a) := by
  simp [peelHom]

/-- A base polynomial with coefficients in `K` is untouched by a peel. -/
theorem map_peelHom_map_C (m : ℕ) (b : K[X]) :
    (b.map MvPolynomial.C).map (peelHom K m) = (b.map MvPolynomial.C).map C := by
  rw [Polynomial.map_map, Polynomial.map_map]
  congr 1
  ext a
  simp

end PeelHom

section Cascade

variable {K : Type*} [CommRing K] {g : ℕ}

/-- **The singles cascade**: a base polynomial `b` over `K` of degree at most `r₀` with
nonzero stage-`r₀` determinant, times `k` generic single nodes in descending order, has
nonzero stage-`(r₀ + k)` determinant. -/
theorem momentDet_singles_ne_zero {b : K[X]} {r₀ : ℕ} (hb : b.natDegree ≤ r₀)
    (hb0 : momentDet g b (peelPattern g r₀) ≠ 0) {k : ℕ} (hk : r₀ + k ≤ g) :
    momentDet g (b.map MvPolynomial.C
        * singlesPoly (fun i ↦ (MvPolynomial.X (k - 1 - i) : MvPolynomial ℕ K)) k)
      (peelPattern g (r₀ + k)) ≠ 0 := by
  induction k with
  | zero =>
    rw [singlesPoly_zero, mul_one, momentDet_map, add_zero]
    exact (map_ne_zero_iff _ (MvPolynomial.C_injective ℕ K)).mpr hb0
  | succ k ih =>
    refine momentDet_ne_zero_of_map (peelHom K 0) fun h0 ↦ ?_
    have hmap : (b.map MvPolynomial.C
          * singlesPoly (fun i ↦ (MvPolynomial.X (k + 1 - 1 - i) : MvPolynomial ℕ K)) (k + 1)).map
            (peelHom K 0)
        = (b.map MvPolynomial.C
            * singlesPoly (fun i ↦ (MvPolynomial.X (k - 1 - i) : MvPolynomial ℕ K)) k).map C
          * (C X + X) := by
      rw [singlesPoly_succ, ← mul_assoc]
      simp only [Polynomial.map_mul, map_peelHom_map_C, Polynomial.map_add, Polynomial.map_C,
        Polynomial.map_X, show k + 1 - 1 - k = 0 by lia, peelHom_X_self, singlesPoly_map]
      congr 2
      refine singlesPoly_congr fun i hi ↦ ?_
      rw [peelHom_X_of_gt (by lia),
        show k + 1 - 1 - i - 1 = k - 1 - i by lia]
    have hdeg : (b.map MvPolynomial.C
        * singlesPoly (fun i ↦ (MvPolynomial.X (k - 1 - i) : MvPolynomial ℕ K)) k).natDegree
          ≤ r₀ + k :=
      (natDegree_mul_le ..).trans
        (add_le_add (natDegree_map_le.trans hb) (natDegree_singlesPoly_le _ _))
    have hc := coeff_momentDet_single hdeg (by lia : r₀ + k < g)
    rw [← hmap, show r₀ + k + 1 = r₀ + (k + 1) by lia, h0, coeff_zero] at hc
    exact ih (by lia) hc.symm

/-- The survivor constant `2` of the doubled and identity stages is nonzero at generic
nodes whenever it is in `K`. -/
theorem two_ne_zero_mvPolynomial [NeZero (2 : K)] : (2 : MvPolynomial ℕ K) ≠ 0 := by
  rw [show (2 : MvPolynomial ℕ K) = MvPolynomial.C 2 from (map_ofNat _ 2).symm]
  exact (map_ne_zero_iff _ (MvPolynomial.C_injective ℕ K)).mpr two_ne_zero

variable [NoZeroDivisors K] [NeZero (2 : K)]

/-- **The doubles cascade**: a base polynomial `b` over `K` of degree at most `r₀` with
nonzero stage-`r₀` determinant, times `d` generic doubled nodes and `k` generic single nodes
in descending order, has nonzero determinant at the pattern index `min g (2d + k + r₀)` —
the three-regime flavor law: each doubled peel is a doubled stage (`2(d+1) + k + r₀ ≤ g`),
an identity stage (`= g + 1`) or a lead (`≥ g + 2`). -/
theorem momentDet_doubles_ne_zero {b : K[X]} {r₀ : ℕ} (hb : b.natDegree ≤ r₀)
    (hb0 : momentDet g b (peelPattern g r₀) ≠ 0) {d k : ℕ} (hk : r₀ + k ≤ g) :
    momentDet g (b.map MvPolynomial.C
        * doublesPoly (fun l ↦ (MvPolynomial.X (d - 1 - l) : MvPolynomial ℕ K))
          (fun i ↦ MvPolynomial.X (d + k - 1 - i)) d k)
      (peelPattern g (min g (2 * d + k + r₀))) ≠ 0 := by
  induction d with
  | zero =>
    simp only [doublesPoly_zero, zero_add, mul_zero, show min g (k + r₀) = r₀ + k by lia]
    exact momentDet_singles_ne_zero hb hb0 hk
  | succ d ih =>
    refine momentDet_ne_zero_of_map (peelHom K 0) fun h0 ↦ ?_
    have hmap : (b.map MvPolynomial.C
          * doublesPoly (fun l ↦ (MvPolynomial.X (d + 1 - 1 - l) : MvPolynomial ℕ K))
            (fun i ↦ MvPolynomial.X (d + 1 + k - 1 - i)) (d + 1) k).map (peelHom K 0)
        = (b.map MvPolynomial.C
            * doublesPoly (fun l ↦ (MvPolynomial.X (d - 1 - l) : MvPolynomial ℕ K))
              (fun i ↦ MvPolynomial.X (d + k - 1 - i)) d k).map C * (C X + X) ^ 2 := by
      rw [doublesPoly_succ, ← mul_assoc]
      simp only [Polynomial.map_mul, map_peelHom_map_C, Polynomial.map_pow, Polynomial.map_add,
        Polynomial.map_C, Polynomial.map_X, show d + 1 - 1 - d = 0 by lia, peelHom_X_self,
        doublesPoly_map]
      refine congrArg (· * _) (congrArg (_ * ·) (doublesPoly_congr (fun l hl ↦ ?_) fun i hi ↦ ?_))
      · rw [peelHom_X_of_gt (by lia : 0 < d + 1 - 1 - l),
          show d + 1 - 1 - l - 1 = d - 1 - l by lia]
      · rw [peelHom_X_of_gt (by lia : 0 < d + 1 + k - 1 - i),
          show d + 1 + k - 1 - i - 1 = d + k - 1 - i by lia]
    have hdeg : (b.map MvPolynomial.C
        * doublesPoly (fun l ↦ (MvPolynomial.X (d - 1 - l) : MvPolynomial ℕ K))
          (fun i ↦ MvPolynomial.X (d + k - 1 - i)) d k).natDegree ≤ 2 * d + k + r₀ := by
      have h1 := natDegree_doublesPoly_le (fun l ↦ (MvPolynomial.X (d - 1 - l) : MvPolynomial ℕ K))
        (fun i ↦ MvPolynomial.X (d + k - 1 - i)) d k
      have h2 := natDegree_map_le (p := b) (f := (MvPolynomial.C : K →+* MvPolynomial ℕ K))
      exact (natDegree_mul_le ..).trans (by lia)
    set q := b.map MvPolynomial.C
      * doublesPoly (fun l ↦ (MvPolynomial.X (d - 1 - l) : MvPolynomial ℕ K))
        (fun i ↦ MvPolynomial.X (d + k - 1 - i)) d k
    clear_value q
    have hF := natDegree_C_add_X_sq_lt (X : (MvPolynomial ℕ K)[X])
    rw [hmap] at h0
    rcases lt_or_ge g (2 * d + k + r₀ + 2) with hreg | hreg
    · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hreg) with hid | hlead
      · -- the identity-stage regime
        obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by lia⟩
        rw [show min (g' + 1) (2 * (d + 1) + k + r₀) = g' + 1 by lia,
          peelPattern_eq_id le_rfl] at h0
        rw [show min (g' + 1) (2 * d + k + r₀) = g' by lia] at ih
        have hc := coeff_momentDet_id (g := g') (by norm_num) hF (Nat.lt_add_one_iff.mp hF)
          natDegree_coeff_C_add_X_sq_le coeff_zero_C_add_X_sq coeff_one_C_add_X_sq (by lia)
          (hdeg.trans (by lia))
        rw [h0, coeff_zero, one_pow, one_mul] at hc
        exact mul_ne_zero two_ne_zero_mvPolynomial ih hc.symm
      · -- the lead regime
        rw [show min g (2 * (d + 1) + k + r₀) = g by lia] at h0
        rw [show min g (2 * d + k + r₀) = g by lia] at ih
        have hc := coeff_momentDet_lead q hF (Nat.lt_add_one_iff.mp hF)
          natDegree_coeff_C_add_X_sq_le coeff_zero_C_add_X_sq (peelPattern g g)
        rw [h0, coeff_zero, one_pow, one_mul] at hc
        exact ih hc.symm
    · -- the doubled-stage regime
      rw [show min g (2 * (d + 1) + k + r₀) = 2 * d + k + r₀ + 2 by lia] at h0
      rw [show min g (2 * d + k + r₀) = 2 * d + k + r₀ by lia] at ih
      have hc := coeff_momentDet_double hdeg hreg
      rw [h0, coeff_zero] at hc
      exact mul_ne_zero two_ne_zero_mvPolynomial ih hc.symm

end Cascade

end ChabautyColeman

end
