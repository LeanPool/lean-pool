/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Disks.OrdPoint

import LeanPool.HyperellipticCurves.ForMathlib.PolynomialDegreeLT

/-!
# The vanishing budget of a space of differentials

The Chabauty–Coleman bound counts, in each residue disk, the zeros of *one* differential.
Nothing forces the same differential to be used in every disk: any differential annihilating
the Mordell–Weil group will do. `ChabautyColeman.ordSpace` is the order of the best one,

`n(V, P_bar) = min {ord_P_bar(h_bar dx/y) | 0 ≠ h_bar ∈ V}`,

for a space `V` of numerators, and `ChabautyColeman.sum_ordSpace_le` is the resulting budget:
if `V` has codimension at most `r` in the space of numerators of the regular differentials
(the polynomials of degree `< g`), then

`∑_P_bar n(V, P_bar) ≤ 2r`,

which for `r = g - 1` is the classical `2g - 2` of `ChabautyColeman.sum_ordPoint_le` but is
sharp when the Mordell–Weil rank is small. This is Theorem 6.4 of Stoll's *Independence of
rational points on twists of a given curve* specialized to an odd hyperelliptic curve, where
it is elementary: the minimal multiplicities at the affine points assemble into a polynomial
`q` dividing every element of `V`, and the maximal degree `D` attained in `V` bounds the
order at infinity by `2(g - 1 - D)`, so

`dim V + deg q ≤ D + 1`

(`Polynomial.finrank_add_natDegree_le_of_forall_dvd` — the space of polynomials of degree
`≤ D` divisible by `q` has dimension `D + 1 - deg q`) leaves exactly `2·deg q + 2(g-1-D) ≤ 2r`
for the total. The affine half of the sum is then the ordinary budget of `q`
(`ChabautyColeman.sum_ordPoint_le_two_mul_natDegree`).

## References

* M. Stoll, *Independence of rational points on twists of a given curve*, Compositio Math.
  142 (2006), 1201–1214, Theorem 6.4.

Blueprint node: `cor:sum-ord-space`.
-/

@[expose] public section

open Module Polynomial

namespace ChabautyColeman

variable {κ : Type*} [Field κ] {f : κ[X]} {V : Submodule κ κ[X]}

/-- **The order of the best differential of a space at a point of the residue curve**:
`n(V, P_bar) = min {ord_P_bar(h_bar dx/y) | 0 ≠ h_bar ∈ V}`, for `V` a space of numerators. -/
noncomputable def ordSpace (f : κ[X]) (V : Submodule κ κ[X]) (P : CurvePoint κ f) : ℕ :=
  sInf {n | ∃ h ∈ V, h ≠ 0 ∧ ordPoint f h P = n}

theorem ordSpace_le {h : κ[X]} (hh : h ∈ V) (hh0 : h ≠ 0) (P : CurvePoint κ f) :
    ordSpace f V P ≤ ordPoint f h P :=
  Nat.sInf_le ⟨h, hh, hh0, rfl⟩

/-- The minimum defining `ChabautyColeman.ordSpace` is attained. -/
theorem exists_ordPoint_eq_ordSpace (hV : V ≠ ⊥) (P : CurvePoint κ f) :
    ∃ h ∈ V, h ≠ 0 ∧ ordPoint f h P = ordSpace f V P := by
  obtain ⟨h, hhV, hh0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
  exact Nat.sInf_mem (s := {n | ∃ h ∈ V, h ≠ 0 ∧ ordPoint f h P = n}) ⟨_, h, hhV, hh0, rfl⟩

/-! ### The budget -/

variable [NeZero (2 : κ)] [Fact (Odd f.natDegree)] [Fact (Squarefree f)]

/-- **The vanishing budget of a space of differentials** (blueprint `cor:sum-ord-space`):
if the numerators in `V` have degree `< g` and `V` has codimension at most `r` in that
space, then the orders of the best differentials sum to at most `2r` over any finite set
of points.

At `r = g - 1` this is the classical `2g - 2`; the gain over
`ChabautyColeman.sum_ordPoint_le` is that each point may use its own differential. -/
theorem sum_ordSpace_le (hV : V ≠ ⊥) (hdeg : ∀ h ∈ V, h.degree < genus f) {r : ℕ}
    (hr : genus f ≤ finrank κ V + r) (T : Finset (CurvePoint κ f)) :
    ∑ P ∈ T, ordSpace f V P ≤ 2 * r := by
  classical
  obtain ⟨hm, hmV, hm0, hD⟩ := exists_forall_natDegree_le_of_ne_bot hV hdeg
  obtain ⟨q, hq0, hqdvd, hqmult⟩ := exists_dvd_forall_mem_and_rootMultiplicity_le hV
    ((T.erase CurvePoint.infinity).image CurvePoint.xCoord)
  have hDg : hm.natDegree < genus f := (natDegree_lt_iff_degree_lt hm0).mpr (hdeg hm hmV)
  have hLA : finrank κ V + q.natDegree ≤ hm.natDegree + 1 :=
    finrank_add_natDegree_le_of_forall_dvd hV hqdvd fun h hh ↦
      degree_le_natDegree.trans_lt (mod_cast Nat.lt_succ_of_le (hD h hh))
  -- the affine points: the minimal multiplicities are those of `q`
  have haff : ∑ P ∈ T.erase CurvePoint.infinity, ordSpace f V P ≤ 2 * q.natDegree := by
    refine (Finset.sum_le_sum fun P hP ↦ ?_).trans
      (sum_ordPoint_le_two_mul_natDegree _ hq0 (Finset.notMem_erase _ _))
    cases P with
    | infinity => exact absurd rfl (Finset.ne_of_mem_erase hP)
    | affine x y he =>
      obtain ⟨h, hhV, hh0, hmult⟩ := hqmult x (Finset.mem_image_of_mem _ hP)
      exact (ordSpace_le hhV hh0 _).trans (ordAffine_le_ordAffine he hh0 hq0 hmult)
  -- the point at infinity: the element of maximal degree
  have hi := ordSpace_le hmV hm0 (CurvePoint.infinity (f := f))
  rw [ordPoint_infinity, ordInf_eq] at hi
  have hsum : ∑ P ∈ T, ordSpace f V P
      ≤ ordSpace f V CurvePoint.infinity + ∑ P ∈ T.erase CurvePoint.infinity, ordSpace f V P :=
    (Finset.sum_le_sum_of_subset (Finset.insert_erase_subset _ T)).trans
      (Finset.sum_insert (Finset.notMem_erase _ _)).le
  lia

end ChabautyColeman

end
