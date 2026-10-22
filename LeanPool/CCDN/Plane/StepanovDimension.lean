/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hilbert.FilteredIntersection
public import LeanPool.CCDN.Plane.FiniteFieldConstants
import LeanPool.CCDN.Hilbert.PlaneHilbert
import LeanPool.CCDN.Plane.StepanovParameters
import Mathlib.Data.Nat.Choose.Bounds

/-! The exact plane Hilbert function verifies the Stepanov dimension inequality
for the constructed integer parameters. -/

@[expose] public section
namespace CCDN
noncomputable section

private lemma principal_plane_hilbert_balance {K : Type*} [Field K]
    (f : MvPolynomial (Fin 2) K) (hf : f ≠ 0) {M : ℕ} (hM : f.totalDegree ≤ M) :
    Module.finrank K (filteredCoordinateSpace (Ideal.span {f}) M) + f.totalDegree.choose 2 =
      f.totalDegree * M + f.totalDegree := by
  have hh := principal_plane_hilbert_function f hf hM
  have he : (Module.finrank K (filteredCoordinateSpace (Ideal.span {f}) M) : ℤ) +
      f.totalDegree.choose 2 = (f.totalDegree : ℤ) * M + f.totalDegree := by omega
  exact_mod_cast he

private lemma principal_plane_hilbert_bounds {K : Type*} [Field K]
    (f : MvPolynomial (Fin 2) K) (hf : f ≠ 0) {M : ℕ} (hM : f.totalDegree ≤ M) :
    f.totalDegree * M - f.totalDegree ^ 2 ≤
      Module.finrank K (filteredCoordinateSpace (Ideal.span {f}) M) ∧
    Module.finrank K (filteredCoordinateSpace (Ideal.span {f}) M) ≤ f.totalDegree * (M + 1) := by
  have hh := principal_plane_hilbert_balance f hf hM
  have hc := Nat.choose_le_pow f.totalDegree 2
  constructor
  · omega
  · nlinarith

/-- The numerical inequality suffices for the exact filtered dimensions. -/
theorem stepanov_hilbert_dimension_inequality {K : Type*} [Field K]
    (f : MvPolynomial (Fin 2) K) (hf : f ≠ 0) (p A D N : ℕ)
    (hd : 0 < f.totalDegree) (hp : stepanovThreshold f.totalDegree < p)
    (hA : f.totalDegree ≤ A) (hD : f.totalDegree ≤ D)
    (hx : (f.totalDegree * A) ^ 2 ≤ p) (hy : p ≤ f.totalDegree * D + f.totalDegree)
    (hN : N + 4 * f.totalDegree ^ 2 = f.totalDegree * A) (hNpos : 0 < N) :
    (∑ r : Fin N, Module.finrank K
      (filteredCoordinateSpace (Ideal.span {f}) (D + A + r.val * f.totalDegree))) <
      Module.finrank K (filteredCoordinateSpace (Ideal.span {f}) D) *
      Module.finrank K (filteredCoordinateSpace (Ideal.span {f}) A) := by
  have hsum : (∑ r : Fin N, Module.finrank K
      (filteredCoordinateSpace (Ideal.span {f}) (D + A + r.val * f.totalDegree))) ≤
      N * (f.totalDegree * A + f.totalDegree * D + f.totalDegree + f.totalDegree ^ 2 * N) := by
    calc
      _ ≤ ∑ _r : Fin N, f.totalDegree * (D + A + N * f.totalDegree + 1) := by
        apply Finset.sum_le_sum
        intro r _
        apply (principal_plane_hilbert_bounds f hf
          (by omega : f.totalDegree ≤ D + A + r.val * f.totalDegree)).2.trans
        apply Nat.mul_le_mul_left
        have hh := Nat.mul_le_mul_right f.totalDegree (Nat.le_of_lt r.isLt)
        omega
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring
  have hn := stepanov_numeric_dimension f.totalDegree p (f.totalDegree * A)
    (f.totalDegree * D) N hd hp hx hy hN hNpos
  have hprod := Nat.mul_le_mul (principal_plane_hilbert_bounds f hf hA).1
    (principal_plane_hilbert_bounds f hf hD).1
  exact hsum.trans_lt (hn.trans_le (by nlinarith only [hprod]))

end
end CCDN
