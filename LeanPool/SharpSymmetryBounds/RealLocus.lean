/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.SharpSymmetryBounds.Irreducibility

/-!
# The real locus in complex coordinates

The real zero set of a plane polynomial written in the coordinates `X = z`, `Y = conj z`, and the
centered rotation bound for an irreducible, non-circle curve with infinite real locus.
-/

@[expose] public section

namespace CurveSymmetry

open MvPolynomial

/-- The real locus in complex coordinates: `X=z`, `Y=conj z`. -/
def realLocus (P : BPoly) : Set ℂ :=
  {z | eval (fun i : Fin 2 => if i = 0 then z else star z) P = 0}

lemma mem_realLocus_radial {a r z : ℂ} (ha : a ≠ 0) :
    z ∈ realLocus (C a * ((X 0 : BPoly) * X 1 - C r)) ↔ z * star z = r := by
  simp [realLocus, ha, sub_eq_zero]

/-- Infinitely many real points make an irreducible radial equation a genuine circle. -/
theorem radial_realLocus_is_circle {P : BPoly}
    (hinf : (realLocus P).Infinite)
    (hform : ∃ a r : ℂ, a ≠ 0 ∧ P = C a * ((X 0 : BPoly) * X 1 - C r)) :
    ∃ R : ℝ, 0 < R ∧ realLocus P = Metric.sphere (0 : ℂ) R := by
  obtain ⟨a, r, ha, rfl⟩ := hform
  obtain ⟨z, hz, hzne⟩ := hinf.exists_notMem_finite (Set.finite_singleton (0 : ℂ))
  have hz0 : z ≠ 0 := by simpa using hzne
  have hr : r = (Complex.normSq z : ℂ) := by
    rw [mem_realLocus_radial ha] at hz
    simpa [Complex.mul_conj] using hz.symm
  refine ⟨‖z‖, norm_pos_iff.mpr hz0, ?_⟩
  ext w
  rw [mem_realLocus_radial ha, hr]
  simp only [Metric.mem_sphere, dist_zero_right, Complex.star_def, Complex.mul_conj,
    Complex.ofReal_inj, Complex.normSq_eq_norm_sq]
  exact sq_eq_sq₀ (norm_nonneg w) (norm_nonneg z)

/-- The centered rotation bound with actual irreducibility and a non-circle real locus.

The remaining polynomial-level input is the sign transformation identity.
-/
theorem realLocus_rotation_bound {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    {P : BPoly} (hirr : Irreducible P) (hd : 2 ≤ P.totalDegree)
    (hinf : (realLocus P).Infinite)
    (hcircle : ¬ ∃ R : ℝ, 0 < R ∧ realLocus P = Metric.sphere (0 : ℂ) R)
    (hsign : rotate ζ P = P ∨ rotate ζ P = -P) :
    N ≤ max P.totalDegree (2 * P.totalDegree - 4) := by
  apply irreducible_rotation_bound hζ hirr hd _ hsign
  intro hradial
  exact hcircle (radial_realLocus_is_circle hinf hradial)

end CurveSymmetry
