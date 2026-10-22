/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Height.ProjectiveBox
import LeanPool.CCDN.Algebra.BoundedRowSeparation
import LeanPool.CCDN.Height.ProjectiveIntegerHeight

/-! An explicit integral linear projection away from a bounded rational
linear center. Its kernel is exactly the span of the given independent
rows, and its coefficient bound is uniform in their entries. -/

@[expose] public section
namespace CCDN
noncomputable section
open Matrix

private lemma scalar_complement_projection_square {R ι κ : Type*} [CommRing R]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A L : Matrix ι κ R) (D : R)
    (hLA : L * A.transpose = D • (1 : Matrix ι ι R)) :
    (D • (1 : Matrix κ κ R) - A.transpose * L) *
        (D • (1 : Matrix κ κ R) - A.transpose * L) =
      D • (D • (1 : Matrix κ κ R) - A.transpose * L) := by
  have hPA : (D • (1 : Matrix κ κ R) - A.transpose * L) * A.transpose = 0 := by
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc,
      hLA, Matrix.mul_smul, Matrix.mul_one, sub_self]
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
    ← Matrix.mul_assoc, hPA, Matrix.zero_mul, sub_zero]

private lemma scalar_complement_projection_kernel {K ι κ : Type*} [Field K]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A L : Matrix ι κ K) (D : K) (hD : D ≠ 0)
    (hLA : L * A.transpose = D • (1 : Matrix ι ι K)) (x : κ → K) :
    (D • (1 : Matrix κ κ K) - A.transpose * L) *ᵥ x = 0 ↔
      x ∈ Submodule.span K (Set.range A.row) := by
  have hrange : Submodule.span K (Set.range A.row) =
      LinearMap.range A.transpose.mulVecLin := by
    rw [Matrix.range_mulVecLin]
    rfl
  rw [hrange]
  constructor
  · intro hx
    have he : D • x = A.transpose *ᵥ (L *ᵥ x) := by
      apply sub_eq_zero.mp
      simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        Matrix.mulVec_mulVec] using hx
    refine ⟨D⁻¹ • (L *ᵥ x), ?_⟩
    change A.transpose *ᵥ (D⁻¹ • (L *ᵥ x)) = x
    rw [Matrix.mulVec_smul, ← he, smul_smul, inv_mul_cancel₀ hD, one_smul]
  · rintro ⟨y, rfl⟩
    change (D • (1 : Matrix κ κ K) - A.transpose * L) *ᵥ (A.transpose *ᵥ y) = 0
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_mulVec, Matrix.mul_assoc, hLA, Matrix.mul_smul,
      Matrix.mul_one, Matrix.smul_mulVec, sub_self]

/-- Constructing the matrix requires only independent bounded integer rows.
In particular it is nonvanishing off their span. -/
theorem exists_bounded_integer_scaled_projection {s r : ℕ}
    (A : Matrix (Fin (s + 1)) (Fin r) ℤ)
    (hli : LinearIndependent ℚ (fun i => fun j => (A i j : ℚ)))
    (T : ℕ) (hA : ∀ i j, |A i j| ≤ (T : ℤ)) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ P : Matrix (Fin r) (Fin r) ℤ,
      (∀ i j, |P i j| ≤
        2 * ((s + 1).factorial : ℤ) * (T : ℤ) ^ (s + 1)) ∧
      P * P = D • P ∧
      ∀ x : Fin r → ℚ,
        (P.map (Int.castRingHom ℚ)) *ᵥ x = 0 ↔
          x ∈ Submodule.span ℚ (Set.range (fun i => fun j => (A i j : ℚ))) := by
  classical
  obtain ⟨D, hD, hDb, b, hb, hbb⟩ := exists_bounded_integer_dual_rows A hli T hA
  let L : Matrix (Fin (s + 1)) (Fin r) ℤ := Matrix.of b
  let P : Matrix (Fin r) (Fin r) ℤ := D • 1 - A.transpose * L
  let AQ := A.map (Int.castRingHom ℚ)
  let LQ := L.map (Int.castRingHom ℚ)
  have hLAZ : L * A.transpose = D • (1 : Matrix (Fin (s + 1)) (Fin (s + 1)) ℤ) := by
    ext i ℓ
    simpa only [L, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
      Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      mul_comm, eq_comm] using hb i ℓ
  have hDQ : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  have hLA : LQ * AQ.transpose = (D : ℚ) • (1 : Matrix (Fin (s + 1)) (Fin (s + 1)) ℚ) := by
    ext i ℓ
    have hh : (∑ j, (A ℓ j : ℚ) * (b i j : ℚ)) = if ℓ = i then (D : ℚ) else 0 := by
      exact_mod_cast hb i ℓ
    simpa only [LQ, AQ, L, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Int.coe_castRingHom, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero, mul_comm, eq_comm] using hh
  have hPmap : P.map (Int.castRingHom ℚ) =
      (D : ℚ) • (1 : Matrix (Fin r) (Fin r) ℚ) - AQ.transpose * LQ := by
    ext i j
    simp [P, AQ, LQ, Matrix.mul_apply, Matrix.one_apply, Matrix.intCast_apply]
  refine ⟨D, hD, P, ?_, scalar_complement_projection_square A L D hLAZ, ?_⟩
  · intro j k
    have hfirst : |D * (1 : Matrix (Fin r) (Fin r) ℤ) j k| ≤
        ((s + 1).factorial : ℤ) * (T : ℤ) ^ (s + 1) := by
      by_cases h : j = k
      · simpa only [Matrix.one_apply, ite_eq_left h, mul_one] using hDb
      · simp only [Matrix.one_apply, ite_eq_right h, mul_zero, abs_zero]
        positivity
    have hsum : |∑ i, A i j * b i k| ≤
        (s + 1 : ℕ) * ((T : ℤ) * ((s.factorial : ℤ) * (T : ℤ) ^ s)) := by
      calc
        _ ≤ ∑ i, |A i j * b i k| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin (s + 1), (T : ℤ) * ((s.factorial : ℤ) * (T : ℤ) ^ s) := by
          apply Finset.sum_le_sum
          intro i _
          rw [abs_mul]
          exact mul_le_mul (hA i j) (hbb i k) (abs_nonneg _) (Int.natCast_nonneg _)
        _ = _ := by simp
    change |D * (1 : Matrix (Fin r) (Fin r) ℤ) j k - ∑ i, A i j * b i k| ≤ _
    calc
      _ ≤ |D * (1 : Matrix (Fin r) (Fin r) ℤ) j k| + |∑ i, A i j * b i k| :=
        abs_sub _ _
      _ ≤ ((s + 1).factorial : ℤ) * (T : ℤ) ^ (s + 1) +
          (s + 1 : ℕ) * ((T : ℤ) * ((s.factorial : ℤ) * (T : ℤ) ^ s)) :=
        add_le_add hfirst hsum
      _ = _ := by rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]; ring
  · intro x
    rw [hPmap]
    exact scalar_complement_projection_kernel AQ LQ D hDQ hLA x

private theorem integer_linear_map_box_bound {m n : ℕ}
    (P : Matrix (Fin m) (Fin n) ℤ) {H B : ℝ} (hH : 0 ≤ H)
    (hP : ∀ i j, |(P i j : ℝ)| ≤ H)
    (z : IntPoint n) (hz : InBox z B) :
    ∀ i, |((P *ᵥ z) i : ℝ)| ≤ (n : ℝ) * H * B := by
  intro i
  simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul]
  calc
    _ ≤ ∑ j, |(P i j : ℝ) * (z j : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, H * B := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hP i j) (hz j) (abs_nonneg _) hH
    _ = _ := by simp [mul_assoc]

/-- An integer matrix with entries bounded by `H` maps an integer point of the box of radius
`B` to a projective point of multiplicative height at most `n H B` (when the image is nonzero),
since primitive reduction cannot enlarge an integral representative. -/
private theorem projective_integer_linear_map_height {m n : ℕ}
    (P : Matrix (Fin (m + 1)) (Fin n) ℤ) {H B : ℝ} (hH : 0 ≤ H)
    (hP : ∀ i j, |(P i j : ℝ)| ≤ H)
    (z : IntPoint n) (hz : InBox z B) (himage : P *ᵥ z ≠ 0) :
    (Projectivization.mk ℚ (rationalPoint (P *ᵥ z))
      (rationalPoint_ne_zero himage)).mulHeight ≤ (n : ℝ) * H * B :=
  projective_integer_height_le _ himage (integer_linear_map_box_bound P hH hP z hz)

private lemma rationalPoint_integer_mulVec {m n : ℕ}
    (P : Matrix (Fin m) (Fin n) ℤ) (z : IntPoint n) :
    rationalPoint (P *ᵥ z) =
      (P.map (Int.castRingHom ℚ)) *ᵥ rationalPoint z := by
  funext i
  simp [rationalPoint, Matrix.mulVec, dotProduct]

/-- The height estimate for the projective linear image of any
point outside the matrix kernel. The input height is its intrinsic
multiplicative projective height. -/
theorem projective_linear_map_height {m n : ℕ}
    (P : Matrix (Fin (m + 1)) (Fin (n + 1)) ℤ)
    {H : ℝ} (hH : 0 ≤ H) (hP : ∀ i j, |(P i j : ℝ)| ≤ H)
    (x : ProjectivePoint n)
    (himage : (P.map (Int.castRingHom ℚ)) *ᵥ x.rep ≠ 0) :
    (Projectivization.mk ℚ ((P.map (Int.castRingHom ℚ)) *ᵥ x.rep) himage).mulHeight ≤
      (n + 1 : ℕ) * H * x.mulHeight := by
  let z := primitiveProjectiveRep x
  let w := P *ᵥ z
  have hrep := (primitiveProjectiveRep_mk x).trans x.mk_rep.symm
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℚ _ _ _ _).mp hrep
  have hw : rationalPoint w =
      (c : ℚ) • ((P.map (Int.castRingHom ℚ)) *ᵥ x.rep) := by
    rw [rationalPoint_integer_mulVec]
    change (P.map (Int.castRingHom ℚ)) *ᵥ rationalPoint (primitiveProjectiveRep x) = _
    rw [← hc, Matrix.mulVec_smul]
    rfl
  have hw0 : w ≠ 0 := by
    intro hz
    have hzero : (c : ℚ) • ((P.map (Int.castRingHom ℚ)) *ᵥ x.rep) = 0 := by
      rw [← hw, hz]
      rfl
    exact himage ((smul_eq_zero.mp hzero).resolve_left c.ne_zero)
  have hproj :
      Projectivization.mk ℚ (rationalPoint w) (rationalPoint_ne_zero hw0) =
        Projectivization.mk ℚ ((P.map (Int.castRingHom ℚ)) *ᵥ x.rep) himage := by
    apply (Projectivization.mk_eq_mk_iff' ℚ _ _ _ _).mpr
    exact ⟨c, hw.symm⟩
  rw [← hproj]
  exact projective_integer_linear_map_height P hH hP z
    (primitiveProjectiveRep_bound x) hw0

end
end CCDN
