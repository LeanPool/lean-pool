/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.RupertMinimality.MainTheorem

/-! # Similarity -/

@[expose] public section

namespace RupertMinimality

/-!
# Similarities preserve Rupert-ness

Nonzero scalings (`isRupert_image_smul`), translations (`isRupert_image_add`),
rotations (`isRupert_image_rotation`) and so every similarity
(`isRupert_image_similarity`) map Rupert vertex sets to Rupert vertex sets.
This module depends only on `MainTheorem` and Mathlib, so that both the
certificate pipeline and the minimality proof can use it.
-/

namespace Noperts.Pipeline

open scoped Matrix

theorem proj_xy_smul (t : ℝ) (v : EuclideanSpace ℝ (Fin 3)) : projXy (t • v) = t • projXy v := by
  ext i; fin_cases i <;> simp [projXy]

theorem proj_xy_add (u v : EuclideanSpace ℝ (Fin 3)) : projXy (u + v) = projXy u + projXy v := by
  ext i; fin_cases i <;> simp [projXy]

/-- Rupert-ness is invariant under a nonzero scaling (a negative one is a
point reflection). -/
theorem isRupert_image_smul (t : ℝ) (ht : t ≠ 0)
    (V : Finset (EuclideanSpace ℝ (Fin 3))) (h : IsRupert V) :
    IsRupert (V.image fun x => t • x) := by
  obtain ⟨R1, hR1, off, R2, hR2, hsub⟩ := h
  refine ⟨R1, hR1, t • off, R2, hR2, ?_⟩
  dsimp only at hsub ⊢
  have hhull : convexHull ℝ (↑(V.image fun x => t • x) : Set (EuclideanSpace ℝ (Fin 3))) =
      (fun x => t • x) '' convexHull ℝ ↑V := by
    rw [Finset.coe_image]
    have := LinearMap.image_convexHull (t • (LinearMap.id : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] _))
      (↑V : Set (EuclideanSpace ℝ (Fin 3)))
    simpa using this.symm
  let e : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2) := Homeomorph.smulOfNeZero t ht
  have himg : ∀ (o : EuclideanSpace ℝ (Fin 2)) (R : Matrix (Fin 3) (Fin 3) ℝ),
      { x | ∃ p ∈ convexHull ℝ (↑(V.image fun x => t • x) : Set (EuclideanSpace ℝ (Fin 3))),
          t • o + projXy (R.toEuclideanLin p) = x } =
        e '' { x | ∃ p ∈ convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin 3))),
          o + projXy (R.toEuclideanLin p) = x } := by
    intro o R
    rw [hhull]
    ext y
    constructor
    · rintro ⟨p, ⟨q, hq, rfl⟩, rfl⟩
      refine ⟨o + projXy (R.toEuclideanLin q), ⟨q, hq, rfl⟩, ?_⟩
      simp [e, Homeomorph.smulOfNeZero, map_smul, proj_xy_smul, smul_add]
    · rintro ⟨x, ⟨q, hq, rfl⟩, rfl⟩
      refine ⟨t • q, ⟨q, hq, rfl⟩, ?_⟩
      simp [e, Homeomorph.smulOfNeZero, map_smul, proj_xy_smul, smul_add]
  have h1 := himg off R1
  have h2 := himg 0 R2
  simp only [smul_zero, zero_add] at h2
  rw [h1, h2, ← e.image_interior]
  exact Set.image_mono hsub

/-- Rupert-ness is invariant under translation. -/
theorem isRupert_image_add (c : EuclideanSpace ℝ (Fin 3))
    (V : Finset (EuclideanSpace ℝ (Fin 3))) (h : IsRupert V) :
    IsRupert (V.image fun x => c + x) := by
  obtain ⟨R1, hR1, off, R2, hR2, hsub⟩ := h
  let d := projXy (R2.toEuclideanLin c)
  refine ⟨R1, hR1, off + d - projXy (R1.toEuclideanLin c), R2, hR2, ?_⟩
  dsimp only at hsub ⊢
  have hhull : convexHull ℝ (↑(V.image fun x => c + x) : Set (EuclideanSpace ℝ (Fin 3))) =
      (fun x => c + x) '' convexHull ℝ ↑V := by
    rw [Finset.coe_image]
    have := AffineMap.image_convexHull
      (AffineEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin 3)) c).toAffineMap
      (↑V : Set (EuclideanSpace ℝ (Fin 3)))
    simpa [vadd_eq_add] using this.symm
  let e : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2) := Homeomorph.addRight d
  have himg : ∀ (o o' : EuclideanSpace ℝ (Fin 2)) (R : Matrix (Fin 3) (Fin 3) ℝ),
      o' = o + d - projXy (R.toEuclideanLin c) →
      { x | ∃ p ∈ convexHull ℝ (↑(V.image fun x => c + x) : Set (EuclideanSpace ℝ (Fin 3))),
          o' + projXy (R.toEuclideanLin p) = x } =
        e '' { x | ∃ p ∈ convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin 3))),
          o + projXy (R.toEuclideanLin p) = x } := by
    intro o o' R ho
    rw [hhull]
    ext y
    constructor
    · rintro ⟨p, ⟨q, hq, rfl⟩, rfl⟩
      refine ⟨o + projXy (R.toEuclideanLin q), ⟨q, hq, rfl⟩, ?_⟩
      simp only [e, Homeomorph.coe_addRight, ho, map_add, proj_xy_add]
      abel
    · rintro ⟨x, ⟨q, hq, rfl⟩, rfl⟩
      refine ⟨c + q, ⟨q, hq, rfl⟩, ?_⟩
      simp only [e, Homeomorph.coe_addRight, ho, map_add, proj_xy_add]
      abel
  have h1 := himg off _ R1 rfl
  have h2 := himg 0 0 R2 (by simp [d])
  simp only [zero_add] at h2
  rw [h1, h2, ← e.image_interior]
  exact Set.image_mono hsub
/-- Rupert-ness is invariant under rotating the vertex set. -/
theorem isRupert_image_rotation (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ : Q ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (V : Finset (EuclideanSpace ℝ (Fin 3))) (h : IsRupert V) :
    IsRupert (V.image Q.toEuclideanLin) := by
  obtain ⟨R1, hR1, off, R2, hR2, hsub⟩ := h
  have hQt : Qᵀ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
    have := (Matrix.mem_specialOrthogonalGroup_iff).mp hQ
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    exact ⟨by simpa using (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp this.1,
      by simpa using this.2⟩
  have hQtQ : Qᵀ * Q = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hQ.1
  have hhull : convexHull ℝ (↑(V.image Q.toEuclideanLin) : Set (EuclideanSpace ℝ (Fin 3))) =
      Q.toEuclideanLin '' convexHull ℝ ↑V := by
    rw [Finset.coe_image, LinearMap.image_convexHull]
  have hback : ∀ (R : Matrix (Fin 3) (Fin 3) ℝ) (p : EuclideanSpace ℝ (Fin 3)),
      (R * Qᵀ).toEuclideanLin (Q.toEuclideanLin p) = R.toEuclideanLin p := by
    intro R p
    simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec, hQtQ]
  have hset : ∀ (R : Matrix (Fin 3) (Fin 3) ℝ) (o : EuclideanSpace ℝ (Fin 2)),
      { x | ∃ p ∈ convexHull ℝ (↑(V.image Q.toEuclideanLin) : Set (EuclideanSpace ℝ (Fin 3))),
          o + projXy ((R * Qᵀ).toEuclideanLin p) = x } =
        { x | ∃ p ∈ convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin 3))),
          o + projXy (R.toEuclideanLin p) = x } := by
    intro R o
    rw [hhull]
    ext y
    constructor
    · rintro ⟨p, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨q, hq, by rw [hback]⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨Q.toEuclideanLin q, ⟨q, hq, rfl⟩, by rw [hback]⟩
  refine ⟨R1 * Qᵀ, Submonoid.mul_mem _ hR1 hQt, off, R2 * Qᵀ,
    Submonoid.mul_mem _ hR2 hQt, ?_⟩
  dsimp only at hsub ⊢
  have h2 := hset R2 0
  simp only [zero_add] at h2
  rw [hset R1 off, h2]
  exact hsub

/-- Rupert-ness is invariant under every similarity x ↦ c + s M x (s > 0, M
orthogonal, including reflections). -/
theorem isRupert_image_similarity (c : EuclideanSpace ℝ (Fin 3)) (s : ℝ) (hs : 0 < s)
    (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (V : Finset (EuclideanSpace ℝ (Fin 3))) (h : IsRupert V) :
    IsRupert (V.image fun x => c + s • M.toEuclideanLin x) := by
  have hdet : M.det = 1 ∨ M.det = -1 := by
    have hMM : Mᵀ * M = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hM
    have := congrArg Matrix.det hMM
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
    rcases mul_self_eq_one_iff.mp this with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  -- M = σ Q with Q a rotation and σ = ±1; then x ↦ c + (σ s) Q x.
  obtain ⟨Q, hQ, σ, hσ, hMQ⟩ : ∃ Q ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∃ σ : ℝ,
      σ ≠ 0 ∧ ∀ x, M.toEuclideanLin x = σ • Q.toEuclideanLin x := by
    rcases hdet with h1 | h1
    · exact ⟨M, Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨hM, h1⟩, 1, one_ne_zero,
        fun x => by simp⟩
    · refine ⟨-M, Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨?_, ?_⟩, -1, by norm_num,
        fun x => by simp [Matrix.toLpLin_apply]⟩
      · rw [Matrix.mem_orthogonalGroup_iff']
        simpa using (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hM
      · rw [Matrix.det_neg]
        simp [h1]; norm_num
  have h1 := isRupert_image_rotation Q hQ V h
  have h2 := isRupert_image_smul (σ * s) (mul_ne_zero hσ hs.ne') _ h1
  have h3 := isRupert_image_add c _ h2
  convert h3 using 1
  simp only [Finset.image_image]
  congr 1
  funext x
  simp [hMQ, smul_smul, mul_comm]

end Noperts.Pipeline

end RupertMinimality
