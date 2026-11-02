/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.ProjectiveSection
public import LeanPool.CCDN.Height.ProjectiveBox

/-! Finite affine fibers of a linear map exclude a projective base point.
Projective fibers inject into affine fibers after choosing a fixed
nonzero representative in the target. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- If the zeros of `I` in `ℚ^(n+1)` killed by the linear map `L` form a set of at most `M`
elements, then `L` does not vanish on the representative of any point of the projective zero
locus of `I`. -/
theorem projective_linear_image_ne_zero_of_finite_zero_fiber
    {n r : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
    (L : (Fin (n + 1) → ℚ) →ₗ[ℚ] (Fin r → ℚ)) (M : ℕ)
    (hfinite : ∀ s : Finset (Fin (n + 1) → ℚ),
      (∀ z ∈ s, z ∈ idealZeroLocus I) →
      (∀ z ∈ s, L z = 0) → s.card ≤ M)
    (x : ProjectivePoint n) (hx : x ∈ projectiveIdealZeroLocus I) :
    L x.rep ≠ 0 := by
  classical
  intro hzero
  let z : Fin (M + 1) → (Fin (n + 1) → ℚ) := fun j => (j.val + 1 : ℚ) • x.rep
  have hz (j : Fin (M + 1)) : z j ≠ 0 := by
    apply smul_ne_zero _ x.rep_nonzero
    positivity
  have hmk (j : Fin (M + 1)) : Projectivization.mk ℚ (z j) (hz j) = x := by
    rw [← x.mk_rep, Projectivization.mk_eq_mk_iff']
    exact ⟨(j.val + 1 : ℚ), rfl⟩
  have hinj : Function.Injective z := by
    intro i j hij
    have hh := smul_left_injective ℚ x.rep_nonzero hij
    apply Fin.ext
    exact_mod_cast (add_right_cancel hh)
  have hh := hfinite (Finset.univ.image z) (by
    intro w hw f hf
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw
    exact hx (z j) (hz j) (hmk j) f hf) (by
    intro w hw
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw
    simp only [z, map_smul, hzero, smul_zero])
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at hh
  omega

/-- Let `s` be a finite set of points of the projective zero locus of `I` on which the linear
map `L` is nonzero and which `L` sends to the single projective point `y`. If at most `M` zeros
of `I` in `ℚ^(n+1)` are sent by `L` to the representative of `y`, then `s` has at most `M`
elements. -/
theorem projective_linear_fiber_card_le
    {n m : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
    (L : (Fin (n + 1) → ℚ) →ₗ[ℚ] (Fin (m + 1) → ℚ))
    (s : Finset (ProjectivePoint n))
    (hs : ∀ x ∈ s, x ∈ projectiveIdealZeroLocus I)
    (hL : ∀ x ∈ s, L x.rep ≠ 0)
    (y : ProjectivePoint m)
    (he : ∀ (x) (hx : x ∈ s), Projectivization.mk ℚ (L x.rep) (hL x hx) = y)
    (M : ℕ)
    (hfinite : ∀ t : Finset (Fin (n + 1) → ℚ),
      (∀ z ∈ t, z ∈ idealZeroLocus I) →
      (∀ z ∈ t, L z = y.rep) → t.card ≤ M) :
    s.card ≤ M := by
  classical
  have hscale (x : s) : ∃ c : ℚˣ, c • y.rep = L x.val.rep := by
    exact (Projectivization.mk_eq_mk_iff ℚ _ _ _ _).mp
      ((he x.val x.property).trans y.mk_rep.symm)
  choose c hc using hscale
  let z : s → (Fin (n + 1) → ℚ) := fun x => (c x : ℚ)⁻¹ • x.val.rep
  have hz (x : s) : z x ≠ 0 := smul_ne_zero (inv_ne_zero (c x).ne_zero) x.val.rep_nonzero
  have hmk (x : s) : Projectivization.mk ℚ (z x) (hz x) = x.val := by
    rw [← x.val.mk_rep, Projectivization.mk_eq_mk_iff']
    exact ⟨(c x : ℚ)⁻¹, rfl⟩
  have himage (x : s) : L (z x) = y.rep := by
    dsimp only [z]
    rw [map_smul, ← hc x]
    change (c x : ℚ)⁻¹ • ((c x : ℚ) • y.rep) = y.rep
    rw [smul_smul, inv_mul_cancel₀ (c x).ne_zero, one_smul]
  have hinj : Function.Injective z := by
    intro x x' heq
    apply Subtype.ext
    rw [← hmk x, ← hmk x']
    exact (Projectivization.mk_eq_mk_iff' ℚ _ _ _ _).mpr ⟨1, by simpa using heq.symm⟩
  have hh := hfinite (Finset.univ.image z) (by
    intro w hw f hf
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hw
    exact hs x.val x.property (z x) (hz x) (hmk x) f hf) (by
    intro w hw
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hw
    exact himage x)
  simpa only [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe] using hh

end
end CCDN
