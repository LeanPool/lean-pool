/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization

/-! Homogeneous interpolation on distinct projective points. The separating
polynomials have one common degree, so their classes belong to a single
graded coordinate space. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
variable {K : Type*} [Field K]

private lemma exists_projective_separating_minor {n : ℕ}
    {x y : Projectivization K (Fin (n + 1) → K)}
    (hxy : x ≠ y) :
    ∃ a b, y.rep b * x.rep a - y.rep a * x.rep b ≠ 0 := by
  by_contra! h
  obtain ⟨b, hb⟩ := Function.ne_iff.mp y.rep_nonzero
  change y.rep b ≠ 0 at hb
  apply hxy
  have he : x.rep = (x.rep b / y.rep b) • y.rep := by
    funext a
    have ha := sub_eq_zero.mp (h a b)
    change x.rep a = (x.rep b / y.rep b) * y.rep a
    apply (mul_left_cancel₀ hb)
    rw [ha]
    field_simp
  calc
    x = Projectivization.mk K x.rep x.rep_nonzero := x.mk_rep.symm
    _ = Projectivization.mk K y.rep y.rep_nonzero := by
      rw [Projectivization.mk_eq_mk_iff']
      exact ⟨_, he.symm⟩
    _ = y := y.mk_rep

private lemma exists_projective_linear_separator {n : ℕ}
    {x y : Projectivization K (Fin (n + 1) → K)}
    (hxy : x ≠ y) :
    ∃ f : MvPolynomial (Fin (n + 1)) K,
      f.IsHomogeneous 1 ∧ eval x.rep f = 1 ∧ eval y.rep f = 0 := by
  obtain ⟨a, b, hab⟩ := exists_projective_separating_minor hxy
  let D := y.rep b * x.rep a - y.rep a * x.rep b
  refine ⟨C D⁻¹ * (C (y.rep b) * X a - C (y.rep a) * X b), ?_, ?_, ?_⟩
  · exact ((isHomogeneous_C_mul_X _ _).sub (isHomogeneous_C_mul_X _ _)).C_mul _
  · simp only [eval_mul, eval_C, eval_sub, eval_X]
    exact inv_mul_cancel₀ hab
  · simp only [eval_mul, eval_C, eval_sub, eval_X]
    ring

/-- Homogeneous Lagrange separators in degree `card ι - 1`, with exact
Kronecker-delta values on the selected representatives. -/
private theorem exists_projective_point_separators {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (z : ι → Projectivization K (Fin (n + 1) → K))
    (hz : Function.Injective z) :
    ∃ h : ι → MvPolynomial (Fin (n + 1)) K,
      (∀ j, (h j).IsHomogeneous (Fintype.card ι - 1)) ∧
      ∀ i j, eval (z i).rep (h j) = if i = j then 1 else 0 := by
  classical
  have hex (i : ι) : ∃ f : MvPolynomial (Fin (n + 1)) K,
      f.IsHomogeneous (Fintype.card ι - 1) ∧ eval (z i).rep f = 1 ∧
      ∀ j, j ≠ i → eval (z j).rep f = 0 := by
    have hp (j : {j : ι // j ≠ i}) := exists_projective_linear_separator
      (show z i ≠ z j.val from fun he => j.property (hz he).symm)
    choose f hf hon hoff using hp
    refine ⟨∏ j, f j, ?_, ?_, ?_⟩
    · have hcard : Fintype.card {j : ι // j ≠ i} = Fintype.card ι - 1 := by
        simp [Fintype.card_subtype_compl]
      simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, hcard]
        using IsHomogeneous.prod (Finset.univ) f (fun _ => 1) (fun j _ => hf j)
    · rw [eval_prod]
      exact Finset.prod_eq_one (fun j _ => hon j)
    · intro j hji
      rw [eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ (⟨j, hji⟩ : {j : ι // j ≠ i}))
        (hoff ⟨j, hji⟩)
  choose h hhom hon hoff using hex
  refine ⟨h, hhom, ?_⟩
  intro i j
  by_cases hij : i = j
  · subst j
    simpa using hon i
  · simpa [hij] using hoff j i hij

/-- Separators can be raised to any larger common degree without changing
their values on the selected representatives. -/
theorem exists_projective_point_separators_degree {n M : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (z : ι → Projectivization K (Fin (n + 1) → K))
    (hz : Function.Injective z) (hM : Fintype.card ι - 1 ≤ M) :
    ∃ h : ι → MvPolynomial (Fin (n + 1)) K,
      (∀ j, (h j).IsHomogeneous M) ∧
      ∀ i j, eval (z i).rep (h j) = if i = j then 1 else 0 := by
  classical
  obtain ⟨h, hhom, heval⟩ := exists_projective_point_separators z hz
  have hcoord (j : ι) : ∃ k, (z j).rep k ≠ 0 :=
    Function.ne_iff.mp (z j).rep_nonzero
  choose k hk using hcoord
  let L (j : ι) := C ((z j).rep (k j))⁻¹ * X (k j)
  have hL (j : ι) : (L j).IsHomogeneous 1 := isHomogeneous_C_mul_X _ _
  refine ⟨fun j => h j * L j ^ (M - (Fintype.card ι - 1)), ?_, ?_⟩
  · intro j
    convert (hhom j).mul ((hL j).pow (M - (Fintype.card ι - 1))) using 1
    simp only [one_mul, Nat.add_sub_of_le hM]
  · intro i j
    rw [eval_mul, eval_pow, heval]
    by_cases hij : i = j
    · subst j
      simp [L, hk]
    · simp [hij]

end
end CCDN
