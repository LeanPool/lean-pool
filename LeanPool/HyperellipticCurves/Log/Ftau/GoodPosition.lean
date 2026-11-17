/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Disks.CurvePoint
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Coprime.Basic

import LeanPool.HyperellipticCurves.ForMathlib.Polynomial

/-!
# Good position and abundance of residue points (blueprint `def:goodpos`, `lem:many-points`)

`ChabautyColeman.GoodPosition f u` collects the Zariski-open ("resultant-unit") conditions
on (the reduction of) the `u`-polynomial of a Mumford datum on `y² = f(x)` under which the
disk chart and the translated formal group law of chapter `03-log` are well-behaved:
full degree `g`, squarefree, and coprime to `f`. The coprimality conditions on the
`v`-polynomial needed downstream are *consequences* (`GoodPosition.isCoprime_right`,
`GoodPosition.isCoprime_two_mul_right` — the latter is the Jacobian-unit condition of the
disk chart `def:chart`), so they are not part of the definition.

`ChabautyColeman.residue_curve_points_infinite` (`lem:many-points`) provides the supply of
residue points from which data in good position will be chosen (`lem:tau-exists`): over an
algebraically closed field, the affine curve `y² = f_bar(x)` has infinitely many
non-Weierstrass points; excluding the finitely many points hitting a given finite list of
bad loci is then `Set.Infinite.diff`.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

section GoodPosition

variable {R : Type*} [CommRing R] (f u : R[X])

/-- **Good position** (blueprint `def:goodpos`): the Zariski-open conditions on (the
reduction of) the `u`-polynomial of a Mumford datum on `y² = f(x)` making the disk chart
and the translated formal group law well-behaved: `u` has full degree `g`, is squarefree,
and is coprime to `f` (the divisor avoids the Weierstrass points). The conditions only
involve `u`; the coprimality conditions on `v` needed downstream are consequences
(`GoodPosition.isCoprime_right`). -/
structure GoodPosition : Prop where
  /-- The support has full degree `g`. -/
  natDegree_eq : u.natDegree = genus f
  /-- The support is squarefree: the divisor has `g` distinct points. -/
  squarefree : Squarefree u
  /-- The support avoids the Weierstrass points. -/
  isCoprime : IsCoprime u f

variable {f u}

namespace GoodPosition

theorem ne_zero [Nontrivial R] (hp : GoodPosition f u) : u ≠ 0 := hp.squarefree.ne_zero

/-- In good position, `u` is coprime to any `v` with `u ∣ v² - f`: a Mumford datum whose
`u`-polynomial is in good position has coprime components. -/
theorem isCoprime_right {v : R[X]} (hp : GoodPosition f u) (hdvd : u ∣ v ^ 2 - f) :
    IsCoprime u v := by
  obtain ⟨a, b, hab⟩ := hp.isCoprime
  obtain ⟨w, hw⟩ := hdvd
  exact ⟨a - b * w, b * v, by linear_combination hab + b * hw⟩

/-- In good position over a field of characteristic `≠ 2`, `2v` is invertible modulo `u` —
the Jacobian-unit condition of the disk chart (`def:chart`). -/
theorem isCoprime_two_mul_right {κ : Type*} [Field κ] [NeZero (2 : κ)] {f u v : κ[X]}
    (hp : GoodPosition f u) (hdvd : u ∣ v ^ 2 - f) : IsCoprime u (2 * v) := by
  obtain ⟨a, b, hab⟩ := hp.isCoprime_right hdvd
  have h21 : (C ((2 : κ)⁻¹) * 2 : κ[X]) = 1 := by
    rw [← map_ofNat (C : κ →+* κ[X]) 2, ← C_mul, inv_mul_cancel₀ (NeZero.ne (2 : κ)), C_1]
  exact ⟨a, C ((2 : κ)⁻¹) * b, by linear_combination hab + b * v * h21⟩

end GoodPosition

end GoodPosition

section ManyPoints

theorem infinite_setOf_eval_ne_zero {R : Type*} [CommRing R] [IsDomain R] [Infinite R]
    {f : R[X]} (hf : f ≠ 0) : {a : R | f.eval a ≠ 0}.Infinite := by
  simpa [Set.compl_ofPred, Polynomial.IsRoot] using
    (Polynomial.finite_setOfPred_isRoot hf).infinite_compl

/-- **Plenty of points** (blueprint `lem:many-points`): over an algebraically closed field,
the affine curve `y² = f(x)` has infinitely many non-Weierstrass points. Combined with
`Set.Infinite.diff`, points avoiding any finite list of bad loci exist. -/
theorem residue_curve_points_infinite {κ : Type*} [Field κ] [IsAlgClosed κ] {f : κ[X]}
    (hf : f ≠ 0) : {z : κ × κ | z.2 ^ 2 = f.eval z.1 ∧ z.2 ≠ 0}.Infinite := by
  have hx := infinite_setOf_eval_ne_zero hf
  set b : κ → κ := fun a ↦ (IsAlgClosed.exists_pow_nat_eq (f.eval a) two_pos).choose
  have hsq a : b a ^ 2 = f.eval a :=
    (IsAlgClosed.exists_pow_nat_eq (f.eval a) two_pos).choose_spec
  have himg : (fun a ↦ (a, b a)) '' {a : κ | f.eval a ≠ 0}
      ⊆ {z : κ × κ | z.2 ^ 2 = f.eval z.1 ∧ z.2 ≠ 0} := by
    rintro z ⟨a, ha, rfl⟩
    dsimp only
    exact ⟨hsq a, fun h0 ↦ ha (by rw [← hsq a, show b a = 0 from h0]; ring)⟩
  exact (hx.image fun a _ a' _ h ↦ congrArg Prod.fst h).mono himg

/-- **The avoidance engine** for genericity arguments on the curve: a nonzero function
`g₀ + g₁·y` on the affine curve `y² = f(x)` (`f` monic of odd degree) vanishes at only
finitely many points — its norm `g₀² - f·g₁²` is a nonzero polynomial by degree parity,
and zeros lie over its roots. -/
theorem finite_curve_zeros {κ : Type*} [Field κ] {f g₀ g₁ : κ[X]} (hf : f.Monic)
    (hodd : Odd f.natDegree) (hg : g₀ ≠ 0 ∨ g₁ ≠ 0) :
    {p : κ × κ | p.2 ^ 2 = f.eval p.1
      ∧ g₀.eval p.1 + g₁.eval p.1 * p.2 = 0}.Finite := by
  classical
  -- the norm is nonzero by degree parity
  have hN : g₀ ^ 2 - f * g₁ ^ 2 ≠ 0 := by
    rcases eq_or_ne g₀ 0 with rfl | hg₀
    · simpa [hf.ne_zero] using pow_ne_zero 2 (hg.resolve_left (by simp))
    · exact fun h0 ↦ sq_mul_ne_sq_of_odd_natDegree (A := g₁) hf.ne_zero hodd hg₀
        (by linear_combination -h0)
  -- zeros lie over the finitely many roots of the norm
  refine Set.Finite.subset (Set.Finite.biUnion
    ((g₀ ^ 2 - f * g₁ ^ 2).roots.toFinset.finite_toSet)
    (fun a _ ↦ Set.Finite.image (fun b ↦ (a, b))
      (finite_setOfPred_isRoot (X_pow_sub_C_ne_zero two_pos (f.eval a))))) ?_
  intro ⟨a, b⟩ ⟨hb, hE⟩
  have ha : a ∈ (↑(g₀ ^ 2 - f * g₁ ^ 2).roots.toFinset : Set κ) := by
    refine Multiset.mem_toFinset.mpr (mem_roots'.mpr ⟨hN, ?_⟩)
    change (g₀ ^ 2 - f * g₁ ^ 2).eval a = 0
    simp only [eval_sub, eval_pow, eval_mul]
    linear_combination (g₀.eval a - g₁.eval a * b) * hE + (g₁.eval a) ^ 2 * hb
  exact Set.mem_biUnion ha ⟨b, by simp [IsRoot, hb], rfl⟩

end ManyPoints

end ChabautyColeman

end
