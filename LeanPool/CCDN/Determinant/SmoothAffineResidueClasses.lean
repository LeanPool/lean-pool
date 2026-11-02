/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Height.Box
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.ZMod.Basic
import LeanPool.CCDN.Determinant.PlaneMultiplicity
import LeanPool.CCDN.Plane.FiniteFieldPolynomialZeros

/-! Smooth affine residue classes and their simultaneous cardinality
bound. The elementary d*p^(ambient-1) bound suffices when the number of
chosen primes is absorbed by a small power of the box size. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- The nonsingular `𝔽_p`-points of the reduction modulo `p` of the affine hypersurface `f = 0`. -/
def SmoothAffineResidue {n : ℕ} (f : MvPolynomial (Fin n) ℤ) (p : ℕ) :=
  {a : Fin n → ZMod p //
    eval₂ (Int.castRingHom (ZMod p)) a f = 0 ∧
    ∃ j, eval a (pderiv j (map (Int.castRingHom (ZMod p)) f)) ≠ 0}

instance {n : ℕ} (f : MvPolynomial (Fin n) ℤ) (p : ℕ) [NeZero p] :
    Fintype (SmoothAffineResidue f p) := by
  classical
  unfold SmoothAffineResidue
  infer_instance

private theorem smoothAffineResidue_card_le {n p : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 1)) ℤ) :
    Fintype.card (SmoothAffineResidue f p) ≤ f.totalDegree * p ^ n := by
  classical
  let g := map (Int.castRingHom (ZMod p)) f
  by_cases hg : g = 0
  · have hempty : IsEmpty (SmoothAffineResidue f p) := by
      refine ⟨fun a => ?_⟩
      obtain ⟨j, hj⟩ := a.property.2
      change eval a.val (pderiv j g) ≠ 0 at hj
      simp only [hg, map_zero] at hj
      exact hj rfl
    let := hempty
    simp only [Fintype.card_of_isEmpty]
    omega
  · let φ : SmoothAffineResidue f p → {a : Fin (n + 1) → ZMod p // eval a g = 0} :=
      fun a => ⟨a.val, by simpa only [g, eval_map] using a.property.1⟩
    have hφ : Function.Injective φ := by
      intro a b h
      apply Subtype.ext
      exact congrArg (fun z : {a : Fin (n + 1) → ZMod p // eval a g = 0} => z.val) h
    have hcard := Fintype.card_le_of_injective φ hφ
    have hsz := finite_field_polynomial_zeros_mul_card g hg
    rw [Nat.card_eq_fintype_card, ZMod.card, Fintype.card_fin] at hsz
    have hdeg : g.totalDegree ≤ f.totalDegree := by
      change (map (Int.castRingHom (ZMod p)) f).totalDegree ≤ _
      rw [map_eq_eval₂Hom_C_comp]
      exact linear_eval₂_totalDegree_le _ X (fun j => le_of_eq (totalDegree_X j)) f
    have hbound := ((Nat.mul_le_mul_right p hcard).trans hsz).trans
      (Nat.mul_le_mul_right (p ^ (n + 1)) hdeg)
    rw [pow_succ, ← Nat.mul_assoc] at hbound
    exact le_of_mul_le_mul_right hbound (Fact.out : p.Prime).pos

/-- A choice, for each prime `p` in `P`, of a nonsingular `𝔽_p`-point of `f mod p`. -/
def SmoothAffineResidueFamily {n : ℕ} (f : MvPolynomial (Fin n) ℤ) (P : Finset ℕ) :=
  (p : P) → SmoothAffineResidue f p.val

/-- The number of families of nonsingular residue points of `f` modulo the primes in `P` is at most
`deg(f) ^ #P · (∏_{p ∈ P} p) ^ n`. -/
theorem smoothAffineResidueFamily_card_le {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    Nat.card (SmoothAffineResidueFamily f P) ≤
      f.totalDegree ^ P.card * (∏ p ∈ P, p) ^ n := by
  classical
  let (p : P) : Fact p.val.Prime := ⟨hP p.val p.property⟩
  let (p : P) : NeZero p.val := ⟨(hP p.val p.property).ne_zero⟩
  let : Fintype (SmoothAffineResidueFamily f P) := Pi.instFintype
  rw [Nat.card_eq_fintype_card]
  change Fintype.card ((p : P) → SmoothAffineResidue f p.val) ≤ _
  rw [Fintype.card_pi]
  calc
    _ ≤ ∏ p : P, f.totalDegree * p.val ^ n :=
      prod_le_prod (fun p _ => smoothAffineResidue_card_le f)
    _ = f.totalDegree ^ P.card * (∏ p : P, p.val) ^ n := by
      rw [prod_mul_distrib]
      simp only [prod_const, card_univ, Fintype.card_coe]
      rw [Finset.prod_pow]
    _ = _ := by rw [Finset.prod_coe_sort P (fun p : ℕ => p)]

/-- The integer lift, with coordinates in `[0, p)`, of the residue point modulo `p` chosen by the
family `r` (and `0` for `p ∉ P`). -/
def smoothResidueIntegerLift {n : ℕ} {f : MvPolynomial (Fin n) ℤ}
    {P : Finset ℕ} (r : SmoothAffineResidueFamily f P) : ℕ → IntPoint n :=
  fun p j => if hp : p ∈ P then ((r ⟨p, hp⟩).val j).val else 0

private lemma smoothResidueIntegerLift_cast {n : ℕ} {f : MvPolynomial (Fin n) ℤ}
    {P : Finset ℕ} (r : SmoothAffineResidueFamily f P) (p : P) [NeZero p.val] (j : Fin n) :
    (smoothResidueIntegerLift r p.val j : ZMod p.val) = (r p).val j := by
  simp only [smoothResidueIntegerLift, dite_eq_left p.property, Int.cast_natCast,
    ZMod.natCast_zmod_val]

/-- The reduction of `f` modulo `p ∈ P` vanishes at the lift of the residue point chosen by `r`. -/
theorem smoothResidueIntegerLift_zero {n : ℕ} {f : MvPolynomial (Fin n) ℤ}
    {P : Finset ℕ} (r : SmoothAffineResidueFamily f P) (p : ℕ) [NeZero p] (hp : p ∈ P) :
    eval₂ (Int.castRingHom (ZMod p)) (fun j => (smoothResidueIntegerLift r p j : ZMod p)) f =
      0 := by
  simpa only [smoothResidueIntegerLift_cast r ⟨p, hp⟩] using (r ⟨p, hp⟩).property.1

/-- The lift of the residue point chosen by `r` modulo `p ∈ P` is a nonsingular point of `f mod p`.
-/
theorem smoothResidueIntegerLift_smooth {n : ℕ} {f : MvPolynomial (Fin n) ℤ}
    {P : Finset ℕ} (r : SmoothAffineResidueFamily f P) (p : ℕ) [NeZero p] (hp : p ∈ P) :
    ∃ j, eval (fun i => (smoothResidueIntegerLift r p i : ZMod p))
      (pderiv j (map (Int.castRingHom (ZMod p)) f)) ≠ 0 := by
  simpa only [smoothResidueIntegerLift_cast r ⟨p, hp⟩] using (r ⟨p, hp⟩).property.2

/-- The family of residue points obtained by reducing an integer zero `x` of `f` modulo each prime
in `P` at which it is nonsingular. -/
def smoothResidueFamilyOfPoint {n : ℕ} {f : MvPolynomial (Fin n) ℤ}
    (x : IntPoint n) (hxf : eval x f = 0) (P : Finset ℕ)
    (hs : ∀ p ∈ P, ∃ j, eval (fun i => (x i : ZMod p))
      (pderiv j (map (Int.castRingHom (ZMod p)) f)) ≠ 0) :
    SmoothAffineResidueFamily f P := fun p =>
  ⟨fun j => (x j : ZMod p.val), by
    constructor
    · have h := congrArg (Int.castRingHom (ZMod p.val)) hxf
      rw [map_eval, map_zero, eval_map] at h
      exact h
    · exact hs p.val p.property⟩

/-- An integer zero `x` of `f` is congruent modulo each `p ∈ P` to the integer lift of its own
residue family. -/
theorem smoothResidueFamilyOfPoint_congruence {n : ℕ} {f : MvPolynomial (Fin n) ℤ}
    (x : IntPoint n) (hxf : eval x f = 0) (P : Finset ℕ)
    (hs : ∀ p ∈ P, ∃ j, eval (fun i => (x i : ZMod p))
      (pderiv j (map (Int.castRingHom (ZMod p)) f)) ≠ 0)
    (p : ℕ) [NeZero p] (hp : p ∈ P) (j : Fin n) :
    (p : ℤ) ∣ x j - smoothResidueIntegerLift (smoothResidueFamilyOfPoint x hxf P hs) p j := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  rw [Int.cast_sub, smoothResidueIntegerLift_cast _ ⟨p, hp⟩]
  exact sub_self _

end
end CCDN
