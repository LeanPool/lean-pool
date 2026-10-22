/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Determinant.SmoothAffineResidueClasses
public import LeanPool.CCDN.Surface.CongruenceCutoff

/-! A coherent choice of proper auxiliaries for every finite
smooth residue family. The structure stores conclusions of the determinant
theorem; its existence is proved from the equation. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- The restriction of a family of smooth residues, indexed by the primes of `P`, to a subset
`Q ⊆ P`. -/
def SmoothAffineResidueFamily.restrict {n : ℕ} {f : MvPolynomial (Fin n) ℤ}
    {P Q : Finset ℕ} (r : SmoothAffineResidueFamily f P) (hQP : Q ⊆ P) :
    SmoothAffineResidueFamily f Q := fun q => r ⟨q.val, hQP q.property⟩

/-- The unique family of smooth residues indexed by the empty set of primes. -/
def emptySmoothAffineResidueFamily {n : ℕ} (f : MvPolynomial (Fin n) ℤ) :
    SmoothAffineResidueFamily f ∅ := fun p => False.elim (notMem_empty p.val p.property)

/-- A choice, for every finite set `P` of primes and every family `r` of smooth residues of `f`
modulo the primes of `P`, of a nonzero integer polynomial that is not divisible by `f` over `ℚ`,
has degree at most `A (B^(1/√d) / ∏ p + 1)(1 + log B + ∑ log p)` (with `d` the degree of `f`
and `p` ranging over `P`) and vanishes at every integer zero of `f` in the box of radius `B`
lying in the residue classes `r`. -/
structure SurfaceCongruenceFamily (f : MvPolynomial (Fin 3) ℤ) (B A : ℝ) where
  /-- The auxiliary polynomial attached to a set `P` of primes and smooth residues modulo
  `P`. -/
  auxiliary : (P : Finset ℕ) → (∀ p ∈ P, p.Prime) →
    SmoothAffineResidueFamily f P → MvPolynomial (Fin 3) ℤ
  /-- Every auxiliary is nonzero. -/
  nonzero : ∀ P hP r, auxiliary P hP r ≠ 0
  /-- No auxiliary is divisible by `f` over `ℚ`. -/
  proper : ∀ P hP r, ¬ map (Int.castRingHom ℚ) f ∣
    map (Int.castRingHom ℚ) (auxiliary P hP r)
  /-- The degree of the auxiliary attached to `P` is at most
  `A (B^(1/√d) / ∏ p + 1)(1 + log B + ∑ log p)`. -/
  degree_le : ∀ P hP r, ((auxiliary P hP r).totalDegree : ℝ) ≤
    A * (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) /
      Real.exp (∑ p ∈ P, Real.log p) + 1) * (1 + Real.log B + ∑ p ∈ P, Real.log p)
  /-- The auxiliary attached to `P` and `r` vanishes at the integer zeros of `f` in the box
  that lie in the residue classes `r`. -/
  vanishes : ∀ P hP r x, x ∈ affineCongruencePoints f B P (smoothResidueIntegerLift r) →
    eval x (auxiliary P hP r) = 0

/-- An absolutely irreducible integer surface equation `f` of positive degree, whose
coefficient height `H` satisfies `log H ≤ K (log B + 1)`, admits a congruence family of
auxiliaries with degree constant `surfaceCongruenceDegreeConstant d K`, where `d` is the degree
of `f`. -/
theorem exists_surface_congruence_family
    (f : MvPolynomial (Fin 3) ℤ)
    (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree) {K H B : ℝ} (hK : 0 ≤ K) (hH : 1 ≤ H) (hB : 1 ≤ B)
    (hcoeff : CoefficientHeightLE f H)
    (hheight : Real.log H ≤ K * (Real.log B + 1)) :
    Nonempty (SurfaceCongruenceFamily f B (surfaceCongruenceDegreeConstant f.totalDegree K)) := by
  classical
  have hex (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (r : SmoothAffineResidueFamily f P) :=
    exists_surface_congruence_auxiliary f hir hd hK hH hB hcoeff hheight P hP
      (smoothResidueIntegerLift r)
      (fun p hp => by
        let : NeZero p := ⟨(hP p hp).ne_zero⟩
        exact smoothResidueIntegerLift_zero r p hp)
      (fun p hp => by
        let : NeZero p := ⟨(hP p hp).ne_zero⟩
        exact smoothResidueIntegerLift_smooth r p hp)
  choose g hg0 hgproper hgdegree hgzero using hex
  exact ⟨⟨g, hg0, hgproper, hgdegree, hgzero⟩⟩

/-- The auxiliary polynomial of a congruence family attached to the empty set of primes: it
vanishes at every integer zero of `f` in the box. -/
def SurfaceCongruenceFamily.initial {f : MvPolynomial (Fin 3) ℤ} {B A : ℝ}
    (F : SurfaceCongruenceFamily f B A) : MvPolynomial (Fin 3) ℤ :=
  F.auxiliary ∅ (by simp) (emptySmoothAffineResidueFamily f)

/-- The auxiliary attached to the empty set of primes is `F.initial`, whatever the (unique)
residue family and primality proof. -/
lemma SurfaceCongruenceFamily.initial_eq {f : MvPolynomial (Fin 3) ℤ} {B A : ℝ}
    (F : SurfaceCongruenceFamily f B A) (r : SmoothAffineResidueFamily f ∅)
    (hP : ∀ p ∈ (∅ : Finset ℕ), p.Prime) :
    F.auxiliary ∅ hP r = F.initial := by
  have he : r = emptySmoothAffineResidueFamily f := by
    funext p
    exact False.elim (notMem_empty p.val p.property)
  rw [he]
  rfl

/-- The initial auxiliary `F.initial` vanishes at every integer zero of `f` in the box of
radius `B`. -/
lemma SurfaceCongruenceFamily.initial_vanishes {f : MvPolynomial (Fin 3) ℤ} {B A : ℝ}
    (F : SurfaceCongruenceFamily f B A) (x : IntPoint 3)
    (hx : InBox x B) (hxf : eval x f = 0) :
    eval x F.initial = 0 :=
  F.vanishes ∅ (by simp) (emptySmoothAffineResidueFamily f) x
    (mem_affineCongruencePoints.mpr ⟨hx, hxf, by simp⟩)

/-- If an integer zero `x` of `f` in the box is a smooth point of `f` modulo every prime of `P`,
then the auxiliary attached to `P` and to the residues of `x` vanishes at `x`. -/
lemma SurfaceCongruenceFamily.point_vanishes {f : MvPolynomial (Fin 3) ℤ} {B A : ℝ}
    (F : SurfaceCongruenceFamily f B A) (x : IntPoint 3)
    (hx : InBox x B) (hxf : eval x f = 0)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hs : ∀ p ∈ P, ∃ j, eval (fun i => (x i : ZMod p))
      (pderiv j (map (Int.castRingHom (ZMod p)) f)) ≠ 0) :
    eval x (F.auxiliary P hP (smoothResidueFamilyOfPoint x hxf P hs)) = 0 := by
  apply F.vanishes
  apply mem_affineCongruencePoints.mpr
  refine ⟨hx, hxf, ?_⟩
  intro p hp j
  let : NeZero p := ⟨(hP p hp).ne_zero⟩
  exact smoothResidueFamilyOfPoint_congruence x hxf P hs p hp j

end
end CCDN
