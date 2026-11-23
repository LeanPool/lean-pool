/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.C19Geometry
public import Mathlib.Analysis.Complex.Trigonometric

/-! # Plane waves for the C19 lattice -/

@[expose] public section

namespace LeanDirac.V2

noncomputable section
open BigOperators Complex

/-- The three real Fourier coordinates of a mode of the cubic lattice. -/
abbrev LatticeMomentum := Fin 3 → ℝ

/-- A site in the infinite simple cubic lattice, indexed by three integers. -/
abbrev InfiniteCubicSite := Fin 3 → ℤ

/-- Translate a lattice site by the given face or edge offset. -/
def infiniteC19Neighbor (site : InfiniteCubicSite)
    (direction : C19Neighbor) : InfiniteCubicSite :=
  fun axis => site axis + c19Coord axis direction

/-- The oriented weighted bond associated with a C19 offset at a site. -/
def infiniteC19Bond (site : InfiniteCubicSite)
    (direction : C19Neighbor) : Bond InfiniteCubicSite where
  source := site
  target := infiniteC19Neighbor site direction
  weight := c19Weight direction

/-- The momentum paired with an integer lattice site before taking the complex exponential. -/
def latticePhase (momentum : LatticeMomentum)
    (site : InfiniteCubicSite) : ℝ :=
  ∑ axis, momentum axis * (site axis : ℝ)

/-- The phase increment between the source and target of an oriented C19 bond. -/
def c19PhaseAngle (momentum : LatticeMomentum)
    (direction : C19Neighbor) : ℝ :=
  ∑ axis, momentum axis * (c19Coord axis direction : ℝ)

/-- The unit complex multiplier for translation by one C19 offset. -/
def c19Character (momentum : LatticeMomentum)
    (direction : C19Neighbor) : ℂ :=
  Complex.exp (I * (c19PhaseAngle momentum direction : ℂ))

/-- The plane wave with the given real lattice momentum. -/
def cubicLatticeCharacter (momentum : LatticeMomentum)
    (site : InfiniteCubicSite) : ℂ :=
  Complex.exp (I * (latticePhase momentum site : ℂ))

theorem lattice_phase_neighbor (momentum : LatticeMomentum)
    (site : InfiniteCubicSite) (direction : C19Neighbor) :
    latticePhase momentum (infiniteC19Neighbor site direction) =
      latticePhase momentum site + c19PhaseAngle momentum direction := by
  unfold latticePhase infiniteC19Neighbor c19PhaseAngle
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro axis _
  push_cast
  ring

theorem cubic_character_neighbor (momentum : LatticeMomentum)
    (site : InfiniteCubicSite) (direction : C19Neighbor) :
    cubicLatticeCharacter momentum (infiniteC19Neighbor site direction) =
      cubicLatticeCharacter momentum site * c19Character momentum direction := by
  unfold cubicLatticeCharacter c19Character
  rw [lattice_phase_neighbor]
  push_cast
  rw [mul_add, Complex.exp_add]

theorem cubic_character_normSq_one (momentum : LatticeMomentum)
    (site : InfiniteCubicSite) :
    Complex.normSq (cubicLatticeCharacter momentum site) = 1 := by
  rw [Complex.normSq_eq_norm_sq]
  simp [cubicLatticeCharacter, Complex.norm_exp_I_mul_ofReal]

end
end LeanDirac.V2
