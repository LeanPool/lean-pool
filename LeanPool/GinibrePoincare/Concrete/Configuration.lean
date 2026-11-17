/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Concrete/Configuration.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Configuration space and particle permutations

The configuration space of `n` planar particles is `Fin n → ℂ`.  This file
defines particle relabelling, symmetric and alternating observables, and the
collision locus.  It contains no measure-theoretic or analytic input.
-/


@[expose] public section


namespace GinibrePoincare

/-- The configuration space of `n` labelled particles in the complex plane. -/
abbrev Configuration (n : ℕ) := Fin n → ℂ

/-- The symmetric group acting on `n` labelled particles. -/
abbrev ParticlePermutation (n : ℕ) := Equiv.Perm (Fin n)

/-- Relabelling of a configuration by a permutation. -/
def permute {n : ℕ} (σ : ParticlePermutation n) (z : Configuration n) :
    Configuration n :=
  fun i => z (σ i)

@[simp]
theorem permute_apply {n : ℕ} (σ : ParticlePermutation n)
    (z : Configuration n) (i : Fin n) :
    permute σ z i = z (σ i) :=
  rfl

@[simp]
theorem permute_refl {n : ℕ} (z : Configuration n) :
    permute (Equiv.refl (Fin n)) z = z := by
  rfl

/-- A scalar-valued observable invariant under every particle relabelling. -/
def IsSymmetric {n : ℕ} {α : Type*} (f : Configuration n → α) : Prop :=
  ∀ (σ : ParticlePermutation n) (z : Configuration n),
    f (permute σ z) = f z

/-- The complex scalar corresponding to the sign of a permutation. -/
def permutationSign {n : ℕ} (σ : ParticlePermutation n) : ℂ :=
  ((↑(Equiv.Perm.sign σ) : ℤ) : ℂ)

/-- A complex-valued observable transforming according to the sign character. -/
def IsAlternating {n : ℕ} (f : Configuration n → ℂ) : Prop :=
  ∀ (σ : ParticlePermutation n) (z : Configuration n),
    f (permute σ z) = permutationSign σ * f z

/-- The collision locus: at least two particle coordinates coincide. -/
def collisionSet (n : ℕ) : Set (Configuration n) :=
  {z | ∃ i j : Fin n, z i = z j ∧ i ≠ j}

/-- A collision-free configuration has pairwise distinct coordinates. -/
def CollisionFree {n : ℕ} (z : Configuration n) : Prop :=
  Function.Injective z

@[simp]
theorem mem_collisionSet_iff {n : ℕ} {z : Configuration n} :
    z ∈ collisionSet n ↔ ∃ i j : Fin n, z i = z j ∧ i ≠ j :=
  Iff.rfl

/-- Collision-freeness is exactly exclusion from the collision locus. -/
theorem collisionFree_iff_not_mem_collisionSet {n : ℕ}
    (z : Configuration n) :
    CollisionFree z ↔ z ∉ collisionSet n := by
  constructor
  · intro hz hmem
    rcases hmem with ⟨i, j, hij, hne⟩
    exact hne (hz hij)
  · intro hz i j hij
    by_contra hne
    exact hz ⟨i, j, hij, hne⟩

end GinibrePoincare
