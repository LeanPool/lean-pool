/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset

/-!
# Definitions

The definitions of Section 2 of the paper: the cube, the points `x^S`, the antipode and the set
`Δ(x,y)`; the numbers `b_j(g)` and the zone of a Boolean function; 1-wings and rows; the
influences of Boolean and of real functions, mean and variance, the mean absolute increments; the
characters and the degree.

Points of the cube are functions `ι → Bool` for a finite index type `ι` (the paper's `[n]`).
The paper writes the cube as `Q_n = {-1,1}^n`, and as `{0,1}^n` in Corollary 1.2; the
identification is `false ↦ 0 ↦ +1`, `true ↦ 1 ↦ -1`.
-/

@[expose] public section

namespace AaronsonAmbainis

open Finset

/-- The Boolean cube `{0,1}^n`. -/
abbrev Cube (ι : Type*) := ι → Bool

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `flipSet x S` is the point `x` with exactly the coordinates in `S` flipped
(written `x^S` in the paper). -/
def flipSet (x : Cube ι) (S : Finset ι) : Cube ι :=
  fun i => if i ∈ S then !(x i) else x i

/-- The antipode of `x` (all coordinates flipped). -/
def antipode (x : Cube ι) : Cube ι := fun i => !(x i)

/-- `diffSet x y` is the set of coordinates in which `x` and `y` differ
(written `Δ(x,y)` in the paper). -/
def diffSet (x y : Cube ι) : Finset ι := univ.filter fun i => x i ≠ y i

/-- `bdry g j = b_j(g)`: the number of bichromatic `j`-edges of `g`; each such
edge is counted once, at its endpoint where `g = true`. -/
def bdry (g : Cube ι → Bool) (j : ι) : ℕ :=
  (univ.filter fun x : Cube ι => g x = true ∧ g (flipSet x {j}) = false).card

/-- `zone g = Z(g)`: the points `u` with `g u = true` and `g (antipode u) = false`. -/
def zone (g : Cube ι → Bool) : Finset (Cube ι) :=
  univ.filter fun u => g u = true ∧ g (antipode u) = false

/-- `A` is a 1-wing of `g` at `u`: flipping any subset of `A` at `u` keeps `g = true`. -/
def IsWing (g : Cube ι → Bool) (u : Cube ι) (A : Finset ι) : Prop :=
  ∀ S : Finset ι, S ⊆ A → g (flipSet u S) = true

/-- `lam` is a row (fractional certificate) of `g` at `x`: it is nonnegative and has
total weight at least one on every sensitive block of `g` at `x`. -/
def IsRow (g : Cube ι → Bool) (x : Cube ι) (lam : ι → ℝ) : Prop :=
  (∀ j, 0 ≤ lam j) ∧ ∀ S : Finset ι, g (flipSet x S) ≠ g x → 1 ≤ ∑ j ∈ S, lam j

/-- Influence of coordinate `j` on a Boolean function, uniform measure: the fraction
of points `x` with `g (x^j) ≠ g x` (written `I_j(g)` in the paper). -/
noncomputable def infl (g : Cube ι → Bool) (j : ι) : ℝ :=
  ((univ.filter fun x : Cube ι => g (flipSet x {j}) ≠ g x).card : ℝ) / 2 ^ Fintype.card ι

/-- Mean of a real function on the cube. -/
noncomputable def mean (f : Cube ι → ℝ) : ℝ := (∑ x, f x) / 2 ^ Fintype.card ι

/-- Variance of a real function on the cube. -/
noncomputable def variance (f : Cube ι → ℝ) : ℝ := (∑ x, (f x - mean f) ^ 2) / 2 ^ Fintype.card ι

/-- Influence of coordinate `j` on a real function: `E[((f(x) - f(x^j))/2)^2]`
(written `Inf_j(f)` in the paper). -/
noncomputable def inflR (f : Cube ι → ℝ) (j : ι) : ℝ :=
  (∑ x, ((f x - f (flipSet x {j})) / 2) ^ 2) / 2 ^ Fintype.card ι

/-- The mean absolute increment of a real function in the coordinate `j`: `E_x |f(x) - f(x^j)|`
(written `L_j(f)` in the paper; their sum over `j` is written `L(f)`). There is no factor `1/2`
here, so that `L_j(f)^2 ≤ 4 Inf_j(f)`. -/
noncomputable def meanAbsIncr (f : Cube ι → ℝ) (j : ι) : ℝ :=
  (∑ x, |f x - f (flipSet x {j})|) / 2 ^ Fintype.card ι

/-- The character `χ_S(x) = ∏_{i ∈ S} (-1)^{x_i}`. -/
noncomputable def chi (S : Finset ι) (x : Cube ι) : ℝ :=
  ∏ i ∈ S, (if x i then (-1 : ℝ) else 1)

/-- `f` is the restriction to the cube of a multilinear polynomial of degree at most `d`:
its expansion in characters uses only sets of size at most `d`. -/
def HasDegreeLE (f : Cube ι → ℝ) (d : ℕ) : Prop :=
  ∃ c : Finset ι → ℝ, (∀ S, d < S.card → c S = 0) ∧ ∀ x, f x = ∑ S, c S * chi S x

section Basic

omit [Fintype ι] in
lemma flipSet_empty (x : Cube ι) : flipSet x ∅ = x := by
  funext i
  simp [flipSet]

omit [Fintype ι] in
lemma flipSet_flipSet_self (x : Cube ι) (S : Finset ι) : flipSet (flipSet x S) S = x := by
  funext i
  by_cases h : i ∈ S <;> simp [flipSet, h]

lemma antipode_eq_flipSet_univ (x : Cube ι) : antipode x = flipSet x univ := by
  funext i
  simp [flipSet, antipode]

lemma diffSet_flipSet (x : Cube ι) (S : Finset ι) : diffSet x (flipSet x S) = S := by
  ext i
  by_cases h : i ∈ S <;> simp [diffSet, flipSet, h]

lemma flipSet_diffSet (x y : Cube ι) : flipSet x (diffSet x y) = y := by
  funext i
  by_cases h : x i = y i
  · simp [flipSet, diffSet, h]
  · have h' : (!(x i)) = y i := by
      cases hx : x i <;> cases hy : y i <;> simp_all
    simp [flipSet, diffSet, h, h']

lemma card_cube : Fintype.card (Cube ι) = 2 ^ Fintype.card ι := by
  simp [Cube]

end Basic

end AaronsonAmbainis
