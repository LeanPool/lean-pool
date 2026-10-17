/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Campanato.TriadicRadii
public import LeanPool.HighContrastHomogenization.Support.Ambient.Basic

/-!
# TriadicLattice

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The triadic lattice of centres, and rounding toward the origin

An oscillation estimate produced by a scale-by-scale iteration is available
only at *lattice* centres: at each triadic scale the estimate is proved for the
cubes centred at the points of a lattice of that spacing.  A Hölder seminorm,
by contrast, is a statement about **every** pair of points.  Moving from the
one to the other requires replacing an arbitrary centre `x` by a nearby lattice
point `z`, and the whole cost of that replacement is governed by how far `z`
can be from `x`.

This file supplies the lattice and the rounding map.  Two properties of the
rounding are used downstream and both are sharp:

* the displacement is **strictly** below the lattice spacing, which is what
  allows the enclosing lattice cube to be exactly one triadic scale up; and
* rounding is done **toward the centre of the cube**, so `|z - c| ≤ |x - c|`
  coordinatewise and the rounded centre never leaves a cube centred at `c` that
  contains `x`.

The second property is what makes the lattice family applicable at the rounded
centre: the estimate is available only at lattice points **of the cube**, and
rounding to the *nearest* lattice point can leave it.

In the ambient space `Vec d = Fin d → ℝ` the norm is the supremum norm, so a
coordinatewise bound on the displacement is a bound on `‖x - z‖`.

## Main definitions

* `triadicLattice s` — the set of points of `Vec d` all of whose coordinates
  are integer multiples of the spacing `s`.
* `triadicGridPoint s x` — the coordinatewise rounding of `x` toward the
  origin at spacing `s`.
* `triadicLatticeAt c s`, `triadicGridPointAt c s x` — the same objects for a
  lattice through an arbitrary base point `c`, with the rounding done toward
  `c`.

## Main results

* `triadicGridPoint_mem_triadicLattice` — the rounded point is a lattice point.
* `norm_sub_triadicGridPoint_lt` — the displacement is below the spacing.
* `norm_triadicGridPoint_le` — rounding toward the origin does not increase the
  norm.
* `norm_sub_triadicGridPointAt_lt`, `triadicGridPointAt_mem_ball` — the same two
  statements for a cube centred at `c`.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Campanato

open HCPolySupport

noncomputable section

variable {d : ℕ}

/-! ## 1. Rounding one coordinate toward the origin -/

/-- **One coordinate of the rounding toward the origin** at spacing `s`: the
multiple of `s` obtained from `t` by truncating, rather than by rounding to the
nearest multiple. -/
def triadicGridCoord (s t : ℝ) : ℝ :=
  if 0 ≤ t then s * (⌊t / s⌋ : ℤ) else s * (⌈t / s⌉ : ℤ)

theorem exists_int_triadicGridCoord (s t : ℝ) :
    ∃ n : ℤ, triadicGridCoord s t = s * (n : ℝ) := by
  unfold triadicGridCoord
  by_cases ht : 0 ≤ t
  · exact ⟨⌊t / s⌋, by rw [ite_eq_left ht]⟩
  · exact ⟨⌈t / s⌉, by rw [ite_eq_right ht]⟩

/-- The truncated coordinate is within one spacing of the original, strictly. -/
theorem abs_sub_triadicGridCoord_lt {s : ℝ} (hs : 0 < s) (t : ℝ) :
    |t - triadicGridCoord s t| < s := by
  unfold triadicGridCoord
  by_cases ht : 0 ≤ t
  · rw [ite_eq_left ht]
    have hlo : s * (⌊t / s⌋ : ℝ) ≤ t := by
      have h := Int.floor_le (t / s)
      have := mul_le_mul_of_nonneg_left h hs.le
      rwa [mul_div_cancel₀ t hs.ne'] at this
    have hhi : t < s * (⌊t / s⌋ : ℝ) + s := by
      have h := Int.lt_floor_add_one (t / s)
      have := mul_lt_mul_of_pos_left h hs
      rw [mul_div_cancel₀ t hs.ne'] at this
      linarith only [this]
    rw [abs_of_nonneg (by linarith only [hlo])]
    linarith only [hhi]
  · rw [ite_eq_right ht]
    have hhi : t ≤ s * (⌈t / s⌉ : ℝ) := by
      have h := Int.le_ceil (t / s)
      have := mul_le_mul_of_nonneg_left h hs.le
      rwa [mul_div_cancel₀ t hs.ne'] at this
    have hlo : s * (⌈t / s⌉ : ℝ) < t + s := by
      have h := Int.ceil_lt_add_one (t / s)
      have := mul_lt_mul_of_pos_left h hs
      rw [mul_add, mul_one, mul_div_cancel₀ t hs.ne'] at this
      linarith only [this]
    rw [abs_of_nonpos (by linarith only [hhi])]
    linarith only [hlo]

/-- Truncation toward the origin does not increase the absolute value. -/
theorem abs_triadicGridCoord_le {s : ℝ} (hs : 0 < s) (t : ℝ) :
    |triadicGridCoord s t| ≤ |t| := by
  unfold triadicGridCoord
  by_cases ht : 0 ≤ t
  · rw [ite_eq_left ht]
    have hnonneg : (0 : ℤ) ≤ ⌊t / s⌋ :=
      Int.le_floor.2 (by simpa only [Int.cast_zero] using div_nonneg ht hs.le)
    have hnonnegR : (0 : ℝ) ≤ (⌊t / s⌋ : ℝ) := by exact_mod_cast hnonneg
    have hlo : s * (⌊t / s⌋ : ℝ) ≤ t := by
      have h := Int.floor_le (t / s)
      have := mul_le_mul_of_nonneg_left h hs.le
      rwa [mul_div_cancel₀ t hs.ne'] at this
    rw [abs_of_nonneg (by positivity), abs_of_nonneg ht]
    exact hlo
  · rw [ite_eq_right ht]
    have htneg : t ≤ 0 := le_of_not_ge ht
    have hnonpos : ⌈t / s⌉ ≤ (0 : ℤ) :=
      Int.ceil_le.2 (by simpa only [Int.cast_zero] using div_nonpos_of_nonpos_of_nonneg htneg hs.le)
    have hnonposR : (⌈t / s⌉ : ℝ) ≤ 0 := by exact_mod_cast hnonpos
    have hhi : t ≤ s * (⌈t / s⌉ : ℝ) := by
      have h := Int.le_ceil (t / s)
      have := mul_le_mul_of_nonneg_left h hs.le
      rwa [mul_div_cancel₀ t hs.ne'] at this
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hs.le hnonposR), abs_of_nonpos htneg]
    linarith only [hhi]

/-! ## 2. The lattice and the rounding map -/

/-- **The triadic lattice of spacing `s`**: the points of `Vec d` all of whose
coordinates are integer multiples of `s`.  For `s = 3 ^ k` this is the lattice
`3 ^ k ℤ ^ d` of the scale-`k` cubes. -/
def triadicLattice (s : ℝ) : Set (Vec d) := {z | ∀ i, ∃ n : ℤ, z i = s * (n : ℝ)}

/-- **Rounding toward the origin** at spacing `s`, coordinate by coordinate. -/
def triadicGridPoint (s : ℝ) (x : Vec d) : Vec d := fun i => triadicGridCoord s (x i)

@[simp] theorem triadicGridPoint_apply (s : ℝ) (x : Vec d) (i : Fin d) :
    triadicGridPoint s x i = triadicGridCoord s (x i) := rfl

theorem triadicGridPoint_mem_triadicLattice (s : ℝ) (x : Vec d) :
    triadicGridPoint s x ∈ (triadicLattice s : Set (Vec d)) :=
  fun i => exists_int_triadicGridCoord s (x i)

/-- **The displacement of the rounding is below the spacing.**  Because the
ambient norm is the supremum norm, the coordinatewise bound is the bound on the
displacement vector. -/
theorem norm_sub_triadicGridPoint_lt {s : ℝ} (hs : 0 < s) (x : Vec d) :
    ‖x - triadicGridPoint s x‖ < s := by
  refine (pi_norm_lt_iff hs).2 fun i => ?_
  simpa only [Pi.sub_apply, triadicGridPoint_apply, Real.norm_eq_abs] using
    abs_sub_triadicGridCoord_lt hs (x i)

/-- **Rounding toward the origin does not increase the norm.** -/
theorem norm_triadicGridPoint_le {s : ℝ} (hs : 0 < s) (x : Vec d) :
    ‖triadicGridPoint s x‖ ≤ ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun i => ?_
  calc ‖triadicGridPoint s x i‖ = |triadicGridCoord s (x i)| := by
        rw [triadicGridPoint_apply, Real.norm_eq_abs]
    _ ≤ |x i| := abs_triadicGridCoord_le hs (x i)
    _ = ‖x i‖ := (Real.norm_eq_abs (x i)).symm
    _ ≤ ‖x‖ := norm_le_pi_norm x i

/-! ## 3. The lattice through an arbitrary base point -/

/-- **The triadic lattice of spacing `s` through `c`.** -/
def triadicLatticeAt (c : Vec d) (s : ℝ) : Set (Vec d) :=
  {z | z - c ∈ (triadicLattice s : Set (Vec d))}

/-- **Rounding toward `c`** at spacing `s`. -/
def triadicGridPointAt (c : Vec d) (s : ℝ) (x : Vec d) : Vec d :=
  c + triadicGridPoint s (x - c)

theorem triadicGridPointAt_mem_triadicLatticeAt (c : Vec d) (s : ℝ) (x : Vec d) :
    triadicGridPointAt c s x ∈ (triadicLatticeAt c s : Set (Vec d)) := by
  change triadicGridPointAt c s x - c ∈ (triadicLattice s : Set (Vec d))
  rw [triadicGridPointAt, add_sub_cancel_left]
  exact triadicGridPoint_mem_triadicLattice s (x - c)

theorem norm_sub_triadicGridPointAt_lt {s : ℝ} (hs : 0 < s) (c x : Vec d) :
    ‖x - triadicGridPointAt c s x‖ < s := by
  have hid : x - triadicGridPointAt c s x = (x - c) - triadicGridPoint s (x - c) := by
    rw [triadicGridPointAt]
    abel
  rw [hid]
  exact norm_sub_triadicGridPoint_lt hs (x - c)

/-- **Rounding toward the centre keeps the point inside the cube.** -/
theorem triadicGridPointAt_mem_ball {s rho : ℝ} (hs : 0 < s) {c x : Vec d}
    (hx : x ∈ Metric.ball c rho) : triadicGridPointAt c s x ∈ Metric.ball c rho := by
  have hxnorm : ‖x - c‖ < rho := by
    rwa [Metric.mem_ball, dist_eq_norm] at hx
  have hid : triadicGridPointAt c s x - c = triadicGridPoint s (x - c) := by
    rw [triadicGridPointAt, add_sub_cancel_left]
  rw [Metric.mem_ball, dist_eq_norm, hid]
  exact lt_of_le_of_lt (norm_triadicGridPoint_le hs (x - c)) hxnorm

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Campanato
