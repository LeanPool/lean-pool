/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.Lattice
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Coloring

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Triadic lattice cubes and the separation colouring

ABK26 states its concentration corollary for a family `{X_z}_{z ∈ 3^n ℤ^d ∩
□_m}` whose members are independent whenever the corresponding subcubes do not
touch. Turning that hypothesis into an application of the concentration
inequality requires a *colouring*: the lattice is split into finitely many
classes, each of which is pairwise separated beyond the range of dependence, the
concentration inequality is applied inside each class, and the classes are
recombined by the triangle inequality.

This module supplies the two purely combinatorial ingredients.

* The finite set `cubeFinset m` of lattice points of `□_m`, with cardinality
  `3 ^ (d * m)`; `mem_cubeFinset_iff` characterizes its members by
  `2 · latDist 0 x < 3 ^ m`, which is what `Lattice.mem_cubeAt_iff` says of the
  set `cubeAt m 0`, i.e. of ABK26's `□_m ∩ ℤ^d`.
* The colouring `siteColor L`, the residue of a site modulo `3 ^ L + 1`. Two
  distinct sites of the same colour differ by a multiple of `3 ^ L + 1` in some
  coordinate, hence are separated at range `3 ^ L`, which is exactly the
  separation demanded by ABK26's finite-range hypothesis.

The recombination cost is the Cauchy--Schwarz bound
`sum_sqrt_card_colorClass_le`, which controls `∑_c √(#class c)` by
`√(colourCount) · √(#S)`. The colour count is taken to be the *minimum* of the
number `(3 ^ L + 1) ^ d` of residues and the total site count `#S`: the second
bound, valid because `√n ≤ n` for a nonempty class, is the sharper one once the
range of dependence exceeds the diameter of the cube, and it is what keeps the
scale sum of the ABK26 density bound convergent.

## Main definitions

* `Algsuperdiff.Section3.Provider.Percolation.cubeFinset`
* `Algsuperdiff.Section3.Provider.Percolation.siteColor`
* `Algsuperdiff.Section3.Provider.Percolation.colorClass`

## Main results

* `card_cubeFinset`, `mem_cubeFinset_iff`, `cubeFinset_nonempty`
* `three_pow_lt_latDist_of_siteColor_eq`: same colour and distinct implies
  separated at range `3 ^ L`.
* `sum_sqrt_card_colorClass_le`: the Cauchy--Schwarz recombination cost.

## References

* ABK26, triadic cubes, the concentration corollary, the finite-range
  hypothesis.
-/

namespace Algsuperdiff.Section3.Provider.Percolation

open Finset

variable {d : ℕ}

/-! ### The lattice points of a triadic cube -/

/-- Half-width of the triadic cube `□_m`: the lattice points of `□_m` are those
whose coordinates all lie in `[-cubeRadius m, cubeRadius m]`. -/
def cubeRadius (m : ℕ) : ℕ := (3 ^ m - 1) / 2

theorem two_mul_cubeRadius_add_one (m : ℕ) : 2 * cubeRadius m + 1 = 3 ^ m := by
  have hodd : (3 : ℕ) ^ m % 2 = 1 := by simp [Nat.pow_mod]
  have hpos : 0 < (3 : ℕ) ^ m := three_pow_pos m
  rw [cubeRadius]
  omega

/-- The lattice points of the triadic cube `□_m`, as a `Finset`. -/
noncomputable def cubeFinset (m : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(cubeRadius m : ℤ)) (cubeRadius m : ℤ)

theorem mem_cubeFinset_iff {m : ℕ} {x : Fin d → ℤ} :
    x ∈ cubeFinset m ↔ 2 * latDist 0 x < 3 ^ m := by
  classical
  have hr := two_mul_cubeRadius_add_one (m := m)
  rw [cubeFinset, Fintype.mem_piFinset]
  constructor
  · intro hx
    have hsup : latDist 0 x ≤ cubeRadius m :=
      latDist_le_iff.mpr fun j => by
        have hj := Finset.mem_Icc.mp (hx j)
        simp only [Pi.zero_apply]
        omega
    omega
  · intro hx j
    have hj : ((0 : Fin d → ℤ) j - x j).natAbs ≤ latDist 0 x := coord_le_latDist 0 x j
    simp only [Pi.zero_apply] at hj
    rw [Finset.mem_Icc]
    omega


theorem cubeFinset_nonempty (m : ℕ) : (cubeFinset (d := d) m).Nonempty :=
  ⟨0, mem_cubeFinset_iff.mpr (by rw [latDist_self]; simp [three_pow_pos m])⟩

theorem card_cubeFinset (m : ℕ) : (cubeFinset (d := d) m).card = 3 ^ (d * m) := by
  classical
  have hr := two_mul_cubeRadius_add_one (m := m)
  rw [cubeFinset, Fintype.card_piFinset]
  have hfac : ∀ _j : Fin d,
      (Finset.Icc (-(cubeRadius m : ℤ)) (cubeRadius m : ℤ)).card = 3 ^ m := by
    intro _j
    rw [Int.card_Icc]
    omega
  rw [Finset.prod_congr rfl fun j _ => hfac j, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← pow_mul, Nat.mul_comm]

/-! ### The separation colouring -/

/-- The colour of a lattice site at separation scale `L`: its residue modulo
`3 ^ L + 1`. -/
def siteColor (L : ℕ) (x : Fin d → ℤ) : Fin d → ZMod (3 ^ L + 1) :=
  fun j => ((x j : ZMod (3 ^ L + 1)))

/-- **Distinct sites of the same colour are separated.** This is the geometric
content of the colouring: it converts the colour classes into families to which
ABK26's finite-range independence hypothesis at range `3 ^ L` applies. -/
theorem three_pow_lt_latDist_of_siteColor_eq {L : ℕ} {x y : Fin d → ℤ}
    (hc : siteColor L x = siteColor L y) (hxy : x ≠ y) : 3 ^ L < latDist x y := by
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
    by_contra hcon
    push Not at hcon
    exact hxy (funext hcon)
  have hzero : (((x j - y j : ℤ)) : ZMod (3 ^ L + 1)) = 0 := by
    have hcj : ((x j : ZMod (3 ^ L + 1))) = ((y j : ZMod (3 ^ L + 1))) := congrFun hc j
    push_cast
    rw [hcj]
    ring
  have hdvd : ((3 ^ L + 1 : ℕ) : ℤ) ∣ (x j - y j) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  have hdvd' : (3 ^ L + 1 : ℕ) ∣ (x j - y j).natAbs := by
    have h := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa only [Int.natAbs_natCast] using h
  have hne : (x j - y j).natAbs ≠ 0 := by
    intro h
    exact hj (by omega)
  have hle : 3 ^ L + 1 ≤ (x j - y j).natAbs :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd'
  have hcoord : (x j - y j).natAbs ≤ latDist x y := coord_le_latDist x y j
  omega

/-- The colour class of `c` inside a finite set of sites. -/
def colorClass (L : ℕ) (S : Finset (Fin d → ℤ)) (c : Fin d → ZMod (3 ^ L + 1)) :
    Finset (Fin d → ℤ) :=
  S.filter fun x => siteColor L x = c

theorem mem_colorClass_iff {L : ℕ} {S : Finset (Fin d → ℤ)}
    {c : Fin d → ZMod (3 ^ L + 1)} {x : Fin d → ℤ} :
    x ∈ colorClass L S c ↔ x ∈ S ∧ siteColor L x = c := by
  rw [colorClass, Finset.mem_filter]

theorem colorClass_subset {L : ℕ} {S : Finset (Fin d → ℤ)}
    {c : Fin d → ZMod (3 ^ L + 1)} : colorClass L S c ⊆ S :=
  Finset.filter_subset _ _

theorem colorClass_nonempty {L : ℕ} {S : Finset (Fin d → ℤ)}
    {c : Fin d → ZMod (3 ^ L + 1)} (hc : c ∈ S.image (siteColor L)) :
    (colorClass L S c).Nonempty := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
  exact ⟨x, mem_colorClass_iff.mpr ⟨hx, rfl⟩⟩

/-- Sites of one colour class are pairwise separated at range `3 ^ L`. -/
theorem three_pow_lt_latDist_of_mem_colorClass {L : ℕ} {S : Finset (Fin d → ℤ)}
    {c : Fin d → ZMod (3 ^ L + 1)} {x y : Fin d → ℤ}
    (hx : x ∈ colorClass L S c) (hy : y ∈ colorClass L S c) (hxy : x ≠ y) :
    3 ^ L < latDist x y :=
  three_pow_lt_latDist_of_siteColor_eq
    ((mem_colorClass_iff.mp hx).2.trans (mem_colorClass_iff.mp hy).2.symm) hxy

/-! ### The recombination cost -/

/-- At most `(3 ^ L + 1) ^ d` colours occur: the number of residue vectors
modulo `3 ^ L + 1`. -/
theorem card_image_siteColor_le (L : ℕ) (S : Finset (Fin d → ℤ)) :
    (S.image (siteColor L)).card ≤ (3 ^ L + 1) ^ d := by
  classical
  refine le_trans (Finset.card_le_univ _) (le_of_eq ?_)
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

private theorem sum_sqrt_le_sqrt_card_mul {κ : Type*} (s : Finset κ) (n : κ → ℝ)
    (hn : ∀ c, 0 ≤ n c) :
    ∑ c ∈ s, Real.sqrt (n c) ≤ Real.sqrt (s.card : ℝ) * Real.sqrt (∑ c ∈ s, n c) := by
  simpa using
    Real.sum_sqrt_mul_sqrt_le (s := s) (f := fun _ => (1 : ℝ)) (g := n)
      (fun _ => zero_le_one) hn

theorem sum_card_colorClass (L : ℕ) (S : Finset (Fin d → ℤ)) :
    ∑ c ∈ S.image (siteColor L), ((colorClass L S c).card : ℝ) = (S.card : ℝ) := by
  classical
  rw [← Nat.cast_sum]
  exact_mod_cast
    (Finset.card_eq_sum_card_fiberwise
      (f := siteColor L) (s := S) (t := S.image (siteColor L))
      fun x hx => Finset.mem_image_of_mem _ hx).symm

/-- **The Cauchy--Schwarz recombination cost of the colouring.**

The colour count is the minimum of the number `(3 ^ L + 1) ^ d` of residues and
the total number of sites. -/
theorem sum_sqrt_card_colorClass_le (L : ℕ) (S : Finset (Fin d → ℤ)) :
    ∑ c ∈ S.image (siteColor L), Real.sqrt ((colorClass L S c).card : ℝ) ≤
      Real.sqrt (min (((3 ^ L + 1) ^ d : ℕ) : ℝ) ((S.card : ℝ))) *
        Real.sqrt (S.card : ℝ) := by
  classical
  have htotal : ∑ c ∈ S.image (siteColor L), ((colorClass L S c).card : ℝ) = (S.card : ℝ) :=
    sum_card_colorClass L S
  have hcard_nonneg : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  rcases le_total (((3 ^ L + 1) ^ d : ℕ) : ℝ) ((S.card : ℝ)) with hmin | hmin
  · rw [min_eq_left hmin]
    have hcs := sum_sqrt_le_sqrt_card_mul (S.image (siteColor L))
      (fun c => ((colorClass L S c).card : ℝ)) fun c => Nat.cast_nonneg _
    rw [htotal] at hcs
    refine hcs.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
    refine Real.sqrt_le_sqrt ?_
    exact_mod_cast card_image_siteColor_le L S
  · rw [min_eq_right hmin, Real.mul_self_sqrt hcard_nonneg]
    refine le_trans (Finset.sum_le_sum fun c hc => ?_) (le_of_eq htotal)
    have hone : 1 ≤ ((colorClass L S c).card : ℝ) := by
      exact_mod_cast (colorClass_nonempty hc).card_pos
    calc Real.sqrt ((colorClass L S c).card : ℝ)
        ≤ Real.sqrt (((colorClass L S c).card : ℝ) * ((colorClass L S c).card : ℝ)) :=
          Real.sqrt_le_sqrt (le_mul_of_one_le_left (by linarith) hone)
      _ = ((colorClass L S c).card : ℝ) := Real.sqrt_mul_self (by linarith)

end Algsuperdiff.Section3.Provider.Percolation
