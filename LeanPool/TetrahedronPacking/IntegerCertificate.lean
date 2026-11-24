/-
Copyright (c) 2026 Mike Lady. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Lady
-/

-- Modified for Lean Pool.

module

public import LeanPool.TetrahedronPacking.PeriodicSeparation
public import LeanPool.TetrahedronPacking.IntegerProjections
public import Mathlib.Data.Pi.Interval
public import Mathlib.Data.Int.Interval
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Tactic.NormNum

/-!
# Transport a checked integer projection to real space

The integer dot product extends to a continuous real linear functional.
A nonzero coordinate of the direction supplies a unit vector on which
the functional is nonzero. The checked inequalities extend from the
vertices to separating hulls, including cases of boundary contact.
-/

@[expose] public section

namespace TetrahedronPacking

open Set

/-- An accepted integer comparison gives a separating real plane for
four arbitrary real-cast vertices and an arbitrary integer displacement. -/
theorem integer_separator_plane
    (n : Fin 3 → ℤ) (v w : Fin 4 → Fin 3 → ℤ) (t : Fin 3 → ℤ)
    (h : integerSeparates n v w (integerDot n t) = true) :
    ∃ (f : (Fin 3 → ℝ) →L[ℝ] ℝ) (a : ℝ), f ≠ 0 ∧
      (∀ i, f (fun j => (v i j : ℝ)) ≤ a) ∧
      ∀ i, a ≤ f ((fun j => (w i j : ℝ)) + fun j => (t j : ℝ)) := by
  obtain ⟨⟨r, hr⟩, hp⟩ := integerSeparates_sound n v w _ h
  let f : (Fin 3 → ℝ) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((n 0 : ℝ) • LinearMap.proj 0 + (n 1 : ℝ) • LinearMap.proj 1 +
      (n 2 : ℝ) • LinearMap.proj 2)
  have hf_apply (u : Fin 3 → ℝ) : f u = n 0 * u 0 + n 1 * u 1 + n 2 * u 2 := rfl
  have hf_ne : f ≠ 0 := by
    intro hzero
    have hz := congrArg (fun g : (Fin 3 → ℝ) →L[ℝ] ℝ => g (Pi.single r 1)) hzero
    change f (Pi.single r 1) = 0 at hz
    have hs : f (Pi.single r 1) = n r := by
      fin_cases r
      · norm_num [hf_apply, Pi.single_apply, Fin.ext_iff]
      · norm_num [hf_apply, Pi.single_apply, Fin.ext_iff]
      · norm_num [hf_apply, Pi.single_apply, Fin.ext_iff]
    rw [hs] at hz
    exact hr (by exact_mod_cast hz)
  have hf_int (u : Fin 3 → ℤ) : f (fun j => (u j : ℝ)) = (integerDot n u : ℝ) := by
    simp [hf_apply, integerDot]
  apply separator_of_vertex_comparisons f hf_ne
  obtain h | h := hp
  · left
    intro i j
    rw [map_add, hf_int, hf_int, hf_int]
    exact_mod_cast h i j
  · right
    intro i j
    rw [map_add, hf_int, hf_int, hf_int]
    exact_mod_cast h i j

/-- Integer certificates on a bounded set of shifts give disjoint real
interiors for every required shift. The coordinate chart and integer shifts
must describe the same lattice translations. -/
theorem integer_shift_certificates
    (C : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ))
    (translation : (Fin 3 → ℤ) → Fin 3 → ℤ)
    (ht : ∀ k, C.symm (fun j => (k j : ℝ)) = (fun j => (translation k j : ℝ)))
    (v w : Fin 4 → Fin 3 → ℤ) (required : (Fin 3 → ℤ) → Prop)
    (loV hiV loW hiW : Fin 3 → ℝ)
    (hv : ∀ i j, loV j ≤ C (fun r => (v i r : ℝ)) j ∧
      C (fun r => (v i r : ℝ)) j ≤ hiV j)
    (hw : ∀ i j, loW j ≤ C (fun r => (w i r : ℝ)) j ∧
      C (fun r => (w i r : ℝ)) j ≤ hiW j)
    (cert : ∀ k, required k →
      (∀ j, loV j - hiW j ≤ (k j : ℝ) ∧ (k j : ℝ) ≤ hiV j - loW j) →
      ∃ n, integerSeparates n v w (integerDot n (translation k)) = true) :
    ∀ k, required k →
      Disjoint (interior (convexHull ℝ (range (fun i r => (v i r : ℝ)))))
        (interior (convexHull ℝ (range (fun i =>
          (fun r => (w i r : ℝ)) + fun r => (translation k r : ℝ))))) := by
  intro k hk
  rw [← ht k]
  apply disjoint_interiors_of_bounded_shift_certificates C
    (fun i r => (v i r : ℝ)) (fun i r => (w i r : ℝ)) required loV hiV loW hiW hv hw _ k hk
  intro l hl hb
  obtain ⟨n, hn⟩ := cert l hl hb
  rw [ht l]
  exact integer_separator_plane n v w (translation l) hn

/-- Enumerate the integer points in an inclusive coordinate box. -/
def integerShiftBox (lo hi : Fin 3 → ℤ) : Finset (Fin 3 → ℤ) :=
  Finset.Icc lo hi

theorem mem_integerShiftBox (lo hi k : Fin 3 → ℤ) :
    k ∈ integerShiftBox lo hi ↔ ∀ j, lo j ≤ k j ∧ k j ≤ hi j := by
  simp only [integerShiftBox, Finset.mem_Icc, Pi.le_def, forall_and]

example : (![0, 0, 0] : Fin 3 → ℤ) ∈ integerShiftBox ![-1, 0, 0] ![1, 0, 0] := by decide
example : (![2, 0, 0] : Fin 3 → ℤ) ∉ integerShiftBox ![-1, 0, 0] ![1, 0, 0] := by decide

/-- Pair-specific finite shift enumeration with independently verified bounds.
The strict margins let either endpoint be rounded inward to an integer. -/
theorem integer_shift_certificates_of_box
    (C : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ))
    (translation : (Fin 3 → ℤ) → Fin 3 → ℤ)
    (ht : ∀ k, C.symm (fun j => (k j : ℝ)) = (fun j => (translation k j : ℝ)))
    (v w : Fin 4 → Fin 3 → ℤ) (required : (Fin 3 → ℤ) → Prop)
    (loV hiV loW hiW : Fin 3 → ℝ) (lo hi : Fin 3 → ℤ)
    (hv : ∀ i j, loV j ≤ C (fun r => (v i r : ℝ)) j ∧
      C (fun r => (v i r : ℝ)) j ≤ hiV j)
    (hw : ∀ i j, loW j ≤ C (fun r => (w i r : ℝ)) j ∧
      C (fun r => (w i r : ℝ)) j ≤ hiW j)
    (hlo : ∀ j, (lo j : ℝ) - 1 < loV j - hiW j)
    (hhi : ∀ j, hiV j - loW j < (hi j : ℝ) + 1)
    (cert : ∀ k ∈ integerShiftBox lo hi, required k →
      ∃ n, integerSeparates n v w (integerDot n (translation k)) = true) :
    ∀ k, required k →
      Disjoint (interior (convexHull ℝ (range (fun i r => (v i r : ℝ)))))
        (interior (convexHull ℝ (range (fun i =>
          (fun r => (w i r : ℝ)) + fun r => (translation k r : ℝ))))) := by
  apply integer_shift_certificates C translation ht v w required loV hiV loW hiW hv hw
  intro k hk hb
  apply cert k _ hk
  apply (mem_integerShiftBox lo hi k).mpr
  intro j
  have hl : (lo j : ℝ) - 1 < (k j : ℝ) := (hlo j).trans_le (hb j).1
  have hh : (k j : ℝ) < (hi j : ℝ) + 1 := (hb j).2.trans_lt (hhi j)
  have hl' : lo j - 1 < k j := by exact_mod_cast hl
  have hh' : k j < hi j + 1 := by exact_mod_cast hh
  omega

end TetrahedronPacking
