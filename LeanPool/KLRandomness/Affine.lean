/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.ZMod.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Positivity

/-!
# The algebra behind fair and forced answers

Section 3 of Liu and Meng, arXiv:2611.31004v1, removes the queried column `c`
from the unread matrix. Let `D` be the linear map given by the other unread
columns, and `z` the remaining syndrome. The two possible answers have
completion fibers `D x = z` and `D x = z - c`.

If `c` is in the range of `D`, translation gives a bijection between the
fibers. If `c` is outside the range, the two fibers cannot both be nonempty.
The dimension of the span drops by exactly one in the latter case.

These algebraic statements are proved over any field. They apply in
particular to binary parity equations over `ZMod 2`. The measure-theoretic
statement about conditioning an adaptive transcript is a subsequent task.
-/

@[expose] public section

namespace Klr.Affine

variable {K V W : Type*} [Field K] [AddCommGroup V] [AddCommGroup W]
  [Module K V] [Module K W]

/-- All completions realizing a given residual syndrome. -/
def Fiber (D : V →ₗ[K] W) (z : W) := {x : V // D x = z}

/-- Adding back the queried column to the span of the other columns. -/
def withColumn (D : V →ₗ[K] W) (c : W) : Submodule K W :=
  LinearMap.range D ⊔ Submodule.span K {c}

/-- Every nonempty affine fiber is a translate of the kernel. -/
def fiberEquivKer (D : V →ₗ[K] W) {z : W} (u : V) (hu : D u = z) :
    Fiber D z ≃ LinearMap.ker D where
  toFun x := ⟨x.val - u, by
    change D (x.val - u) = 0
    rw [map_sub, x.property, hu, sub_self]⟩
  invFun x := ⟨x.val + u, by
    have hx : D x.val = 0 := x.property
    rw [map_add, hx, hu, zero_add]⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp

/-- Counting solutions of a full-row-rank finite-dimensional affine system. -/
theorem card_fiber_of_surjective [Module.Finite K V]
    (D : V →ₗ[K] W) (hD : Function.Surjective D) (z : W) :
    Nat.card (Fiber D z) = Nat.card K ^ (Module.finrank K V - Module.finrank K W) := by
  obtain ⟨u, hu⟩ := hD z
  rw [Nat.card_congr (fiberEquivKer D u hu), Module.natCard_eq_pow_finrank (K := K)]
  have hd := D.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hD, finrank_top] at hd
  congr 1
  omega

/-- A rank-`r` system of parity equations on `m` bits has `2^(m-r)` solutions. -/
theorem card_binary_fiber {m r : ℕ}
    (D : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    (hD : Function.Surjective D) (z : Fin r → ZMod 2) :
    Nat.card (Fiber D z) = 2 ^ (m - r) := by
  simpa using card_fiber_of_surjective D hD z

/-- The fraction of assignments satisfying `r` independent parity equations
is exactly `2⁻ʳ`. This is the finite counting form of the fair-coin measure
calculation used to build the Martin-Löf test. -/
theorem binary_fiber_fraction {m r : ℕ}
    (D : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    (hD : Function.Surjective D) (z : Fin r → ZMod 2) :
    (Nat.card (Fiber D z) : ℚ) / Nat.card (Fin m → ZMod 2) = (1 / 2 : ℚ) ^ r := by
  have hd := D.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hD, finrank_top] at hd
  simp only [Module.finrank_pi, Fintype.card_fin] at hd
  have hr : r ≤ m := by omega
  rw [card_binary_fiber D hD z, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  push_cast
  have hp : (2 : ℚ) ^ m = 2 ^ (m - r) * 2 ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hr]
  rw [hp, div_mul_eq_div_div, div_self (by positivity : (2 : ℚ) ^ (m - r) ≠ 0)]
  simp

/-- Subtracting a preimage of the queried column switches the possible
answer while preserving the residual affine equations. -/
def fiberEquiv (D : V →ₗ[K] W) (z : W) {c : W} (u : V) (hu : D u = c) :
    Fiber D z ≃ Fiber D (z - c) where
  toFun x := ⟨x.val - u, by simp [map_sub, x.property, hu]⟩
  invFun x := ⟨x.val + u, by simp [map_add, x.property, hu]⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp

/-- When deleting a column preserves the span, both bit values have equally
many completions. For a finite uniform solution space this is the counting
identity behind a fair conditional answer. -/
theorem card_fiber_eq_of_mem_range (D : V →ₗ[K] W) (z : W) {c : W}
    (hc : c ∈ LinearMap.range D) :
    Nat.card (Fiber D z) = Nat.card (Fiber D (z - c)) := by
  obtain ⟨u, hu⟩ := hc
  exact Nat.card_congr (fiberEquiv D z u hu)

theorem nonempty_fiber_iff_of_mem_range (D : V →ₗ[K] W) (z : W) {c : W}
    (hc : c ∈ LinearMap.range D) :
    Nonempty (Fiber D z) ↔ Nonempty (Fiber D (z - c)) := by
  obtain ⟨u, hu⟩ := hc
  exact (fiberEquiv D z u hu).nonempty_congr

/-- Two feasible answers would express the queried column as a difference
of images of the remaining columns. -/
theorem mem_range_of_both_fibers (D : V →ₗ[K] W) (z c : W)
    (h₀ : Nonempty (Fiber D z)) (h₁ : Nonempty (Fiber D (z - c))) :
    c ∈ LinearMap.range D := by
  obtain ⟨x₀⟩ := h₀
  obtain ⟨x₁⟩ := h₁
  refine ⟨x₀.val - x₁.val, ?_⟩
  rw [map_sub, x₀.property, x₁.property]
  abel

/-- If deleting the queried column loses span, at most one answer is
compatible. Compatibility of the observed history supplies existence. -/
theorem not_both_fibers_of_not_mem_range (D : V →ₗ[K] W) (z : W) {c : W}
    (hc : c ∉ LinearMap.range D) :
    ¬ (Nonempty (Fiber D z) ∧ Nonempty (Fiber D (z - c))) := by
  rintro ⟨h₀, h₁⟩
  exact hc (mem_range_of_both_fibers D z c h₀ h₁)

/-- For a compatible history, an answer is forced exactly when the queried
column is outside the span of the other unread columns. -/
theorem forced_iff_not_mem_range (D : V →ₗ[K] W) (z c : W)
    (compatible : Nonempty (Fiber D z) ∨ Nonempty (Fiber D (z - c))) :
    (¬ (Nonempty (Fiber D z) ∧ Nonempty (Fiber D (z - c)))) ↔
      c ∉ LinearMap.range D := by
  constructor
  · intro h hc
    have he := nonempty_fiber_iff_of_mem_range D z hc
    rcases compatible with h₀ | h₁
    · exact h ⟨h₀, he.mp h₀⟩
    · exact h ⟨he.mpr h₁, h₁⟩
  · exact not_both_fibers_of_not_mem_range D z

theorem withColumn_eq_of_mem_range (D : V →ₗ[K] W) {c : W}
    (hc : c ∈ LinearMap.range D) : withColumn D c = LinearMap.range D := by
  apply sup_eq_left.mpr
  apply Submodule.span_le.mpr
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  exact hc

/-- A column outside the remaining span raises the rank by exactly one. -/
theorem finrank_withColumn_of_not_mem_range [Module.Finite K W]
    (D : V →ₗ[K] W) {c : W} (hc : c ∉ LinearMap.range D) :
    Module.finrank K (withColumn D c) = Module.finrank K (LinearMap.range D) + 1 := by
  exact Submodule.finrank_sup_span_singleton hc

/-- The rank-drop criterion in Section 3, expressed without choosing bases. -/
theorem rank_drop_iff_not_mem_range [Module.Finite K W]
    (D : V →ₗ[K] W) (c : W) :
    Module.finrank K (LinearMap.range D) < Module.finrank K (withColumn D c) ↔
      c ∉ LinearMap.range D := by
  by_cases hc : c ∈ LinearMap.range D
  · rw [withColumn_eq_of_mem_range D hc]
    simp [hc]
  · rw [finrank_withColumn_of_not_mem_range D hc]
    simp [hc]

/-- A compatible query is forced exactly when deleting its column lowers
the rank. This is the algebraic part of the paper's adaptive-query lemma. -/
theorem forced_iff_rank_drop [Module.Finite K W]
    (D : V →ₗ[K] W) (z c : W)
    (compatible : Nonempty (Fiber D z) ∨ Nonempty (Fiber D (z - c))) :
    (¬ (Nonempty (Fiber D z) ∧ Nonempty (Fiber D (z - c)))) ↔
      Module.finrank K (LinearMap.range D) < Module.finrank K (withColumn D c) := by
  rw [forced_iff_not_mem_range D z c compatible, rank_drop_iff_not_mem_range]

end Klr.Affine
