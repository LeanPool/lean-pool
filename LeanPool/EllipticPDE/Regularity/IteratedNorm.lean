/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Regularity.HigherWeakDeriv


/-!
# `H^k` norm of an iterated family

Evans, *Partial Differential Equations* (2nd ed.), §5.2.2 (p. 259) defines

`‖u‖_{W^{k,p}(U)} = (Σ_{|α| ≤ k} ∫_U |D^α u|^p dx)^{1/p}`

for multi-indices `α`. A family `HasIteratedWeakDerivOn V k u` indexes derivatives by lists of
directions, one list per ordered sequence of differentiations, so a multi-index of order `j`
corresponds to as many lists as it has orderings. `iteratedNorm` is the same sum taken over
lists:

`iteratedNorm H = (Σ_{j ≤ k} Σ_{α ∈ (Fin d)^j} ‖D_α u‖²_{L²(V)})^{1/2}`.

Weak derivatives commute, so each multi-index contributes its `L²` norm squared with the
multiplicity of its orderings, between `1` and `j!`; the two norms are equivalent with constants
depending on `d` and `k` alone. Weak derivatives on an open set are unique, so the value does
not depend on the family chosen.

## Main declarations

* `iteratedNorm`: the norm.
* `norm_D_le_iteratedNorm`: every entry of the family is bounded by it.
* `iteratedNorm_le`: a uniform bound on the entries bounds it, with a constant in `d` and `k`.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ} {V : Set (EuclideanSpace ℝ (Fin d))} {k : ℕ} {u : L2D V}

/-- **`H^k(V)` norm of an iterated family**, summed over lists of directions of length at
most `k`. -/
def iteratedNorm (H : HasIteratedWeakDerivOn V k u) : ℝ :=
  Real.sqrt (∑ m ∈ Finset.range (k + 1), ∑ α : Fin m → Fin d, ‖H.D (List.ofFn α)‖ ^ 2)

theorem iteratedNorm_nonneg (H : HasIteratedWeakDerivOn V k u) : 0 ≤ iteratedNorm H :=
  Real.sqrt_nonneg _

/-- Every entry of the family up to order `k` is bounded by the norm. -/
theorem norm_D_le_iteratedNorm (H : HasIteratedWeakDerivOn V k u) {α : List (Fin d)}
    (hα : α.length ≤ k) : ‖H.D α‖ ≤ iteratedNorm H := by
  have hmem : α.length ∈ Finset.range (k + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hα)
  have h1 : ‖H.D α‖ ^ 2 ≤ ∑ β : Fin α.length → Fin d, ‖H.D (List.ofFn β)‖ ^ 2 := by
    have h := Finset.single_le_sum (f := fun β : Fin α.length → Fin d => ‖H.D (List.ofFn β)‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ α.get)
    simpa [List.ofFn_get] using h
  have h2 := Finset.single_le_sum
    (f := fun m => ∑ β : Fin m → Fin d, ‖H.D (List.ofFn β)‖ ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) hmem
  rw [iteratedNorm, ← Real.sqrt_sq (norm_nonneg (H.D α))]
  exact Real.sqrt_le_sqrt (h1.trans h2)

/-- The norm is a uniform bound on the family. -/
theorem iteratedL2Bound_iteratedNorm (H : HasIteratedWeakDerivOn V k u) :
    IteratedL2Bound H (iteratedNorm H) := fun _ hα => norm_D_le_iteratedNorm H hα

/-- The number of lists of directions of length at most `k`, as a real number. -/
def listCount (d k : ℕ) : ℝ := ∑ m ∈ Finset.range (k + 1), (d : ℝ) ^ m

theorem listCount_nonneg (d k : ℕ) : 0 ≤ listCount d k :=
  Finset.sum_nonneg fun _ _ => pow_nonneg (Nat.cast_nonneg d) _

/-- **Norm bound from a uniform bound on the family**, with the factor `√N` for `N` the number
of lists of length at most `k`. -/
theorem iteratedNorm_le {H : HasIteratedWeakDerivOn V k u} {C : ℝ} (hC : IteratedL2Bound H C) :
    iteratedNorm H ≤ Real.sqrt (listCount d k) * C := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) hC.norm_le
  have hsum : ∑ m ∈ Finset.range (k + 1), ∑ α : Fin m → Fin d, ‖H.D (List.ofFn α)‖ ^ 2
      ≤ listCount d k * C ^ 2 := by
    rw [listCount, Finset.sum_mul]
    refine Finset.sum_le_sum fun m hm => ?_
    have hmk : m ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    calc ∑ α : Fin m → Fin d, ‖H.D (List.ofFn α)‖ ^ 2
        ≤ ∑ _α : Fin m → Fin d, C ^ 2 := Finset.sum_le_sum fun α _ =>
          pow_le_pow_left₀ (norm_nonneg _) (hC _ (by simpa using hmk)) 2
      _ = (d : ℝ) ^ m * C ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  calc iteratedNorm H ≤ Real.sqrt (listCount d k * C ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (listCount d k) * C := by
        rw [Real.sqrt_mul (listCount_nonneg d k), Real.sqrt_sq hC0]

end EllipticPdes.Regularity
