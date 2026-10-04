/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Regularity.MulIterated


/-!
# Linear algebra of iterated weak derivatives

The datum of the differentiated equation is a finite sum of signed terms, each a bounded
weight against a derivative of the solution. `EllipticPdes.Regularity.MulIterated` supplies
the weight; this file supplies the sum.

The same observation appears at three levels: weak differentiation is linear, so an order-`k`
family of a sum is the entrywise sum of the families, and the triangle inequality turns a bound
on each summand into a bound on the sum. The constants add rather than being optimised, which is
all the induction of Guo, *Partial Differential Equations I and II* (Course Lecture Notes),
Theorem VIII.3.2 (p. 65) needs: its constant is quantified before the solution and the datum,
and nothing constrains its size.

## Main declarations

* `HasWeakDerivOn.zero`, `HasWeakDerivOn.neg`, `HasWeakDerivOn.sum`: linearity of the weak
  derivative on a region.
* `HasIteratedWeakDerivOn.neg`, `.sub`, `.sum`: the families.
* `IteratedL2Bound.add`, `.neg`, `.sub`, `.sum`: the bounds.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ} {V : Set (EuclideanSpace ℝ (Fin d))} {k : ℕ} {ℓ : Fin d}

/-! ### Linearity of the weak derivative -/

/-- The zero class has zero weak derivative: both sides of the integration by parts vanish. -/
theorem HasWeakDerivOn.zero : HasWeakDerivOn V ℓ (0 : L2D V) (0 : L2D V) := by
  have hvan : ∀ ψ : EuclideanSpace ℝ (Fin d) → ℝ,
      (∫ x in V, ((0 : L2D V) x : ℝ) * ψ x) = 0 := by
    intro ψ
    rw [show (∫ x in V, ((0 : L2D V) x : ℝ) * ψ x) = ∫ _x in V, (0 : ℝ) from
      integral_congr_ae (by
        filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict V)] with x hx
        rw [hx, Pi.zero_apply, zero_mul])]
    simp
  intro φ _ _ _
  rw [hvan, hvan, neg_zero]

/-- A weak derivative of a negation is the negation of the weak derivative. -/
theorem HasWeakDerivOn.neg {g g' : L2D V} (hg : HasWeakDerivOn V ℓ g g') :
    HasWeakDerivOn V ℓ (-g) (-g') := by
  intro φ hφc hφcs hφV
  have hrw : ∀ (p : L2D V) (ψ : EuclideanSpace ℝ (Fin d) → ℝ),
      (∫ x in V, ((-p) x : ℝ) * ψ x) = - ∫ x in V, (p x : ℝ) * ψ x := by
    intro p ψ
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_neg p] with x hx
    rw [hx, Pi.neg_apply, neg_mul]
  rw [hrw, hrw, hg φ hφc hφcs hφV, neg_neg]

/-- A weak derivative of a finite sum is the sum of the weak derivatives. -/
theorem HasWeakDerivOn.sum {ι : Type*} {g g' : ι → L2D V}
    (h : ∀ i, HasWeakDerivOn V ℓ (g i) (g' i)) (s : Finset ι) :
    HasWeakDerivOn V ℓ (∑ i ∈ s, g i) (∑ i ∈ s, g' i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using HasWeakDerivOn.zero
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (h i).add ih

/-! ### Families -/

/-- The order-`k` family of a negation, entry by entry. -/
def HasIteratedWeakDerivOn.neg {g : L2D V} (hg : HasIteratedWeakDerivOn V k g) :
    HasIteratedWeakDerivOn V k (-g) where
  D α := -hg.D α
  D_nil := by rw [hg.D_nil]
  D_step m α hα := (hg.D_step m α hα).neg

/-- The order-`k` family of a difference. The datum of the induction step is a signed
combination, so subtraction is as basic here as addition. -/
def HasIteratedWeakDerivOn.sub {g h : L2D V} (hg : HasIteratedWeakDerivOn V k g)
    (hh : HasIteratedWeakDerivOn V k h) : HasIteratedWeakDerivOn V k (g - h) :=
  (hg.add hh.neg).congr (sub_eq_add_neg g h).symm

/-- The order-`k` family of a finite sum, entry by entry. -/
def HasIteratedWeakDerivOn.sum {ι : Type*} [Fintype ι] {g : ι → L2D V}
    (H : ∀ i, HasIteratedWeakDerivOn V k (g i)) :
    HasIteratedWeakDerivOn V k (∑ i, g i) where
  D α := ∑ i, (H i).D α
  D_nil := Finset.sum_congr rfl fun i _ => (H i).D_nil
  D_step m α hα := HasWeakDerivOn.sum (fun i => (H i).D_step m α hα) Finset.univ

/-! ### Bounds -/

namespace IteratedL2Bound

variable {C C' : ℝ}

/-- The bound on a sum of two families is the sum of the bounds. -/
theorem add {g h : L2D V} {hg : HasIteratedWeakDerivOn V k g}
    {hh : HasIteratedWeakDerivOn V k h} (hC : IteratedL2Bound hg C)
    (hC' : IteratedL2Bound hh C') : IteratedL2Bound (hg.add hh) (C + C') :=
  fun α hα => (norm_add_le _ _).trans (add_le_add (hC α hα) (hC' α hα))

/-- A negation has the same bound. -/
theorem neg {g : L2D V} {hg : HasIteratedWeakDerivOn V k g} (hC : IteratedL2Bound hg C) :
    IteratedL2Bound hg.neg C :=
  fun α hα => by
    change ‖-hg.D α‖ ≤ C
    rw [norm_neg]
    exact hC α hα

/-- The bound on a difference of families is the sum of the bounds. -/
theorem sub {g h : L2D V} {hg : HasIteratedWeakDerivOn V k g}
    {hh : HasIteratedWeakDerivOn V k h} (hC : IteratedL2Bound hg C)
    (hC' : IteratedL2Bound hh C') : IteratedL2Bound (hg.sub hh) (C + C') :=
  IteratedL2Bound.congr (IteratedL2Bound.add hC (IteratedL2Bound.neg hC'))

/-- The bound on a finite sum of families is the sum of the bounds. -/
theorem sum {ι : Type*} [Fintype ι] {g : ι → L2D V}
    {H : ∀ i, HasIteratedWeakDerivOn V k (g i)} {C : ι → ℝ}
    (hC : ∀ i, IteratedL2Bound (H i) (C i)) :
    IteratedL2Bound (HasIteratedWeakDerivOn.sum H) (∑ i, C i) :=
  fun α hα => (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hC i α hα)

end IteratedL2Bound

end EllipticPdes.Regularity
