/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Regularity.CoeffBridge
public import LeanPool.EllipticPDE.Existence.Garding


/-!
# `W^{k,∞}` regularity for the transport and zeroth-order coefficients

`EllipticPdes.Sobolev.FullEllipticOp` gives `b` and `c` sup bounds and measurability and no
derivatives at all, which is everything the existence theory and the interior `H²` estimate
need. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem VIII.3.2
(p. 65) asks for `a_{ij} ∈ W^{k+2,∞}` and `b_i, c ∈ W^{k+1,∞}`, one order less on the lower-order
coefficients than on the principal part, because the lower-order terms are differentiated once
less often on the way to the same conclusion. This file supplies the missing hypothesis.

## Scalar predicate and bundle

`IsWkInfty f k` states the hypothesis for a single scalar function, and `IsWkInftyLower`
bundles it over the `d + 1` lower-order coefficients with a constant uniform across them.
Splitting it this way lets `IsWkInfty.deriv` be stated once and used for `b`, for `c`, and for
anything else the induction differentiates.

## Main declarations

* `IsWkInfty`: weak derivatives to order `k` of a scalar function, essentially bounded.
* `IsWkInfty.deriv`: an order-`k+1` bundle for `f` gives an order-`k` bundle for `∂_l f`.
* `IsWkInfty.ofContDiff`: a `Cᵏ` function with bounded derivatives satisfies it.
* `IsWkInfty.const`: a constant satisfies it at every order.
* `IsWkInftyCoeff.entry`: one entry of the coefficient matrix, as a scalar bundle.
* `IsWkInftyLower`: Guo's hypothesis on `b` and `c`, with a uniform constant.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-! ### Scalar hypothesis -/

/-- **`f ∈ W^{k,∞}`**, given as data: a family of weak derivatives indexed by lists of
directions, each measurable and essentially bounded, with no continuity assumed. The order-zero
member is `f` itself, so `bound 0` is a sup bound on `f`. -/
structure IsWkInfty (f : EuclideanSpace ℝ (Fin d) → ℝ) (k : ℕ) where
  /-- The chosen representative of the iterated weak derivative along a list of directions. -/
  D : List (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ
  /-- The empty list of directions is the function itself. -/
  D_nil : D [] = f
  /-- Every entry of the family is measurable. -/
  D_meas : ∀ α, α.length ≤ k → Measurable (D α)
  /-- Each successive entry is a weak partial derivative of its parent, up to order `k`. -/
  D_step : ∀ (l : Fin d) (α : List (Fin d)), α.length < k → HasWeakPartial l (D α) (D (l :: α))
  /-- The uniform bound on the derivatives of each order. -/
  bound : ℕ → ℝ
  /-- Every bound is nonnegative. -/
  bound_nonneg : ∀ m, 0 ≤ bound m
  /-- Each derivative of order `m ≤ k` is bounded by `bound m` almost everywhere. -/
  ess_bdd : ∀ α, α.length ≤ k →
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |D α x| ≤ bound α.length

namespace IsWkInfty

variable {f : EuclideanSpace ℝ (Fin d) → ℝ} {k l : ℕ}

/-- An order-`k` bundle is an order-`l` bundle for every `l ≤ k`. -/
def mono (hf : IsWkInfty f k) (hlk : l ≤ k) : IsWkInfty f l where
  D := hf.D
  D_nil := hf.D_nil
  D_meas α hα := hf.D_meas α (hα.trans hlk)
  D_step m α hα := hf.D_step m α (lt_of_lt_of_le hα hlk)
  bound := hf.bound
  bound_nonneg := hf.bound_nonneg
  ess_bdd α hα := hf.ess_bdd α (hα.trans hlk)

/-- **Differentiating the hypothesis.** From `f ∈ W^{k+1,∞}`, the first derivative `D [m]` is in
`W^{k,∞}`, with family `α ↦ D (α ++ [m])` and the bounds shifted by one order. Appending on the
right makes the lengths line up, exactly as in `HasIteratedWeakDerivOn.deriv`; this step lets
the induction of Guo's Theorem VIII.3.2 keep its coefficient hypothesis. -/
def deriv (hf : IsWkInfty f (k + 1)) (m : Fin d) : IsWkInfty (hf.D [m]) k where
  D α := hf.D (α ++ [m])
  D_nil := by simp
  D_meas α hα := by
    refine hf.D_meas (α ++ [m]) ?_
    simpa [List.length_append] using Nat.succ_le_succ hα
  D_step n α hα := by
    have hlen : (α ++ [m]).length < k + 1 := by
      simpa [List.length_append] using Nat.succ_lt_succ hα
    simpa using hf.D_step n (α ++ [m]) hlen
  bound j := hf.bound (j + 1)
  bound_nonneg j := hf.bound_nonneg (j + 1)
  ess_bdd α hα := by
    have h := hf.ess_bdd (α ++ [m]) (by simpa [List.length_append] using Nat.succ_le_succ hα)
    simpa [List.length_append] using h

/-- **`Cᵏ` function with bounded derivatives in `W^{k,∞}`.** The classical iterated
partials serve as the family, through `hasWeakPartial_partialD`, and the pointwise
`iteratedFDeriv` bounds transfer through `abs_iterPartial_le`. Order zero is included here,
unlike in `IsCkCoeff`, where `EllipticCoeff.Λ` already has it. -/
def ofContDiff {B : ℕ → ℝ} (hf : ContDiff ℝ ((k : ℕ) : ℕ∞) f) (hB : ∀ m, 0 ≤ B m)
    (hbd : ∀ m, m ≤ k → ∀ x, ‖iteratedFDeriv ℝ m f x‖ ≤ B m) : IsWkInfty f k where
  D := iterPartial f
  D_nil := rfl
  D_meas α hα := by
    have hk : (((0 + α.length : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ (((k : ℕ) : ℕ∞) : WithTop ℕ∞) := by
      have : 0 + α.length ≤ k := by omega
      exact_mod_cast this
    exact (contDiff_iterPartial (n := 0) α (hf.of_le hk)).continuous.measurable
  D_step m α hα := by
    have hk : (((1 + α.length : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ (((k : ℕ) : ℕ∞) : WithTop ℕ∞) := by
      have : 1 + α.length ≤ k := by omega
      exact_mod_cast this
    exact hasWeakPartial_partialD (contDiff_iterPartial (n := 1) α (hf.of_le hk)) m
  bound := B
  bound_nonneg := hB
  ess_bdd α hα :=
    Filter.Eventually.of_forall fun x =>
      (abs_iterPartial_le α hα hf x).trans (hbd α.length hα x)

/-- **Constants in `W^{k,∞}` at every order.** Its derivatives past the zeroth vanish, so
one bound serves every order. The datum of the induction step has a term with no coefficient at
all, namely the derivative of the datum itself, and this is what lets it be treated as a
weighted term like the rest. -/
def const (c : ℝ) (k : ℕ) : IsWkInfty (fun _ : EuclideanSpace ℝ (Fin d) => c) k :=
  IsWkInfty.ofContDiff (B := fun _ => |c|) contDiff_const (fun _ => abs_nonneg c) (by
    intro m _ x
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    · rw [iteratedFDeriv_const_of_ne (by omega)]
      simp [abs_nonneg c])

end IsWkInfty

/-- **Single entry of the coefficient matrix as a `W^{k,∞}` function.** The matrix bundle
already has a family for each entry, so the scalar bundle is that family read at a fixed pair of
indices. -/
def IsWkInftyCoeff.entry {A : EllipticCoeff d} {k : ℕ} (hA : IsWkInftyCoeff A k) (i j : Fin d) :
    IsWkInfty (fun x => A.a x i j) k where
  D α := hA.D α i j
  D_nil := hA.D_nil i j
  D_meas α hα := hA.D_meas i j α hα
  D_step l α hα := hA.D_step i j l α hα
  bound := hA.bound
  bound_nonneg := hA.bound_nonneg
  ess_bdd α hα := hA.ess_bdd i j α hα

/-! ### Bundle over the lower-order coefficients -/

/-- **Guo's hypothesis on the lower-order coefficients.** Every transport component and the
zeroth-order coefficient lie in `W^{k,∞}`, with one constant serving all of them. The uniform
constant is what the estimate of Theorem VIII.3.2 is stated against, so it is recorded here
rather than reconstructed as a maximum at the point of use. -/
structure IsWkInftyLower (Op : FullEllipticOp d) (k : ℕ) where
  /-- Each transport component is in `W^{k,∞}`. -/
  bReg : ∀ i, IsWkInfty (fun x => Op.b x i) k
  /-- The zeroth-order coefficient is in `W^{k,∞}`. -/
  cReg : IsWkInfty Op.c k
  /-- The constant uniform across the lower-order coefficients. -/
  bound : ℕ → ℝ
  /-- Every bound is nonnegative. -/
  bound_nonneg : ∀ m, 0 ≤ bound m
  /-- The transport bounds are dominated by the uniform constant. -/
  b_le : ∀ i m, (bReg i).bound m ≤ bound m
  /-- The zeroth-order bound is dominated by the uniform constant. -/
  c_le : ∀ m, cReg.bound m ≤ bound m

namespace IsWkInftyLower

variable {Op : FullEllipticOp d} {k l : ℕ}

/-- An order-`k` bundle is an order-`l` bundle for every `l ≤ k`. -/
def mono (hOp : IsWkInftyLower Op k) (hlk : l ≤ k) : IsWkInftyLower Op l where
  bReg i := (hOp.bReg i).mono hlk
  cReg := hOp.cReg.mono hlk
  bound := hOp.bound
  bound_nonneg := hOp.bound_nonneg
  b_le i m := hOp.b_le i m
  c_le m := hOp.c_le m

/-- Every transport component is essentially bounded by the uniform constant at every order
up to `k`. -/
theorem ae_abs_b_le (hOp : IsWkInftyLower Op k) (i : Fin d) (α : List (Fin d))
    (hα : α.length ≤ k) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      |(hOp.bReg i).D α x| ≤ hOp.bound α.length := by
  filter_upwards [(hOp.bReg i).ess_bdd α hα] with x hx
  exact hx.trans (hOp.b_le i α.length)

/-- The zeroth-order coefficient is essentially bounded by the uniform constant at every order
up to `k`. -/
theorem ae_abs_c_le (hOp : IsWkInftyLower Op k) (α : List (Fin d)) (hα : α.length ≤ k) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      |hOp.cReg.D α x| ≤ hOp.bound α.length := by
  filter_upwards [hOp.cReg.ess_bdd α hα] with x hx
  exact hx.trans (hOp.c_le α.length)

end IsWkInftyLower

end EllipticPdes.Regularity
