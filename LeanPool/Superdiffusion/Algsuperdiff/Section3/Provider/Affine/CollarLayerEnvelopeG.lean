/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Affine.CollarLayerEnvelope

/-!
# CollarLayerEnvelopeG

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The collar layer envelope of the `G`-leg (`∇·D̂_q`)

`CollarLayerEnvelope` proves a local `F`-leg estimate associated with
`l.piecewise.affine.approx`: on
every cell of every layer-`k` Whitney cube

```
|∇ℓ̂_p − p|²  ≤  (648 d)² · 3^{2 b (k + h_k)} · |p|² .
```

This module proves the corresponding local `p ↦ q` estimate, the **`G`-leg**:
the constant value on the cell of the divergence `∇·D̂_q` of the antisymmetric
matrix `D̂_q` of `e.hatdq`, at the **same** constant `648 d`, the **same**
exponent `3^{2 b (k + h_k)}` and `|q|²` on the right.  Together the two are the
pair `hFv`, `hGv` that `Multiscale.LayerUniform` and the Step-3 assembly carry
as a collar A antecedent's `|∇·D̂_q(𝔰)|²/|q|² + |∇ℓ̂_p(𝔰)|²/|p|² ≤^{2b(k+h_k)}`
is their sum.

## The object

`e.hatdq` reads, for the family `{ℓ̂_p}` of `e.hat.linear.1`,

```
(D̂_q)_{ij} := (d−1)⁻¹ ( q_j ℓ̂_{e_i} − q_i ℓ̂_{e_j} ) ,
```

and the manuscript's divergence convention (the footnote) is `(∇·A)_j = ∑_i
∂_{x_i} A_{ij}`.  `competitorAntisymDatum` is the vertex datum of the `(i,j)`
entry at the repository's competitor family `ℓ̂_p = competitorVertexData ℐ p`
and `competitorDivergence` is the resulting cell-constant divergence, i.e.
ABK26's `(∇·D̂_q)(𝔰)`.  Only the `d` basis slopes `ℓ̂_{e_i}` enter, exactly as
printed, so **no linearity of `p ↦ ℓ̂_p` is assumed anywhere**:
`e.hat.linear.linearity` is used only through `kuhnSlope`'s own unconditional
linearity in the datum, which `kuhnSlope_competitorAntisymDatum` records.

## The route

The `F`-leg's Euclidean conclusion is *not* strong enough to feed the `G`-leg at
the same constant — it has already paid the `ℓ¹ → ℓ²` factor `d`, and re-paying
it inside the divergence would cost a further factor.  What the `G`-leg needs is
the **coordinatewise** Step-2 estimate, one level below:

1. `abs_kuhnSlope_competitorVertexData_sub_le_of_forall_touching` is
   `KuhnInterpolation.abs_kuhnSlope_sub_le_of_vertex_oscillation` fed by the
   Step-2 vertex bound of `CompetitorVertexData`: every coordinate of
   `∇ℓ̂_p − p` on the cell is at most `2 |p|_{ℓ¹} D / (cell side)`, with `D` the
   active-component diameter bound.  At `p = e_i` the `ℓ¹` size is `1`, so all
   `d²` entries of the deviation matrix `u_i := ∇ℓ̂_{e_i} − e_i` obey the one
   bound `η = 2 D / (cell side)`.
2. `competitorDivergence_sub_eq` is the exact algebraic identity `(∇·D̂_q)_j −
   q_j = (d−1)⁻¹ ((∑_i (u_i)_i) q_j − ∑_i q_i (u_j)_i)`; the `d` and the `q_j`
   of the two sums cancel against the `(d−1)` precisely because `∇·D_q = q` for
   the exact family (the display and the sentence).
3. `vecNormSq_divergenceDeviation_le` is the pure `ℓ^∞`-to-`ℓ²` core: the
   `i = j` term of that sum vanishes identically, so each coordinate is a sum of
   `d − 1` terms, giving `|·|_j ≤ η ((d−2)|q_j| + |q|_{ℓ¹})` and, with
   `|q|_{ℓ¹}² ≤ d |q|²` and `(d−2)² + 2d(d−2) + d² = (2d−2)²`, the bound
   `|(∇·D̂_q) − q|² ≤ (2η)² |q|²`.  It is here that `2 ≤ d` is used, twice:
   `(d−1)⁻¹` must be finite and `(d−2)` nonnegative.
4. The scale step is the `F`-leg's own `four_mul_three_rpow_layer_envelope_le`
   (shared directly; de-privatized): `D / (cell side) ≤ 324 · 3^{b(k+h_k)}`, so
   `2η ≤ 1296 · 3^{b(k+h_k)}`.

## The constant, itemized

`2η ≤ 4 · 324 · 3^{b(k+h_k)} = 1296 · 3^{b(k+h_k)} = 648 · 2 · 3^{b(k+h_k)}`,
and `648 · 2 ≤ 648 d` exactly because `d ≥ 2`.  So the `G`-leg meets the
`F`-leg's constant `648 d` **with equality at `d = 2`** and with slack for
`d > 2`: the `F`-leg spends its second `d` on `ℓ¹ → ℓ²` for a general slope `p`,
while the `G`-leg spends `2` on the divergence's own `(2d−2)/(d−1)` and inherits
`ℓ¹`-size `1` from the basis slopes.  Nothing is optimized; as in the `F`-leg,
no random quantity, no layer index and no component enters the constant.

## Scope

This module is the per-cell estimate only, at the level `e.sum-of-a-decomp`
consumes.  It constructs **no** global field: nothing is claimed about `∇·D̂_q
∈ q + L²_{sol,0}(□_m)` (`e.hat.D.bc`), about divergence-freeness of the
assembled piecewise-constant field (: the face jumps cancel only because `D̂_q
∈ W^{1,∞}`, which needs the global continuity of `ℓ̂_{e_i}` that
`CompetitorVertexData` explicitly does not supply), or about `e.hat.linear.1`.
Those remain the open obligations recorded in `CompetitorVertexData`'s scope
section/`-c`.  No overlap count is consumed (as in the `F`-leg: the `hact`
binder is the max over the active components, and `max ≤ sum`), and no layer
window is assumed.

## References

* ABK26, (`e.dq`), (the divergence convention footnote), (`e.hatdq`),
  (`e.hat.D.bc`), (the cell-constant values), (`e.hat.linear.linearity`), (Step
  2), (label, `r.gradient.bound.simplified`), (`e.bounds.on.slopes.when.bad`).
-/

namespace Algsuperdiff.Section3.Provider.Affine

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

/-! ## The `ℓ^∞`-to-`ℓ²` core -/

/-- **The pure algebra of the `G`-leg.**  If every entry of the deviation family
`u` is at most `η` in absolute value, then

```
| (d−1)⁻¹ ( (∑_i (u_i)_i) q − (u_·ᵀ q) ) |²  ≤  (2 η)² |q|² .
```

The `i = j` term of the inner sum vanishes identically, so each coordinate is a
sum of `d − 1` terms and obeys `η ((d−2)|q_j| + |q|_{ℓ¹})`; squaring, summing
and using `|q|_{ℓ¹}² ≤ d |q|²` gives `(d−2)² + 2d(d−2) + d² = (2d−2)²`, which is
exactly cancelled by the `(d−1)⁻¹`.  This is the only place `2 ≤ d` is
consumed, and it is consumed sharply: at `d = 2` the bound is `(2η)²`. -/
theorem vecNormSq_divergenceDeviation_le (hd : 2 ≤ d) (q : Vec d) (u : Fin d → Vec d)
    {eta : ℝ} (hu : ∀ i l, |u i l| ≤ eta) :
    vecNormSq (fun j => ((d : ℝ) - 1)⁻¹ *
        ((∑ i, u i i) * q j - ∑ i, q i * u j i)) ≤
      (2 * eta) ^ 2 * vecNormSq q := by
  classical
  set w : Vec d := fun j => (∑ i, u i i) * q j - ∑ i, q i * u j i with hw
  set N : ℝ := vecNormOne q with hN
  set Q : ℝ := vecNormSq q with hQ
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdne : ((d : ℝ) - 1) ≠ 0 := by intro h; linarith [h]
  have heta : 0 ≤ eta := le_trans (abs_nonneg _) (hu ⟨0, by omega⟩ ⟨0, by omega⟩)
  have hN0 : 0 ≤ N := vecNormOne_nonneg q
  have hQ0 : 0 ≤ Q := vecNormSq_nonneg q
  have hNQ : N ^ 2 ≤ (d : ℝ) * Q := sq_vecNormOne_le q
  -- the coordinatewise bound, on `d − 1` terms
  have hwj : ∀ j, |w j| ≤ eta * (((d : ℝ) - 2) * |q j| + N) := by
    intro j
    have hsplit : w j = ∑ i ∈ Finset.univ.erase j, (u i i * q j - q i * u j i) := by
      have h1 : ∑ i ∈ Finset.univ.erase j, (u i i * q j - q i * u j i) =
          ∑ i, (u i i * q j - q i * u j i) :=
        Finset.sum_erase _ (by ring)
      rw [h1, Finset.sum_sub_distrib, ← Finset.sum_mul]
    have hb : ∀ i ∈ Finset.univ.erase j,
        |u i i * q j - q i * u j i| ≤ eta * |q j| + eta * |q i| := by
      intro i _
      have h1 : |u i i * q j| ≤ eta * |q j| := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hu i i) (abs_nonneg _)
      have h2 : |q i * u j i| ≤ eta * |q i| := by
        rw [abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hu j i) (abs_nonneg _)
      exact le_trans (abs_sub _ _) (by linarith)
    have hcard : ((Finset.univ.erase j).card : ℝ) = (d : ℝ) - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin,
        Nat.cast_sub (by omega : 1 ≤ d)]
      norm_num
    have hse : ∑ i ∈ Finset.univ.erase j, |q i| = N - |q j| := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ j), hN, vecNormOne_apply]
    calc |w j| = |∑ i ∈ Finset.univ.erase j, (u i i * q j - q i * u j i)| := by rw [hsplit]
      _ ≤ ∑ i ∈ Finset.univ.erase j, |u i i * q j - q i * u j i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.univ.erase j, (eta * |q j| + eta * |q i|) := Finset.sum_le_sum hb
      _ = ((d : ℝ) - 1) * (eta * |q j|) + eta * (N - |q j|) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, hse, nsmul_eq_mul,
            hcard]
      _ = eta * (((d : ℝ) - 2) * |q j| + N) := by ring
  have hwsq : ∀ j, w j ^ 2 ≤ eta ^ 2 * (((d : ℝ) - 2) * |q j| + N) ^ 2 := by
    intro j
    calc w j ^ 2 = |w j| ^ 2 := (sq_abs _).symm
      _ ≤ (eta * (((d : ℝ) - 2) * |q j| + N)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) (hwj j) 2
      _ = eta ^ 2 * (((d : ℝ) - 2) * |q j| + N) ^ 2 := by ring
  have habsq : ∑ j, |q j| ^ 2 = Q := by
    rw [hQ]
    simp only [vecNormSq, vecDot, sq_abs]
    exact Finset.sum_congr rfl fun j _ => by ring
  have habs1 : ∑ j, |q j| = N := by rw [hN, vecNormOne_apply]
  have hexpand : ∑ j, (((d : ℝ) - 2) * |q j| + N) ^ 2 =
      ((d : ℝ) - 2) ^ 2 * Q + 2 * ((d : ℝ) - 2) * N ^ 2 + (d : ℝ) * N ^ 2 := by
    have hcong : ∀ j : Fin d, (((d : ℝ) - 2) * |q j| + N) ^ 2 =
        ((d : ℝ) - 2) ^ 2 * |q j| ^ 2 + (2 * ((d : ℝ) - 2) * N) * |q j| + N ^ 2 :=
      fun j => by ring
    rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hcong j),
      Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, habsq, habs1]
    ring
  have hsumsq : ∑ j, w j ^ 2 ≤ eta ^ 2 * ((2 * (d : ℝ) - 2) ^ 2 * Q) := by
    have hstep : ∑ j, w j ^ 2 ≤
        eta ^ 2 * (((d : ℝ) - 2) ^ 2 * Q + 2 * ((d : ℝ) - 2) * N ^ 2 + (d : ℝ) * N ^ 2) := by
      calc ∑ j, w j ^ 2 ≤ ∑ j, eta ^ 2 * (((d : ℝ) - 2) * |q j| + N) ^ 2 :=
            Finset.sum_le_sum fun j _ => hwsq j
        _ = eta ^ 2 * ∑ j, (((d : ℝ) - 2) * |q j| + N) ^ 2 := by rw [Finset.mul_sum]
        _ = eta ^ 2 * (((d : ℝ) - 2) ^ 2 * Q + 2 * ((d : ℝ) - 2) * N ^ 2 +
              (d : ℝ) * N ^ 2) := by rw [hexpand]
    refine le_trans hstep ?_
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := by linarith
    have h1 : 2 * ((d : ℝ) - 2) * N ^ 2 ≤ 2 * ((d : ℝ) - 2) * ((d : ℝ) * Q) :=
      mul_le_mul_of_nonneg_left hNQ (by linarith)
    have h2 : (d : ℝ) * N ^ 2 ≤ (d : ℝ) * ((d : ℝ) * Q) :=
      mul_le_mul_of_nonneg_left hNQ hd0
    have heq : ((d : ℝ) - 2) ^ 2 * Q + 2 * ((d : ℝ) - 2) * ((d : ℝ) * Q) +
        (d : ℝ) * ((d : ℝ) * Q) = (2 * (d : ℝ) - 2) ^ 2 * Q := by ring
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg eta)
    linarith
  have hnorm : vecNormSq (fun j => ((d : ℝ) - 1)⁻¹ * w j) =
      (((d : ℝ) - 1)⁻¹) ^ 2 * ∑ j, w j ^ 2 := by
    simp only [vecNormSq, vecDot, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [show (fun j => ((d : ℝ) - 1)⁻¹ * ((∑ i, u i i) * q j - ∑ i, q i * u j i)) =
      (fun j => ((d : ℝ) - 1)⁻¹ * w j) from rfl, hnorm]
  refine le_trans (mul_le_mul_of_nonneg_left hsumsq (sq_nonneg _)) ?_
  have hfinal : (((d : ℝ) - 1)⁻¹) ^ 2 * (eta ^ 2 * ((2 * (d : ℝ) - 2) ^ 2 * Q)) =
      (2 * eta) ^ 2 * Q := by
    field_simp
  exact le_of_eq hfinal

end

end Algsuperdiff.Section3.Provider.Affine
