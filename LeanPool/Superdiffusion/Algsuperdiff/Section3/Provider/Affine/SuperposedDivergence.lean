/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Affine.CollarLayerEnvelopeG
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Affine.SuperposedEnvelope

/-!
# SuperposedDivergence

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# `∇·D̂_q` at the superposed competitor (the `G`-leg of the superposed branch)

`CollarLayerEnvelopeG.lean` builds the manuscript's antisymmetric matrix `D̂_q`
(`e.hatdq`) and its cell divergence `∇·D̂_q(𝔰)` at the **single-mesh**
competitor family `ℓ̂_p = competitorVertexData ℐ p`.  This module runs the
*same* construction on the **superposed** family `ℓ̂_p = ℓ_p + Σ_𝒞 (ℓ̂_p^𝒞 −
ℓ_p)`, the second of the two admissible constructions, and provides the
following local `G`-leg objects and estimates:

* the field `superposedCompetitorDivergence` — this is `∇·D̂_q`, the object
  `e.hat.D.bc` speaks about, and the object whose solenoidality is the `hG` leg
  of `Multiscale.sum_of_a_decomp_cutoff`;
* its cell constants `superposedCompetitorCellDivergence`;
* the three cell-constant clauses of `e.hat.linear.properties` at that field
  (`hGc`, `hbadG`, `hoffG`); and
* its collar layer envelope, at `superposedDivConst d = 2 · superposedGradConst d`.

## Why this module exists (finding M-1)

The superposed branch of the Step-3 conclusion had used
`superposedCompetitorSlope … q` — the **gradient** construction re-run at the
load `q` — in its `G` leg.  That is the wrong object: the manuscript's `G` leg
is `∇·D̂_q`, the divergence of the antisymmetric matrix built from the `d`
basis members `ℓ̂_{e_i}`, not `∇ℓ̂_q`.  The two agree neither in law nor in
shape, and the solenoidality binder stated at `∇ℓ̂_q` is refutable.  Everything
below is stated at `∇·D̂_q`; nothing below refers to, or corrects, the branch
that used the gradient.

## The object

For the superposed family, `e.hatdq` reads entrywise

```
(D̂_q)_{ij} = (d − 1)⁻¹ ( q_j ℓ̂_{e_i} − q_i ℓ̂_{e_j} ) ,
```

which is `superposedCompetitorAntisymEntry`: `competitorAntisymDatum`'s formula
with the single-mesh vertex datum replaced by the superposed competitor, so
only the `d` basis members occur, exactly as printed, and **no linearity of `p
↦ ℓ̂_p` is assumed** (`e.hat.linear.linearity`, is not used).
`superposedCompetitorAntisymEntry_antisymm` is the antisymmetry.

At the manuscript's divergence convention `(∇·A)_j = ∑_i ∂_{x_i} A_{ij}` (the
footnote) the `j`-th coordinate of `∇·D̂_q` is the sum over `i` of the `i`-th
coordinate of the gradient of the `(i,j)` entry.  The superposed competitor
carries a **defined** piecewise-constant gradient field
`superposedCompetitorSlope` (there is no single mesh whose Kuhn-slope operator
applies to the entry — that is exactly what denies), so
`superposedCompetitorDivergence` is defined by that distributed expression:

```
(∇·D̂_q)(x)_j = ∑_i (d − 1)⁻¹ ( q_j (∇ℓ̂_{e_i})(x)_i − q_i (∇ℓ̂_{e_j})(x)_i ) .
```

Two theorems show that this is the proved single-mesh construction and not a new one:
`competitorDivergence_eq_sum_entrywise` says the distributed expression at
single-mesh Kuhn slopes IS `CollarLayerEnvelopeG.competitorDivergence` (it is
`kuhnSlope_competitorAntisymDatum`, i.e. the unconditional linearity of
`kuhnSlope` in its datum, re-summed), and
`globalCompetitorDivergence_eq_competitorDivergence` says that at ONE component
— where a single mesh does govern — the distributed expression evaluated on
that component's own field is literally `competitorDivergence` at the root cell
containing the point.

## The normalization `∇·D_q = q`

`superposedCompetitorCellDivergence_sub_eq` is the exact algebraic identity

```
(∇·D̂_q)(𝔰)_j − q_j = (d−1)⁻¹ ( (∑_i (u_i)_i) q_j − ∑_i q_i (u_j)_i ) ,
u_i = ∇ℓ̂_{e_i}(𝔰) − e_i ,
```

the `d` of `∑_i (e_i)_i` and the `q_j` of `∑_i q_i (e_j)_i` cancelling against
the `(d−1)` of `e.dq` — this is the display `∇·D_q = q` in its cellwise form,
and `superposedCompetitorCellDivergence_eq_of_cellSlope_basisVec` is that
display itself: on a cell where the superposed basis slopes are the basis
vectors (clause 3 of `e.hat.linear.properties`, off the collar) the divergence
is exactly `q`.  It is the reason `hoffG` is a theorem here.

## The route to the layer envelope, and the constant

The `(2d−2)²`-cancellation core `vecNormSq_divergenceDeviation_le` of
`CollarLayerEnvelopeG` is reused verbatim: if every entry of the deviation
family `u` is at most `η`, then `|(∇·D̂_q)(𝔰) − q|² ≤ (2η)² |q|²`.  What feeds
it here is not the coordinatewise Step-2 estimate of the single-mesh branch (no
single mesh, hence no `kuhnSlope`-level bound) but the proved **summed
active-component envelope**, read at the `d` basis loads:

```
|∇ℓ̂_{e_i}(𝔰) − e_i|²  ≤  superposedGradConst d ² · 3^{2b(k+h_k)} · |e_i|²
```

(`SuperposedEnvelope.badFamily_vecNormSq_superposedCompetitorCellSlope_sub_le_layerEnvelope`
at `p := basisVec i`, with `|e_i|² = 1`), and a coordinate of a vector is at
most its Euclidean norm, so `η = superposedGradConst d · 3^{b(k+h_k)}` serves.

**The constant, itemized honestly.**  `2η` gives

```
superposedDivConst d = 2 · superposedGradConst d = 2 · M(d) · 648 d = 3888 d · 11^d ,
```

i.e. the summed gradient constant times **2**, and nothing else. A further factor of order
`d · |q|_{ℓ¹}` does **not** appear, for two reasons, both checkable in the proof: (i) the
`d` entries of the inner sum are priced through the proved local core, whose `(d−2)² +
2d(d−2) + d² = (2d−2)²` is exactly cancelled by the `(d−1)⁻¹` of `e.dq`, leaving the
factor `2` and not a factor `d`; and (ii) the `ℓ¹` size of the load never enters, because
the deviation bound fed into the core is an `ℓ^∞` bound obtained from the Euclidean
envelope at the **basis** loads (`|e_i|_{ℓ¹} = 1`), so the `ℓ¹ → ℓ²` conversion is already
inside `superposedGradConst d`.  The comparison with the single-mesh branch is the
expected one: there the `G`-leg constant equals the `F`-leg's `648 d` because the `F` leg
pays an extra `d` for a general slope `p`; here the `F`-leg constant `superposedGradConst
d` already contains that `d`, so the `G` leg is `2 ×` it.  Nothing is optimized, and no
random quantity, layer index or component enters the constant.

## Scope: what is NOT claimed

This module is the per-cell estimate and the three cell-constant clauses, only.

* **No divergence-freeness.**  `e.hat.D.bc`, `∇·D̂_q ∈ q + L²_{sol,0}(□_m)`, is
  **not** proved and is not implied by anything below.  is explicit that the
  parenthetical "(since `D̂_q` is antisymmetric)" carries the whole face-jump
  argument, and that it works only because `D̂_q ∈ W^{1,∞}`: for the
  superposition that needs the global continuity of the superposed `ℓ̂_{e_i}`,
  which needs local finiteness of the component family, which
  `GlobalSuperposition.lean` explicitly does not supply.  The `hG` leg of the
  composition therefore remains an O disclosed binder — but it is now stated at
  the right object.
* **No gradient identification.**  `superposedCompetitorSlope`, and hence
  `superposedCompetitorDivergence`, are *defined* piecewise-constant fields;
  nothing identifies either with a distributional gradient or divergence.
* **No new probabilistic input, no new geometry.**  The diameter datum, the
  window, the multiplicity bound `|𝒜_R| ≤ M(d)` and the cluster geometry are
  consumed only through the proved summed envelope; none is re-derived, and no
  overlap count occurs below.

## References

* ABK26, (`e.hat.linear.1`), (`e.hat.linear.linearity`), (`e.dq`), (the
  divergence-convention footnote), (`∇·D_q = q`), (`e.hatdq`), (`e.hat.D.bc`),
  (the cell-constant values), (`l.piecewise.affine.approx`,
  `e.hat.linear.properties`; clause 1, clause 3), (Step 2),
  (`r.gradient.bound.simplified`), (`e.bounds.on.slopes.when.bad`).
* That is the factor `d²` the proved local core removes.
-/

namespace Algsuperdiff.Section3.Provider.Affine

open HCPolySupport
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

/-! ## `e.hatdq` at the superposed family -/

/-- **`∇·D̂_q` at the superposed family**, at the manuscript's divergence
convention `(∇·A)_j = ∑_i ∂_{x_i} A_{ij}` (the footnote): the sum over `i` of
the `i`-th coordinate of the gradient of the `(i,j)` entry, at the
superposition's own defined gradient field.

This is the field whose solenoidality is `e.hat.D.bc`; that statement is NOT
proved here (see the module Scope). -/
def superposedCompetitorDivergence (m : ℤ) (hn : ℕ → ℕ) (I : Set (TriadicCube d))
    (q : Vec d) : Vec d → Vec d :=
  fun x j => ∑ i, ((d : ℝ) - 1)⁻¹ *
    (q j * superposedCompetitorSlope m hn I (basisVec i) x i -
      q i * superposedCompetitorSlope m hn I (basisVec j) x i)

/-- **The constant value `∇·D̂_q(𝔰)` on a cell**, read at the cell's interior point
exactly as `superposedCompetitorCellSlope` is. -/
def superposedCompetitorCellDivergence (m : ℤ) (hn : ℕ → ℕ) (I : Set (TriadicCube d))
    (q : Vec d) (T : KuhnCell d) : Vec d :=
  superposedCompetitorDivergence m hn I q (Multiscale.kuhnCellInteriorPoint T)

theorem superposedCompetitorDivergence_apply (m : ℤ) (hn : ℕ → ℕ)
    (I : Set (TriadicCube d)) (q : Vec d) (x : Vec d) (j : Fin d) :
    superposedCompetitorDivergence m hn I q x j =
      ∑ i, ((d : ℝ) - 1)⁻¹ *
        (q j * superposedCompetitorSlope m hn I (basisVec i) x i -
          q i * superposedCompetitorSlope m hn I (basisVec j) x i) := rfl

theorem superposedCompetitorCellDivergence_apply (m : ℤ) (hn : ℕ → ℕ)
    (I : Set (TriadicCube d)) (q : Vec d) (T : KuhnCell d) (j : Fin d) :
    superposedCompetitorCellDivergence m hn I q T j =
      ∑ i, ((d : ℝ) - 1)⁻¹ *
        (q j * superposedCompetitorCellSlope m hn I (basisVec i) T i -
          q i * superposedCompetitorCellSlope m hn I (basisVec j) T i) := rfl

/-! ## The deviation identity and `∇·D_q = q` -/

/-- **The deviation identity, as pure algebra on a family of cell slopes.**  For
any family `S` of vectors (the roles: `S i = ∇ℓ̂_{e_i}(𝔰)`),

```
(∑_i (d−1)⁻¹ ( q_j S_i i − q_i S_j i))_j − q_j
   = (d−1)⁻¹ ( (∑_i (S_i − e_i)_i) q_j − ∑_i q_i (S_j − e_j)_i ) .
```

The `d` produced by `∑_i (e_i)_i` and the `q_j` produced by `∑_i q_i (e_j)_i`
cancel against the `(d−1)` of `e.dq`; this is the display `∇·D_q = q` in its
cellwise form, and it is what makes the left-hand side a deviation. -/
private theorem divergence_sub_eq (hd : 2 ≤ d) (q : Vec d) (S : Fin d → Vec d) :
    (fun j => ∑ i, ((d : ℝ) - 1)⁻¹ * (q j * S i i - q i * S j i)) - q =
      fun j => ((d : ℝ) - 1)⁻¹ *
        ((∑ i, (S i - basisVec i) i) * q j - ∑ i, q i * (S j - basisVec j) i) := by
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdne : ((d : ℝ) - 1) ≠ 0 := by intro h; linarith
  have hdiag : ∑ i : Fin d, basisVec (d := d) i i = (d : ℝ) := by
    simp [basisVec_apply]
  have hrow : ∀ j : Fin d, ∑ i, q i * basisVec (d := d) j i = q j := by
    intro j
    rw [Finset.sum_eq_single j]
    · simp [basisVec_apply]
    · intro i _ hij
      simp [basisVec_apply, hij]
    · intro h
      exact absurd (Finset.mem_univ j) h
  funext j
  have hL : ∑ i, ((d : ℝ) - 1)⁻¹ * (q j * S i i - q i * S j i) =
      ((d : ℝ) - 1)⁻¹ * (q j * (∑ i, S i i) - ∑ i, q i * S j i) := by
    have hterm : ∀ i : Fin d, ((d : ℝ) - 1)⁻¹ * (q j * S i i - q i * S j i) =
        ((d : ℝ) - 1)⁻¹ * q j * S i i - ((d : ℝ) - 1)⁻¹ * (q i * S j i) :=
      fun i => by ring
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hterm i),
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  have hS : ∑ i, (S i - basisVec i) i = (∑ i, S i i) - (d : ℝ) := by
    simp only [Pi.sub_apply]
    rw [Finset.sum_sub_distrib, hdiag]
  have hR : ∑ i, q i * (S j - basisVec j) i = (∑ i, q i * S j i) - q j := by
    simp only [Pi.sub_apply, mul_sub]
    rw [Finset.sum_sub_distrib, hrow j]
  rw [Pi.sub_apply, hL, hS, hR]
  field_simp
  ring

/-- **The deviation identity at the superposed cell divergence** (in cellwise
form): with `u_i = ∇ℓ̂_{e_i}(𝔰) − e_i`,

```
(∇·D̂_q)(𝔰) − q = (d−1)⁻¹ ( (∑_i (u_i)_i) q − (u_·ᵀ q) ) .
```
-/
theorem superposedCompetitorCellDivergence_sub_eq (hd : 2 ≤ d) (m : ℤ) (hn : ℕ → ℕ)
    (I : Set (TriadicCube d)) (q : Vec d) (T : KuhnCell d) :
    superposedCompetitorCellDivergence m hn I q T - q =
      fun j => ((d : ℝ) - 1)⁻¹ *
        ((∑ i, (superposedCompetitorCellSlope m hn I (basisVec i) T - basisVec i) i) * q j -
          ∑ i, q i * (superposedCompetitorCellSlope m hn I (basisVec j) T - basisVec j) i) :=
  divergence_sub_eq hd q fun i => superposedCompetitorCellSlope m hn I (basisVec i) T

/-- **`∇·D_q = q`** (the display), cellwise: on a cell where the superposed basis
slopes are the basis vectors themselves — the situation of clause 3 of
`e.hat.linear.properties` off the collar — the divergence of `D̂_q` is exactly
`q`.  This is the normalization that makes the deviation identity a statement
about a deviation, and it is the reason `hoffG` below is a theorem. -/
theorem superposedCompetitorCellDivergence_eq_of_cellSlope_basisVec (hd : 2 ≤ d)
    {m : ℤ} {hn : ℕ → ℕ} {I : Set (TriadicCube d)} (q : Vec d) {T : KuhnCell d}
    (h : ∀ i : Fin d, superposedCompetitorCellSlope m hn I (basisVec i) T = basisVec i) :
    superposedCompetitorCellDivergence m hn I q T = q := by
  refine eq_of_sub_eq_zero ?_
  rw [superposedCompetitorCellDivergence_sub_eq hd]
  funext j
  simp [h]

/-! ## The three cell-constant clauses at `∇·D̂_q` -/

/-- **The `G`-half of the `sum_of_a_decomp` clauses at `∇·D̂_q`, at one cell.**

* the field is constant on the open cell — every basis slope is
  (`e.hat.linear.properties` clause on the superposition), and `∇·D̂_q` is built
  from those pointwise;
* the constant is `0` when the cell's Whitney cube is **bad**: every basis
  slope is `0` there (clause 1), so every entry of `D̂_q` has zero gradient;
* the constant is `q` when the cube lies off `𝒩(ℐ)`: every basis slope is `e_i`
  there (clause 3), and the normalization `∇·D_q = q` applies.

Only the proved superposition clauses are used; no disjointness of collars, no
overlap count and no finiteness of the component family enters. -/
theorem superposedCompetitorDivergence_eq_cellDivergence (hd : 2 ≤ d) {m : ℤ}
    {hn : ℕ → ℕ} (hmono : Monotone hn) {I : Set (TriadicCube d)}
    (hI : I ⊆ whitneyPartition m hn)
    (hwin : ∀ C ∈ badComponents I, (whitneyNeighborhood m hn C).Finite ∧
      ∀ R ∈ whitneyNeighborhood m hn C,
        R ∈ whitneyLayer m hn (componentWindowLayer m hn C) ∨
          R ∈ whitneyLayer m hn (componentWindowLayer m hn C + 1))
    (q : Vec d) {T : KuhnCell d} (hT : T ∈ simplexPartition m hn) :
    (∀ x ∈ T.openCarrier,
        superposedCompetitorDivergence m hn I q x =
          superposedCompetitorCellDivergence m hn I q T) ∧
      (Multiscale.whitneyCubeOf m hn T ∈ I →
        superposedCompetitorCellDivergence m hn I q T = 0) ∧
      (Multiscale.whitneyCubeOf m hn T ∉ whitneyNeighborhood m hn I →
        superposedCompetitorCellDivergence m hn I q T = q) := by
  have : NeZero d := ⟨by omega⟩
  have hcl : ∀ i : Fin d, _ := fun i =>
    superposedCompetitorSlope_eq_cellSlope hmono hI hwin (basisVec i) hT
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    funext j
    rw [superposedCompetitorDivergence_apply, superposedCompetitorCellDivergence_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [(hcl i).1 x hx, (hcl j).1 x hx]
  · intro hbad
    have hz : ∀ i : Fin d, superposedCompetitorCellSlope m hn I (basisVec i) T = 0 :=
      fun i => (hcl i).2.1 hbad
    funext j
    rw [superposedCompetitorCellDivergence_apply]
    simp [hz]
  · intro hoff
    exact superposedCompetitorCellDivergence_eq_of_cellSlope_basisVec hd q
      fun i => (hcl i).2.2 hoff

/-- Over the subtype `↥(simplexPartition m hn)` these are literally the `hGc`,
`hbadG` and `hoffG` hypotheses of `Multiscale.sum_of_a_decomp_cutoff`. -/
theorem superposedCompetitorDivergence_decomp_clauses_badFamily (hd : 2 ≤ d) {m : ℤ}
    {hn : ℕ → ℕ} (hmono : Monotone hn) (M : ABKModel d) (omega : Cutoff.CutoffSample d)
    (hwin : ∀ C ∈ badComponents (badFamily M m hn omega),
      (whitneyNeighborhood m hn C).Finite ∧
      ∀ R ∈ whitneyNeighborhood m hn C,
        R ∈ whitneyLayer m hn (componentWindowLayer m hn C) ∨
          R ∈ whitneyLayer m hn (componentWindowLayer m hn C + 1))
    (q : Vec d) :
    (∀ T : ↥(simplexPartition (d := d) m hn), ∀ x ∈ (T : KuhnCell d).openCarrier,
        superposedCompetitorDivergence m hn (badFamily M m hn omega) q x =
          superposedCompetitorCellDivergence m hn (badFamily M m hn omega) q
            (T : KuhnCell d)) ∧
      (∀ T : ↥(simplexPartition (d := d) m hn),
        Multiscale.whitneyCubeOf m hn (T : KuhnCell d) ∈ badFamily M m hn omega →
          superposedCompetitorCellDivergence m hn (badFamily M m hn omega) q
            (T : KuhnCell d) = 0) ∧
      (∀ T : ↥(simplexPartition (d := d) m hn),
        Multiscale.whitneyCubeOf m hn (T : KuhnCell d) ∉
            whitneyNeighborhood m hn (badFamily M m hn omega) →
          superposedCompetitorCellDivergence m hn (badFamily M m hn omega) q
            (T : KuhnCell d) = q) :=
  ⟨fun T =>
      (superposedCompetitorDivergence_eq_cellDivergence hd hmono (fun _ hQ => hQ.1) hwin
        q T.2).1,
    fun T =>
      (superposedCompetitorDivergence_eq_cellDivergence hd hmono (fun _ hQ => hQ.1) hwin
        q T.2).2.1,
    fun T =>
      (superposedCompetitorDivergence_eq_cellDivergence hd hmono (fun _ hQ => hQ.1) hwin
        q T.2).2.2⟩

/-! ## The collar layer envelope of `∇·D̂_q` -/

/-- A coordinate is at most the Euclidean length: `v_l² ≤ |v|²`. -/
private theorem sq_le_vecNormSq (v : Vec d) (l : Fin d) : v l ^ 2 ≤ vecNormSq v := by
  have hnn : ∀ i ∈ (Finset.univ : Finset (Fin d)), 0 ≤ v i * v i :=
    fun i _ => mul_self_nonneg _
  have hle := Finset.single_le_sum hnn (Finset.mem_univ l)
  simpa [vecNormSq, vecDot, pow_two] using hle

/-- The `ℓ²`-to-`ℓ^∞` step: a Euclidean bound `|v|² ≤ c²` bounds every
coordinate by `c`.  This is what replaces the single-mesh branch's coordinatewise
Step-2 estimate, which is unavailable at the superposition (there is no single
mesh whose `kuhnSlope` prices a coordinate). -/
private theorem abs_le_of_vecNormSq_le {v : Vec d} {c : ℝ} (hc : 0 ≤ c)
    (h : vecNormSq v ≤ c ^ 2) (l : Fin d) : |v l| ≤ c := by
  have h1 : v l ^ 2 ≤ c ^ 2 := le_trans (sq_le_vecNormSq v l) h
  calc |v l| = Real.sqrt (v l ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (c ^ 2) := Real.sqrt_le_sqrt h1
    _ = c := Real.sqrt_sq hc

/-- **The collar gradient constant of the `G` leg of the superposed branch**, `2 ·
superposedGradConst d = 3888 d · 11^d`: the summed active-component constant
times the factor `2` produced by the `(2d−2)²` cancellation of `e.dq`.  It is
the `Cgrad` of `r.gradient.bound.simplified` for `∇·D̂_q` at the superposed
competitor. -/
def superposedDivConst (d : ℕ) : ℝ := 2 * superposedGradConst d

theorem one_le_superposedDivConst {d : ℕ} (hd : 1 ≤ d) : 1 ≤ superposedDivConst d := by
  have h := one_le_superposedGradConst hd
  rw [superposedDivConst]
  linarith

theorem superposedGradConst_le_superposedDivConst {d : ℕ} (hd : 1 ≤ d) :
    superposedGradConst d ≤ superposedDivConst d := by
  have h := one_le_superposedGradConst hd
  rw [superposedDivConst]
  linarith

/-- **The collar layer envelope of `∇·D̂_q` at the superposed competitor**: on
every cell of every layer-`k` Whitney cube

```
|(∇·D̂_q)(𝔰) − q|²  ≤  (2 · superposedGradConst d)² · 3^{2 b (k + h_k)} · |q|² .
```

The route follows the proved single-mesh one at the superposed input: the
proved summed active-component envelope  at each of the `d` basis loads `e_i`
bounds every coordinate of `u_i = ∇ℓ̂_{e_i}(𝔰) − e_i` by `η =
superposedGradConst d · 3^{b(k+h_k)}` (a coordinate is at most the Euclidean
length, and `|e_i|² = 1`), and `CollarLayerEnvelopeG`'s
`vecNormSq_divergenceDeviation_le` turns that into `(2η)²|q|²`, the `(2d−2)²`
of the `d − 1` surviving terms being cancelled by the `(d−1)⁻¹` of `e.dq`.

As in the `F` leg nothing on the right depends on a component, on a layer of a
component or on the sample: the whole random content is in `havoid`. -/
theorem vecNormSq_superposedCompetitorCellDivergence_sub_le_layerEnvelope
    {M : ABKModel d} {m : ℤ} {b : ℝ} {hs k₀ : ℕ} {omega : Cutoff.CutoffSample d}
    (hd : 2 ≤ d) (hb0 : 0 < b) (hb : b ≤ 1 / 8) (hk₀ : 3 ≤ k₀)
    (havoid : ∀ h : ℕ, hs ≤ h → ∀ u ∈ Percolation.cubeFinset (d := d) h,
      (Percolation.badClusterDiam M m h omega u : ℝ) < (3 : ℝ) ^ (b * (h : ℝ)))
    {S : Set (TriadicCube d)} (hSsub : S ⊆ whitneyPartition m (whitneyScaleSeq b hs k₀))
    (hSbad : ∀ Q ∈ S, omega ∈ BadEvents.bad M Q) (q : Vec d) {k : ℕ}
    {R : TriadicCube d} (hRlay : R ∈ whitneyLayer m (whitneyScaleSeq b hs k₀) k)
    {T : KuhnCell d} (hT : T ∈ whitneySimplexCells m (whitneyScaleSeq b hs k₀) k R) :
    vecNormSq (superposedCompetitorCellDivergence m (whitneyScaleSeq b hs k₀) S q T - q) ≤
      superposedDivConst d ^ 2 *
        (3 : ℝ) ^ (2 * (b * ((k : ℝ) + (whitneyScaleSeq b hs k₀ k : ℝ)))) *
        vecNormSq q := by
  have : NeZero d := ⟨by omega⟩
  set r : ℝ := (3 : ℝ) ^ (b * ((k : ℝ) + (whitneyScaleSeq b hs k₀ k : ℝ))) with hr
  have hr0 : (0 : ℝ) ≤ r := Real.rpow_nonneg (by norm_num) _
  have hrsq : r ^ 2 =
      (3 : ℝ) ^ (2 * (b * ((k : ℝ) + (whitneyScaleSeq b hs k₀ k : ℝ)))) := by
    rw [hr, ← Real.rpow_natCast
        ((3 : ℝ) ^ (b * ((k : ℝ) + (whitneyScaleSeq b hs k₀ k : ℝ)))) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  have hC0 : (0 : ℝ) ≤ superposedGradConst d :=
    le_trans zero_le_one (one_le_superposedGradConst (by omega))
  set eta : ℝ := superposedGradConst d * r with heta
  have heta0 : (0 : ℝ) ≤ eta := mul_nonneg hC0 hr0
  have hu : ∀ i l : Fin d,
      |(superposedCompetitorCellSlope m (whitneyScaleSeq b hs k₀) S (basisVec i) T -
        basisVec i) l| ≤ eta := by
    intro i l
    refine abs_le_of_vecNormSq_le heta0 ?_ l
    have hbase := vecNormSq_superposedCompetitorCellSlope_sub_le_layerEnvelope hb0 hb hk₀
      havoid hSsub hSbad (basisVec i) hRlay hT
    rw [vecNormSq_basisVec, mul_one] at hbase
    refine le_trans hbase (le_of_eq ?_)
    rw [heta, ← hrsq]
    ring
  have hcore := vecNormSq_divergenceDeviation_le hd q
    (fun i => superposedCompetitorCellSlope m (whitneyScaleSeq b hs k₀) S (basisVec i) T -
      basisVec i) hu
  rw [superposedCompetitorCellDivergence_sub_eq hd]
  refine le_trans hcore (le_of_eq ?_)
  rw [superposedDivConst, heta, ← hrsq]
  ring

theorem badFamily_vecNormSq_superposedCompetitorCellDivergence_sub_le_layerEnvelope
    {M : ABKModel d} {m : ℤ} {E b : ℝ} {k₀ : ℕ} {omega : Cutoff.CutoffSample d}
    (hd : 2 ≤ d) (hb0 : 0 < b) (hb : b ≤ 1 / 8) (hk₀ : 3 ≤ k₀)
    (hne : (Percolation.hsepSet M m E b omega).Nonempty) (q : Vec d) {k : ℕ}
    {R : TriadicCube d} (hRlay : R ∈ whitneyLayer m (whitneyScale M m E b k₀ omega) k)
    {T : KuhnCell d}
    (hT : T ∈ whitneySimplexCells m (whitneyScale M m E b k₀ omega) k R) :
    vecNormSq (superposedCompetitorCellDivergence m (whitneyScale M m E b k₀ omega)
        (badFamily M m (whitneyScale M m E b k₀ omega) omega) q T - q) ≤
      superposedDivConst d ^ 2 *
        (3 : ℝ) ^ (2 * (b * ((k : ℝ) + (whitneyScale M m E b k₀ omega k : ℝ)))) *
        vecNormSq q :=
  vecNormSq_superposedCompetitorCellDivergence_sub_le_layerEnvelope hd hb0 hb hk₀
    (fun _ hh _ hu => Percolation.badClusterDiam_lt_of_hsep_le hne hh hu)
    (fun _ hQ => hQ.1) (fun _ hQ => hQ.2) q hRlay hT

end

end Algsuperdiff.Section3.Provider.Affine
