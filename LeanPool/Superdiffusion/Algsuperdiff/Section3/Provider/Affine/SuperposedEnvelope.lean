/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Affine.ActiveFamily
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Affine.CollarLayerEnvelope

/-!
# SuperposedEnvelope

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The summed collar envelope of the superposed competitor

This module proves a local **summed active-component gradient estimate** for the
superposition presentation of `l.piecewise.affine.approx`.  On a good **collar**
cube nothing identifies the superposed cell slope with the single-mesh
`kuhnSlope ∘ competitorVertexData`, so pricing it needs the summed estimate
together with the dimension-only multiplicity bound `|𝒜_R| ≤ M(d)`.  That bound
is `ActiveFamily.ncard_activeComponents_le`, with `M(d) = 3·11^d`, and this
module performs the aggregation on top of it.

## The summed display, and what is implemented

The correct form of the gradient estimate of `e.hat.linear.properties` — the
printed component-local display is false for the superposed competitor — is

```
  |∇ℓ̂_p − p|  ≤  C(d) |p| ∑_{𝒞 ∈ 𝒜_R} diam(𝒞) / ρ_𝒞 ,
  𝒜_R = {𝒞 : R ∈ 𝒩(𝒞)} ,   ρ_𝒞 = 3^{m−(j_𝒞+1)−h_{j_𝒞+1}} ,
```

with the equivalent restatement: after proving the dimension-only Whitney
overlap bound `|𝒜_R| ≤ M(d)`, one may use the squared form
`|∇ℓ̂_p − p|² ≤ C(d)|p|² ∑_{𝒞 ∈ 𝒜_R} diam(𝒞)²/ρ_𝒞²`.

**That squared form is what is implemented**, in three steps and with every
constant explicit:

1. *the sum itself* — `superposedCompetitorCellSlope_sub_eq_sum` collapses the
   defining `finsum` to a finite sum over any `Finset` containing `𝒜_R`
   (inactive components have cell constant `p`, so they contribute `0`);
2. *one summand* — `vecNormSq_globalCompetitorCellSlope_sub_le_diam` is exactly
   `d (2 |p|_{ℓ¹} diam(𝒞) / ρ_𝒞)²` at the component's **own** common coarse
   cell, with `ρ_𝒞 = componentInterpolationScale` the interpolation scale of
   that component;
3. *the aggregation* — `vecNormSq_sum_le_card_mul_sum_vecNormSq` (finite-vector
   Cauchy--Schwarz, `|∑ v|² ≤ |A| ∑ |v|²`) followed by
   `card_le_multiplicityBound_of_forall_mem_activeComponents`.  This is the
   "after proving `|𝒜_R| ≤ M(d)`" clause; `M(d)` enters **twice**, once from
   Cauchy--Schwarz and once from summing the uniform per-component envelope.

The `L¹` display is the pre-Cauchy--Schwarz form of the same sum and is not
separately stated: the consumers below take squares.

## The layer envelope, and the constant

Feeding the proved local cluster-diameter datum into the summand gives the
per-component layer envelope at the **same** constant as the single-mesh
envelope of `CollarLayerEnvelope.lean`,

```
  |∇ℓ̂_p^𝒞 − p|²  ≤  (648 d)² 3^{2 b (k + h_k)} |p|²    on every cell of a
                                                        layer-`k` Whitney cube,
```

and the aggregation then gives the deliverable

```
  |∇ℓ̂_p − p|²  ≤  (M(d) · 648 d)² 3^{2 b (k + h_k)} |p|² ,
  superposedGradConst d = M(d) · 648 d = 1944 d · 11^d .
```

Itemized: `648 d` is `CollarLayerEnvelope`'s own constant (`2` for the
two-vertex oscillation, one `d` for the Kuhn coordinates, one `d` for the
`ℓ¹`-to-`ℓ²` conversion, `324 = 4·3⁴` for the cluster-diameter bound's factor
`4` times the scale step), and `M(d) = 3·11^d` is
`ActiveFamily.multiplicityBound` (three layers times the cubewise per-layer
packing).  Nothing on the right depends on a component, a layer of a component,
or the sample.  This is the `Cgrad` of `r.gradient.bound.simplified`,
discharged here at `Cgrad = superposedGradConst d` for the superposed
competitor.

## Why the single-mesh endpoint is not instantiated directly

The single-mesh collar layer envelope prices
`kuhnSlope 𝔰 (competitorVertexData ℐ p) − p` at the **final** `e.SW.def` cell
`𝔰` and the **whole** family `ℐ`.  The summand of the superposition is a
different object: the cell constant of one component's correction is
`kuhnSlope U (competitorVertexData 𝒞 p)` at the **coarse root cell** `U` of that
component's own common mesh, whose side is `ρ_𝒞` and not the final cell side.
So the single-mesh *endpoint* is not instantiable here, but its proved local
*route* is: this module reuses the public instruments
(`active_badComponent_finite_and_diam_le`,
`four_mul_three_rpow_layer_envelope_le`, `closedCubeCarrier_mono`) together
with `CompetitorVertexData`'s
`vecNormSq_kuhnSlope_competitorVertexData_sub_le_of_forall_touching`, which is
already stated at an *arbitrary* `descendantsAtScale Q j` and therefore applies
verbatim at the coarse cell.  The diameter datum is the proved local one, at
the single component recovered from its own touching bad cube.

## Scope

The estimate is per cell of `SW(□_m)`, which is the level at which
`e.hat.linear.properties` states its gradient estimate, and the level
`Multiscale.sum_of_a_decomp` consumes.  It is a statement about the **defined**
field `superposedCompetitorSlope`, which
`ActiveFamily.superposedCompetitor_sub_eq_vecDot` identifies as the classical
per-cell gradient; no a.e./weak-gradient identification, no `H¹₀` membership
and no solenoidal leg is claimed here.  The `G`-leg of the superposed branch of
`Multiscale.ConclusionRoot` is the *same* object at the load `q`, so the
deliverable, being stated for every `p : Vec d`, discharges both legs; the
divergence competitor of
`CollarLayerEnvelopeG.lean` is the `G`-leg of the *single-mesh* branch and is
not used here.  No global function, continuity or subordination statement is
made (they are `ActiveFamily.lean`'s).

## Consumer shape

The conclusion is character-for-character the `hFv`/`hGv` binder of

* `Multiscale.ConclusionAssemblyFinal.collarCellForm_le_collarEnvelopeConst_mul_layerQuantity_ae`,
* `Multiscale.ConclusionRoot.tsum_simplexPartition_cutoff_two_leg_le_ofReal_payload_assembled_ae`,
* `Multiscale.LayerUniform.blockVecDot_coarseBlockMatrix_collar_whitneySimplexCells_le_ae`
  and `Multiscale.ConclusionCompetitor.collarCellForm_le_stepOneLayerMajorant_ae`,

namely `vecNormSq (Fv T − p) ≤ Cgrad² 3^{2(b(n+h_n))} vecNormSq p` quantified
over `n`, `Q ∈ 𝒲(□_m,n)` and `T ∈ S(□)`, at `Cgrad := superposedGradConst d`
(`1 ≤ Cgrad` is `one_le_superposedGradConst`).  This module does **not** perform
that composition and closes no node.

## References

* ABK26: `l.piecewise.affine.approx` and `e.hat.linear.properties`; Step 1 with
  the common coarse mesh and its scale `3^{m−(n_j+1)−h_{n_j+1}}`, and Step 2;
  `r.gradient.bound.simplified`; `e.SW.def`; `e.neighborhood.def`;
  `l.bad.clusters.geometry` and `e.cluster.diameter.bound`; `e.hn.gap`;
  `e.bounds.on.slopes.when.bad`.
-/

namespace Algsuperdiff.Section3.Provider.Affine

open HCPolySupport
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

/-! ## The aggregation device -/

/-- **Finite-vector Cauchy--Schwarz**: `|∑_{a ∈ A} v_a|² ≤ |A| ∑_{a ∈ A} |v_a|²`. -/
theorem vecNormSq_sum_le_card_mul_sum_vecNormSq {ι : Type*} (A : Finset ι)
    (v : ι → Vec d) :
    vecNormSq (∑ C ∈ A, v C) ≤ (A.card : ℝ) * ∑ C ∈ A, vecNormSq (v C) := by
  classical
  have hcoord : ∀ i : Fin d, (∑ C ∈ A, v C i) ^ 2 ≤ (A.card : ℝ) * ∑ C ∈ A, v C i ^ 2 :=
    fun i => sq_sum_le_card_mul_sum_sq (s := A) (f := fun C => v C i)
  have hL : vecNormSq (∑ C ∈ A, v C) = ∑ i, (∑ C ∈ A, v C i) ^ 2 := by
    simp only [vecNormSq, vecDot, Finset.sum_apply, pow_two]
  have hR : ∀ C : ι, vecNormSq (v C) = ∑ i, v C i ^ 2 := by
    intro C
    simp only [vecNormSq, vecDot, pow_two]
  calc
    vecNormSq (∑ C ∈ A, v C) = ∑ i, (∑ C ∈ A, v C i) ^ 2 := hL
    _ ≤ ∑ i, (A.card : ℝ) * ∑ C ∈ A, v C i ^ 2 := Finset.sum_le_sum fun i _ => hcoord i
    _ = (A.card : ℝ) * ∑ i, ∑ C ∈ A, v C i ^ 2 := by rw [Finset.mul_sum]
    _ = (A.card : ℝ) * ∑ C ∈ A, ∑ i, v C i ^ 2 := by rw [Finset.sum_comm]
    _ = (A.card : ℝ) * ∑ C ∈ A, vecNormSq (v C) :=
        congrArg _ (Finset.sum_congr rfl fun C _ => (hR C).symm)

/-! ## The interpolation scale `ρ_𝒞` -/

/-- **`ρ_𝒞 = 3^{m−(j_𝒞+1)−h_{j_𝒞+1}}`**: the side of the common coarse mesh on
which the correction belonging to the component `𝒞` is interpolated, with `j_𝒞`
the least Whitney layer met by `𝒩(𝒞)` (represented by
`componentWindowLayer`). -/
def componentInterpolationScale (m : ℤ) (hn : ℕ → ℕ) (C : Set (TriadicCube d)) : ℝ :=
  (3 : ℝ) ^ simplexScale m hn (componentWindowLayer m hn C)

/-! ## The cell slope of the superposition is a finite sum over `𝒜_R` -/

private theorem finsum_badComponents_eq_sum {β : Type*} [AddCommMonoid β]
    {I : Set (TriadicCube d)} (f : Set (TriadicCube d) → β)
    {A : Finset (Set (TriadicCube d))} (hA : ∀ C ∈ A, C ∈ badComponents I)
    (hzero : ∀ C ∈ badComponents I, C ∉ A → f C = 0) :
    ∑ᶠ C ∈ badComponents I, f C = ∑ C ∈ A, f C := by
  refine finsum_mem_eq_sum_of_inter_support_eq f ?_
  ext C
  constructor
  · rintro ⟨hC, hsupp⟩
    exact ⟨Finset.mem_coe.2 (by by_contra hcon; exact hsupp (hzero C hC hcon)), hsupp⟩
  · rintro ⟨hC, hsupp⟩
    exact ⟨hA C (Finset.mem_coe.mp hC), hsupp⟩

/-- **The superposed cell slope is `p` plus a finite sum over the active
components** ('s `𝒜_R`).  Any finite family `A` of components containing `𝒜_R`
may be used: a component inactive at the cell's Whitney cube has cell constant
`p` and contributes `0` (clause 3 of `e.hat.linear.properties`).  This
exports, publicly, the collapse proved inside
`ActiveFamily.superposedCompetitor_sub_eq_vecDot`. -/
theorem superposedCompetitorCellSlope_sub_eq_sum [NeZero d] {m : ℤ} {hn : ℕ → ℕ}
    (hmono : Monotone hn) {I : Set (TriadicCube d)} (hI : I ⊆ whitneyPartition m hn)
    (hwin : ∀ C ∈ badComponents I, (whitneyNeighborhood m hn C).Finite ∧
      ∀ R ∈ whitneyNeighborhood m hn C,
        R ∈ whitneyLayer m hn (componentWindowLayer m hn C) ∨
          R ∈ whitneyLayer m hn (componentWindowLayer m hn C + 1))
    (p : Vec d) {n : ℕ} {Q : TriadicCube d} (hQ : Q ∈ whitneyLayer m hn n)
    {T : KuhnCell d} (hT : T ∈ whitneySimplexCells m hn n Q)
    {A : Finset (Set (TriadicCube d))} (hAsub : ∀ C ∈ A, C ∈ badComponents I)
    (hAact : ∀ C ∈ activeComponents m hn I Q, C ∈ A) :
    superposedCompetitorCellSlope m hn I p T - p =
      ∑ C ∈ A, (globalCompetitorCellSlope m
        (simplexScale m hn (componentWindowLayer m hn C)) C p T - p) := by
  classical
  rw [superposedCompetitorCellSlope_eq_sum, add_sub_cancel_left]
  exact finsum_badComponents_eq_sum _ hAsub fun C hC hCnot => by
    rw [globalCompetitorCellSlope_eq_of_notMem_activeComponents hmono hI hwin p hQ hT hC
      (fun hmem => hCnot (hAact C hmem))]
    exact sub_self _

/-! ## One summand: a single component, at its own scale `ρ_𝒞` -/

/-- **An active component is finite** — it sits inside its own touching
neighborhood, which the proved cluster geometry makes finite. -/
theorem finite_of_mem_activeComponents {m : ℤ} {hn : ℕ → ℕ} {I : Set (TriadicCube d)}
    (hI : I ⊆ whitneyPartition m hn)
    (hwin : ∀ C ∈ badComponents I, (whitneyNeighborhood m hn C).Finite ∧
      ∀ R ∈ whitneyNeighborhood m hn C,
        R ∈ whitneyLayer m hn (componentWindowLayer m hn C) ∨
          R ∈ whitneyLayer m hn (componentWindowLayer m hn C + 1))
    {Q : TriadicCube d} {C : Set (TriadicCube d)}
    (hC : C ∈ activeComponents m hn I Q) : C.Finite :=
  (hwin C hC.1).1.subset (subset_whitneyNeighborhood ((badComponents_subset hC.1).trans hI))

/-- **An active component is the component of one of its own bad cubes touching
`R`** — the maximality fact isolates, in the form that hands the proved local
diameter datum to a single component. -/
theorem exists_mem_cubeTouch_badComponent_eq_of_mem_activeComponents {m : ℤ} {hn : ℕ → ℕ}
    {I : Set (TriadicCube d)} {R : TriadicCube d} {C : Set (TriadicCube d)}
    (hC : C ∈ activeComponents m hn I R) :
    ∃ B ∈ I, CubeTouch R B ∧ badComponent I B = C := by
  obtain ⟨⟨Q₀, hQ₀, rfl⟩, -, B, hBC, htouch⟩ := hC
  exact ⟨B, hBC.1, htouch, (badComponent_eq_of_badChain hBC.2).symm⟩

/-- **The summand's corrected estimate**: the cell constant of one component's
correction deviates from `p` by at most `d (2 |p|_{ℓ¹} diam(𝒞) / ρ_𝒞)²` in
squared Euclidean norm, on every cell of every Whitney cube at which the
component is active.

This is Step 2 of `l.piecewise.affine.approx` read at the component's own
common coarse mesh: the final `e.SW.def` cell sits inside a single cell `U` of
that mesh, `U` has side `ρ_𝒞`, and the Step-2 vertex bound applies at `U`
because `U` is a triadic descendant of the Whitney cube. -/
theorem vecNormSq_globalCompetitorCellSlope_sub_le_diam [NeZero d] {m : ℤ} {hn : ℕ → ℕ}
    (hmono : Monotone hn) {I : Set (TriadicCube d)} (hI : I ⊆ whitneyPartition m hn)
    (hwin : ∀ C ∈ badComponents I, (whitneyNeighborhood m hn C).Finite ∧
      ∀ R ∈ whitneyNeighborhood m hn C,
        R ∈ whitneyLayer m hn (componentWindowLayer m hn C) ∨
          R ∈ whitneyLayer m hn (componentWindowLayer m hn C + 1))
    (p : Vec d) {n : ℕ} {Q : TriadicCube d} (hQ : Q ∈ whitneyLayer m hn n)
    {T : KuhnCell d} (hT : T ∈ whitneySimplexCells m hn n Q)
    {C : Set (TriadicCube d)} (hC : C ∈ activeComponents m hn I Q)
    {D : ℝ} (hD0 : 0 ≤ D) (hCdiam : Metric.diam (closedCubeCarrier C) ≤ D) :
    vecNormSq (globalCompetitorCellSlope m
        (simplexScale m hn (componentWindowLayer m hn C)) C p T - p) ≤
      (d : ℝ) * (2 * (vecNormOne p * D) / componentInterpolationScale m hn C) ^ 2 := by
  classical
  have hCbad : C ∈ badComponents I := hC.1
  have hCfin : C.Finite := finite_of_mem_activeComponents hI hwin hC
  have hwindow : n = componentWindowLayer m hn C ∨ n = componentWindowLayer m hn C + 1 := by
    rcases (hwin C hCbad).2 Q hC.2 with h | h
    · exact Or.inl (whitneyLayer_index_unique hmono hQ h)
    · exact Or.inr (whitneyLayer_index_unique hmono hQ h)
  have hsQ : simplexScale m hn (componentWindowLayer m hn C) ≤ Q.scale := by
    rcases hwindow with h | h
    · rw [← h]
      exact simplexScale_le_scale_of_mem_whitneyLayer (step_of_monotone hmono n) hQ
    · rw [scale_eq_of_mem_whitneyLayer hQ, h, simplexScale]
      omega
  have hns : simplexScale m hn n ≤ simplexScale m hn (componentWindowLayer m hn C) := by
    rcases hwindow with h | h
    · rw [h]
    · rw [h]
      exact simplexScale_succ_le m (step_of_monotone hmono (componentWindowLayer m hn C + 1))
  have hsm : simplexScale m hn (componentWindowLayer m hn C) ≤ m :=
    simplexScale_le_self m hn _
  obtain ⟨U, hU, hTU⟩ := exists_rootCell_openCarrier_subset (step_of_monotone hmono) hns hQ hT
  have hinner : Multiscale.kuhnCellInteriorPoint T ∈ T.openCarrier :=
    Multiscale.kuhnCellInteriorPoint_mem_openCarrier T
  have hslope : globalCompetitorCellSlope m
      (simplexScale m hn (componentWindowLayer m hn C)) C p T =
      kuhnSlope U (competitorVertexData C p) :=
    globalCompetitorSlope_of_mem_openCarrier hsm C p hU (hTU hinner)
  have hUQ : U.supportCube ∈
      descendantsAtScale Q (simplexScale m hn (componentWindowLayer m hn C)) :=
    mem_descendantsAtScale_of_cubeSet_inter_nonempty ⟨n, hQ⟩
      (mem_rootCoarseMesh_iff.mp hU) hsQ
      ⟨Multiscale.kuhnCellInteriorPoint T,
        carrier_subset_cubeSet_of_mem_whitneySimplexCells hT
          (T.openCarrier_subset_carrier hinner),
        openCubeSet_subset_cubeSet _ (U.openCarrier_subset_openCubeSet (hTU hinner))⟩
  have hact : ∀ R' ∈ C, CubeTouch Q R' →
      (badComponent C R').Finite ∧
        Metric.diam (closedCubeCarrier (badComponent C R')) ≤ D := fun _ _ _ =>
    ⟨hCfin.subset fun _ hS => hS.1,
      le_trans (Metric.diam_mono (closedCubeCarrier_mono fun _ hS => hS.1)
        (isCompact_closedCubeCarrier hCfin).isBounded) hCdiam⟩
  have hbase := vecNormSq_kuhnSlope_competitorVertexData_sub_le_of_forall_touching
    (I := C) (Q := Q) (p := p) hD0 hact hUQ
  have hscale : cubeScaleFactor U.supportCube = componentInterpolationScale m hn C := by
    show (3 : ℝ) ^ U.supportCube.scale =
      (3 : ℝ) ^ simplexScale m hn (componentWindowLayer m hn C)
    rw [supportCube_scale_eq_of_mem_rootCoarseMesh hsm hU]
  rw [hslope, ← hscale]
  exact hbase

/-! ## The per-component layer envelope -/

/-- The scale bookkeeping of the per-component envelope, isolated as pure
arithmetic on `ℕ`. -/
private theorem window_scale_index_le {hn : ℕ → ℕ} (hmono : Monotone hn)
    (hstep : ∀ j : ℕ, hn (j + 1) ≤ hn j + 1) {k j : ℕ} (hk1 : 1 ≤ k)
    (hkj : k = j ∨ k = j + 1) :
    (j + 1) + hn (j + 1) ≤ (max (k - 1) 1 + hn (max (k - 1) 1)) + 4 ∧
      max (k - 1) 1 + hn (max (k - 1) 1) ≤ k + hn k := by
  have hlk : max (k - 1) 1 ≤ k := by omega
  have hml : hn (max (k - 1) 1) ≤ hn k := hmono hlk
  have hje : j + 1 = k + 1 ∨ j + 1 = k := by
    rcases hkj with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr h.symm
  refine ⟨?_, by omega⟩
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have hkval : k = 1 := by omega
    have hl : max (k - 1) 1 = 1 := by omega
    rw [hl]
    have h1 := hstep 1
    rcases hje with h | h <;> rw [h, hkval] <;> omega
  · have hl : max (k - 1) 1 = k - 1 := by omega
    rw [hl]
    have h1 := hstep k
    have h2 := hstep (k - 1)
    rw [show k - 1 + 1 = k from by omega] at h2
    rcases hje with h | h <;> rw [h] <;> omega

/-- The conversion of the Step-2 ratio bound into the layer envelope, isolated
from every geometric input.  It is the tail of `CollarLayerEnvelope`'s own
argument: `(∑_i |p_i|)² ≤ d |p|²` turns the `ℓ¹` size of the slope into its
Euclidean square, and the constant is `4 · d · d · 324² = (648 d)²`. -/
private theorem envelope_of_ratio {D r : ℝ} (hD0 : 0 ≤ D) (hr : 0 < r) (p : Vec d)
    {X : Vec d} {b q : ℝ}
    (hbase : vecNormSq X ≤ (d : ℝ) * (2 * (vecNormOne p * D) / r) ^ 2)
    (hratio : D / r ≤ 324 * (3 : ℝ) ^ (b * q)) :
    vecNormSq X ≤ (648 * (d : ℝ)) ^ 2 * (3 : ℝ) ^ (2 * (b * q)) * vecNormSq p := by
  have hn1 : 0 ≤ vecNormOne p := vecNormOne_nonneg p
  have hrewrite : 2 * (vecNormOne p * D) / r = 2 * vecNormOne p * (D / r) := by
    field_simp
  have hsq : (2 * vecNormOne p * (D / r)) ^ 2 ≤
      (2 * vecNormOne p * (324 * (3 : ℝ) ^ (b * q))) ^ 2 := by
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    exact mul_le_mul_of_nonneg_left hratio (by linarith)
  have hcs : vecNormOne p ^ 2 ≤ (d : ℝ) * vecNormSq p := sq_vecNormOne_le p
  have hrq : ((3 : ℝ) ^ (b * q)) ^ 2 = (3 : ℝ) ^ (2 * (b * q)) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (b * q)) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  rw [hrewrite] at hbase
  calc
    vecNormSq X ≤ (d : ℝ) * (2 * vecNormOne p * (D / r)) ^ 2 := hbase
    _ ≤ (d : ℝ) * (2 * vecNormOne p * (324 * (3 : ℝ) ^ (b * q))) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hd0
    _ = (d : ℝ) * (419904 * vecNormOne p ^ 2 * ((3 : ℝ) ^ (b * q)) ^ 2) := by ring
    _ ≤ (d : ℝ) * (419904 * ((d : ℝ) * vecNormSq p) * ((3 : ℝ) ^ (b * q)) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hd0
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcs (by norm_num : (0 : ℝ) ≤ 419904)) (sq_nonneg _)
    _ = (648 * (d : ℝ)) ^ 2 * (3 : ℝ) ^ (2 * (b * q)) * vecNormSq p := by
        rw [← hrq]; ring

/-- **The layer envelope of ONE component's correction**: on every cell of a
layer-`k` Whitney cube at which the component `𝒞` is active,

```
  |∇ℓ̂_p^𝒞 − p|²  ≤  (648 d)² 3^{2 b (k + h_k)} |p|² .
```

This is's summand with the proved local cluster diameter inserted: `diam(𝒞) ≤
4·3^{b(l+h_l)}3^{m−l−h_l}` (`l.bad.clusters.geometry`(2)'s factor `4`, via
`active_badComponent_finite_and_diam_le` at the component recovered from its
own touching bad cube), divided by `ρ_𝒞 = 3^{m−(j_𝒞+1)−h_{j_𝒞+1}}`.  The
constant is the same `648 d` as the single-mesh local envelope; the window
binder is discharged, not assumed. -/
theorem vecNormSq_globalCompetitorCellSlope_sub_le_layerEnvelope [NeZero d]
    {M : ABKModel d} {m : ℤ} {b : ℝ} {hs k₀ : ℕ} {omega : Cutoff.CutoffSample d}
    (hb0 : 0 < b) (hb : b ≤ 1 / 8) (hk₀ : 3 ≤ k₀)
    (havoid : ∀ h : ℕ, hs ≤ h → ∀ u ∈ Percolation.cubeFinset (d := d) h,
      (Percolation.badClusterDiam M m h omega u : ℝ) < (3 : ℝ) ^ (b * (h : ℝ)))
    {S : Set (TriadicCube d)} (hSsub : S ⊆ whitneyPartition m (whitneyScaleSeq b hs k₀))
    (hSbad : ∀ Q ∈ S, omega ∈ BadEvents.bad M Q) (p : Vec d) {k : ℕ}
    {R : TriadicCube d} (hRlay : R ∈ whitneyLayer m (whitneyScaleSeq b hs k₀) k)
    {T : KuhnCell d} (hT : T ∈ whitneySimplexCells m (whitneyScaleSeq b hs k₀) k R)
    {C : Set (TriadicCube d)}
    (hC : C ∈ activeComponents m (whitneyScaleSeq b hs k₀) S R) :
    vecNormSq (globalCompetitorCellSlope m
        (simplexScale m (whitneyScaleSeq b hs k₀)
          (componentWindowLayer m (whitneyScaleSeq b hs k₀) C)) C p T - p) ≤
      (648 * (d : ℝ)) ^ 2 *
        (3 : ℝ) ^ (2 * (b * ((k : ℝ) + (whitneyScaleSeq b hs k₀ k : ℝ)))) *
        vecNormSq p := by
  classical
  set hn : ℕ → ℕ := whitneyScaleSeq b hs k₀ with hhn
  have hmono : Monotone hn := whitneyScaleSeq_mono hb0.le (by linarith) hs k₀
  have hstep : ∀ j : ℕ, hn (j + 1) ≤ hn j + 1 := fun j =>
    whitneyScaleSeq_succ_le hb0 hb hs k₀ j
  have hwin := badComponents_window hb0 hb hk₀ havoid hSsub hSbad
  have hk1 : 1 ≤ k := one_le_of_mem_whitneyLayer hRlay
  -- the two-layer window of the component
  have hwindow : k = componentWindowLayer m hn C ∨ k = componentWindowLayer m hn C + 1 := by
    rcases (hwin C hC.1).2 R hC.2 with h | h
    · exact Or.inl (whitneyLayer_index_unique hmono hRlay h)
    · exact Or.inr (whitneyLayer_index_unique hmono hRlay h)
  obtain ⟨hca, haq⟩ := window_scale_index_le hmono hstep hk1 hwindow
  -- the proved local diameter datum, at this component
  obtain ⟨B, hB, htouch, hBC⟩ :=
    exists_mem_cubeTouch_badComponent_eq_of_mem_activeComponents hC
  obtain ⟨-, hdiam⟩ :=
    active_badComponent_finite_and_diam_le hb0 hb hk₀ havoid hSsub hSbad hRlay B hB htouch
  rw [hBC] at hdiam
  set l : ℕ := max (k - 1) 1 with hl
  set a : ℕ := l + hn l with ha
  set c : ℕ := componentWindowLayer m hn C + 1 + hn (componentWindowLayer m hn C + 1) with hc
  set D : ℝ := 4 * (3 : ℝ) ^ (b * (a : ℝ)) * (3 : ℝ) ^ (m - (a : ℤ)) with hD
  have hD0 : 0 ≤ D := by
    have h1 : (0 : ℝ) < (3 : ℝ) ^ (b * (a : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    have h2 : (0 : ℝ) < (3 : ℝ) ^ (m - (a : ℤ)) := zpow_pos (by norm_num) _
    rw [hD]
    exact le_of_lt (mul_pos (mul_pos (by norm_num) h1) h2)
  have hbase := vecNormSq_globalCompetitorCellSlope_sub_le_diam hmono hSsub hwin p hRlay hT
    hC hD0 hdiam
  -- the interpolation scale, in the `3^{m−c}` form the scale core consumes
  have hrho : componentInterpolationScale m hn C = (3 : ℝ) ^ (m - (c : ℤ)) := by
    show (3 : ℝ) ^ simplexScale m hn (componentWindowLayer m hn C) = _
    rw [simplexScale, hc]
    congr 1
    push_cast
    ring
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (m - (c : ℤ)) := zpow_pos (by norm_num) _
  have hratio : D / (3 : ℝ) ^ (m - (c : ℤ)) ≤ 324 * (3 : ℝ) ^ (b * ((k + hn k : ℕ) : ℝ)) := by
    rw [div_le_iff₀ hpos, hD]
    exact four_mul_three_rpow_layer_envelope_le hb0.le haq hca m
  rw [hrho] at hbase
  have hcast : ((k + hn k : ℕ) : ℝ) = (k : ℝ) + (hn k : ℝ) := by push_cast; ring
  rw [hcast] at hratio
  exact envelope_of_ratio hD0 hpos p hbase hratio

/-! ## The deliverable: the layer envelope of the superposed competitor -/

/-- It is the `Cgrad` of `r.gradient.bound.simplified` for the superposed
competitor. -/
def superposedGradConst (d : ℕ) : ℝ := (multiplicityBound d : ℝ) * (648 * (d : ℝ))

theorem superposedGradConst_eq (d : ℕ) :
    superposedGradConst d = 1944 * (d : ℝ) * 11 ^ d := by
  rw [superposedGradConst, multiplicityBound]
  push_cast
  ring

theorem one_le_superposedGradConst {d : ℕ} (hd : 1 ≤ d) : 1 ≤ superposedGradConst d := by
  rw [superposedGradConst_eq]
  have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h2 : (1 : ℝ) ≤ (11 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  nlinarith

/-- **'s summed active-component estimate, in the layer-envelope form the collar A
consumes** — the deliverable of this module and the bridge that
`Multiscale.ConclusionRoot`'s F-1 leaves open.  On every cell of every
layer-`k` Whitney cube,

```
  |∇ℓ̂_p − p|²  ≤  (M(d) · 648 d)² 3^{2 b (k + h_k)} |p|² ,
```

for the **superposed** competitor `ℓ̂_p = ℓ_p + Σ_𝒞 (ℓ̂_p^𝒞 − ℓ_p)`'s
overlap-safe presentation.  The multiplicity `M(d)` enters twice — once through
Cauchy--Schwarz, once through summing the uniform per-component envelope —
which is exactly's requirement that the overlap multiplicity be paid "in the
gradient and energy constants".

Nothing on the right depends on a component, on a layer of a component or on the
sample: the whole random content sits in the binder `havoid`, the deterministic
diameter-avoidance datum the cluster node already runs on.  The window binder
`hwin` of the superposition chain is discharged here, not assumed. -/
theorem vecNormSq_superposedCompetitorCellSlope_sub_le_layerEnvelope [NeZero d]
    {M : ABKModel d} {m : ℤ} {b : ℝ} {hs k₀ : ℕ} {omega : Cutoff.CutoffSample d}
    (hb0 : 0 < b) (hb : b ≤ 1 / 8) (hk₀ : 3 ≤ k₀)
    (havoid : ∀ h : ℕ, hs ≤ h → ∀ u ∈ Percolation.cubeFinset (d := d) h,
      (Percolation.badClusterDiam M m h omega u : ℝ) < (3 : ℝ) ^ (b * (h : ℝ)))
    {S : Set (TriadicCube d)} (hSsub : S ⊆ whitneyPartition m (whitneyScaleSeq b hs k₀))
    (hSbad : ∀ Q ∈ S, omega ∈ BadEvents.bad M Q) (p : Vec d) {k : ℕ}
    {R : TriadicCube d} (hRlay : R ∈ whitneyLayer m (whitneyScaleSeq b hs k₀) k)
    {T : KuhnCell d} (hT : T ∈ whitneySimplexCells m (whitneyScaleSeq b hs k₀) k R) :
    vecNormSq (superposedCompetitorCellSlope m (whitneyScaleSeq b hs k₀) S p T - p) ≤
      superposedGradConst d ^ 2 *
        (3 : ℝ) ^ (2 * (b * ((k : ℝ) + (whitneyScaleSeq b hs k₀ k : ℝ)))) *
        vecNormSq p := by
  classical
  have hn1 : ∀ j, 1 ≤ whitneyScaleSeq b hs k₀ j := fun j => by
    have := add_le_whitneyScaleSeq b hs k₀ j
    omega
  have hmono : Monotone (whitneyScaleSeq b hs k₀) :=
    whitneyScaleSeq_mono hb0.le (by linarith) hs k₀
  have hgap : ∀ j, whitneyScaleSeq b hs k₀ (j + 1) ≤ whitneyScaleSeq b hs k₀ j + 1 :=
    fun j => whitneyScaleSeq_succ_le hb0 hb hs k₀ j
  have hwin := badComponents_window hb0 hb hk₀ havoid hSsub hSbad
  have hfin := activeComponents_finite hn1 hSsub hRlay
  have hAmem : ∀ C : Set (TriadicCube d),
      C ∈ hfin.toFinset ↔ C ∈ activeComponents m (whitneyScaleSeq b hs k₀) S R := fun C =>
    Set.Finite.mem_toFinset hfin
  have hcard : ((hfin.toFinset).card : ℝ) ≤ (multiplicityBound d : ℝ) := by
    exact_mod_cast card_le_multiplicityBound_of_forall_mem_activeComponents hn1 hmono hgap
      hSsub hRlay (fun C hC => (hAmem C).mp hC)
  set X : ℝ := (648 * (d : ℝ)) ^ 2 *
    (3 : ℝ) ^ (2 * (b * ((k : ℝ) + (whitneyScaleSeq b hs k₀ k : ℝ)))) * vecNormSq p with hX
  have hX0 : 0 ≤ X := by
    rw [hX]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by norm_num) _))
      (vecNormSq_nonneg p)
  have hterm : ∀ C ∈ hfin.toFinset,
      vecNormSq (globalCompetitorCellSlope m
        (simplexScale m (whitneyScaleSeq b hs k₀)
          (componentWindowLayer m (whitneyScaleSeq b hs k₀) C)) C p T - p) ≤ X := fun C hC =>
    vecNormSq_globalCompetitorCellSlope_sub_le_layerEnvelope hb0 hb hk₀ havoid hSsub hSbad p
      hRlay hT ((hAmem C).mp hC)
  have hsum : ∑ C ∈ hfin.toFinset,
      vecNormSq (globalCompetitorCellSlope m
        (simplexScale m (whitneyScaleSeq b hs k₀)
          (componentWindowLayer m (whitneyScaleSeq b hs k₀) C)) C p T - p) ≤
      ((hfin.toFinset).card : ℝ) * X := by
    calc
      ∑ C ∈ hfin.toFinset, vecNormSq (globalCompetitorCellSlope m
          (simplexScale m (whitneyScaleSeq b hs k₀)
            (componentWindowLayer m (whitneyScaleSeq b hs k₀) C)) C p T - p)
          ≤ ∑ _C ∈ hfin.toFinset, X := Finset.sum_le_sum hterm
      _ = ((hfin.toFinset).card : ℝ) * X := by rw [Finset.sum_const, nsmul_eq_mul]
  have hM0 : (0 : ℝ) ≤ (multiplicityBound d : ℝ) := Nat.cast_nonneg _
  rw [superposedCompetitorCellSlope_sub_eq_sum hmono hSsub hwin p hRlay hT
    (fun C hC => ((hAmem C).mp hC).1) (fun C hC => (hAmem C).mpr hC)]
  calc
    vecNormSq (∑ C ∈ hfin.toFinset, (globalCompetitorCellSlope m
          (simplexScale m (whitneyScaleSeq b hs k₀)
            (componentWindowLayer m (whitneyScaleSeq b hs k₀) C)) C p T - p))
        ≤ ((hfin.toFinset).card : ℝ) *
            ∑ C ∈ hfin.toFinset, vecNormSq (globalCompetitorCellSlope m
              (simplexScale m (whitneyScaleSeq b hs k₀)
                (componentWindowLayer m (whitneyScaleSeq b hs k₀) C)) C p T - p) :=
          vecNormSq_sum_le_card_mul_sum_vecNormSq _ _
    _ ≤ ((hfin.toFinset).card : ℝ) * (((hfin.toFinset).card : ℝ) * X) :=
          mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ ≤ (multiplicityBound d : ℝ) * (((hfin.toFinset).card : ℝ) * X) :=
          mul_le_mul_of_nonneg_right hcard (mul_nonneg (Nat.cast_nonneg _) hX0)
    _ ≤ (multiplicityBound d : ℝ) * ((multiplicityBound d : ℝ) * X) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hX0) hM0
    _ = superposedGradConst d ^ 2 *
          (3 : ℝ) ^ (2 * (b * ((k : ℝ) + (whitneyScaleSeq b hs k₀ k : ℝ)))) *
          vecNormSq p := by
          rw [superposedGradConst, hX]
          ring

/-- **The deliverable at the manuscript's own bad family and profile** `ℐ =
badFamily M m h_n omega`, `h_n = whitneyScale M m E b k₀ omega`, with the
avoidance binder discharged by the proved `e.diameter.deterministic`, exactly
as in the proved single-mesh envelope's own concrete corollary.  Applied at the
load `q` this is also the `G`-leg of the superposed branch of
`Multiscale.ConclusionRoot`. -/
theorem badFamily_vecNormSq_superposedCompetitorCellSlope_sub_le_layerEnvelope [NeZero d]
    {M : ABKModel d} {m : ℤ} {E b : ℝ} {k₀ : ℕ} {omega : Cutoff.CutoffSample d}
    (hb0 : 0 < b) (hb : b ≤ 1 / 8) (hk₀ : 3 ≤ k₀)
    (hne : (Percolation.hsepSet M m E b omega).Nonempty) (p : Vec d) {k : ℕ}
    {R : TriadicCube d} (hRlay : R ∈ whitneyLayer m (whitneyScale M m E b k₀ omega) k)
    {T : KuhnCell d}
    (hT : T ∈ whitneySimplexCells m (whitneyScale M m E b k₀ omega) k R) :
    vecNormSq (superposedCompetitorCellSlope m (whitneyScale M m E b k₀ omega)
        (badFamily M m (whitneyScale M m E b k₀ omega) omega) p T - p) ≤
      superposedGradConst d ^ 2 *
        (3 : ℝ) ^ (2 * (b * ((k : ℝ) + (whitneyScale M m E b k₀ omega k : ℝ)))) *
        vecNormSq p :=
  vecNormSq_superposedCompetitorCellSlope_sub_le_layerEnvelope hb0 hb hk₀
    (fun _ hh _ hu => Percolation.badClusterDiam_lt_of_hsep_le hne hh hu)
    (fun _ hQ => hQ.1) (fun _ hQ => hQ.2) p hRlay hT

end

end Algsuperdiff.Section3.Provider.Affine
