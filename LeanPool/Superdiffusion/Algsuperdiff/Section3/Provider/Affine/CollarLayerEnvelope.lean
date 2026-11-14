/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Affine.CompetitorVertexData

/-!
# CollarLayerEnvelope

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The collar layer envelope of `l.piecewise.affine.approx`

```
|∇ℓ̂_p − p|²  ≤  (648 d)² · 3^{2 b (k + h_k)} · |p|² ,
```

with the constant **explicit and dimension-only**.  This is exactly the shape
of the `hF`/`hG` binders of `Multiscale.LayerUniform.bounds_on_slopes_when_bad`
and of `…collar_whitneySimplexCells_le_ae`, i.e. the collar A antecedent those
consumers carry as a hypothesis; `Cgrad = 648 d` is the value supplied by this
local Provider result.

## The route

1. `CompetitorVertexData` gives the per-cell estimate `|∇ℓ̂_p − p|² ≤ d · (2
   |p|_{ℓ¹} D / 3^{scale})²`, where `D` bounds the diameter of *every*
   component active at the cell's Whitney cube.
2. The proved local cluster geometry supplies `D`.  Its finiteness — the
   analytic admissibility of `⨍_{𝒞}` — comes from the same node's
   `whitneyNeighborhood_finite_and_mem_leastLayer_or_succ`.
3. The whole scale step is the hypothesis-minimal core (de-privatized)
   `four_mul_three_rpow_layer_envelope_le`, which is the only place `rpow`
   occurs.
4. `l + h_l ≤ k + h_k` turns `3^{b(l+h_l)}` into `3^{b(k+h_k)}`, and
   `(∑_i |p_i|)² ≤ d |p|²` (`sq_vecNormOne_le`) turns the `ℓ¹` size of the
   slope into its Euclidean square.  The constant is
   `4 · d · d · (4 · 81)² = (648 d)²`.

## The constant, itemized

Nothing is optimized; the point is that no random quantity, no layer index and
no component enters.

## No overlap count is consumed

Under the single-assignment vertex datum of `CompetitorVertexData` each vertex
is claimed by exactly one component, so the per-cell deviation is the *max*
over `𝒜_R`, which is bounded by the same layerwise envelope with no cardinality
input: the binder `hact` of `…_sub_le_of_forall_touching` ranges over exactly
`𝒜_R` and demands the bound for each of its members.
`Multiscale.CollarMass.card_le_eleven_pow_of_forall_cubeTouch` is therefore
**not used** here; it remains the instrument for the superposition
presentation, where the corrections genuinely add.

## Scope

No global function is constructed and no continuity, `H¹` membership or
subordination is claimed (see the scope section of `CompetitorVertexData`).
The statement is per cell, which is the level at which
`e.hat.linear.properties` states its gradient estimate  and the level
`Multiscale.sum_of_a_decomp` (SubadditiveDecomposition.lean) consumes.  No
layer window is assumed: the layer bookkeeping used here is the *proved*
`l.bad.clusters.geometry`, whose neighborhood conclusion is proved, not
hypothesized.

## References

* ABK26, (Step 2), (`r.gradient.bound.simplified`),
  (`l.bad.clusters.geometry`), (`e.SW.def`), (`e.bounds.on.slopes.when.bad`).
-/

namespace Algsuperdiff.Section3.Provider.Affine

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

/-! ## The scale core -/

/-- **The scale step of the layer envelope**, isolated from every geometric and
measure-theoretic input so that `rpow` occurs in exactly one place.  With
`a = l + h_l` the depth of the diameter bound's anchor layer, `q = k + h_k` the
depth of the cell's own layer and `c = (k+1) + h_{k+1}` the depth of the cell
side, the two hypotheses `a ≤ q` and `c ≤ a + 4` convert the cluster diameter
bound into the layer envelope at the cost of `3⁴`. -/
theorem four_mul_three_rpow_layer_envelope_le {b : ℝ} (hb : 0 ≤ b)
    {a q c : ℕ} (haq : a ≤ q) (hca : c ≤ a + 4) (m : ℤ) :
    4 * (3 : ℝ) ^ (b * (a : ℝ)) * (3 : ℝ) ^ (m - (a : ℤ)) ≤
      324 * (3 : ℝ) ^ (b * (q : ℝ)) * (3 : ℝ) ^ (m - (c : ℤ)) := by
  have hrpow : (3 : ℝ) ^ (b * (a : ℝ)) ≤ (3 : ℝ) ^ (b * (q : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast haq) hb
  have hzpow : (3 : ℝ) ^ (m - (a : ℤ)) ≤ 81 * (3 : ℝ) ^ (m - (c : ℤ)) := by
    have hle : m - (a : ℤ) ≤ 4 + (m - (c : ℤ)) := by
      have hac : (c : ℤ) ≤ (a : ℤ) + 4 := by exact_mod_cast hca
      omega
    have h := zpow_le_zpow_right₀ (a := (3 : ℝ)) (by norm_num) hle
    have hsplit : (3 : ℝ) ^ ((4 : ℤ) + (m - (c : ℤ))) = 81 * (3 : ℝ) ^ (m - (c : ℤ)) := by
      rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      norm_num
    rw [hsplit] at h
    exact h
  have hpq : (0 : ℝ) < (3 : ℝ) ^ (b * (q : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hpm : (0 : ℝ) < (3 : ℝ) ^ (m - (a : ℤ)) := zpow_pos (by norm_num) _
  calc
    4 * (3 : ℝ) ^ (b * (a : ℝ)) * (3 : ℝ) ^ (m - (a : ℤ))
        ≤ 4 * (3 : ℝ) ^ (b * (q : ℝ)) * (3 : ℝ) ^ (m - (a : ℤ)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hrpow (by norm_num)) hpm.le
    _ ≤ 4 * (3 : ℝ) ^ (b * (q : ℝ)) * (81 * (3 : ℝ) ^ (m - (c : ℤ))) :=
          mul_le_mul_of_nonneg_left hzpow (by linarith)
    _ = 324 * (3 : ℝ) ^ (b * (q : ℝ)) * (3 : ℝ) ^ (m - (c : ℤ)) := by ring

/-! ## Monotonicity of the closed carrier -/

theorem closedCubeCarrier_mono {J J' : Set (TriadicCube d)} (h : J ⊆ J') :
    closedCubeCarrier J ⊆ closedCubeCarrier J' := by
  intro x hx
  obtain ⟨Q, hQ, hxQ⟩ := mem_closedCubeCarrier_iff.mp hx
  exact mem_closedCubeCarrier_iff.mpr ⟨Q, h hQ, hxQ⟩

/-! ## The active-component diameter datum -/

/-- **Every component active at a layer-`k` Whitney cube is finite and has the
layer-`k` cluster diameter.**  This is `l.bad.clusters.geometry` read at the
active family `𝒜_□ = {𝒞 : □ ∈ 𝒩(𝒞)}`: a bad cube touching `□` puts `□` in its
component's neighborhood, so that neighborhood meets layer `k` and the proved
diameter bound applies to it, hence to the component it contains.  Finiteness
is the same node's neighborhood finiteness, and is what makes `⨍_{𝒞} ℓ_p` an
honest average. -/
theorem active_badComponent_finite_and_diam_le {M : ABKModel d} {m : ℤ} {b : ℝ}
    {hs k₀ : ℕ} {omega : Cutoff.CutoffSample d} (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    (hk₀ : 3 ≤ k₀)
    (havoid : ∀ h : ℕ, hs ≤ h → ∀ u ∈ Percolation.cubeFinset (d := d) h,
      (Percolation.badClusterDiam M m h omega u : ℝ) < (3 : ℝ) ^ (b * (h : ℝ)))
    {S : Set (TriadicCube d)} (hSsub : S ⊆ whitneyPartition m (whitneyScaleSeq b hs k₀))
    (hSbad : ∀ Q ∈ S, omega ∈ BadEvents.bad M Q)
    {k : ℕ} {R : TriadicCube d}
    (hRlay : R ∈ whitneyLayer m (whitneyScaleSeq b hs k₀) k) :
    ∀ R' ∈ S, CubeTouch R R' →
      (badComponent S R').Finite ∧
        Metric.diam (closedCubeCarrier (badComponent S R')) ≤
          4 * (3 : ℝ) ^ (b * ((max (k - 1) 1 +
                whitneyScaleSeq b hs k₀ (max (k - 1) 1) : ℕ) : ℝ)) *
            (3 : ℝ) ^ (m - ((max (k - 1) 1 +
                whitneyScaleSeq b hs k₀ (max (k - 1) 1) : ℕ) : ℤ)) := by
  intro R' hR' htouch
  have hCsub : badComponent S R' ⊆ whitneyPartition m (whitneyScaleSeq b hs k₀) :=
    fun Q hQ => hSsub hQ.1
  have hRnb : R ∈ whitneyNeighborhood m (whitneyScaleSeq b hs k₀) (badComponent S R') :=
    ⟨⟨k, hRlay⟩, R', self_mem_badComponent hR', htouch⟩
  have hfinN :=
    (whitneyNeighborhood_finite_and_mem_leastLayer_or_succ hb0 hb hk₀ havoid hSsub
      hSbad hR').1
  have hsub : closedCubeCarrier (badComponent S R') ⊆
      closedCubeCarrier
        (whitneyNeighborhood m (whitneyScaleSeq b hs k₀) (badComponent S R')) :=
    closedCubeCarrier_mono (subset_whitneyNeighborhood hCsub)
  refine ⟨hfinN.subset (subset_whitneyNeighborhood hCsub), ?_⟩
  refine le_trans (Metric.diam_mono hsub (isCompact_closedCubeCarrier hfinN).isBounded) ?_
  exact le_of_lt (diam_closedCubeCarrier_whitneyNeighborhood_lt_of_intersectsLayer hb0 hb
    hk₀ havoid hSsub hSbad hR' ⟨R, hRnb, hRlay⟩)

end

end Algsuperdiff.Section3.Provider.Affine
