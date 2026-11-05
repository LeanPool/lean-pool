/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenEnvelopeInputGrid

/-!
# GammaTenInteriorFamily

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Besov envelope of Step 2 on an arbitrary sub-mesh

ABK26, Step 2 of `l.approximate.recurrence.formula`,
`e.lower.bound.oscillations`.

## Why the proved grid device is not enough

The envelope device of `Closure.GammaTenEnvelopeInputGrid` is set up on the
**full** mesh `descendantsAtDepth Q j`, so its per-depth input `D i` is the
**full**-mesh grid fourth moment of the oscillation cells at depth `i`.  The
depth-indexed endpoints of
`Closure.GammaTenDepthOscillation` are stated on the *interior* mesh
`interiorMesoCubeGrid d K (nmesh - i) (m - h - 1)`, the carrier, and --- as
that module records --- the boundary-strip transfer of
`LocalizationOscillationFullMesh` does **not** survive the depth index: the
missing fraction `d 3^{(m-h)-K}` is the same at every depth, while the Besov
tower's own weights `2^{i+1} 3^{4 s i}` grow geometrically, so a
depth-independent remainder is not summable.

This module removes that obstruction by running the *same* envelope device on
an **arbitrary sub-family** `I` of the mesh.  Nothing analytic changes: the
proved `exists_grid_pathwise_envelope_of_monotone` is already stated at an
arbitrary `Finset (TriadicCube d)`; what has to be redone is only the **fold**,
because the proved fold identifies `avsum_{R in mesh} avsum_{R' in desc(R,i)}`
with the refined mesh average through
`descendantsAverage_add_eq_descendantsAverage_descendantsAverage`, an identity
that holds for the full mesh only.

The replacement is the finite combinatorics of this module: the depth-`i`
descendant families of *distinct* cells of a common mesh are disjoint
(`disjoint_descendantsAtDepth_of_ne`), so for a nonnegative cell functional the
sub-family's iterated sum is dominated by any grid `T` containing all those
descendants (`sum_descendantsAtDepth_le_of_subset`), at the explicit cardinality
cost `|T| / (|I| 3^{d i})` (`cubeFamilyAverage_descendantsAverage_le`).  On the
interior mesh that cost is `1 / (1 - boundary fraction)`, i.e. below `2` under
the recurrence's own large-cube gate, and it is carried in the statement.

## What is proved

* `disjoint_descendantsAtDepth_of_ne` --- distinct cells of a common mesh have
  disjoint depth-`i` descendant families.
* `sum_descendantsAtDepth_le_of_subset` --- the iterated sum over a sub-family is
  below the sum over any grid containing the descendants.
* `cubeFamilyAverage_descendantsAverage_le` --- the same with the two averages
  normalized, with the cardinality ratio explicit.
* `cubeFamilyAverage_integral_pow_four_oscMajorant_le_family` --- **the fold at an
  arbitrary sub-family**: the sub-family average of the fourth moment of
  `Closure.GammaTenEnvelopeInputGrid.oscMajorant`, bounded by the weighted sum
  over depths of per-depth inputs read at the sub-family itself.
* `integrable_pow_four_oscMajorant_family` --- the fourth power of the majorant is
  integrable at every cell of the sub-family.
* `exists_besovEnvelope_of_family_depth_oscillation` --- **the composite**: the
  envelope on the sub-family, from per-depth sub-family oscillation moments alone.

## Binders

Measurability and fourth-power integrability of the oscillation cells at the
descendants of the sub-family's cells, the `L^2` membership of the field there,
the common scale of the sub-family and the per-depth bounds.  No smallness gate,
no geometry beyond the triadic mesh, and nothing about the corrector or the
coefficient field occurs.

## Scope

Internal Provider infrastructure for the Step-2 fluctuation estimate.  There is
no `sorry`, no `admit`, no custom axiom and no `set_option maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2,
  `e.lower.bound.oscillations`, `e.nablaw.oscillations`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]

/-! ## Disjointness of the descendant families of a common mesh -/

/-- **Distinct cells of a common mesh have disjoint descendant families.**  Two
distinct cells of `descendantsAtDepth Q j` have disjoint open cubes, and a cube
is contained in the open cube of each of its ancestors, so a common descendant
would have empty open cube.  Unconditional. -/
theorem disjoint_descendantsAtDepth_of_ne {Q R S : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (hS : S ∈ descendantsAtDepth Q j) (hne : R ≠ S)
    (i : ℕ) : Disjoint (descendantsAtDepth R i) (descendantsAtDepth S i) := by
  classical
  refine Finset.disjoint_left.mpr fun T hTR hTS => ?_
  have hdisj : Disjoint (openCubeSet R) (openCubeSet S) :=
    pairwiseDisjoint_openCubeSet_descendantsAtDepth Q j (Finset.mem_coe.mpr hR)
      (Finset.mem_coe.mpr hS) hne
  obtain ⟨x, hx⟩ := Book.Ch02.openCubeSet_nonempty T
  exact Set.disjoint_left.mp hdisj
    (openCubeSet_subset_of_mem_descendantsAtDepth hTR hx)
    (openCubeSet_subset_of_mem_descendantsAtDepth hTS hx)

/-- **The iterated sum over a sub-mesh is below the sum over any grid containing
the descendants.**  Unconditional for a family nonnegative on that grid. -/
theorem sum_descendantsAtDepth_le_of_subset {Q : TriadicCube d} {j : ℕ}
    {I T : Finset (TriadicCube d)} (hI : I ⊆ descendantsAtDepth Q j) {i : ℕ}
    (hsub : ∀ R ∈ I, descendantsAtDepth R i ⊆ T)
    (f : TriadicCube d → ℝ) (hf : ∀ R' ∈ T, 0 ≤ f R') :
    ∑ R ∈ I, ∑ R' ∈ descendantsAtDepth R i, f R' ≤ ∑ R' ∈ T, f R' := by
  classical
  have hdisj : (I : Set (TriadicCube d)).PairwiseDisjoint
      fun R => descendantsAtDepth R i := by
    intro R hRmem S hSmem hne
    exact disjoint_descendantsAtDepth_of_ne (hI (Finset.mem_coe.mp hRmem))
      (hI (Finset.mem_coe.mp hSmem)) hne i
  rw [← Finset.sum_biUnion hdisj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun R' hR' _ => hf R' hR'
  intro R' hR'
  obtain ⟨R, hRmem, hR'mem⟩ := Finset.mem_biUnion.mp hR'
  exact hsub R hRmem hR'mem

/-- **The sub-mesh depth average, against a containing grid.**

If every depth-`i` descendant family of the sub-mesh `I` proves inside the grid
`T`, and `f` is nonnegative on `T`, then the sub-mesh average of the depth-`i`
descendant averages is below `rho` times the `T`-average, `rho` being any bound
for the cardinality ratio `|T| / (|I| 3^{d i})`.

Unconditional finite combinatorics. -/
theorem cubeFamilyAverage_descendantsAverage_le {Q : TriadicCube d} {j : ℕ}
    {I T : Finset (TriadicCube d)} (hI : I ⊆ descendantsAtDepth Q j) {i : ℕ}
    (hsub : ∀ R ∈ I, descendantsAtDepth R i ⊆ T)
    (f : TriadicCube d → ℝ) (hf : ∀ R' ∈ T, 0 ≤ f R') {rho : ℝ} (hrho : 0 ≤ rho)
    (hcard : (T.card : ℝ) ≤ rho * ((I.card : ℝ) * ((3 : ℝ) ^ d) ^ i)) :
    cubeFamilyAverage I (fun R => descendantsAverage R i f) ≤
      rho * cubeFamilyAverage T f := by
  classical
  have hTnn : 0 ≤ cubeFamilyAverage T f := cubeFamilyAverage_nonneg hf
  rcases I.eq_empty_or_nonempty with hIempty | hIne
  · rw [hIempty]
    simp only [cubeFamilyAverage, Finset.sum_empty, mul_zero]
    exact mul_nonneg hrho hTnn
  -- the sub-mesh is nonempty, hence so is the containing grid
  obtain ⟨R0, hR0⟩ := hIne
  have hTne : T.Nonempty := by
    obtain ⟨S0, hS0⟩ := descendantsAtDepth_nonempty R0 i
    exact ⟨S0, hsub R0 hR0 hS0⟩
  have hIcard : (0 : ℝ) < (I.card : ℝ) := by
    have : 0 < I.card := Finset.card_pos.mpr ⟨R0, hR0⟩
    exact_mod_cast this
  have hTcard : (0 : ℝ) < (T.card : ℝ) := by
    have : 0 < T.card := Finset.card_pos.mpr hTne
    exact_mod_cast this
  have hDcard : (0 : ℝ) < ((3 : ℝ) ^ d) ^ i := by positivity
  have hsum := sum_descendantsAtDepth_le_of_subset hI hsub f hf
  have hdesc : ∀ R : TriadicCube d, descendantsAverage R i f =
      (((3 : ℝ) ^ d) ^ i)⁻¹ * ∑ R' ∈ descendantsAtDepth R i, f R' := by
    intro R
    change ((descendantsAtDepth R i).card : ℝ)⁻¹ * _ = _
    rw [descendantsAtDepth_card]
    congr 2
    push_cast
    ring
  have hLHS : cubeFamilyAverage I (fun R => descendantsAverage R i f) =
      ((I.card : ℝ))⁻¹ * (((3 : ℝ) ^ d) ^ i)⁻¹ *
        ∑ R ∈ I, ∑ R' ∈ descendantsAtDepth R i, f R' := by
    change ((I.card : ℝ))⁻¹ * ∑ R ∈ I, descendantsAverage R i f = _
    rw [Finset.sum_congr rfl fun R _ => hdesc R, ← Finset.mul_sum]
    ring
  have hRHS : rho * cubeFamilyAverage T f =
      rho * ((T.card : ℝ))⁻¹ * ∑ R' ∈ T, f R' := by
    change rho * (((T.card : ℝ))⁻¹ * _) = _
    ring
  have hTsumnn : (0 : ℝ) ≤ ∑ R' ∈ T, f R' := Finset.sum_nonneg hf
  have hcoef : ((I.card : ℝ))⁻¹ * (((3 : ℝ) ^ d) ^ i)⁻¹ ≤ rho * ((T.card : ℝ))⁻¹ := by
    rw [← mul_inv, inv_le_iff_one_le_mul₀ (by positivity)]
    have hTinv : (0 : ℝ) < ((T.card : ℝ))⁻¹ := by positivity
    calc (1 : ℝ) = (T.card : ℝ) * ((T.card : ℝ))⁻¹ :=
          (mul_inv_cancel₀ (ne_of_gt hTcard)).symm
      _ ≤ (rho * ((I.card : ℝ) * ((3 : ℝ) ^ d) ^ i)) * ((T.card : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_right hcard hTinv.le
      _ = rho * ((T.card : ℝ))⁻¹ * ((I.card : ℝ) * ((3 : ℝ) ^ d) ^ i) := by ring
  rw [hLHS, hRHS]
  calc ((I.card : ℝ))⁻¹ * (((3 : ℝ) ^ d) ^ i)⁻¹ *
        ∑ R ∈ I, ∑ R' ∈ descendantsAtDepth R i, f R'
      ≤ ((I.card : ℝ))⁻¹ * (((3 : ℝ) ^ d) ^ i)⁻¹ * ∑ R' ∈ T, f R' :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ rho * ((T.card : ℝ))⁻¹ * ∑ R' ∈ T, f R' :=
        mul_le_mul_of_nonneg_right hcoef hTsumnn

/-! ## The fold at an arbitrary sub-mesh -/

/-- **The grid fourth moment of the majorant, folded over depths, at an arbitrary
sub-mesh.**

The fold of `Closure.GammaTenEnvelopeInputGrid.oscMajorant` whose per-depth
input `D i` is read at the sub-mesh `I` itself rather than at the full mesh.
The proof is the full-mesh one with the closing identity
`descendantsAverage_add_eq_descendantsAverage_descendantsAverage` --- which is
available only on the full mesh --- replaced by the hypothesis `hD`.

on `hint`, the standing fourth-power integrability of the oscillation cells at
the descendants of the sub-mesh, and on the per-depth bounds `hD`. -/
theorem cubeFamilyAverage_integral_pow_four_oscMajorant_le_family
    (mu : Measure Omega) (I : Finset (TriadicCube d)) (nbase : ℤ) (s : ℝ) (N : ℕ)
    (U : Omega → Vec d → Vec d)
    (hint : ∀ i ∈ Finset.range (N + 1), ∀ R ∈ I, ∀ R' ∈ descendantsAtDepth R i,
      Integrable (fun w => meshOscillationCell (nbase - (i : ℤ)) (U w) R' ^ (4 : ℕ)) mu)
    (D : ℕ → ℝ)
    (hD : ∀ i ∈ Finset.range (N + 1),
      cubeFamilyAverage I (fun R => descendantsAverage R i
          (fun R' => ∫ w, meshOscillationCell (nbase - (i : ℤ)) (U w) R' ^ (4 : ℕ) ∂mu)) ≤
        D i) :
    cubeFamilyAverage I (fun R => ∫ w, oscMajorant nbase s N (U w) R ^ (4 : ℕ) ∂mu) ≤
      ∑ i ∈ Finset.range (N + 1),
        (2 : ℝ) ^ (i + 1) * (Real.rpow (3 : ℝ) (s * (i : ℝ))) ^ (4 : ℕ) * D i := by
  classical
  set c : ℕ → ℝ := fun i => (2 : ℝ) ^ (i + 1) * (Real.rpow (3 : ℝ) (s * (i : ℝ))) ^ (4 : ℕ)
    with hc
  have hc0 : ∀ i : ℕ, (0 : ℝ) ≤ c i := fun i => by rw [hc]; positivity
  set g : ℕ → TriadicCube d → Omega → ℝ := fun i R' w =>
    meshOscillationCell (nbase - (i : ℤ)) (U w) R' ^ (4 : ℕ) with hg
  have hcell : ∀ R ∈ I,
      (∫ w, oscMajorant nbase s N (U w) R ^ (4 : ℕ) ∂mu) ≤
        ∑ i ∈ Finset.range (N + 1),
          c i * descendantsAverage R i (fun R' => ∫ w, g i R' w ∂mu) := by
    intro R hR
    have hsub : ∀ i ∈ Finset.range (N + 1), ∀ R' ∈ descendantsAtDepth R i,
        Integrable (g i R') mu := fun i hi R' hR' => hint i hi R hR R' hR'
    have hGint : Integrable (fun w => ∑ i ∈ Finset.range (N + 1),
        c i * descendantsAverage R i (fun R' => g i R' w)) mu := by
      refine integrable_finsetSum _ fun i hi => ?_
      exact (integrable_descendantsAverage mu R i (g i) (hsub i hi)).const_mul _
    have hptw : ∀ w : Omega,
        oscMajorant nbase s N (U w) R ^ (4 : ℕ) ≤
          ∑ i ∈ Finset.range (N + 1),
            c i * descendantsAverage R i (fun R' => g i R' w) := fun w =>
      pow_four_oscMajorant_le nbase s N (U w) R
    have hstep : (∫ w, oscMajorant nbase s N (U w) R ^ (4 : ℕ) ∂mu) ≤
        ∫ w, ∑ i ∈ Finset.range (N + 1),
          c i * descendantsAverage R i (fun R' => g i R' w) ∂mu :=
      integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun w => by positivity) hGint
        (Filter.Eventually.of_forall hptw)
    refine hstep.trans_eq ?_
    rw [integral_finsetSum _ fun i hi =>
      (integrable_descendantsAverage mu R i (g i) (hsub i hi)).const_mul _]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [integral_const_mul, integral_descendantsAverage mu R i (g i) (hsub i hi)]
  refine le_trans (cubeFamilyAverage_mono hcell) ?_
  rw [cubeFamilyAverage_finsetSum]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [cubeFamilyAverage_const_mul]
  exact mul_le_mul_of_nonneg_left (hD i hi) (hc0 i)

/-- The fourth power of the majorant is integrable at every cell of the sub-mesh,
by domination through the fold.

on the measurability and the fourth-power integrability of the oscillation
cells at the descendants of that cell. -/
theorem integrable_pow_four_oscMajorant_family (mu : Measure Omega) (nbase : ℤ)
    (s : ℝ) (N : ℕ) (U : Omega → Vec d → Vec d) (R : TriadicCube d)
    (hmeascell : ∀ (i : ℕ), ∀ R' ∈ descendantsAtDepth R i,
      Measurable fun w => meshOscillationCell (nbase - (i : ℤ)) (U w) R')
    (hintcell : ∀ (i : ℕ), ∀ R' ∈ descendantsAtDepth R i,
      Integrable (fun w => meshOscillationCell (nbase - (i : ℤ)) (U w) R' ^ (4 : ℕ)) mu) :
    Integrable (fun w => oscMajorant nbase s N (U w) R ^ (4 : ℕ)) mu := by
  classical
  set g : ℕ → TriadicCube d → Omega → ℝ := fun i R' w =>
    meshOscillationCell (nbase - (i : ℤ)) (U w) R' ^ (4 : ℕ) with hg
  have hGint : Integrable (fun w => ∑ i ∈ Finset.range (N + 1),
      (2 : ℝ) ^ (i + 1) * (Real.rpow (3 : ℝ) (s * (i : ℝ))) ^ (4 : ℕ) *
        descendantsAverage R i (fun R' => g i R' w)) mu := by
    refine integrable_finsetSum _ fun i _ => ?_
    exact (integrable_descendantsAverage mu R i (g i) (hintcell i)).const_mul _
  have hmeas : Measurable fun w => oscMajorant nbase s N (U w) R :=
    measurable_oscMajorant _ s N R U fun i _ R' hR' => hmeascell i R' hR'
  refine Integrable.mono' hGint (hmeas.pow_const 4).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun w => ?_
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_four_oscMajorant_le nbase s N (U w) R

/-! ## The composite -/

/-- **The Besov envelope of Step 2 on an arbitrary sub-mesh, from per-depth
sub-mesh oscillation moments alone.**

The envelope device of `Closure.GammaTenEnvelopeInputGrid`, run at an arbitrary
family `I` of cells of a common scale `nbase`.  The conclusion is the exact
shape `Closure.ClosureInteriorSplit.ClosureInteriorBesovEnvelopeInput`
consumes.

on `hscale`, `hmeascell`, `hintcell`, `hmem2`, `hD` and `hsum`. -/
theorem exists_besovEnvelope_of_family_depth_oscillation (mu : Measure Omega)
    (I : Finset (TriadicCube d)) (nbase : ℤ) (s : ℝ) (U : Omega → Vec d → Vec d)
    (hscale : ∀ R ∈ I, R.scale = nbase)
    (hmeascell : ∀ (i : ℕ), ∀ R ∈ I, ∀ R' ∈ descendantsAtDepth R i,
      Measurable fun w => meshOscillationCell (nbase - (i : ℤ)) (U w) R')
    (hintcell : ∀ (i : ℕ), ∀ R ∈ I, ∀ R' ∈ descendantsAtDepth R i,
      Integrable (fun w => meshOscillationCell (nbase - (i : ℤ)) (U w) R' ^ (4 : ℕ)) mu)
    (hmem2 : ∀ (w : Omega) (i : ℕ), ∀ R ∈ I, ∀ R' ∈ descendantsAtDepth R i,
      MemLp (U w) (2 : ℝ≥0∞) (normalizedCubeMeasure R'))
    (D : ℕ → ℝ)
    (hD : ∀ i : ℕ, cubeFamilyAverage I (fun R => descendantsAverage R i
      (fun R' => ∫ w, meshOscillationCell (nbase - (i : ℤ)) (U w) R' ^ (4 : ℕ) ∂mu)) ≤ D i)
    {C : ℝ} (hC : 0 ≤ C)
    (hsum : ∀ N : ℕ, ∑ i ∈ Finset.range (N + 1),
      (2 : ℝ) ^ (i + 1) * (Real.rpow (3 : ℝ) (s * (i : ℝ))) ^ (4 : ℕ) * D i ≤ C) :
    ∃ B : TriadicCube d → Omega → ℝ,
      (∀ R w, 0 ≤ B R w) ∧
      (∀ R ∈ I, MemLp (B R) 4 mu) ∧
      cubeFamilyAverage I (fun R => ∫ w, B R w ^ (4 : ℕ) ∂mu) ≤ C ∧
      (∀ R ∈ I, ∀ᵐ w ∂mu, ∀ N : ℕ,
        cubeBesovPositiveVectorPartialSeminormTwo R s N (U w) ≤ B R w) := by
  classical
  obtain ⟨B, hB0, -, hBdom, hBmem, hBgrid⟩ :=
    exists_grid_pathwise_envelope_of_monotone mu I
      (fun N R w => oscMajorant nbase s N (U w) R)
      (fun N R hR => measurable_oscMajorant _ s N R U fun i _ R' hR' =>
        hmeascell i R hR R' hR')
      (fun N R w => oscMajorant_nonneg _ s N (U w) R)
      (fun R w => monotone_oscMajorant _ s (U w) R)
      (fun N R hR => integrable_pow_four_oscMajorant_family mu nbase s N U R
        (fun i R' hR' => hmeascell i R hR R' hR')
        (fun i R' hR' => hintcell i R hR R' hR'))
      hC
      (fun N => le_trans (cubeFamilyAverage_integral_pow_four_oscMajorant_le_family mu I
        nbase s N U (fun i _ R hR R' hR' => hintcell i R hR R' hR') D (fun i _ => hD i))
        (hsum N))
  refine ⟨B, hB0, hBmem, hBgrid, ?_⟩
  intro R hR
  filter_upwards [hBdom R hR] with w hw
  intro N
  refine le_trans ?_ (hw N)
  have hmaj := cubeBesovPositiveVectorPartialSeminormTwo_le_oscMajorant R s N (U w)
    (fun i _ R' hR' => hmem2 w i R hR R' hR')
  rwa [hscale R hR] at hmaj

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
