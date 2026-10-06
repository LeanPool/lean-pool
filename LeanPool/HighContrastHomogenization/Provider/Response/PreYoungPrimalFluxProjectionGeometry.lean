/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungPrimalProjectionGeometry

/-!
# High-contrast homogenization: Provider.Response.PreYoungPrimalFluxProjectionGeometry

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Finite projection geometry for the primal flux readout

The second block component of the primal optimizer is handled by the same
finite cube projections as the first component.  Swapping the two components
of an arbitrary doubled field makes the common projection geometry directly
reusable while preserving the physical flux pairing.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- A flux component of the terminal optimizer is integrable on every aligned
subcell of its terminal domain. -/
theorem integrableOn_diagonalWeakState_snd_component_of_aligned
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q k t)
    (a : CoeffSpace d) (p r : Vec d) (i : Fin d) :
    IntegrableOn (fun x ↦ (diagonalWeakState hq t a p r x).2 i)
      (adaptedCellAt q k w) volume := by
  obtain ⟨_hgrad, hflux⟩ := diagonalWeakState_memVectorL2 hq t a p r
  have hi := integrableOn_component (U := adaptedDomain hq t) hflux i
  simpa only [adaptedDomain_carrier] using
    hi.mono_set (adaptedCellAt_subset_of_mem_alignedIndex hq hkt hw)

/-- The scalar flux readout remains integrable after pulling an aligned cell
back to its reference cube. -/
theorem integrableOn_vecDot_diagonalWeakState_flux_pullback
    {q : Mat d} (hq : q.PosDef) {s t : ℤ} (hst : s ≤ t)
    {z : Fin d → ℤ} (hz : z ∈ alignedIndex q s t)
    (a : CoeffSpace d) (p r Pcen : Vec d) :
    IntegrableOn (fun y ↦ vecDot Pcen
        (diagonalWeakState hq t a p r (matVecMul q y)).2)
      (cubeSet (translateCube z (originCube d s))) volume := by
  let R : TriadicCube d := translateCube z (originCube d s)
  obtain ⟨_hgrad, hflux⟩ := diagonalWeakState_memVectorL2 hq t a p r
  have hsub := adaptedCellAt_subset_of_mem_alignedIndex hq hst hz
  have hqdet : IsUnit q.det :=
    (Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit
  have hU : MeasurableSet (adaptedCellAt q s z) :=
    (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq s z).isOpen.measurableSet
  have hpull := memVectorL2_affinePullback hqdet hU
    (memVectorL2_mono hsub hflux)
  rw [matImage_inv_adaptedCellAt_eq hq s z] at hpull
  have hidentityCell : adaptedCellAt (1 : Mat d) s z = openCubeSet R := by
    dsimp only [R]
    rw [Recurrence.adaptedCellAt_eq_image]
    have hone : matVecMul (1 : Mat d) = id :=
      funext fun x ↦ matVecMul_one x
    rw [hone, Set.image_id]
    rfl
  have hi : ∀ i, IntegrableOn (fun y ↦
      (diagonalWeakState hq t a p r (matVecMul q y)).2 i)
      (cubeSet R) volume := by
    intro i
    have hiOpen := integrableOn_component
      (U := adaptedDomainAt Matrix.PosDef.one s z) hpull i
    change Integrable (fun y ↦
      (diagonalWeakState hq t a p r (matVecMul q y)).2 i)
      (volume.restrict (cubeSet R))
    rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    simpa only [adaptedDomainAt_carrier, hidentityCell] using! hiOpen
  simpa only [vecDot] using! integrable_finsetSum
    (s := (Finset.univ : Finset (Fin d)))
    (fun i _ ↦ (hi i).const_mul (Pcen i))

/-- A projected scalar flux pairing is controlled by the nested-cell depth
sum with the sharp cutoff coefficient. -/
theorem abs_cutoff_projected_primal_flux_pairing_le_nested_depth_sum
    [NeZero d] {q : Mat d} (hq : q.PosDef) (s t : ℤ)
    (z : Fin d → ℤ) (F : Vec d → BlockVec d) (Pcen : Vec d)
    (N : ℕ)
    (hGInt : IntegrableOn (fun y ↦ vecDot Pcen (F (matVecMul q y)).2)
      (cubeSet (translateCube z (originCube d s))) volume)
    (hF : ∀ j < N, ∀ w ∈ alignedIndex q (s - ((j + 1 : ℕ) : ℤ)) s,
      ∀ i, IntegrableOn (fun x ↦ (F x).2 i)
        (adaptedCellAt q (s - ((j + 1 : ℕ) : ℤ))
          (nestedLabel (s - ((j + 1 : ℕ) : ℤ)) s z w)) volume) :
    let R : TriadicCube d := translateCube z (originCube d s)
    let phi : Vec d → ℝ := fun y ↦
      adaptedPreYoungCutoff q hq t (matVecMul q y)
    let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
    let G : Vec d → ℝ := fun y ↦ vecDot Pcen (F (matVecMul q y)).2
    |cubeBesovPairing R f (cubeProjection R N G)| ≤
      ∑ j ∈ Finset.range N,
        (32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound *
          (3 : ℝ) ^ (-((t - s) + (j : ℤ)))) *
            avsum (alignedIndex q (s - ((j + 1 : ℕ) : ℤ)) s)
              (fun w ↦ |vecDot Pcen
                (blockCellAverage
                  (adaptedCellAt q (s - ((j + 1 : ℕ) : ℤ))
                    (nestedLabel (s - ((j + 1 : ℕ) : ℤ)) s z w)) F).2|) := by
  simpa only [blockCellAverage_fst, blockCellAverage_snd] using
    (abs_cutoff_projected_primal_pairing_le_nested_depth_sum
      hq s t z (fun x ↦ ((F x).2, (F x).1)) Pcen N hGInt hF)

/-- The preceding projected flux estimate specialized to a recentered primal
optimizer sample. -/
theorem abs_cutoff_projected_primal_flux_pairing_subSkew_le_nested_depth_sum
    [NeZero d] {q : Mat d} (hq : q.PosDef) {s t : ℤ} (hst : s ≤ t)
    {z : Fin d → ℤ} (hz : z ∈ alignedIndex q s t)
    (g : Mat d) (hg : IsSkewMat g) (a : CoeffSpace d)
    (p r Pcen : Vec d) (N : ℕ) :
    let R : TriadicCube d := translateCube z (originCube d s)
    let phi : Vec d → ℝ := fun y ↦
      adaptedPreYoungCutoff q hq t (matVecMul q y)
    let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
    let F : Vec d → BlockVec d := diagonalWeakState hq t (a.subSkew g hg) p r
    let G : Vec d → ℝ := fun y ↦ vecDot Pcen (F (matVecMul q y)).2
    |cubeBesovPairing R f (cubeProjection R N G)| ≤
      ∑ j ∈ Finset.range N,
        (32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound *
          (3 : ℝ) ^ (-((t - s) + (j : ℤ)))) *
            avsum (alignedIndex q (s - ((j + 1 : ℕ) : ℤ)) s)
              (fun w ↦ |vecDot Pcen
                (blockCellAverage
                  (adaptedCellAt q (s - ((j + 1 : ℕ) : ℤ))
                    (nestedLabel (s - ((j + 1 : ℕ) : ℤ)) s z w)) F).2|) := by
  dsimp only
  apply abs_cutoff_projected_primal_flux_pairing_le_nested_depth_sum
    hq s t z (diagonalWeakState hq t (a.subSkew g hg) p r) Pcen N
  · exact integrableOn_vecDot_diagonalWeakState_flux_pullback
      hq hst hz (a.subSkew g hg) p r Pcen
  · intro j hj w hw i
    have hks : s - ((j + 1 : ℕ) : ℤ) ≤ s := by omega
    have hmem := nestedLabel_mem_alignedIndex hq hks hst hw hz
    exact integrableOn_diagonalWeakState_snd_component_of_aligned
      hq (hks.trans hst) hmem (a.subSkew g hg) p r i

/-- The finite-depth primal flux oscillation, averaged over terminal parents. -/
@[expose]
def primal_flux_projected_oscillation [NeZero d]
    {q : Mat d} (hq : q.PosDef) (s t : ℤ)
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen : Vec d)
    (N : ℕ) (a : CoeffSpace d) : ℝ :=
  avsum (alignedIndex q s t) fun z ↦
    let R : TriadicCube d := translateCube z (originCube d s)
    let phi : Vec d → ℝ := fun y ↦
      adaptedPreYoungCutoff q hq t (matVecMul q y)
    let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
    let F : Vec d → BlockVec d :=
      diagonalWeakState hq t (a.subSkew g hg) p r
    let G : Vec d → ℝ := fun y ↦ vecDot Pcen (F (matVecMul q y)).2
    cubeBesovPairing R f (cubeProjection R N G)

/-- The full physical primal flux oscillation, averaged over terminal parents. -/
@[expose]
def primal_flux_physical_oscillation [NeZero d]
    {q : Mat d} (hq : q.PosDef) (s t : ℤ)
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen : Vec d)
    (a : CoeffSpace d) : ℝ :=
  avsum (alignedIndex q s t) fun z ↦
    let R : TriadicCube d := translateCube z (originCube d s)
    let phi : Vec d → ℝ := fun y ↦
      adaptedPreYoungCutoff q hq t (matVecMul q y)
    let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
    let F : Vec d → BlockVec d :=
      diagonalWeakState hq t (a.subSkew g hg) p r
    let G : Vec d → ℝ := fun y ↦ vecDot Pcen (F (matVecMul q y)).2
    cubeBesovPairing R f G

/-- The projected primal flux oscillation obeys the terminal-parent nested
depth-sum estimate. -/
theorem abs_primal_flux_projected_oscillation_le_nested_depth_sum
    [NeZero d] {q : Mat d} (hq : q.PosDef) {s t : ℤ} (hst : s ≤ t)
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen : Vec d)
    (N : ℕ) (a : CoeffSpace d) :
    |primal_flux_projected_oscillation hq s t g hg p r Pcen N a| ≤
      ∑ j ∈ Finset.range N,
        (32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound *
          (3 : ℝ) ^ (-((t - s) + (j : ℤ)))) *
            avsum (alignedIndex q s t) (fun z ↦
              avsum (alignedIndex q (s - ((j + 1 : ℕ) : ℤ)) s)
                (fun w ↦ |vecDot Pcen
                  (blockCellAverage
                    (adaptedCellAt q (s - ((j + 1 : ℕ) : ℤ))
                      (nestedLabel (s - ((j + 1 : ℕ) : ℤ)) s z w))
                    (diagonalWeakState hq t (a.subSkew g hg) p r)).2|)) := by
  let Z := alignedIndex q s t
  let pair : (Fin d → ℤ) → ℝ := fun z ↦
    let R : TriadicCube d := translateCube z (originCube d s)
    let phi : Vec d → ℝ := fun y ↦
      adaptedPreYoungCutoff q hq t (matVecMul q y)
    let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
    let F : Vec d → BlockVec d :=
      diagonalWeakState hq t (a.subSkew g hg) p r
    let G : Vec d → ℝ := fun y ↦ vecDot Pcen (F (matVecMul q y)).2
    cubeBesovPairing R f (cubeProjection R N G)
  have hcell : ∀ z ∈ Z, |pair z| ≤
      ∑ j ∈ Finset.range N,
        (32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound *
          (3 : ℝ) ^ (-((t - s) + (j : ℤ)))) *
            avsum (alignedIndex q (s - ((j + 1 : ℕ) : ℤ)) s)
              (fun w ↦ |vecDot Pcen
                (blockCellAverage
                  (adaptedCellAt q (s - ((j + 1 : ℕ) : ℤ))
                    (nestedLabel (s - ((j + 1 : ℕ) : ℤ)) s z w))
                  (diagonalWeakState hq t (a.subSkew g hg) p r)).2|) := by
    intro z hz
    simpa only [pair] using
      abs_cutoff_projected_primal_flux_pairing_subSkew_le_nested_depth_sum
        hq hst hz g hg a p r Pcen N
  change |avsum Z pair| ≤ _
  calc
    |avsum Z pair| ≤ avsum Z (fun z ↦ |pair z|) :=
      abs_avsum_le_avsum_abs Z pair
    _ ≤ avsum Z (fun z ↦ ∑ j ∈ Finset.range N,
          (32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound *
            (3 : ℝ) ^ (-((t - s) + (j : ℤ)))) *
              avsum (alignedIndex q (s - ((j + 1 : ℕ) : ℤ)) s)
                (fun w ↦ |vecDot Pcen
                  (blockCellAverage
                    (adaptedCellAt q (s - ((j + 1 : ℕ) : ℤ))
                      (nestedLabel (s - ((j + 1 : ℕ) : ℤ)) s z w))
                    (diagonalWeakState hq t (a.subSkew g hg) p r)).2|)) :=
      avsum_le_avsum hcell
    _ = _ := by
      rw [avsum_finset_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [avsum_const_mul]

/-- The physical primal flux cutoff oscillation is the unprojected Besov
pairing on the reference cube. -/
theorem primal_flux_cutoff_oscillation_eq_unprojected_pairing
    [NeZero d] {q : Mat d} (hq : q.PosDef) (s t : ℤ) (w : Fin d → ℤ)
    (F : Vec d → BlockVec d) (Pcen : Vec d) :
    let R : TriadicCube d := translateCube w (originCube d s)
    let phi : Vec d → ℝ := fun y ↦
      adaptedPreYoungCutoff q hq t (matVecMul q y)
    let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
    let G : Vec d → ℝ := fun y ↦ vecDot Pcen (F (matVecMul q y)).2
    volumeAverage (adaptedCellAt q s w) (fun x ↦
        (adaptedPreYoungCutoff q hq t x -
          volumeAverage (adaptedCellAt q s w)
            (adaptedPreYoungCutoff q hq t)) *
          vecDot Pcen (F x).2) =
      cubeBesovPairing R f G := by
  simpa only using
    (primal_cutoff_oscillation_eq_unprojected_pairing hq s t w
      (fun x ↦ ((F x).2, (F x).1)) Pcen)

end

end HCPolySupport.HighContrast.Response
