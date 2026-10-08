/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungPrimalFluxProjectionGeometry

/-!
# High-contrast homogenization: Provider.Response.PreYoungAdjointProjectionGeometry

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Finite projection geometry for adjoint optimizer readouts

The adjoint optimizer is the canonical optimizer for the transposed
coefficient sample.  Consequently both adjoint block components inherit the
primal finite-projection geometry, with separate scalar loads for the gradient
and flux readouts.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- A gradient component of the adjoint terminal optimizer is integrable on
every aligned subcell. -/
theorem integrableOn_diagonalWeakAdjointState_fst_component_of_aligned
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q k t)
    (a : CoeffSpace d) (p r : Vec d) (i : Fin d) :
    IntegrableOn (fun x ↦ (diagonalWeakAdjointState hq t a p r x).1 i)
      (adaptedCellAt q k w) volume := by
  simpa only [diagonalWeakAdjointState] using
    integrableOn_diagonalWeakState_fst_component_of_aligned
      hq hkt hw a.transpose p r i

/-- A flux component of the adjoint terminal optimizer is integrable on every
aligned subcell. -/
theorem integrableOn_diagonalWeakAdjointState_snd_component_of_aligned
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q k t)
    (a : CoeffSpace d) (p r : Vec d) (i : Fin d) :
    IntegrableOn (fun x ↦ (diagonalWeakAdjointState hq t a p r x).2 i)
      (adaptedCellAt q k w) volume := by
  simpa only [diagonalWeakAdjointState] using
    integrableOn_diagonalWeakState_snd_component_of_aligned
      hq hkt hw a.transpose p r i

/-- The scalar adjoint gradient readout is integrable on a pulled-back parent
cube. -/
theorem integrableOn_vecDot_diagonalWeakAdjointState_pullback
    {q : Mat d} (hq : q.PosDef) {s t : ℤ} (hst : s ≤ t)
    {z : Fin d → ℤ} (hz : z ∈ alignedIndex q s t)
    (a : CoeffSpace d) (p r Qcen : Vec d) :
    IntegrableOn (fun y ↦ vecDot Qcen
        (diagonalWeakAdjointState hq t a p r (matVecMul q y)).1)
      (cubeSet (translateCube z (originCube d s))) volume := by
  simpa only [diagonalWeakAdjointState] using
    integrableOn_vecDot_diagonalWeakState_pullback
      hq hst hz a.transpose p r Qcen

/-- The scalar adjoint flux readout is integrable on a pulled-back parent
cube. -/
theorem integrableOn_vecDot_diagonalWeakAdjointState_flux_pullback
    {q : Mat d} (hq : q.PosDef) {s t : ℤ} (hst : s ≤ t)
    {z : Fin d → ℤ} (hz : z ∈ alignedIndex q s t)
    (a : CoeffSpace d) (p r Pcen : Vec d) :
    IntegrableOn (fun y ↦ vecDot Pcen
        (diagonalWeakAdjointState hq t a p r (matVecMul q y)).2)
      (cubeSet (translateCube z (originCube d s))) volume := by
  simpa only [diagonalWeakAdjointState] using
    integrableOn_vecDot_diagonalWeakState_flux_pullback
      hq hst hz a.transpose p r Pcen

/-- The finite projected adjoint gradient pairing has the nested depth-sum
bound. -/
theorem abs_cutoff_projected_adjoint_gradient_pairing_subSkew_le_nested_depth_sum
    [NeZero d] {q : Mat d} (hq : q.PosDef) {s t : ℤ} (hst : s ≤ t)
    {z : Fin d → ℤ} (hz : z ∈ alignedIndex q s t)
    (g : Mat d) (hg : IsSkewMat g) (a : CoeffSpace d)
    (p r Qcen : Vec d) (N : ℕ) :
    let R : TriadicCube d := translateCube z (originCube d s)
    let phi : Vec d → ℝ := fun y ↦
      adaptedPreYoungCutoff q hq t (matVecMul q y)
    let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
    let F : Vec d → BlockVec d :=
      diagonalWeakAdjointState hq t (a.subSkew g hg) p r
    let G : Vec d → ℝ := fun y ↦ vecDot Qcen (F (matVecMul q y)).1
    |cubeBesovPairing R f (cubeProjection R N G)| ≤
      ∑ j ∈ Finset.range N,
        (32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound *
          (3 : ℝ) ^ (-((t - s) + (j : ℤ)))) *
            avsum (alignedIndex q (s - ((j + 1 : ℕ) : ℤ)) s)
              (fun w ↦ |vecDot Qcen
                (blockCellAverage
                  (adaptedCellAt q (s - ((j + 1 : ℕ) : ℤ))
                    (nestedLabel (s - ((j + 1 : ℕ) : ℤ)) s z w)) F).1|) := by
  dsimp only
  apply abs_cutoff_projected_primal_pairing_le_nested_depth_sum
    hq s t z (diagonalWeakAdjointState hq t (a.subSkew g hg) p r) Qcen N
  · exact integrableOn_vecDot_diagonalWeakAdjointState_pullback
      hq hst hz (a.subSkew g hg) p r Qcen
  · intro j hj w hw i
    have hks : s - ((j + 1 : ℕ) : ℤ) ≤ s := by omega
    have hmem := nestedLabel_mem_alignedIndex hq hks hst hw hz
    exact integrableOn_diagonalWeakAdjointState_fst_component_of_aligned
      hq (hks.trans hst) hmem (a.subSkew g hg) p r i

/-- The finite projected adjoint flux pairing has the nested depth-sum bound. -/
theorem abs_cutoff_projected_adjoint_flux_pairing_subSkew_le_nested_depth_sum
    [NeZero d] {q : Mat d} (hq : q.PosDef) {s t : ℤ} (hst : s ≤ t)
    {z : Fin d → ℤ} (hz : z ∈ alignedIndex q s t)
    (g : Mat d) (hg : IsSkewMat g) (a : CoeffSpace d)
    (p r Pcen : Vec d) (N : ℕ) :
    let R : TriadicCube d := translateCube z (originCube d s)
    let phi : Vec d → ℝ := fun y ↦
      adaptedPreYoungCutoff q hq t (matVecMul q y)
    let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
    let F : Vec d → BlockVec d :=
      diagonalWeakAdjointState hq t (a.subSkew g hg) p r
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
    hq s t z (diagonalWeakAdjointState hq t (a.subSkew g hg) p r) Pcen N
  · exact integrableOn_vecDot_diagonalWeakAdjointState_flux_pullback
      hq hst hz (a.subSkew g hg) p r Pcen
  · intro j hj w hw i
    have hks : s - ((j + 1 : ℕ) : ℤ) ≤ s := by omega
    have hmem := nestedLabel_mem_alignedIndex hq hks hst hw hz
    exact integrableOn_diagonalWeakAdjointState_snd_component_of_aligned
      hq (hks.trans hst) hmem (a.subSkew g hg) p r i

/-- The finite-depth adjoint gradient oscillation. -/
@[expose]
def adjointGradientProjectedOscillation
    {q : Mat d} (hq : q.PosDef) (s t : ℤ)
    (g : Mat d) (hg : IsSkewMat g) (p r Qcen : Vec d)
    (N : ℕ) (a : CoeffSpace d) : ℝ :=
  avsum (alignedIndex q s t) fun z ↦
    let R : TriadicCube d := translateCube z (originCube d s)
    let phi : Vec d → ℝ := fun y ↦
      adaptedPreYoungCutoff q hq t (matVecMul q y)
    let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
    let F : Vec d → BlockVec d :=
      diagonalWeakAdjointState hq t (a.subSkew g hg) p r
    let G : Vec d → ℝ := fun y ↦ vecDot Qcen (F (matVecMul q y)).1
    cubeBesovPairing R f (cubeProjection R N G)

/-- The full physical adjoint gradient oscillation. -/
@[expose]
def adjointGradientPhysicalOscillation
    {q : Mat d} (hq : q.PosDef) (s t : ℤ)
    (g : Mat d) (hg : IsSkewMat g) (p r Qcen : Vec d)
    (a : CoeffSpace d) : ℝ :=
  avsum (alignedIndex q s t) fun z ↦
    let R : TriadicCube d := translateCube z (originCube d s)
    let phi : Vec d → ℝ := fun y ↦
      adaptedPreYoungCutoff q hq t (matVecMul q y)
    let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
    let F : Vec d → BlockVec d :=
      diagonalWeakAdjointState hq t (a.subSkew g hg) p r
    let G : Vec d → ℝ := fun y ↦ vecDot Qcen (F (matVecMul q y)).1
    cubeBesovPairing R f G

/-- The finite-depth adjoint flux oscillation. -/
@[expose]
def adjointFluxProjectedOscillation
    {q : Mat d} (hq : q.PosDef) (s t : ℤ)
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen : Vec d)
    (N : ℕ) (a : CoeffSpace d) : ℝ :=
  avsum (alignedIndex q s t) fun z ↦
    let R : TriadicCube d := translateCube z (originCube d s)
    let phi : Vec d → ℝ := fun y ↦
      adaptedPreYoungCutoff q hq t (matVecMul q y)
    let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
    let F : Vec d → BlockVec d :=
      diagonalWeakAdjointState hq t (a.subSkew g hg) p r
    let G : Vec d → ℝ := fun y ↦ vecDot Pcen (F (matVecMul q y)).2
    cubeBesovPairing R f (cubeProjection R N G)

/-- The full physical adjoint flux oscillation. -/
@[expose]
def adjointFluxPhysicalOscillation
    {q : Mat d} (hq : q.PosDef) (s t : ℤ)
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen : Vec d)
    (a : CoeffSpace d) : ℝ :=
  avsum (alignedIndex q s t) fun z ↦
    let R : TriadicCube d := translateCube z (originCube d s)
    let phi : Vec d → ℝ := fun y ↦
      adaptedPreYoungCutoff q hq t (matVecMul q y)
    let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
    let F : Vec d → BlockVec d :=
      diagonalWeakAdjointState hq t (a.subSkew g hg) p r
    let G : Vec d → ℝ := fun y ↦ vecDot Pcen (F (matVecMul q y)).2
    cubeBesovPairing R f G

/-- The projected adjoint gradient oscillation obeys the nested depth-sum
estimate. -/
theorem abs_adjoint_gradient_projected_oscillation_le_nested_depth_sum
    [NeZero d] {q : Mat d} (hq : q.PosDef) {s t : ℤ} (hst : s ≤ t)
    (g : Mat d) (hg : IsSkewMat g) (p r Qcen : Vec d)
    (N : ℕ) (a : CoeffSpace d) :
    |adjointGradientProjectedOscillation hq s t g hg p r Qcen N a| ≤
      ∑ j ∈ Finset.range N,
        (32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound *
          (3 : ℝ) ^ (-((t - s) + (j : ℤ)))) *
            avsum (alignedIndex q s t) (fun z ↦
              avsum (alignedIndex q (s - ((j + 1 : ℕ) : ℤ)) s)
                (fun w ↦ |vecDot Qcen
                  (blockCellAverage
                    (adaptedCellAt q (s - ((j + 1 : ℕ) : ℤ))
                      (nestedLabel (s - ((j + 1 : ℕ) : ℤ)) s z w))
                    (diagonalWeakAdjointState hq t
                      (a.subSkew g hg) p r)).1|)) := by
  let Z := alignedIndex q s t
  let pair : (Fin d → ℤ) → ℝ := fun z ↦
    let R : TriadicCube d := translateCube z (originCube d s)
    let phi : Vec d → ℝ := fun y ↦
      adaptedPreYoungCutoff q hq t (matVecMul q y)
    let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
    let F : Vec d → BlockVec d :=
      diagonalWeakAdjointState hq t (a.subSkew g hg) p r
    let G : Vec d → ℝ := fun y ↦ vecDot Qcen (F (matVecMul q y)).1
    cubeBesovPairing R f (cubeProjection R N G)
  have hcell : ∀ z ∈ Z, |pair z| ≤
      ∑ j ∈ Finset.range N,
        (32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound *
          (3 : ℝ) ^ (-((t - s) + (j : ℤ)))) *
            avsum (alignedIndex q (s - ((j + 1 : ℕ) : ℤ)) s)
              (fun w ↦ |vecDot Qcen
                (blockCellAverage
                  (adaptedCellAt q (s - ((j + 1 : ℕ) : ℤ))
                    (nestedLabel (s - ((j + 1 : ℕ) : ℤ)) s z w))
                  (diagonalWeakAdjointState hq t
                    (a.subSkew g hg) p r)).1|) := by
    intro z hz
    simpa only [pair] using
      abs_cutoff_projected_adjoint_gradient_pairing_subSkew_le_nested_depth_sum
        hq hst hz g hg a p r Qcen N
  change |avsum Z pair| ≤ _
  calc
    |avsum Z pair| ≤ avsum Z (fun z ↦ |pair z|) :=
      abs_avsum_le_avsum_abs Z pair
    _ ≤ avsum Z (fun z ↦ ∑ j ∈ Finset.range N,
          (32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound *
            (3 : ℝ) ^ (-((t - s) + (j : ℤ)))) *
              avsum (alignedIndex q (s - ((j + 1 : ℕ) : ℤ)) s)
                (fun w ↦ |vecDot Qcen
                  (blockCellAverage
                    (adaptedCellAt q (s - ((j + 1 : ℕ) : ℤ))
                      (nestedLabel (s - ((j + 1 : ℕ) : ℤ)) s z w))
                    (diagonalWeakAdjointState hq t
                      (a.subSkew g hg) p r)).1|)) :=
      avsum_le_avsum hcell
    _ = _ := by
      rw [avsum_finset_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [avsum_const_mul]

/-- The projected adjoint flux oscillation obeys the nested depth-sum
estimate. -/
theorem abs_adjoint_flux_projected_oscillation_le_nested_depth_sum
    [NeZero d] {q : Mat d} (hq : q.PosDef) {s t : ℤ} (hst : s ≤ t)
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen : Vec d)
    (N : ℕ) (a : CoeffSpace d) :
    |adjointFluxProjectedOscillation hq s t g hg p r Pcen N a| ≤
      ∑ j ∈ Finset.range N,
        (32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound *
          (3 : ℝ) ^ (-((t - s) + (j : ℤ)))) *
            avsum (alignedIndex q s t) (fun z ↦
              avsum (alignedIndex q (s - ((j + 1 : ℕ) : ℤ)) s)
                (fun w ↦ |vecDot Pcen
                  (blockCellAverage
                    (adaptedCellAt q (s - ((j + 1 : ℕ) : ℤ))
                      (nestedLabel (s - ((j + 1 : ℕ) : ℤ)) s z w))
                    (diagonalWeakAdjointState hq t
                      (a.subSkew g hg) p r)).2|)) := by
  let Z := alignedIndex q s t
  let pair : (Fin d → ℤ) → ℝ := fun z ↦
    let R : TriadicCube d := translateCube z (originCube d s)
    let phi : Vec d → ℝ := fun y ↦
      adaptedPreYoungCutoff q hq t (matVecMul q y)
    let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
    let F : Vec d → BlockVec d :=
      diagonalWeakAdjointState hq t (a.subSkew g hg) p r
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
                  (diagonalWeakAdjointState hq t
                    (a.subSkew g hg) p r)).2|) := by
    intro z hz
    simpa only [pair] using
      abs_cutoff_projected_adjoint_flux_pairing_subSkew_le_nested_depth_sum
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
                    (diagonalWeakAdjointState hq t
                      (a.subSkew g hg) p r)).2|)) :=
      avsum_le_avsum hcell
    _ = _ := by
      rw [avsum_finset_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [avsum_const_mul]

/-- The physical adjoint gradient oscillation is the unprojected scalar
pairing on the reference cube. -/
theorem adjoint_gradient_cutoff_oscillation_eq_unprojected_pairing
    {q : Mat d} (hq : q.PosDef) (s t : ℤ) (w : Fin d → ℤ)
    (F : Vec d → BlockVec d) (Qcen : Vec d) :
    let R : TriadicCube d := translateCube w (originCube d s)
    let phi : Vec d → ℝ := fun y ↦
      adaptedPreYoungCutoff q hq t (matVecMul q y)
    let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
    let G : Vec d → ℝ := fun y ↦ vecDot Qcen (F (matVecMul q y)).1
    volumeAverage (adaptedCellAt q s w) (fun x ↦
        (adaptedPreYoungCutoff q hq t x -
          volumeAverage (adaptedCellAt q s w)
            (adaptedPreYoungCutoff q hq t)) *
          vecDot Qcen (F x).1) =
      cubeBesovPairing R f G :=
  primal_cutoff_oscillation_eq_unprojected_pairing hq s t w F Qcen

/-- The physical adjoint flux oscillation is the unprojected scalar pairing
on the reference cube. -/
theorem adjoint_flux_cutoff_oscillation_eq_unprojected_pairing
    {q : Mat d} (hq : q.PosDef) (s t : ℤ) (w : Fin d → ℤ)
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
      cubeBesovPairing R f G :=
  primal_flux_cutoff_oscillation_eq_unprojected_pairing hq s t w F Pcen

end

end HCPolySupport.HighContrast.Response
