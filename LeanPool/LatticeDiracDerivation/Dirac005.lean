/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac005.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac004DiscreteAction

/-!
DIRAC-005: exact native period-two unit-cell sector.

The sector in this file is not imposed during evolution.  It is the bundle
in which the two native fields at each cube corner lie on the prepared
tetrahedral ray and its companion ray.  The proof below starts from the
action-derived force of DIRAC-003/004 and proves that every force component
normal to that bundle is zero.  The positive diagonal kinetic form then
keeps the unrestricted centered update inside the same bundle.

There are two independent complex amplitudes at each of the eight sites: one
for `Psi` and one for `chi`, hence sixteen complex coordinates on each committed
state slice.  The centered second-order update carries two such slices, hence
thirty-two complex phase-space coordinates.  No four-component split is
supplied at this gate; it must be derived from the native finite-lattice
operator downstream.
-/

@[expose] public section

namespace LeanDirac

variable {Site : Type} {Edge : Type*}

noncomputable section
open BigOperators Complex

/-- A complex amplitude at each of the eight cube corners. -/
abbrev Cell8 := Fin 8 → ℂ
/-- Index set of the sixteen unit-cell coordinates: eight corners for `psi` (left summand) and
eight corners for `chi` (right summand). -/
abbrev NativeUnitCellCoordinate := Fin 8 ⊕ Fin 8
/-- Index set of the thirty-two coordinates of two unit-cell layers, each indexed by
`NativeUnitCellCoordinate`. -/
abbrev NativeUnitCellTwoLayerCoordinate :=
  NativeUnitCellCoordinate ⊕ NativeUnitCellCoordinate
/-- A pair of eight-corner amplitude vectors, the first for `psi` and the second for `chi`. -/
abbrev NativeUnitCellAmplitudes := Cell8 × Cell8

/-- Flattens a pair of eight-corner amplitudes into a function on the sixteen coordinates
`NativeUnitCellCoordinate`. -/
def nativeUnitCellAmplitudeCoordinates
    (amplitudes : NativeUnitCellAmplitudes) :
    NativeUnitCellCoordinate → ℂ
  | Sum.inl corner => amplitudes.1 corner
  | Sum.inr corner => amplitudes.2 corner

/-- Splits a function on the sixteen coordinates `NativeUnitCellCoordinate` into its `psi` and
`chi` eight-corner amplitudes. -/
def nativeUnitCellCoordinatesAmplitude
    (coordinates : NativeUnitCellCoordinate → ℂ) :
    NativeUnitCellAmplitudes :=
  (fun corner => coordinates (Sum.inl corner),
    fun corner => coordinates (Sum.inr corner))

/-- The equivalence between pairs of eight-corner amplitudes and functions on the sixteen
coordinates `NativeUnitCellCoordinate`. -/
def nativeUnitCellAmplitudeCoordinateEquiv :
    NativeUnitCellAmplitudes ≃ (NativeUnitCellCoordinate → ℂ) where
  toFun := nativeUnitCellAmplitudeCoordinates
  invFun := nativeUnitCellCoordinatesAmplitude
  left_inv := by
    intro amplitudes
    rcases amplitudes with ⟨psiAmplitude, chiAmplitude⟩
    rfl
  right_inv := by
    intro coordinates
    funext coordinate
    cases coordinate <;> rfl

theorem native_unit_cell_coordinate_count :
    Fintype.card NativeUnitCellCoordinate = 16 := by
  decide

theorem native_unit_cell_two_layer_coordinate_count :
    Fintype.card NativeUnitCellTwoLayerCoordinate = 32 := by
  decide

/-- Scalar multiplication of the vector `u` in `ℂ³` by the complex number `a`. -/
def c3ScaleComplex (a : ℂ) (u : C3) : C3 :=
  fun component => a * u component

/-- The Hermitian inner product `∑ᵢ conj (u i) * v i` on `ℂ³`, conjugate-linear in `u`. -/
def c3Inner (u v : C3) : ℂ :=
  ∑ component, star (u component) * v component

/-- The cube state whose `psi` field at each corner is `psiAmplitude corner` times
`tetraCorner corner` and whose `chi` field is `chiAmplitude corner` times `companion corner`. -/
def alignedEightSiteState (psiAmplitude chiAmplitude : Cell8) :
    State CubeCorner where
  psi corner := c3ScaleComplex (psiAmplitude corner) (tetraCorner corner)
  chi corner := c3ScaleComplex (chiAmplitude corner) (companion corner)

/-- A cube state lies in the eight-site sector if it equals `alignedEightSiteState` for some
pair of eight-corner amplitudes. -/
def InEightSiteSector (state : State CubeCorner) : Prop :=
  ∃ psiAmplitude chiAmplitude,
    state = alignedEightSiteState psiAmplitude chiAmplitude

/-- `alignedEightSiteState` applied to the two components of an amplitude pair. -/
def alignedEightSiteStateFromAmplitudes
    (amplitudes : NativeUnitCellAmplitudes) : State CubeCorner :=
  alignedEightSiteState amplitudes.1 amplitudes.2

/-- The amplitudes of a cube state along the reference rays: at each corner, the inner products
`c3Inner (tetraCorner corner) (psi corner)` and `c3Inner (companion corner) (chi corner)`. -/
def recoverEightSiteAmplitudes
    (state : State CubeCorner) : NativeUnitCellAmplitudes :=
  (fun corner => c3Inner (tetraCorner corner) (state.psi corner),
    fun corner => c3Inner (companion corner) (state.chi corner))

/-- The vector `eta` is orthogonal to `u` for the Hermitian inner product `c3Inner`. -/
def ComplexNormalTo (u eta : C3) : Prop := c3Inner u eta = 0

/-- At every cube corner, `eta corner` is orthogonal to `tetraCorner corner`. -/
def PsiNormalDirection (eta : CubeCorner → C3) : Prop :=
  ∀ corner, ComplexNormalTo (tetraCorner corner) (eta corner)

/-- At every cube corner, `eta corner` is orthogonal to `companion corner`. -/
def ChiNormalDirection (eta : CubeCorner → C3) : Prop :=
  ∀ corner, ComplexNormalTo (companion corner) (eta corner)

@[simp] theorem wedge_companion_tetra (corner : CubeCorner) :
    wedge (companion corner) (tetraCorner corner) = c3Neg unitArea := by
  have h := tetra_wedge_companion_constant corner
  funext component
  have hc := congrFun h component
  fin_cases component <;> simp only [wedge, Fin.zero_eta, Fin.isValue, c3Neg, Fin.mk_one,
                              Fin.reduceFinMk] at hc ⊢ <;>
    rw [← hc] <;> ring

theorem c3_inner_unitArea_wedge_planar_companion
    (u eta : C3) (hu2 : u 2 = 0) :
    c3Inner unitArea
      (wedge (fun
        | 0 => -star (u 1)
        | 1 => star (u 0)
        | _ => 0) eta) = -c3Inner u eta := by
  apply Complex.ext <;>
    simp [c3Inner, Fin.sum_univ_succ, unitArea, wedge, hu2] <;> ring

theorem c3_inner_unitArea_wedge_planar
    (u eta : C3) (hu2 : u 2 = 0) :
    c3Inner unitArea (wedge eta u) =
      -c3Inner (fun
        | 0 => -star (u 1)
        | 1 => star (u 0)
        | _ => 0) eta := by
  apply Complex.ext <;>
    simp [c3Inner, Fin.sum_univ_succ, unitArea, wedge, hu2] <;> ring

theorem c3_inner_unitArea_wedge_companion
    (corner : CubeCorner) (eta : C3) :
    c3Inner unitArea (wedge (companion corner) eta) =
      -c3Inner (tetraCorner corner) eta := by
  apply c3_inner_unitArea_wedge_planar_companion
  fin_cases corner <;>
    simp [tetraCorner, tetraRay0, tetraRay1, tetraRay2, tetraRay3,
      c3Of, c3Neg]

theorem c3_inner_unitArea_wedge_tetra
    (corner : CubeCorner) (eta : C3) :
    c3Inner unitArea (wedge eta (tetraCorner corner)) =
      -c3Inner (companion corner) eta := by
  apply c3_inner_unitArea_wedge_planar
  fin_cases corner <;>
    simp [tetraCorner, tetraRay0, tetraRay1, tetraRay2, tetraRay3,
      c3Of, c3Neg]

theorem c3_real_pair_eq_inner_re (u v : C3) :
    c3RealPair u v = (c3Inner u v).re := by
  simp [c3RealPair, c3Inner]

theorem c3_inner_scale_left (a : ℂ) (u v : C3) :
    c3Inner (c3ScaleComplex a u) v = star a * c3Inner u v := by
  unfold c3Inner c3ScaleComplex
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro component _
  simp
  ring

theorem wedge_scale_left (a : ℂ) (u v : C3) :
    wedge (c3ScaleComplex a u) v = c3ScaleComplex a (wedge u v) := by
  funext component
  fin_cases component <;> simp [wedge, c3ScaleComplex] <;> ring

theorem wedge_scale_right (a : ℂ) (u v : C3) :
    wedge u (c3ScaleComplex a v) = c3ScaleComplex a (wedge u v) := by
  funext component
  fin_cases component <;> simp [wedge, c3ScaleComplex] <;> ring

theorem aligned_wedge (psiAmplitude chiAmplitude : Cell8)
    (corner : CubeCorner) :
    wedge ((alignedEightSiteState psiAmplitude chiAmplitude).chi corner)
      ((alignedEightSiteState psiAmplitude chiAmplitude).psi corner) =
      c3ScaleComplex (-(chiAmplitude corner * psiAmplitude corner)) unitArea := by
  rw [show (alignedEightSiteState psiAmplitude chiAmplitude).chi corner =
      c3ScaleComplex (chiAmplitude corner) (companion corner) by rfl,
    show (alignedEightSiteState psiAmplitude chiAmplitude).psi corner =
      c3ScaleComplex (psiAmplitude corner) (tetraCorner corner) by rfl,
    wedge_scale_left, wedge_scale_right, wedge_companion_tetra]
  funext component
  simp [c3ScaleComplex, c3Neg]
  ring

theorem aligned_psi_normal_local_pair_zero
    (psiAmplitude chiAmplitude : Cell8) (eta : CubeCorner → C3)
    (hnormal : PsiNormalDirection eta) (corner : CubeCorner) :
    c3RealPair
      ((alignedEightSiteState psiAmplitude chiAmplitude).psi corner)
      (eta corner) = 0 := by
  rw [c3_real_pair_eq_inner_re]
  change (c3Inner (c3ScaleComplex (psiAmplitude corner)
    (tetraCorner corner)) (eta corner)).re = 0
  rw [c3_inner_scale_left,
    hnormal corner]
  simp

theorem aligned_chi_normal_local_pair_zero
    (psiAmplitude chiAmplitude : Cell8) (eta : CubeCorner → C3)
    (hnormal : ChiNormalDirection eta) (corner : CubeCorner) :
    c3RealPair
      ((alignedEightSiteState psiAmplitude chiAmplitude).chi corner)
      (eta corner) = 0 := by
  rw [c3_real_pair_eq_inner_re]
  change (c3Inner (c3ScaleComplex (chiAmplitude corner)
    (companion corner)) (eta corner)).re = 0
  rw [c3_inner_scale_left,
    hnormal corner]
  simp

theorem c3_inner_sub_right (u v z : C3) :
    c3Inner u (difference v z) = c3Inner u z - c3Inner u v := by
  unfold c3Inner difference
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro component _
  ring

theorem c3_inner_scale_left_general (a : ℂ) (u v : C3) :
    c3Inner (c3ScaleComplex a u) v = star a * c3Inner u v :=
  c3_inner_scale_left a u v

theorem aligned_psi_normal_wedge_pair_zero
    (psiAmplitude chiAmplitude : Cell8) (eta : CubeCorner → C3)
    (hnormal : PsiNormalDirection eta) (corner : CubeCorner) :
    c3Inner unitArea
      (wedge
        ((alignedEightSiteState psiAmplitude chiAmplitude).chi corner)
        (eta corner)) = 0 := by
  rw [show (alignedEightSiteState psiAmplitude chiAmplitude).chi corner =
      c3ScaleComplex (chiAmplitude corner) (companion corner) by rfl,
    wedge_scale_left]
  rw [show c3Inner unitArea
      (c3ScaleComplex (chiAmplitude corner)
        (wedge (companion corner) (eta corner))) =
      chiAmplitude corner * c3Inner unitArea
        (wedge (companion corner) (eta corner)) by
        unfold c3Inner c3ScaleComplex
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro component _
        ring,
    c3_inner_unitArea_wedge_companion, hnormal corner]
  simp

theorem aligned_chi_normal_wedge_pair_zero
    (psiAmplitude chiAmplitude : Cell8) (eta : CubeCorner → C3)
    (hnormal : ChiNormalDirection eta) (corner : CubeCorner) :
    c3Inner unitArea
      (wedge (eta corner)
        ((alignedEightSiteState psiAmplitude chiAmplitude).psi corner)) = 0 := by
  rw [show (alignedEightSiteState psiAmplitude chiAmplitude).psi corner =
      c3ScaleComplex (psiAmplitude corner) (tetraCorner corner) by rfl,
    wedge_scale_right]
  rw [show c3Inner unitArea
      (c3ScaleComplex (psiAmplitude corner)
        (wedge (eta corner) (tetraCorner corner))) =
      psiAmplitude corner * c3Inner unitArea
        (wedge (eta corner) (tetraCorner corner)) by
        unfold c3Inner c3ScaleComplex
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro component _
        ring,
    c3_inner_unitArea_wedge_tetra, hnormal corner]
  simp

theorem aligned_psi_normal_bond_pair_zero
    (psiAmplitude chiAmplitude : Cell8) (eta : CubeCorner → C3)
    (hnormal : PsiNormalDirection eta) (edge : Bond CubeCorner) :
    c3RealPair
      (bondAreaDifference (alignedEightSiteState psiAmplitude chiAmplitude) edge)
      (bondAreaFirstVariation (alignedEightSiteState psiAmplitude chiAmplitude)
        (purePsiDirection eta) edge) = 0 := by
  rw [c3_real_pair_eq_inner_re]
  unfold bondAreaDifference bondAreaFirstVariation
  rw [aligned_wedge, aligned_wedge]
  rw [show wedgeFirstVariation
      (alignedEightSiteState psiAmplitude chiAmplitude)
      (purePsiDirection eta) edge.source =
      wedge ((alignedEightSiteState psiAmplitude chiAmplitude).chi edge.source)
        (eta edge.source) by
        funext component
        fin_cases component <;>
          simp [wedgeFirstVariation, purePsiDirection, c3Add, c3Zero, wedge],
    show wedgeFirstVariation
      (alignedEightSiteState psiAmplitude chiAmplitude)
      (purePsiDirection eta) edge.target =
      wedge ((alignedEightSiteState psiAmplitude chiAmplitude).chi edge.target)
        (eta edge.target) by
        funext component
        fin_cases component <;>
          simp [wedgeFirstVariation, purePsiDirection, c3Add, c3Zero, wedge]]
  rw [show difference
      (c3ScaleComplex (-(chiAmplitude edge.source * psiAmplitude edge.source)) unitArea)
      (c3ScaleComplex (-(chiAmplitude edge.target * psiAmplitude edge.target)) unitArea) =
      c3ScaleComplex
        (chiAmplitude edge.source * psiAmplitude edge.source -
          chiAmplitude edge.target * psiAmplitude edge.target) unitArea by
        funext component; simp [difference, c3ScaleComplex]; ring]
  rw [c3_inner_scale_left_general]
  rw [c3_inner_sub_right,
    aligned_psi_normal_wedge_pair_zero _ _ eta hnormal edge.source,
    aligned_psi_normal_wedge_pair_zero _ _ eta hnormal edge.target]
  simp

theorem aligned_chi_normal_bond_pair_zero
    (psiAmplitude chiAmplitude : Cell8) (eta : CubeCorner → C3)
    (hnormal : ChiNormalDirection eta) (edge : Bond CubeCorner) :
    c3RealPair
      (bondAreaDifference (alignedEightSiteState psiAmplitude chiAmplitude) edge)
      (bondAreaFirstVariation (alignedEightSiteState psiAmplitude chiAmplitude)
        (pureChiDirection eta) edge) = 0 := by
  rw [c3_real_pair_eq_inner_re]
  unfold bondAreaDifference bondAreaFirstVariation
  rw [aligned_wedge, aligned_wedge]
  rw [show wedgeFirstVariation
      (alignedEightSiteState psiAmplitude chiAmplitude)
      (pureChiDirection eta) edge.source =
      wedge (eta edge.source)
        ((alignedEightSiteState psiAmplitude chiAmplitude).psi edge.source) by
        funext component
        fin_cases component <;>
          simp [wedgeFirstVariation, pureChiDirection, c3Add, c3Zero, wedge],
    show wedgeFirstVariation
      (alignedEightSiteState psiAmplitude chiAmplitude)
      (pureChiDirection eta) edge.target =
      wedge (eta edge.target)
        ((alignedEightSiteState psiAmplitude chiAmplitude).psi edge.target) by
        funext component
        fin_cases component <;>
          simp [wedgeFirstVariation, pureChiDirection, c3Add, c3Zero, wedge]]
  rw [show difference
      (c3ScaleComplex (-(chiAmplitude edge.source * psiAmplitude edge.source)) unitArea)
      (c3ScaleComplex (-(chiAmplitude edge.target * psiAmplitude edge.target)) unitArea) =
      c3ScaleComplex
        (chiAmplitude edge.source * psiAmplitude edge.source -
          chiAmplitude edge.target * psiAmplitude edge.target) unitArea by
        funext component; simp [difference, c3ScaleComplex]; ring]
  rw [c3_inner_scale_left_general]
  rw [c3_inner_sub_right,
    aligned_chi_normal_wedge_pair_zero _ _ eta hnormal edge.source,
    aligned_chi_normal_wedge_pair_zero _ _ eta hnormal edge.target]
  simp

theorem aligned_psi_cross_block_zero [Fintype Edge]
    (chi0 : ℝ) (psiAmplitude chiAmplitude : Cell8)
    (bond : Edge → Bond CubeCorner) (eta : CubeCorner → C3)
    (hnormal : PsiNormalDirection eta) :
    psiEulerLagrangeForce chi0
      (alignedEightSiteState psiAmplitude chiAmplitude) bond eta = 0 := by
  unfold psiEulerLagrangeForce lagrangianStateFirstVariation
  simp only [potentialFirstVariation, purePsiDirection,
    sitePotentialFirstVariation]
  rw [show (∑ site : CubeCorner,
      let rhoPsi := density
        ((alignedEightSiteState psiAmplitude chiAmplitude).psi site)
      let rhoChi := density
        ((alignedEightSiteState psiAmplitude chiAmplitude).chi site)
      (rhoChi - chi0 ^ 2 + rhoPsi) *
          c3RealPair
            ((alignedEightSiteState psiAmplitude chiAmplitude).chi site) c3Zero +
        (rhoChi + rhoPsi) *
          c3RealPair
            ((alignedEightSiteState psiAmplitude chiAmplitude).psi site)
            (eta site)) = 0 by
      apply Finset.sum_eq_zero
      intro site _
      rw [aligned_psi_normal_local_pair_zero _ _ eta hnormal site]
      simp [c3RealPair, c3Zero]]
  change -(0 + ∑ edge : Edge,
    exteriorAreaBondFirstVariation chi0
      (alignedEightSiteState psiAmplitude chiAmplitude)
      (purePsiDirection eta) (bond edge)) = 0
  rw [show (∑ edge : Edge,
      exteriorAreaBondFirstVariation chi0
        (alignedEightSiteState psiAmplitude chiAmplitude)
        (purePsiDirection eta) (bond edge)) = 0 by
      apply Finset.sum_eq_zero
      intro edge _
      unfold exteriorAreaBondFirstVariation
      rw [aligned_psi_normal_bond_pair_zero _ _ eta hnormal (bond edge)]
      ring]
  ring

theorem aligned_chi_cross_block_zero [Fintype Edge]
    (chi0 : ℝ) (psiAmplitude chiAmplitude : Cell8)
    (bond : Edge → Bond CubeCorner) (eta : CubeCorner → C3)
    (hnormal : ChiNormalDirection eta) :
    chiEulerLagrangeForce chi0
      (alignedEightSiteState psiAmplitude chiAmplitude) bond eta = 0 := by
  unfold chiEulerLagrangeForce lagrangianStateFirstVariation
  simp only [potentialFirstVariation, pureChiDirection,
    sitePotentialFirstVariation]
  rw [show (∑ site : CubeCorner,
      let rhoPsi := density
        ((alignedEightSiteState psiAmplitude chiAmplitude).psi site)
      let rhoChi := density
        ((alignedEightSiteState psiAmplitude chiAmplitude).chi site)
      (rhoChi - chi0 ^ 2 + rhoPsi) *
          c3RealPair
            ((alignedEightSiteState psiAmplitude chiAmplitude).chi site)
            (eta site) +
        (rhoChi + rhoPsi) *
          c3RealPair
            ((alignedEightSiteState psiAmplitude chiAmplitude).psi site) c3Zero) = 0 by
      apply Finset.sum_eq_zero
      intro site _
      rw [aligned_chi_normal_local_pair_zero _ _ eta hnormal site]
      simp [c3RealPair, c3Zero]]
  change -(0 + ∑ edge : Edge,
    exteriorAreaBondFirstVariation chi0
      (alignedEightSiteState psiAmplitude chiAmplitude)
      (pureChiDirection eta) (bond edge)) = 0
  rw [show (∑ edge : Edge,
      exteriorAreaBondFirstVariation chi0
        (alignedEightSiteState psiAmplitude chiAmplitude)
        (pureChiDirection eta) (bond edge)) = 0 by
      apply Finset.sum_eq_zero
      intro edge _
      unfold exteriorAreaBondFirstVariation
      rw [aligned_chi_normal_bond_pair_zero _ _ eta hnormal (bond edge)]
      ring]
  ring

/-- Componentwise difference `u - v` of two vectors in `ℂ³`. -/
def c3Sub (u v : C3) : C3 := fun component => u component - v component

/-- The residual `z - (c3Inner u z) • u` of `z` after removing its component along `u`. -/
def rayResidual (u z : C3) : C3 :=
  c3Sub z (c3ScaleComplex (c3Inner u z) u)

theorem c3_inner_self (u : C3) :
    c3Inner u u = (density u : ℂ) := by
  apply Complex.ext
  · simp [c3Inner, density, Fin.sum_univ_succ, Complex.normSq]
  · simp [c3Inner, density, Fin.sum_univ_succ, Complex.normSq]
    ring

theorem c3_inner_sub_right_general (u v z : C3) :
    c3Inner u (c3Sub v z) = c3Inner u v - c3Inner u z := by
  unfold c3Inner c3Sub
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro component _
  ring

theorem c3_inner_scale_right (a : ℂ) (u v : C3) :
    c3Inner u (c3ScaleComplex a v) = a * c3Inner u v := by
  unfold c3Inner c3ScaleComplex
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro component _
  ring

theorem ray_residual_normal (u z : C3) (hnorm : density u = 1) :
    ComplexNormalTo u (rayResidual u z) := by
  unfold ComplexNormalTo rayResidual
  rw [c3_inner_sub_right_general, c3_inner_scale_right,
    c3_inner_self, hnorm]
  norm_num

theorem c3_real_pair_self (u : C3) : c3RealPair u u = density u := by
  rw [c3_real_pair_eq_inner_re, c3_inner_self]
  simp

theorem c3_real_pair_scale_left_zero (a : ℂ) (u v : C3)
    (h : c3Inner u v = 0) :
    c3RealPair (c3ScaleComplex a u) v = 0 := by
  rw [c3_real_pair_eq_inner_re, c3_inner_scale_left, h]
  simp

theorem ray_plus_residual (u z : C3) :
    c3Add (c3ScaleComplex (c3Inner u z) u) (rayResidual u z) = z := by
  funext component
  simp [c3Add, c3ScaleComplex, rayResidual, c3Sub]

theorem c3_real_pair_with_residual (u z : C3)
    (hnorm : density u = 1) :
    c3RealPair z (rayResidual u z) = density (rayResidual u z) := by
  calc
    c3RealPair z (rayResidual u z) =
        c3RealPair
          (c3Add (c3ScaleComplex (c3Inner u z) u) (rayResidual u z))
          (rayResidual u z) := by rw [ray_plus_residual]
    _ = c3RealPair (c3ScaleComplex (c3Inner u z) u) (rayResidual u z) +
        c3RealPair (rayResidual u z) (rayResidual u z) := by
          change c3RealPair
            (fun component =>
              c3ScaleComplex (c3Inner u z) u component +
                rayResidual u z component)
            (rayResidual u z) = _
          rw [c3_real_pair_add_left]
    _ = density (rayResidual u z) := by
      rw [c3_real_pair_scale_left_zero _ _ _
          (ray_residual_normal u z hnorm),
        c3_real_pair_self]
      ring

theorem density_zero_implies_c3_zero (u : C3) (h : density u = 0) :
    u = c3Zero := by
  have hsum := h
  simp [density, Fin.sum_univ_succ, Complex.normSq] at hsum
  funext component
  fin_cases component <;> apply Complex.ext <;> simp [c3Zero] <;>
    nlinarith [sq_nonneg (u 0).re, sq_nonneg (u 0).im,
      sq_nonneg (u 1).re, sq_nonneg (u 1).im,
      sq_nonneg (u 2).re, sq_nonneg (u 2).im]

/-- The field on the cube corners equal to `z` at the corner `selected` and zero elsewhere. -/
def singleSiteField (selected : CubeCorner) (z : C3) : CubeCorner → C3 :=
  fun site => if site = selected then z else c3Zero

theorem single_site_psi_normal (selected : CubeCorner) (z : C3)
    (h : ComplexNormalTo (tetraCorner selected) z) :
    PsiNormalDirection (singleSiteField selected z) := by
  intro site
  by_cases hs : site = selected
  · subst hs
    simpa [singleSiteField] using h
  · simp [singleSiteField, hs, ComplexNormalTo, c3Inner, c3Zero]

theorem single_site_chi_normal (selected : CubeCorner) (z : C3)
    (h : ComplexNormalTo (companion selected) z) :
    ChiNormalDirection (singleSiteField selected z) := by
  intro site
  by_cases hs : site = selected
  · subst hs
    simpa [singleSiteField] using h
  · simp [singleSiteField, hs, ComplexNormalTo, c3Inner, c3Zero]

theorem psi_momentum_single_site
    (velocity : Velocity CubeCorner) (selected : CubeCorner) (z : C3) :
    psiMomentumPair velocity (singleSiteField selected z) =
      c3RealPair (velocity.psiDot selected) z := by
  unfold psiMomentumPair
  rw [Finset.sum_eq_single selected]
  · simp [singleSiteField]
  · intro other _ hne
    simp [singleSiteField, hne, c3RealPair, c3Zero]
  · simp

theorem chi_momentum_single_site
    (B : ℝ) (velocity : Velocity CubeCorner) (selected : CubeCorner) (z : C3) :
    chiMomentumPair B velocity (singleSiteField selected z) =
      B * c3RealPair (velocity.chiDot selected) z := by
  unfold chiMomentumPair
  rw [Finset.sum_eq_single selected]
  · simp [singleSiteField]
  · intro other _ hne
    simp [singleSiteField, hne, c3RealPair, c3Zero]
  · simp

theorem companion_density_one (corner : CubeCorner) :
    density (companion corner) = 1 := by
  fin_cases corner <;>
    simp [density, Fin.sum_univ_succ, companion, tetraCorner,
      tetraRay0, tetraRay1, tetraRay2, tetraRay3, c3Of, c3Neg,
      tetraA, tetraB, omega, omegaBar, Complex.normSq] <;>
    field_simp [sqrt_three_ne_zero] <;> ring_nf <;>
    nlinarith [sqrt_three_sq, sqrt_two_sq, sqrt_three_pow_four,
      sqrt_three_pow_five, sqrt_three_pow_six, sqrt_three_pow_eight,
      sqrt_two_pow_four]

theorem recover_aligned_eight_site_amplitudes
    (amplitudes : NativeUnitCellAmplitudes) :
    recoverEightSiteAmplitudes
        (alignedEightSiteStateFromAmplitudes amplitudes) = amplitudes := by
  rcases amplitudes with ⟨psiAmplitude, chiAmplitude⟩
  apply Prod.ext <;> funext corner
  · simp [recoverEightSiteAmplitudes,
      alignedEightSiteStateFromAmplitudes, alignedEightSiteState,
      c3_inner_scale_right, c3_inner_self, tetra_corner_density_one]
  · simp [recoverEightSiteAmplitudes,
      alignedEightSiteStateFromAmplitudes, alignedEightSiteState,
      c3_inner_scale_right, c3_inner_self, companion_density_one]

theorem aligned_eight_site_state_from_amplitudes_injective :
    Function.Injective alignedEightSiteStateFromAmplitudes := by
  intro first second hequal
  calc
    first = recoverEightSiteAmplitudes
        (alignedEightSiteStateFromAmplitudes first) :=
      (recover_aligned_eight_site_amplitudes first).symm
    _ = recoverEightSiteAmplitudes
        (alignedEightSiteStateFromAmplitudes second) := congrArg _ hequal
    _ = second := recover_aligned_eight_site_amplitudes second

theorem aligned_recovered_state_of_in_eight_site_sector
    (state : State CubeCorner) (hstate : InEightSiteSector state) :
    alignedEightSiteStateFromAmplitudes
        (recoverEightSiteAmplitudes state) = state := by
  rcases hstate with ⟨psiAmplitude, chiAmplitude, rfl⟩
  change alignedEightSiteStateFromAmplitudes
      (recoverEightSiteAmplitudes
        (alignedEightSiteStateFromAmplitudes
          (psiAmplitude, chiAmplitude))) =
    alignedEightSiteStateFromAmplitudes (psiAmplitude, chiAmplitude)
  rw [recover_aligned_eight_site_amplitudes]

/-- The subtype of cube states lying in the eight-site sector `InEightSiteSector`. -/
abbrev EightSiteSectorState :=
  { state : State CubeCorner // InEightSiteSector state }

/-- The equivalence between pairs of eight-corner amplitudes and states in the eight-site sector,
given by `alignedEightSiteStateFromAmplitudes` with inverse `recoverEightSiteAmplitudes`. -/
def nativeUnitCellAmplitudeSectorEquiv :
    NativeUnitCellAmplitudes ≃ EightSiteSectorState where
  toFun amplitudes :=
    ⟨alignedEightSiteStateFromAmplitudes amplitudes,
      ⟨amplitudes.1, amplitudes.2, rfl⟩⟩
  invFun sectorState := recoverEightSiteAmplitudes sectorState.1
  left_inv := recover_aligned_eight_site_amplitudes
  right_inv := by
    intro sectorState
    apply Subtype.ext
    exact aligned_recovered_state_of_in_eight_site_sector
      sectorState.1 sectorState.2

/-- At each corner, the inner product with `tetraCorner corner` of the `psi` component of
`accelerationVelocity` evaluated at the aligned state built from the two amplitudes. -/
def psiAccelerationAmplitude [Fintype Edge]
    (chi0 B : ℝ) (psiAmplitude chiAmplitude : Cell8)
    (bond : Edge → Bond CubeCorner) : Cell8 :=
  fun corner => c3Inner (tetraCorner corner)
    ((accelerationVelocity chi0 B
      (alignedEightSiteState psiAmplitude chiAmplitude) bond).psiDot corner)

/-- At each corner, the inner product with `companion corner` of the `chi` component of
`accelerationVelocity` evaluated at the aligned state built from the two amplitudes. -/
def chiAccelerationAmplitude [Fintype Edge]
    (chi0 B : ℝ) (psiAmplitude chiAmplitude : Cell8)
    (bond : Edge → Bond CubeCorner) : Cell8 :=
  fun corner => c3Inner (companion corner)
    ((accelerationVelocity chi0 B
      (alignedEightSiteState psiAmplitude chiAmplitude) bond).chiDot corner)

theorem aligned_psi_acceleration [Fintype Edge]
    (chi0 B : ℝ) (psiAmplitude chiAmplitude : Cell8)
    (bond : Edge → Bond CubeCorner) (corner : CubeCorner) :
    (accelerationVelocity chi0 B
      (alignedEightSiteState psiAmplitude chiAmplitude) bond).psiDot corner =
      c3ScaleComplex
        (psiAccelerationAmplitude chi0 B psiAmplitude chiAmplitude bond corner)
        (tetraCorner corner) := by
  let acceleration := accelerationVelocity chi0 B
    (alignedEightSiteState psiAmplitude chiAmplitude) bond
  let residual := rayResidual (tetraCorner corner)
    (acceleration.psiDot corner)
  have hnormal : ComplexNormalTo (tetraCorner corner) residual := by
    exact ray_residual_normal _ _ (tetra_corner_density_one corner)
  have hall := psi_acceleration_all_directions chi0 B
    (alignedEightSiteState psiAmplitude chiAmplitude) bond
    (singleSiteField corner residual)
  rw [aligned_psi_cross_block_zero chi0 psiAmplitude chiAmplitude bond
      (singleSiteField corner residual)
      (single_site_psi_normal corner residual hnormal)] at hall
  rw [psi_momentum_single_site] at hall
  have hpair : c3RealPair (acceleration.psiDot corner) residual = 0 := by
    exact hall
  rw [show residual = rayResidual (tetraCorner corner)
      (acceleration.psiDot corner) by rfl,
    c3_real_pair_with_residual _ _ (tetra_corner_density_one corner)] at hpair
  have hresidual := density_zero_implies_c3_zero residual hpair
  funext component
  have hc := congrFun hresidual component
  simp only [rayResidual, c3Sub, c3ScaleComplex, c3Zero, psiAccelerationAmplitude, residual,
      acceleration] at hc ⊢
  exact sub_eq_zero.mp hc

theorem aligned_chi_acceleration [Fintype Edge]
    (chi0 B : ℝ) (hB : B ≠ 0)
    (psiAmplitude chiAmplitude : Cell8)
    (bond : Edge → Bond CubeCorner) (corner : CubeCorner) :
    (accelerationVelocity chi0 B
      (alignedEightSiteState psiAmplitude chiAmplitude) bond).chiDot corner =
      c3ScaleComplex
        (chiAccelerationAmplitude chi0 B psiAmplitude chiAmplitude bond corner)
        (companion corner) := by
  let acceleration := accelerationVelocity chi0 B
    (alignedEightSiteState psiAmplitude chiAmplitude) bond
  let residual := rayResidual (companion corner)
    (acceleration.chiDot corner)
  have hnormal : ComplexNormalTo (companion corner) residual := by
    exact ray_residual_normal _ _ (companion_density_one corner)
  have hall := chi_acceleration_all_directions chi0 B
    (alignedEightSiteState psiAmplitude chiAmplitude) bond hB
    (singleSiteField corner residual)
  rw [aligned_chi_cross_block_zero chi0 psiAmplitude chiAmplitude bond
      (singleSiteField corner residual)
      (single_site_chi_normal corner residual hnormal)] at hall
  rw [chi_momentum_single_site] at hall
  have hpair : c3RealPair (acceleration.chiDot corner) residual = 0 := by
    exact (mul_eq_zero.mp hall).resolve_left hB
  rw [show residual = rayResidual (companion corner)
      (acceleration.chiDot corner) by rfl,
    c3_real_pair_with_residual _ _ (companion_density_one corner)] at hpair
  have hresidual := density_zero_implies_c3_zero residual hpair
  funext component
  have hc := congrFun hresidual component
  simp only [rayResidual, c3Sub, c3ScaleComplex, c3Zero, chiAccelerationAmplitude, residual,
      acceleration] at hc ⊢
  exact sub_eq_zero.mp hc

theorem native_next_preserves_eight_site_sector [Fintype Edge]
    (chi0 B dt : ℝ) (hB : B ≠ 0) (bond : Edge → Bond CubeCorner)
    (previous current : State CubeCorner)
    (hprevious : InEightSiteSector previous)
    (hcurrent : InEightSiteSector current) :
    InEightSiteSector
      (nativeNextState chi0 B dt bond previous current) := by
  rcases hprevious with ⟨previousPsi, previousChi, rfl⟩
  rcases hcurrent with ⟨currentPsi, currentChi, rfl⟩
  let accelerationPsi :=
    psiAccelerationAmplitude chi0 B currentPsi currentChi bond
  let accelerationChi :=
    chiAccelerationAmplitude chi0 B currentPsi currentChi bond
  refine ⟨fun corner =>
      2 * currentPsi corner - previousPsi corner +
        (dt ^ 2 : ℂ) * accelerationPsi corner,
    fun corner =>
      2 * currentChi corner - previousChi corner +
        (dt ^ 2 : ℂ) * accelerationChi corner, ?_⟩
  apply congrArg₂ State.mk <;> funext corner component
  · rw [show
      (accelerationVelocity chi0 B
        (alignedEightSiteState currentPsi currentChi) bond).psiDot corner =
        c3ScaleComplex (accelerationPsi corner) (tetraCorner corner) by
          exact aligned_psi_acceleration chi0 B currentPsi currentChi bond corner]
    simp [alignedEightSiteState, c3ScaleComplex,
      accelerationPsi]
    ring
  · rw [show
      (accelerationVelocity chi0 B
        (alignedEightSiteState currentPsi currentChi) bond).chiDot corner =
        c3ScaleComplex (accelerationChi corner) (companion corner) by
          exact aligned_chi_acceleration chi0 B hB currentPsi currentChi bond corner]
    simp [alignedEightSiteState, c3ScaleComplex,
      accelerationChi]
    ring

/-!
Period-two C19 geometry.  This connects the eight-site table used by the
sector proof to the already declared periodic C19 coordinate geometry.
-/

/-- The involution of `Fin 8` that toggles the binary digit of value `4` (`i ↦ i xor 4`). -/
def cellFlip0 : Fin 8 → Fin 8
  | 0 => 4 | 1 => 5 | 2 => 6 | 3 => 7
  | 4 => 0 | 5 => 1 | 6 => 2 | _ => 3

/-- The involution of `Fin 8` that toggles the binary digit of value `2` (`i ↦ i xor 2`). -/
def cellFlip1 : Fin 8 → Fin 8
  | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1
  | 4 => 6 | 5 => 7 | 6 => 4 | _ => 5

/-- The involution of `Fin 8` that toggles the binary digit of value `1` (`i ↦ i xor 1`). -/
def cellFlip2 : Fin 8 → Fin 8
  | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2
  | 4 => 5 | 5 => 4 | 6 => 7 | _ => 6

/-- The binary digit of value `1` of an element of `Fin 8`. -/
def cellBit2 : Fin 8 → Nat
  | 0 | 2 | 4 | 6 => 0
  | _ => 1

/-- The binary digit of value `4` of an element of `Fin 8`. -/
def cellBit0 : Fin 8 → Nat
  | 0 | 1 | 2 | 3 => 0
  | _ => 1

/-- The binary digit of value `2` of an element of `Fin 8`. -/
def cellBit1 : Fin 8 → Nat
  | 0 | 1 | 4 | 5 => 0
  | _ => 1

/-- The site of the period-two cubic lattice whose coordinates along axes `0`, `1`, `2` are the
binary digits `cellBit0`, `cellBit1`, `cellBit2` of the corner. -/
def cubeCornerCoordinate (corner : CubeCorner) : PeriodicCubicSite 2
  | 0 => cellBit0 corner
  | 1 => cellBit1 corner
  | _ => cellBit2 corner

theorem cube_corner_coordinate_injective :
    Function.Injective cubeCornerCoordinate := by
  intro a b
  fin_cases a <;> fin_cases b <;> decide

/-- The C19 neighbor map on the eight cube corners with period two: each direction toggles the
binary digits of the corner along the axes on which its offset is nonzero. -/
def cubeC19Neighbor (corner : CubeCorner)
    (direction : C19Neighbor) : CubeCorner :=
  match direction.val with
  | 0 | 1 => cellFlip0 corner
  | 2 | 3 => cellFlip1 corner
  | 4 | 5 => cellFlip2 corner
  | 6 | 7 | 8 | 9 => cellFlip0 (cellFlip1 corner)
  | 10 | 11 | 12 | 13 => cellFlip0 (cellFlip2 corner)
  | _ => cellFlip1 (cellFlip2 corner)

theorem cube_c19_neighbor_reverse (corner : CubeCorner)
    (direction : C19Neighbor) :
    cubeC19Neighbor (cubeC19Neighbor corner direction)
      (c19Reverse direction) = corner := by
  fin_cases corner <;> fin_cases direction <;>
    rfl

theorem cube_c19_neighbor_is_periodic_c19 (corner : CubeCorner)
    (direction : C19Neighbor) :
    cubeCornerCoordinate (cubeC19Neighbor corner direction) =
      periodicC19Neighbor 2 (cubeCornerCoordinate corner) direction := by
  funext axis
  fin_cases corner <;> fin_cases direction <;> fin_cases axis <;>
    decide

/-- The number of axes `axis` with `c19Coord axis direction ≠ 0`. -/
def c19NonzeroAxisCount (direction : C19Neighbor) : Nat :=
  (Finset.univ.filter (fun axis : Fin 3 => c19Coord axis direction ≠ 0)).card

theorem c19_direction_has_declared_class (direction : C19Neighbor) :
    (direction.val < 6 ∧ c19NonzeroAxisCount direction = 1 ∧
      c19Weight direction = 2) ∨
    (6 ≤ direction.val ∧ c19NonzeroAxisCount direction = 2 ∧
      c19Weight direction = 1) := by
  fin_cases direction <;>
    norm_num [c19Weight]
  all_goals decide

/-- The C19 lattice structure on the eight cube corners with neighbor map `cubeC19Neighbor`. -/
def cubeC19Geometry : C19Lattice CubeCorner where
  neighbor := cubeC19Neighbor
  neighbor_reverse := cube_c19_neighbor_reverse

/-- The DIRAC-005 statement bundle: amplitude recovery and reconstruction for the eight-site
sector, the coordinate counts `16` and `32`, vanishing of the `psi` and `chi` first-variation
forces along normal directions, and preservation of the sector by `nativeNextState`. -/
structure Dirac005Certificate [Fintype Edge]
    (chi0 B dt : ℝ) (bond : Edge → Bond CubeCorner)
    (previous current : State CubeCorner) : Prop where
  amplitudeRecovery : ∀ amplitudes : NativeUnitCellAmplitudes,
    recoverEightSiteAmplitudes
        (alignedEightSiteStateFromAmplitudes amplitudes) = amplitudes
  sectorReconstruction : ∀ state : State CubeCorner,
    InEightSiteSector state →
      alignedEightSiteStateFromAmplitudes
        (recoverEightSiteAmplitudes state) = state
  stateSliceCoordinateCount : Fintype.card NativeUnitCellCoordinate = 16
  twoLayerCoordinateCount :
    Fintype.card NativeUnitCellTwoLayerCoordinate = 32
  psiCrossBlockZero : ∀ psiAmplitude chiAmplitude eta,
    PsiNormalDirection eta →
    psiEulerLagrangeForce chi0
      (alignedEightSiteState psiAmplitude chiAmplitude) bond eta = 0
  chiCrossBlockZero : ∀ psiAmplitude chiAmplitude eta,
    ChiNormalDirection eta →
    chiEulerLagrangeForce chi0
      (alignedEightSiteState psiAmplitude chiAmplitude) bond eta = 0
  updateClosure : InEightSiteSector previous → InEightSiteSector current →
    InEightSiteSector (nativeNextState chi0 B dt bond previous current)

theorem dirac005_native_sector [Fintype Edge]
    (chi0 B dt : ℝ) (hB : B ≠ 0) (bond : Edge → Bond CubeCorner)
    (previous current : State CubeCorner) :
    Dirac005Certificate chi0 B dt bond previous current where
  amplitudeRecovery := recover_aligned_eight_site_amplitudes
  sectorReconstruction := aligned_recovered_state_of_in_eight_site_sector
  stateSliceCoordinateCount := native_unit_cell_coordinate_count
  twoLayerCoordinateCount := native_unit_cell_two_layer_coordinate_count
  psiCrossBlockZero := fun psiAmplitude chiAmplitude eta hnormal =>
    aligned_psi_cross_block_zero chi0 psiAmplitude chiAmplitude bond eta hnormal
  chiCrossBlockZero := fun psiAmplitude chiAmplitude eta hnormal =>
    aligned_chi_cross_block_zero chi0 psiAmplitude chiAmplitude bond eta hnormal
  updateClosure := fun hprevious hcurrent =>
    native_next_preserves_eight_site_sector chi0 B dt hB bond
      previous current hprevious hcurrent

theorem dirac005_c19_native_sector
    (dt : ℝ) (previous current : State CubeCorner) :
    Dirac005Certificate chi0 chiKineticNormalization dt
      (c19Bond cubeC19Geometry) previous current :=
  dirac005_native_sector chi0 chiKineticNormalization dt
    (by rw [chi_kinetic_normalization_eq_1197]; norm_num)
    (c19Bond cubeC19Geometry) previous current

end
end LeanDirac
