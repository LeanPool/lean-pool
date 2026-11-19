/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac016.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac015

/-!
# DIRAC-016: exact copy exchange under microscopic cube translation

DIRAC-009 and DIRAC-010 retain two rank-four cubical copies of the same
continuum Dirac representation.  This file asks a narrower question: how do
those two copies transform under the already-defined period-two cube
translations?

`rawCubeTranslation` is the unsigned permutation of the eight corner values.
It is derived from `cubeIncidenceFlip`; it is not a new action term, update
rule, field, or projection.  The proofs below show that translation across
the third cube direction exchanges the two copies exactly, while a second
translation returns to the original copy.  They also show that the signed
incidence operator used in the existing Dirac readout preserves each copy.

Consequently this module proves an exact A--B--A translation algebra.  It
does **not** prove that one native time update is one copy exchange, that a
localized carrier moves by alternating copies, or that either copy is a
second physical particle.  Those require a native moving-state theorem.
-/

@[expose] public section


namespace LeanDirac

noncomputable section

def rawCubeTranslation (axis : Fin 3) (amplitude : Cell8) : Cell8 :=
  fun corner => amplitude (cubeIncidenceFlip axis corner)

/-! The four-component coordinate permutation induced by the exchanging
cube translation.  Its formula is verified below against both embeddings,
and injectivity proves that it is the unique coordinate map with that
property. -/
def standardCopyHalfShift (z : Cell4) : Cell4
  | 0 => z 2
  | 1 => z 3
  | 2 => z 0
  | _ => z 1

theorem standard_copy_half_shift_twice (z : Cell4) :
    standardCopyHalfShift (standardCopyHalfShift z) = z := by
  funext component
  fin_cases component <;> rfl

theorem raw_cube_translation_twice
    (axis : Fin 3) (amplitude : Cell8) :
    rawCubeTranslation axis (rawCubeTranslation axis amplitude) = amplitude := by
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [rawCubeTranslation, cubeIncidenceFlip, cellFlip0, cellFlip1,
      cellFlip2]

theorem raw_axis0_preserves_flavor (amplitude : Cell8) :
    cubeFlavor (rawCubeTranslation 0 amplitude) =
      rawCubeTranslation 0 (cubeFlavor amplitude) := by
  funext corner
  fin_cases corner <;>
    simp [cubeFlavor, cubeFlavorSign, rawCubeTranslation,
      cubeIncidenceFlip, cellFlip0, cellFlip1, cellFlip2, cellBit2]

theorem raw_axis1_preserves_flavor (amplitude : Cell8) :
    cubeFlavor (rawCubeTranslation 1 amplitude) =
      rawCubeTranslation 1 (cubeFlavor amplitude) := by
  funext corner
  fin_cases corner <;>
    simp [cubeFlavor, cubeFlavorSign, rawCubeTranslation,
      cubeIncidenceFlip, cellFlip1, cellFlip2, cellBit2]

theorem raw_axis2_reverses_flavor (amplitude : Cell8) :
    cubeFlavor (rawCubeTranslation 2 amplitude) =
      fun corner => -rawCubeTranslation 2 (cubeFlavor amplitude) corner := by
  funext corner
  fin_cases corner <;>
    simp [cubeFlavor, cubeFlavorSign, rawCubeTranslation,
      cubeIncidenceFlip, cellFlip1, cellFlip2, cellBit2]

theorem raw_axis2_maps_minus_to_plus (z : Cell4) :
    rawCubeTranslation 2 (cubeDiracEmbedMinus z) =
      cubeDiracEmbedPlus (standardCopyHalfShift z) := by
  funext corner
  fin_cases corner <;>
    simp [rawCubeTranslation, cubeIncidenceFlip, cellFlip2,
      cubeDiracEmbedMinus, cubeDiracEmbedPlus, cubeEmbedMinus,
      cubeEmbedPlus, standardToMinusCubeSpinor,
      standardToPlusCubeSpinor, standardCopyHalfShift]

theorem raw_axis2_maps_plus_to_minus (z : Cell4) :
    rawCubeTranslation 2 (cubeDiracEmbedPlus z) =
      cubeDiracEmbedMinus (standardCopyHalfShift z) := by
  funext corner
  fin_cases corner <;>
    simp [rawCubeTranslation, cubeIncidenceFlip, cellFlip2,
      cubeDiracEmbedMinus, cubeDiracEmbedPlus, cubeEmbedMinus,
      cubeEmbedPlus, standardToMinusCubeSpinor,
      standardToPlusCubeSpinor, standardCopyHalfShift]

theorem raw_axis2_minus_coordinate_map_unique (z : Cell4) :
    ∃! shifted : Cell4,
      rawCubeTranslation 2 (cubeDiracEmbedMinus z) =
        cubeDiracEmbedPlus shifted := by
  refine ⟨standardCopyHalfShift z, raw_axis2_maps_minus_to_plus z, ?_⟩
  intro shifted hshifted
  exact cube_dirac_embed_plus_injective
    (hshifted.symm.trans (raw_axis2_maps_minus_to_plus z))

theorem raw_axis2_plus_coordinate_map_unique (z : Cell4) :
    ∃! shifted : Cell4,
      rawCubeTranslation 2 (cubeDiracEmbedPlus z) =
        cubeDiracEmbedMinus shifted := by
  refine ⟨standardCopyHalfShift z, raw_axis2_maps_plus_to_minus z, ?_⟩
  intro shifted hshifted
  exact cube_dirac_embed_minus_injective
    (hshifted.symm.trans (raw_axis2_maps_plus_to_minus z))

theorem raw_axis2_two_steps_return_minus (z : Cell4) :
    rawCubeTranslation 2
        (rawCubeTranslation 2 (cubeDiracEmbedMinus z)) =
      cubeDiracEmbedMinus z := by
  rw [raw_axis2_maps_minus_to_plus, raw_axis2_maps_plus_to_minus,
    standard_copy_half_shift_twice]

theorem raw_axis2_two_steps_return_plus (z : Cell4) :
    rawCubeTranslation 2
        (rawCubeTranslation 2 (cubeDiracEmbedPlus z)) =
      cubeDiracEmbedPlus z := by
  rw [raw_axis2_maps_plus_to_minus, raw_axis2_maps_minus_to_plus,
    standard_copy_half_shift_twice]

theorem raw_cube_translation_preserves_density
    (axis : Fin 3) (amplitude : Cell8) :
    cell8Density (rawCubeTranslation axis amplitude) =
      cell8Density amplitude := by
  fin_cases axis <;>
    simp [cell8Density, rawCubeTranslation, cubeIncidenceFlip,
      cellFlip0, cellFlip1, cellFlip2, Fin.sum_univ_succ] <;>
    ring

/-! The full C19 neighborhood contains both copy-preserving and
copy-exchanging translation classes.  Their declared relative weights are
exactly balanced; this is a consequence of the existing C19 table, not a
new coefficient choice. -/
def rawC19Translation
    (direction : C19Neighbor) (amplitude : Cell8) : Cell8 :=
  fun corner => amplitude (cubeC19Neighbor corner direction)

theorem raw_c19_translation_copy_relation
    (direction : C19Neighbor) (amplitude : Cell8) :
    cubeFlavor (rawC19Translation direction amplitude) =
      if c19Coord 2 direction = 0 then
        rawC19Translation direction (cubeFlavor amplitude)
      else
        fun corner => -rawC19Translation direction
          (cubeFlavor amplitude) corner := by
  funext corner
  fin_cases direction <;> fin_cases corner <;>
    simp [rawC19Translation, cubeC19Neighbor, c19Coord,
      cubeFlavor, cubeFlavorSign, cellFlip0, cellFlip1, cellFlip2,
      cellBit2]

def c19CopyExchangeWeight : ℝ :=
  ∑ direction : C19Neighbor,
    if c19Coord 2 direction = 0 then 0 else c19Weight direction

def c19CopyPreservingWeight : ℝ :=
  ∑ direction : C19Neighbor,
    if c19Coord 2 direction = 0 then c19Weight direction else 0

theorem c19_copy_exchange_weight_eq_twelve :
    c19CopyExchangeWeight = 12 := by
  norm_num [c19CopyExchangeWeight, c19Coord, c19Weight,
    Fin.sum_univ_succ]

theorem c19_copy_preserving_weight_eq_twelve :
    c19CopyPreservingWeight = 12 := by
  norm_num [c19CopyPreservingWeight, c19Coord, c19Weight,
    Fin.sum_univ_succ]

/-! In contrast with unsigned translation, the signed incidence transport
that appears in the existing cubical Dirac readout stays inside each copy. -/
theorem prepared_incidence_axis2_preserves_minus (z : Cell4) :
    cubeIncidenceGamma 2 (cubeDiracEmbedMinus z) =
      fun corner => -cubeDiracEmbedMinus (standardDiracAlphaX z) corner :=
  cube_gamma2_intertwines_minus z

theorem prepared_incidence_axis2_preserves_plus (z : Cell4) :
    cubeIncidenceGamma 2 (cubeDiracEmbedPlus z) =
      fun corner => -cubeDiracEmbedPlus (standardDiracAlphaX z) corner :=
  cube_gamma2_intertwines_plus z

structure Dirac016CopyTranslationCertificate : Prop where
  priorDerivation : LFMFreeDiracContinuumCertificate
  translationIsInvolutive : ∀ axis amplitude,
    rawCubeTranslation axis (rawCubeTranslation axis amplitude) = amplitude
  axis0PreservesCopy : ∀ amplitude,
    cubeFlavor (rawCubeTranslation 0 amplitude) =
      rawCubeTranslation 0 (cubeFlavor amplitude)
  axis1PreservesCopy : ∀ amplitude,
    cubeFlavor (rawCubeTranslation 1 amplitude) =
      rawCubeTranslation 1 (cubeFlavor amplitude)
  axis2ExchangesCopy : ∀ amplitude,
    cubeFlavor (rawCubeTranslation 2 amplitude) =
      fun corner => -rawCubeTranslation 2 (cubeFlavor amplitude) corner
  minusToPlus : ∀ z,
    rawCubeTranslation 2 (cubeDiracEmbedMinus z) =
      cubeDiracEmbedPlus (standardCopyHalfShift z)
  plusToMinus : ∀ z,
    rawCubeTranslation 2 (cubeDiracEmbedPlus z) =
      cubeDiracEmbedMinus (standardCopyHalfShift z)
  coordinateMapIsUnique :
    (∀ z, ∃! shifted,
      rawCubeTranslation 2 (cubeDiracEmbedMinus z) =
        cubeDiracEmbedPlus shifted) ∧
    (∀ z, ∃! shifted,
      rawCubeTranslation 2 (cubeDiracEmbedPlus z) =
        cubeDiracEmbedMinus shifted)
  densityIsPreserved : ∀ axis amplitude,
    cell8Density (rawCubeTranslation axis amplitude) = cell8Density amplitude
  c19DirectionsHaveDerivedCopyClass : ∀ direction amplitude,
    cubeFlavor (rawC19Translation direction amplitude) =
      if c19Coord 2 direction = 0 then
        rawC19Translation direction (cubeFlavor amplitude)
      else
        fun corner => -rawC19Translation direction
          (cubeFlavor amplitude) corner
  c19PathWeightsBalance :
    c19CopyExchangeWeight = 12 ∧ c19CopyPreservingWeight = 12
  signedIncidencePreservesCopies :
    (∀ z, cubeIncidenceGamma 2 (cubeDiracEmbedMinus z) =
      fun corner => -cubeDiracEmbedMinus (standardDiracAlphaX z) corner) ∧
    (∀ z, cubeIncidenceGamma 2 (cubeDiracEmbedPlus z) =
      fun corner => -cubeDiracEmbedPlus (standardDiracAlphaX z) corner)

theorem dirac016_exact_copy_translation_structure :
    Dirac016CopyTranslationCertificate where
  priorDerivation := lfm_free_dirac_continuum_limit
  translationIsInvolutive := raw_cube_translation_twice
  axis0PreservesCopy := raw_axis0_preserves_flavor
  axis1PreservesCopy := raw_axis1_preserves_flavor
  axis2ExchangesCopy := raw_axis2_reverses_flavor
  minusToPlus := raw_axis2_maps_minus_to_plus
  plusToMinus := raw_axis2_maps_plus_to_minus
  coordinateMapIsUnique :=
    ⟨raw_axis2_minus_coordinate_map_unique,
      raw_axis2_plus_coordinate_map_unique⟩
  densityIsPreserved := raw_cube_translation_preserves_density
  c19DirectionsHaveDerivedCopyClass := raw_c19_translation_copy_relation
  c19PathWeightsBalance :=
    ⟨c19_copy_exchange_weight_eq_twelve,
      c19_copy_preserving_weight_eq_twelve⟩
  signedIncidencePreservesCopies :=
    ⟨prepared_incidence_axis2_preserves_minus,
      prepared_incidence_axis2_preserves_plus⟩

end
end LeanDirac
