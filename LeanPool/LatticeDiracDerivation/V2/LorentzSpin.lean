/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin's dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.CompleteFreeDirac

/-!
# Lorentz covariance and spin one-half from the V2 cubical root

This module is downstream of the complete free-Dirac theorem.  It changes no
native field, action term, stencil, update, vacuum, or readout.  The rotation
generators are constructed from the same signed cube-incidence operators that
produce the V2 Clifford root.  The boost generators are then constructed from
the already-derived transport operators.
-/

@[expose] public section

namespace LeanDirac.V2

open Complex BigOperators
noncomputable section

attribute [local simp] cubicalIncidenceSignInteger

/-! ## Native oriented planes and the derived half scale -/

/-- Oriented plane bivector formed by composing the two cubical transport
operators perpendicular to `axis`. -/
def cubicalPlaneBivector
    (axis : Fin 3) (amplitude : CubicalCell8) : CubicalCell8 :=
  match axis with
  | 0 => cubicalGamma 1 (cubicalGamma 2 amplitude)
  | 1 => cubicalGamma 2 (cubicalGamma 0 amplitude)
  | _ => cubicalGamma 0 (cubicalGamma 1 amplitude)

/-- Hermitian-oriented plane operator obtained from the native cubical
bivector. -/
def cubicalSigma
    (axis : Fin 3) (amplitude : CubicalCell8) : CubicalCell8 :=
  fun corner => -I * cubicalPlaneBivector axis amplitude corner

theorem cubical_plane_bivector_square
    (axis : Fin 3) (amplitude : CubicalCell8) :
    cubicalPlaneBivector axis (cubicalPlaneBivector axis amplitude) =
      fun corner => -amplitude corner := by
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubicalPlaneBivector, cubicalGamma, cubicalIncidenceSign,
      cubicalFlip, cubicalFlip0, cubicalFlip1, cubicalFlip2,
      cubicalBit0, cubicalBit1]

theorem cubical_sigma_square
    (axis : Fin 3) (amplitude : CubicalCell8) :
    cubicalSigma axis (cubicalSigma axis amplitude) = amplitude := by
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubicalSigma, cubicalPlaneBivector, cubicalGamma,
      cubicalIncidenceSign, cubicalFlip, cubicalFlip0, cubicalFlip1,
      cubicalFlip2, cubicalBit0, cubicalBit1] <;>
    ring_nf <;> rw [Complex.I_sq] <;> ring

theorem cubical_sigma_01_product (amplitude : CubicalCell8) :
    cubicalSigma 0 (cubicalSigma 1 amplitude) =
      fun corner => I * cubicalSigma 2 amplitude corner := by
  funext corner
  fin_cases corner <;>
    simp [cubicalSigma, cubicalPlaneBivector, cubicalGamma,
      cubicalIncidenceSign, cubicalFlip, cubicalFlip0, cubicalFlip1,
      cubicalFlip2, cubicalBit0, cubicalBit1]

theorem cubical_sigma_10_product (amplitude : CubicalCell8) :
    cubicalSigma 1 (cubicalSigma 0 amplitude) =
      fun corner => -I * cubicalSigma 2 amplitude corner := by
  funext corner
  fin_cases corner <;>
    simp [cubicalSigma, cubicalPlaneBivector, cubicalGamma,
      cubicalIncidenceSign, cubicalFlip, cubicalFlip0, cubicalFlip1,
      cubicalFlip2, cubicalBit0, cubicalBit1]

theorem cubical_sigma_12_product (amplitude : CubicalCell8) :
    cubicalSigma 1 (cubicalSigma 2 amplitude) =
      fun corner => I * cubicalSigma 0 amplitude corner := by
  funext corner
  fin_cases corner <;>
    simp [cubicalSigma, cubicalPlaneBivector, cubicalGamma,
      cubicalIncidenceSign, cubicalFlip, cubicalFlip0, cubicalFlip1,
      cubicalFlip2, cubicalBit0, cubicalBit1]

theorem cubical_sigma_21_product (amplitude : CubicalCell8) :
    cubicalSigma 2 (cubicalSigma 1 amplitude) =
      fun corner => -I * cubicalSigma 0 amplitude corner := by
  funext corner
  fin_cases corner <;>
    simp [cubicalSigma, cubicalPlaneBivector, cubicalGamma,
      cubicalIncidenceSign, cubicalFlip, cubicalFlip0, cubicalFlip1,
      cubicalFlip2, cubicalBit0, cubicalBit1]

theorem cubical_sigma_20_product (amplitude : CubicalCell8) :
    cubicalSigma 2 (cubicalSigma 0 amplitude) =
      fun corner => I * cubicalSigma 1 amplitude corner := by
  funext corner
  fin_cases corner <;>
    simp [cubicalSigma, cubicalPlaneBivector, cubicalGamma,
      cubicalIncidenceSign, cubicalFlip, cubicalFlip0, cubicalFlip1,
      cubicalFlip2, cubicalBit0, cubicalBit1]

theorem cubical_sigma_02_product (amplitude : CubicalCell8) :
    cubicalSigma 0 (cubicalSigma 2 amplitude) =
      fun corner => -I * cubicalSigma 1 amplitude corner := by
  funext corner
  fin_cases corner <;>
    simp [cubicalSigma, cubicalPlaneBivector, cubicalGamma,
      cubicalIncidenceSign, cubicalFlip, cubicalFlip0, cubicalFlip1,
      cubicalFlip2, cubicalBit0, cubicalBit1]

/-- Cubical spin candidate with an arbitrary real normalization scale. -/
def scaledCubicalSpin
    (scale : ℝ) (axis : Fin 3) (amplitude : CubicalCell8) : CubicalCell8 :=
  fun corner => (scale : ℂ) * cubicalSigma axis amplitude corner

/-- States that the three scaled cubical spin candidates close with the
standard cyclic commutator normalization. -/
def cubicalSpinClosureAtScale (scale : ℝ) : Prop :=
  ∀ amplitude : CubicalCell8,
    (fun corner =>
      scaledCubicalSpin scale 0 (scaledCubicalSpin scale 1 amplitude) corner -
        scaledCubicalSpin scale 1 (scaledCubicalSpin scale 0 amplitude) corner) =
      fun corner => I * scaledCubicalSpin scale 2 amplitude corner

/-- Constant amplitude used as a nonzero witness when identifying the native
spin normalization. -/
def cubicalUniformAmplitude : CubicalCell8 := fun _ => 1

/-- Operational rotation criterion inside the local oriented-plane bivector
family. A candidate scale is accepted only when its commutator rotates each
native transport direction into the next oriented cube direction with unit
physical-angle normalization. The comparison class is explicit: scalar
multiples of the local plane bivectors already derived from `cubicalGamma`. -/
def cubicalOperationalRotationAtScale (scale : ℝ) : Prop :=
  (∀ amplitude : CubicalCell8,
    (fun corner =>
      scaledCubicalSpin scale 0 (cubicalGamma 1 amplitude) corner -
        cubicalGamma 1 (scaledCubicalSpin scale 0 amplitude) corner) =
      fun corner => I * cubicalGamma 2 amplitude corner) ∧
  (∀ amplitude : CubicalCell8,
    (fun corner =>
      scaledCubicalSpin scale 1 (cubicalGamma 2 amplitude) corner -
        cubicalGamma 2 (scaledCubicalSpin scale 1 amplitude) corner) =
      fun corner => I * cubicalGamma 0 amplitude corner) ∧
  (∀ amplitude : CubicalCell8,
    (fun corner =>
      scaledCubicalSpin scale 2 (cubicalGamma 0 amplitude) corner -
        cubicalGamma 0 (scaledCubicalSpin scale 2 amplitude) corner) =
      fun corner => I * cubicalGamma 1 amplitude corner)

theorem cubical_operational_rotation_scale_half :
    cubicalOperationalRotationAtScale (1 / 2) := by
  constructor
  · intro amplitude
    funext corner
    fin_cases corner <;>
      simp [scaledCubicalSpin, cubicalSigma, cubicalPlaneBivector,
        cubicalGamma, cubicalIncidenceSign, cubicalFlip,
        cubicalFlip1, cubicalFlip2, cubicalBit0, cubicalBit1] <;>
      ring_nf
  constructor
  · intro amplitude
    funext corner
    fin_cases corner <;>
      simp [scaledCubicalSpin, cubicalSigma, cubicalPlaneBivector,
        cubicalGamma, cubicalIncidenceSign, cubicalFlip, cubicalFlip0,
        cubicalFlip2, cubicalBit0, cubicalBit1] <;>
      ring_nf
  · intro amplitude
    funext corner
    fin_cases corner <;>
      simp [scaledCubicalSpin, cubicalSigma, cubicalPlaneBivector,
        cubicalGamma, cubicalIncidenceSign, cubicalFlip, cubicalFlip0,
        cubicalFlip1, cubicalBit0] <;>
      ring_nf

/-- Operational transport covariance fixes the half scale uniquely within the
stated local plane-bivector class; the `1/2` is not supplied separately. -/
theorem cubical_operational_rotation_scale_unique
    (scale : ℝ) (hscale : cubicalOperationalRotationAtScale scale) :
    scale = 1 / 2 := by
  have hcomponent := congrFun (hscale.1 cubicalUniformAmplitude) 0
  have hreduced : (scale : ℂ) * I + (scale : ℂ) * I = I := by
    simpa [cubicalUniformAmplitude, scaledCubicalSpin, cubicalSigma,
      cubicalPlaneBivector, cubicalGamma, cubicalIncidenceSign,
      cubicalFlip, cubicalFlip1, cubicalFlip2,
      cubicalBit0, cubicalBit1] using hcomponent
  apply_fun Complex.im at hreduced
  norm_num at hreduced
  linarith

theorem exists_unique_cubical_operational_rotation_scale :
    ∃! scale : ℝ, cubicalOperationalRotationAtScale scale := by
  refine ⟨1 / 2, cubical_operational_rotation_scale_half, ?_⟩
  intro scale hscale
  exact cubical_operational_rotation_scale_unique scale hscale

theorem cubical_scaled_spin_commutator_01
    (scale : ℝ) (amplitude : CubicalCell8) :
    (fun corner =>
      scaledCubicalSpin scale 0 (scaledCubicalSpin scale 1 amplitude) corner -
        scaledCubicalSpin scale 1 (scaledCubicalSpin scale 0 amplitude) corner) =
      fun corner =>
        ((2 * scale ^ 2 : ℝ) : ℂ) * I * cubicalSigma 2 amplitude corner := by
  funext corner
  fin_cases corner <;>
    simp [scaledCubicalSpin, cubicalSigma, cubicalPlaneBivector,
      cubicalGamma, cubicalIncidenceSign, cubicalFlip, cubicalFlip0,
      cubicalFlip1, cubicalFlip2, cubicalBit0, cubicalBit1] <;> ring

theorem cubical_spin_closure_iff_scale_equation (scale : ℝ) :
    cubicalSpinClosureAtScale scale ↔ 2 * scale ^ 2 = scale := by
  constructor
  · intro hclosure
    have hcomponent := congrFun (hclosure cubicalUniformAmplitude) 0
    have hreduced :
        (scale : ℂ) * (I * ((scale : ℂ) * I)) +
            (scale : ℂ) * (I * ((scale : ℂ) * I)) =
          I * ((scale : ℂ) * I) := by
      simpa [cubicalUniformAmplitude, scaledCubicalSpin, cubicalSigma,
        cubicalPlaneBivector, cubicalGamma, cubicalIncidenceSign,
        cubicalFlip, cubicalFlip0, cubicalFlip1, cubicalFlip2,
        cubicalBit0, cubicalBit1] using hcomponent
    apply_fun Complex.re at hreduced
    norm_num [Complex.mul_re] at hreduced
    nlinarith [hreduced]
  · intro hscale amplitude
    rw [cubical_scaled_spin_commutator_01]
    funext corner
    rw [hscale]
    simp [scaledCubicalSpin]
    ring

/-- A nonzero spin scale whose generators satisfy cubical spin closure. -/
def admissibleCubicalSpinScale (scale : ℝ) : Prop :=
  scale ≠ 0 ∧ cubicalSpinClosureAtScale scale

theorem admissible_cubical_spin_scale_half :
    admissibleCubicalSpinScale (1 / 2) := by
  constructor
  · norm_num
  · rw [cubical_spin_closure_iff_scale_equation]
    norm_num

theorem admissible_cubical_spin_scale_unique
    (scale : ℝ) (hscale : admissibleCubicalSpinScale scale) :
    scale = 1 / 2 := by
  rcases hscale with ⟨hne, hclosure⟩
  rw [cubical_spin_closure_iff_scale_equation] at hclosure
  have hfactor : scale * (2 * scale - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfactor with hzero | hhalf
  · exact (hne hzero).elim
  · nlinarith

theorem exists_unique_admissible_cubical_spin_scale :
    ∃! scale : ℝ, admissibleCubicalSpinScale scale := by
  refine ⟨1 / 2, admissible_cubical_spin_scale_half, ?_⟩
  intro scale hscale
  exact admissible_cubical_spin_scale_unique scale hscale

/- The normalization used below is selected from the proved unique native
closure condition.  It is not a separately supplied half-angle constant. -/
/-- The unique admissible normalization selected by cubical spin closure. -/
def nativeCubicalSpinScale : ℝ :=
  Classical.choose exists_unique_admissible_cubical_spin_scale

theorem native_cubical_spin_scale_admissible :
    admissibleCubicalSpinScale nativeCubicalSpinScale :=
  (Classical.choose_spec exists_unique_admissible_cubical_spin_scale).1

@[simp] theorem native_cubical_spin_scale_eq_half :
    nativeCubicalSpinScale = 1 / 2 :=
  admissible_cubical_spin_scale_unique nativeCubicalSpinScale
    native_cubical_spin_scale_admissible

theorem native_cubical_spin_is_operational_rotation :
    cubicalOperationalRotationAtScale nativeCubicalSpinScale := by
  rw [native_cubical_spin_scale_eq_half]
  exact cubical_operational_rotation_scale_half

/-- Native cubical spin generator using the closure-selected scale. -/
def cubicalSpin
    (axis : Fin 3) (amplitude : CubicalCell8) : CubicalCell8 :=
  scaledCubicalSpin nativeCubicalSpinScale axis amplitude

theorem cubical_spin_commutator_01 (amplitude : CubicalCell8) :
    (fun corner =>
      cubicalSpin 0 (cubicalSpin 1 amplitude) corner -
        cubicalSpin 1 (cubicalSpin 0 amplitude) corner) =
      fun corner => I * cubicalSpin 2 amplitude corner := by
  exact native_cubical_spin_scale_admissible.2 amplitude

theorem cubical_spin_commutator_12 (amplitude : CubicalCell8) :
    (fun corner =>
      cubicalSpin 1 (cubicalSpin 2 amplitude) corner -
        cubicalSpin 2 (cubicalSpin 1 amplitude) corner) =
      fun corner => I * cubicalSpin 0 amplitude corner := by
  funext corner
  fin_cases corner <;>
    simp [cubicalSpin, scaledCubicalSpin, cubicalSigma,
      cubicalPlaneBivector, cubicalGamma, cubicalIncidenceSign,
      cubicalFlip, cubicalFlip0, cubicalFlip1, cubicalFlip2,
      cubicalBit0, cubicalBit1] <;> ring_nf

theorem cubical_spin_commutator_20 (amplitude : CubicalCell8) :
    (fun corner =>
      cubicalSpin 2 (cubicalSpin 0 amplitude) corner -
        cubicalSpin 0 (cubicalSpin 2 amplitude) corner) =
      fun corner => I * cubicalSpin 1 amplitude corner := by
  funext corner
  fin_cases corner <;>
    simp [cubicalSpin, scaledCubicalSpin, cubicalSigma,
      cubicalPlaneBivector, cubicalGamma, cubicalIncidenceSign,
      cubicalFlip, cubicalFlip0, cubicalFlip1, cubicalFlip2,
      cubicalBit0, cubicalBit1] <;> ring_nf

theorem cubical_spin_component_square
    (axis : Fin 3) (amplitude : CubicalCell8) :
    cubicalSpin axis (cubicalSpin axis amplitude) =
      fun corner => (1 / 4 : ℂ) * amplitude corner := by
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubicalSpin, scaledCubicalSpin, cubicalSigma,
      cubicalPlaneBivector, cubicalGamma, cubicalIncidenceSign,
      cubicalFlip, cubicalFlip0, cubicalFlip1, cubicalFlip2,
      cubicalBit0, cubicalBit1] <;>
    ring_nf <;> rw [Complex.I_sq] <;> ring

theorem cubical_spin_casimir (amplitude : CubicalCell8) :
    (fun corner =>
      cubicalSpin 0 (cubicalSpin 0 amplitude) corner +
        cubicalSpin 1 (cubicalSpin 1 amplitude) corner +
        cubicalSpin 2 (cubicalSpin 2 amplitude) corner) =
      fun corner => (3 / 4 : ℂ) * amplitude corner := by
  funext corner
  rw [congrFun (cubical_spin_component_square 0 amplitude) corner,
    congrFun (cubical_spin_component_square 1 amplitude) corner,
    congrFun (cubical_spin_component_square 2 amplitude) corner]
  ring

/-! ## The same rotation representation in the V2 standard coordinates -/

/-- Cubical transport generator expressed in the standard four-component
coordinates of the free Dirac sector. -/
def standardCubicalGamma
    (axis : Fin 3) (z : CubicalCell4) : CubicalCell4 :=
  match axis with
  | 0 => cubicalStandardAlphaZ z
  | 1 => fun component => -cubicalStandardAlphaY z component
  | _ => fun component => -cubicalStandardAlphaX z component

/-- Oriented plane bivector in standard four-component coordinates. -/
def standardCubicalPlaneBivector
    (axis : Fin 3) (z : CubicalCell4) : CubicalCell4 :=
  match axis with
  | 0 => standardCubicalGamma 1 (standardCubicalGamma 2 z)
  | 1 => standardCubicalGamma 2 (standardCubicalGamma 0 z)
  | _ => standardCubicalGamma 0 (standardCubicalGamma 1 z)

/-- Native cubical spin generator in standard four-component coordinates. -/
def standardCubicalSpin
    (axis : Fin 3) (z : CubicalCell4) : CubicalCell4 :=
  fun component =>
    (nativeCubicalSpinScale : ℂ) *
      (-I * standardCubicalPlaneBivector axis z component)

theorem cubical_spin_intertwines_minus
    (axis : Fin 3) (z : CubicalCell4) :
    cubicalSpin axis (cubicalDiracEmbedMinus z) =
      cubicalDiracEmbedMinus (standardCubicalSpin axis z) := by
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubicalSpin, scaledCubicalSpin, cubicalSigma,
      cubicalPlaneBivector, cubicalGamma, cubicalIncidenceSign,
      cubicalFlip, cubicalFlip0, cubicalFlip1, cubicalFlip2,
      cubicalDiracEmbedMinus, cubicalEmbedMinus, standardToCubicalMinus,
      standardCubicalSpin, standardCubicalPlaneBivector,
      standardCubicalGamma, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ,
      cubicalBit0, cubicalBit1] <;>
    ring_nf <;> simp <;> ring

theorem cubical_spin_intertwines_plus
    (axis : Fin 3) (z : CubicalCell4) :
    cubicalSpin axis (cubicalDiracEmbedPlus z) =
      cubicalDiracEmbedPlus (standardCubicalSpin axis z) := by
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubicalSpin, scaledCubicalSpin, cubicalSigma,
      cubicalPlaneBivector, cubicalGamma, cubicalIncidenceSign,
      cubicalFlip, cubicalFlip0, cubicalFlip1, cubicalFlip2,
      cubicalDiracEmbedPlus, cubicalEmbedPlus, standardToCubicalPlus,
      standardCubicalSpin, standardCubicalPlaneBivector,
      standardCubicalGamma, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ,
      cubicalBit0, cubicalBit1] <;>
    ring_nf <;> simp <;> ring

/-- Coordinate basis vector of the standard four-component cell space. -/
def standardCell4Basis (basis : Fin 4) : CubicalCell4 :=
  fun component => if component = basis then 1 else 0

theorem standard_spin0_basis_spectrum :
    (standardCubicalSpin 0 (standardCell4Basis 0) =
      fun component => (-1 / 2 : ℂ) * standardCell4Basis 0 component) ∧
    (standardCubicalSpin 0 (standardCell4Basis 1) =
      fun component => (1 / 2 : ℂ) * standardCell4Basis 1 component) ∧
    (standardCubicalSpin 0 (standardCell4Basis 2) =
      fun component => (-1 / 2 : ℂ) * standardCell4Basis 2 component) ∧
    (standardCubicalSpin 0 (standardCell4Basis 3) =
      fun component => (1 / 2 : ℂ) * standardCell4Basis 3 component) := by
  constructor
  · funext component
    fin_cases component <;>
      norm_num [standardCubicalSpin, standardCubicalPlaneBivector,
        standardCubicalGamma, standardCell4Basis,
        cubicalStandardAlphaX, cubicalStandardAlphaY, Complex.I_sq]
  constructor
  · funext component
    fin_cases component <;>
      norm_num [standardCubicalSpin, standardCubicalPlaneBivector,
        standardCubicalGamma, standardCell4Basis,
        cubicalStandardAlphaX, cubicalStandardAlphaY, Complex.I_sq]
  constructor
  · funext component
    fin_cases component <;>
      norm_num [standardCubicalSpin, standardCubicalPlaneBivector,
        standardCubicalGamma, standardCell4Basis,
        cubicalStandardAlphaX, cubicalStandardAlphaY, Complex.I_sq]
  · funext component
    fin_cases component <;>
      norm_num [standardCubicalSpin, standardCubicalPlaneBivector,
        standardCubicalGamma, standardCell4Basis,
        cubicalStandardAlphaX, cubicalStandardAlphaY, Complex.I_sq]

theorem cubical_beta_commutes_spin
    (axis : Fin 3) (amplitude : CubicalCell8) :
    cubicalBeta (cubicalSpin axis amplitude) =
      cubicalSpin axis (cubicalBeta amplitude) := by
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubicalSpin, scaledCubicalSpin, cubicalSigma,
      cubicalPlaneBivector, cubicalBeta, cubicalGamma,
      cubicalIncidenceSign, cubicalFlip, cubicalFlip0, cubicalFlip1,
      cubicalFlip2, cubicalBit0, cubicalBit1, cubicalBit2]

theorem cubical_spin_preserves_minus_copy
    (axis : Fin 3) (z : CubicalCell4) :
    cubicalFlavor (cubicalSpin axis (cubicalDiracEmbedMinus z)) =
      fun corner => -cubicalSpin axis (cubicalDiracEmbedMinus z) corner := by
  rw [cubical_spin_intertwines_minus]
  exact cubical_embed_minus_has_negative_flavor (standardToCubicalMinus
    (standardCubicalSpin axis z))

theorem cubical_spin_preserves_plus_copy
    (axis : Fin 3) (z : CubicalCell4) :
    cubicalFlavor (cubicalSpin axis (cubicalDiracEmbedPlus z)) =
      cubicalSpin axis (cubicalDiracEmbedPlus z) := by
  rw [cubical_spin_intertwines_plus]
  exact cubical_embed_plus_has_positive_flavor (standardToCubicalPlus
    (standardCubicalSpin axis z))

/-! ## Continuous rotations and the double-valued return -/

/-- Finite cubical rotation generated directly by a native oriented plane. -/
def cubicalContinuousTurn
    (angle : ℝ) (axis : Fin 3) (amplitude : CubicalCell8) : CubicalCell8 :=
  fun corner =>
    (Real.cos (nativeCubicalSpinScale * angle) : ℂ) * amplitude corner -
      (Real.sin (nativeCubicalSpinScale * angle) : ℂ) *
        cubicalPlaneBivector axis amplitude corner

/-- Four-component rotor with explicitly supplied half-angle coefficients. -/
def standardCubicalRotorCoefficients
    (cosHalf sinHalf : ℝ) (axis : Fin 3)
    (z : CubicalCell4) : CubicalCell4 :=
  fun component =>
    (cosHalf : ℂ) * z component -
      2 * I * (sinHalf : ℂ) *
        standardCubicalSpin axis z component

theorem standard_cubical_rotor_coefficients_preserves_density
    (cosHalf sinHalf : ℝ) (axis : Fin 3) (z : CubicalCell4)
    (hunit : cosHalf ^ 2 + sinHalf ^ 2 = 1) :
    cubicalCell4Density
        (standardCubicalRotorCoefficients cosHalf sinHalf axis z) =
      cubicalCell4Density z := by
  fin_cases axis <;>
    simp [cubicalCell4Density, standardCubicalRotorCoefficients,
      standardCubicalSpin, standardCubicalPlaneBivector,
      standardCubicalGamma, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ,
      native_cubical_spin_scale_eq_half, Complex.normSq,
      Complex.mul_re, Complex.mul_im, Fin.sum_univ_four] <;>
    nlinarith

/-- Finite cubical rotation in standard four-component coordinates. -/
def standardCubicalContinuousTurn
    (angle : ℝ) (axis : Fin 3) (z : CubicalCell4) : CubicalCell4 :=
  standardCubicalRotorCoefficients
    (Real.cos (nativeCubicalSpinScale * angle))
    (Real.sin (nativeCubicalSpinScale * angle)) axis z

/-- The finite rotor preserves the same positive four-component density used
by the V2 current bridge.  Thus the rotation is unitary for the already-derived
Dirac readout, rather than merely having the right return period. -/
theorem standard_cubical_continuous_turn_preserves_density
    (angle : ℝ) (axis : Fin 3) (z : CubicalCell4) :
    cubicalCell4Density (standardCubicalContinuousTurn angle axis z) =
      cubicalCell4Density z := by
  apply standard_cubical_rotor_coefficients_preserves_density
  exact Real.cos_sq_add_sin_sq (nativeCubicalSpinScale * angle)

/-- The positive four-component inner product underlying the density/current
bridge.  It is introduced here only to state Hermiticity of the already
derived rotation generator. -/
def cubicalCell4Inner (z w : CubicalCell4) : ℂ :=
  ∑ component, star (z component) * w component

theorem standard_cubical_spin_is_hermitian
    (axis : Fin 3) (z w : CubicalCell4) :
    cubicalCell4Inner z (standardCubicalSpin axis w) =
      cubicalCell4Inner (standardCubicalSpin axis z) w := by
  fin_cases axis <;> apply Complex.ext <;>
    simp [cubicalCell4Inner, standardCubicalSpin,
      standardCubicalPlaneBivector, standardCubicalGamma,
      cubicalStandardAlphaX, cubicalStandardAlphaY,
      cubicalStandardAlphaZ, Fin.sum_univ_four,
      Complex.mul_re, Complex.mul_im] <;> ring

theorem standard_cubical_continuous_turn_zero
    (axis : Fin 3) (z : CubicalCell4) :
    standardCubicalContinuousTurn 0 axis z = z := by
  funext component
  simp [standardCubicalContinuousTurn, standardCubicalRotorCoefficients]

/-- The finite rotations are a representation of the additive angle group;
the half angle is not reinserted here but is the unique scale proved above. -/
theorem standard_cubical_continuous_turn_add
    (first second : ℝ) (axis : Fin 3) (z : CubicalCell4) :
    standardCubicalContinuousTurn (first + second) axis z =
      standardCubicalContinuousTurn first axis
        (standardCubicalContinuousTurn second axis z) := by
  funext component
  fin_cases axis <;> fin_cases component <;>
    simp [standardCubicalContinuousTurn, standardCubicalRotorCoefficients,
      standardCubicalSpin, standardCubicalPlaneBivector,
      standardCubicalGamma, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ,
      native_cubical_spin_scale_eq_half, mul_add,
      Real.cos_add, Real.sin_add] <;>
    ring_nf <;> norm_num [pow_succ, Complex.I_sq] <;> ring

theorem standard_cubical_continuous_turn_inverse
    (angle : ℝ) (axis : Fin 3) (z : CubicalCell4) :
    standardCubicalContinuousTurn (-angle) axis
        (standardCubicalContinuousTurn angle axis z) = z := by
  rw [← standard_cubical_continuous_turn_add]
  simp [standard_cubical_continuous_turn_zero]

theorem rotor_cosine_has_derivative_zero :
    HasDerivAt
      (fun angle : ℝ => Real.cos (nativeCubicalSpinScale * angle)) 0 0 := by
  have hlinear : HasDerivAt
      (fun angle : ℝ => nativeCubicalSpinScale * angle)
      nativeCubicalSpinScale 0 := by
    convert HasDerivAt.const_mul nativeCubicalSpinScale
      (hasDerivAt_id 0) using 1 <;> norm_num [id_eq]
  convert (Real.hasDerivAt_cos (nativeCubicalSpinScale * 0)).comp 0
    hlinear using 1 <;> simp [Function.comp_def]

theorem rotor_sine_has_derived_half_slope :
    HasDerivAt
      (fun angle : ℝ => Real.sin (nativeCubicalSpinScale * angle))
      nativeCubicalSpinScale 0 := by
  have hlinear : HasDerivAt
      (fun angle : ℝ => nativeCubicalSpinScale * angle)
      nativeCubicalSpinScale 0 := by
    convert HasDerivAt.const_mul nativeCubicalSpinScale
      (hasDerivAt_id 0) using 1 <;> norm_num [id_eq]
  convert (Real.hasDerivAt_sin (nativeCubicalSpinScale * 0)).comp 0
    hlinear using 1 <;> simp [Function.comp_def]

/-- Componentwise differentiation at the identity recovers `-i S` from the
finite rotor, closing the generator-to-group direction rather than merely
checking selected endpoint angles. -/
theorem standard_cubical_continuous_turn_has_derivative
    (axis : Fin 3) (z : CubicalCell4) (component : Fin 4) :
    HasDerivAt
      (fun angle : ℝ => standardCubicalContinuousTurn angle axis z component)
      (-I * standardCubicalSpin axis z component) 0 := by
  have hcos := rotor_cosine_has_derivative_zero.ofReal_comp
  have hsin := rotor_sine_has_derived_half_slope.ofReal_comp
  have hfirst := hcos.mul_const (z component)
  have hsecond :=
    ((hsin.const_mul (2 * I)).mul_const
      (standardCubicalSpin axis z component))
  convert hfirst.sub hsecond using 1
  · funext angle
    simp [standardCubicalContinuousTurn, standardCubicalRotorCoefficients]
  · have hscale : (nativeCubicalSpinScale : ℂ) = (1 / 2 : ℂ) := by
      rw [native_cubical_spin_scale_eq_half]
      norm_num
    have hcoeff : 2 * I * (nativeCubicalSpinScale : ℂ) = I := by
      rw [hscale]
      ring
    rw [hcoeff]
    simp

theorem cubical_continuous_turn_two_pi
    (axis : Fin 3) (amplitude : CubicalCell8) :
    cubicalContinuousTurn (2 * Real.pi) axis amplitude =
      fun corner => -amplitude corner := by
  funext corner
  unfold cubicalContinuousTurn
  rw [show nativeCubicalSpinScale * (2 * Real.pi) = Real.pi by
    rw [native_cubical_spin_scale_eq_half]
    ring]
  simp

theorem cubical_continuous_turn_four_pi
    (axis : Fin 3) (amplitude : CubicalCell8) :
    cubicalContinuousTurn (4 * Real.pi) axis amplitude = amplitude := by
  funext corner
  unfold cubicalContinuousTurn
  rw [show nativeCubicalSpinScale * (4 * Real.pi) = 2 * Real.pi by
    rw [native_cubical_spin_scale_eq_half]
    ring]
  simp [Real.cos_two_pi,
    Real.sin_two_pi]

theorem cubical_continuous_turn_intertwines_minus
    (angle : ℝ) (axis : Fin 3) (z : CubicalCell4) :
    cubicalContinuousTurn angle axis (cubicalDiracEmbedMinus z) =
      cubicalDiracEmbedMinus
        (standardCubicalContinuousTurn angle axis z) := by
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubicalContinuousTurn, standardCubicalContinuousTurn,
      standardCubicalRotorCoefficients,
      cubicalPlaneBivector, cubicalGamma, cubicalIncidenceSign,
      cubicalFlip, cubicalFlip0, cubicalFlip1, cubicalFlip2,
      cubicalBit0, cubicalBit1, standardCubicalSpin,
      standardCubicalPlaneBivector, standardCubicalGamma,
      cubicalStandardAlphaX, cubicalStandardAlphaY,
      cubicalStandardAlphaZ,
      cubicalDiracEmbedMinus, cubicalEmbedMinus,
      standardToCubicalMinus] <;> ring_nf <;>
    norm_num [pow_succ, Complex.I_sq] <;>
    simp [sub_eq_add_neg]

theorem cubical_continuous_turn_intertwines_plus
    (angle : ℝ) (axis : Fin 3) (z : CubicalCell4) :
    cubicalContinuousTurn angle axis (cubicalDiracEmbedPlus z) =
      cubicalDiracEmbedPlus
        (standardCubicalContinuousTurn angle axis z) := by
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubicalContinuousTurn, standardCubicalContinuousTurn,
      standardCubicalRotorCoefficients,
      cubicalPlaneBivector, cubicalGamma, cubicalIncidenceSign,
      cubicalFlip, cubicalFlip0, cubicalFlip1, cubicalFlip2,
      cubicalBit0, cubicalBit1, standardCubicalSpin,
      standardCubicalPlaneBivector, standardCubicalGamma,
      cubicalStandardAlphaX, cubicalStandardAlphaY,
      cubicalStandardAlphaZ,
      cubicalDiracEmbedPlus, cubicalEmbedPlus,
      standardToCubicalPlus] <;> ring_nf <;>
    norm_num [pow_succ, Complex.I_sq] <;>
    simp [sub_eq_add_neg]

/-! ## Lorentz boosts from the already-derived transport operators -/

/-- Boost generator on the native eight-corner cubical amplitude. -/
def cubicalBoost
    (axis : Fin 3) (amplitude : CubicalCell8) : CubicalCell8 :=
  fun corner => (I / 2) * cubicalGamma axis amplitude corner

/-- Boost generator in standard four-component coordinates. -/
def standardCubicalBoost
    (axis : Fin 3) (z : CubicalCell4) : CubicalCell4 :=
  fun component => (I / 2) * standardCubicalGamma axis z component

theorem cubical_boost_intertwines_minus
    (axis : Fin 3) (z : CubicalCell4) :
    cubicalBoost axis (cubicalDiracEmbedMinus z) =
      cubicalDiracEmbedMinus (standardCubicalBoost axis z) := by
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubicalBoost, standardCubicalBoost, cubicalGamma,
      cubicalIncidenceSign, cubicalFlip, cubicalFlip0,
      cubicalFlip1, cubicalFlip2, cubicalBit0, cubicalBit1,
      standardCubicalGamma, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ,
      cubicalDiracEmbedMinus, cubicalEmbedMinus,
      standardToCubicalMinus] <;>
    ring_nf <;> norm_num [pow_succ, Complex.I_sq]

theorem cubical_boost_intertwines_plus
    (axis : Fin 3) (z : CubicalCell4) :
    cubicalBoost axis (cubicalDiracEmbedPlus z) =
      cubicalDiracEmbedPlus (standardCubicalBoost axis z) := by
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubicalBoost, standardCubicalBoost, cubicalGamma,
      cubicalIncidenceSign, cubicalFlip, cubicalFlip0,
      cubicalFlip1, cubicalFlip2, cubicalBit0, cubicalBit1,
      standardCubicalGamma, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ,
      cubicalDiracEmbedPlus, cubicalEmbedPlus,
      standardToCubicalPlus] <;>
    ring_nf <;> norm_num [pow_succ, Complex.I_sq]

theorem standard_cubical_gamma_square
    (axis : Fin 3) (z : CubicalCell4) :
    standardCubicalGamma axis (standardCubicalGamma axis z) = z := by
  funext component
  fin_cases axis <;> fin_cases component <;>
    simp [standardCubicalGamma, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ] <;>
    ring_nf <;> rw [Complex.I_sq] <;> ring

theorem cubical_boost_commutator_01 (z : CubicalCell4) :
    (fun component =>
      standardCubicalBoost 0 (standardCubicalBoost 1 z) component -
        standardCubicalBoost 1 (standardCubicalBoost 0 z) component) =
      fun component => -I * standardCubicalSpin 2 z component := by
  funext component
  fin_cases component <;>
    simp [standardCubicalBoost, standardCubicalSpin,
      standardCubicalPlaneBivector, standardCubicalGamma,
      cubicalStandardAlphaY, cubicalStandardAlphaZ] <;> ring_nf

theorem cubical_boost_commutator_12 (z : CubicalCell4) :
    (fun component =>
      standardCubicalBoost 1 (standardCubicalBoost 2 z) component -
        standardCubicalBoost 2 (standardCubicalBoost 1 z) component) =
      fun component => -I * standardCubicalSpin 0 z component := by
  funext component
  fin_cases component <;>
    simp [standardCubicalBoost, standardCubicalSpin,
      standardCubicalPlaneBivector, standardCubicalGamma,
      cubicalStandardAlphaX, cubicalStandardAlphaY] <;> ring_nf

theorem cubical_boost_commutator_20 (z : CubicalCell4) :
    (fun component =>
      standardCubicalBoost 2 (standardCubicalBoost 0 z) component -
        standardCubicalBoost 0 (standardCubicalBoost 2 z) component) =
      fun component => -I * standardCubicalSpin 1 z component := by
  funext component
  fin_cases component <;>
    simp [standardCubicalBoost, standardCubicalSpin,
      standardCubicalPlaneBivector, standardCubicalGamma,
      cubicalStandardAlphaX, cubicalStandardAlphaZ] <;> ring_nf

theorem cubical_rotation_boost_commutator_01 (z : CubicalCell4) :
    (fun component =>
      standardCubicalSpin 0 (standardCubicalBoost 1 z) component -
        standardCubicalBoost 1 (standardCubicalSpin 0 z) component) =
      fun component => I * standardCubicalBoost 2 z component := by
  funext component
  fin_cases component <;>
    simp [standardCubicalBoost, standardCubicalSpin,
      standardCubicalPlaneBivector, standardCubicalGamma,
      cubicalStandardAlphaX, cubicalStandardAlphaY] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem cubical_rotation_boost_commutator_12 (z : CubicalCell4) :
    (fun component =>
      standardCubicalSpin 1 (standardCubicalBoost 2 z) component -
        standardCubicalBoost 2 (standardCubicalSpin 1 z) component) =
      fun component => I * standardCubicalBoost 0 z component := by
  funext component
  fin_cases component <;>
    simp [standardCubicalBoost, standardCubicalSpin,
      standardCubicalPlaneBivector, standardCubicalGamma,
      cubicalStandardAlphaX, cubicalStandardAlphaZ] <;> ring_nf

theorem cubical_rotation_boost_commutator_20 (z : CubicalCell4) :
    (fun component =>
      standardCubicalSpin 2 (standardCubicalBoost 0 z) component -
        standardCubicalBoost 0 (standardCubicalSpin 2 z) component) =
      fun component => I * standardCubicalBoost 1 z component := by
  funext component
  fin_cases component <;>
    simp [standardCubicalBoost, standardCubicalSpin,
      standardCubicalPlaneBivector, standardCubicalGamma,
      cubicalStandardAlphaY, cubicalStandardAlphaZ] <;> ring_nf

theorem standard_beta_commutes_spin
    (axis : Fin 3) (z : CubicalCell4) :
    cubicalStandardBeta (standardCubicalSpin axis z) =
      standardCubicalSpin axis (cubicalStandardBeta z) := by
  funext component
  fin_cases axis <;> fin_cases component <;>
    simp [standardCubicalSpin, standardCubicalPlaneBivector,
      standardCubicalGamma, cubicalStandardBeta,
      cubicalStandardAlphaX, cubicalStandardAlphaY,
      cubicalStandardAlphaZ]

theorem standard_spin_rotates_transport_01 (z : CubicalCell4) :
    (fun component =>
      standardCubicalSpin 0 (standardCubicalGamma 1 z) component -
        standardCubicalGamma 1 (standardCubicalSpin 0 z) component) =
      fun component => I * standardCubicalGamma 2 z component := by
  funext component
  fin_cases component <;>
    simp [standardCubicalSpin, standardCubicalPlaneBivector,
      standardCubicalGamma, cubicalStandardAlphaX,
      cubicalStandardAlphaY] <;> ring_nf <;>
    norm_num [pow_succ, Complex.I_sq]

theorem standard_spin_rotates_transport_12 (z : CubicalCell4) :
    (fun component =>
      standardCubicalSpin 1 (standardCubicalGamma 2 z) component -
        standardCubicalGamma 2 (standardCubicalSpin 1 z) component) =
      fun component => I * standardCubicalGamma 0 z component := by
  funext component
  fin_cases component <;>
    simp [standardCubicalSpin, standardCubicalPlaneBivector,
      standardCubicalGamma, cubicalStandardAlphaX,
      cubicalStandardAlphaZ] <;> ring_nf

theorem standard_spin_rotates_transport_20 (z : CubicalCell4) :
    (fun component =>
      standardCubicalSpin 2 (standardCubicalGamma 0 z) component -
        standardCubicalGamma 0 (standardCubicalSpin 2 z) component) =
      fun component => I * standardCubicalGamma 1 z component := by
  funext component
  fin_cases component <;>
    simp [standardCubicalSpin, standardCubicalPlaneBivector,
      standardCubicalGamma, cubicalStandardAlphaY,
      cubicalStandardAlphaZ] <;> ring_nf

/-! The following gamma basis is the signed/permuted cubical frame used by
`standardCubicalGamma`.  It is equivalent to the coordinate gamma basis in
`CovariantFreeDirac`; keeping the oriented basis here makes the native cube
incidence signs explicit. -/

/-- Time-directed gamma action in the oriented cubical basis. -/
def orientedCubicalGammaTime (z : CubicalCell4) : CubicalCell4 :=
  cubicalStandardBeta z

/-- Spatial gamma action in the oriented cubical basis. -/
def orientedCubicalGammaSpace
    (axis : Fin 3) (z : CubicalCell4) : CubicalCell4 :=
  orientedCubicalGammaTime (standardCubicalGamma axis z)

/-- Infinitesimal boosts mix the time gamma with the corresponding oriented
spatial gamma.  This is the missing covariance check beyond the abstract
Lorentz-generator commutators. -/
theorem cubical_boost_transforms_gamma_time
    (axis : Fin 3) (z : CubicalCell4) :
    (fun component =>
      standardCubicalBoost axis (orientedCubicalGammaTime z) component -
        orientedCubicalGammaTime (standardCubicalBoost axis z) component) =
      fun component => -I * orientedCubicalGammaSpace axis z component := by
  funext component
  fin_cases axis <;> fin_cases component <;>
    simp [standardCubicalBoost, orientedCubicalGammaTime,
      orientedCubicalGammaSpace, standardCubicalGamma,
      cubicalStandardBeta, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ] <;> ring_nf

theorem cubical_boost_transforms_parallel_gamma_space
    (axis : Fin 3) (z : CubicalCell4) :
    (fun component =>
      standardCubicalBoost axis (orientedCubicalGammaSpace axis z) component -
        orientedCubicalGammaSpace axis
          (standardCubicalBoost axis z) component) =
      fun component => -I * orientedCubicalGammaTime z component := by
  funext component
  fin_cases axis <;> fin_cases component <;>
    simp [standardCubicalBoost, orientedCubicalGammaTime,
      orientedCubicalGammaSpace, standardCubicalGamma,
      cubicalStandardBeta, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ] <;> ring_nf <;>
    norm_num [pow_succ, Complex.I_sq]

theorem cubical_boost_commutes_transverse_gamma_space
    (axis other : Fin 3) (haxis : axis ≠ other) (z : CubicalCell4) :
    standardCubicalBoost axis (orientedCubicalGammaSpace other z) =
      orientedCubicalGammaSpace other (standardCubicalBoost axis z) := by
  funext component
  fin_cases axis <;> fin_cases other <;> try { contradiction }
  all_goals
    fin_cases component <;>
      simp [standardCubicalBoost, orientedCubicalGammaTime,
        orientedCubicalGammaSpace, standardCubicalGamma,
        cubicalStandardBeta, cubicalStandardAlphaX,
        cubicalStandardAlphaY, cubicalStandardAlphaZ] <;> ring_nf

/-! ## The complete continuum symbol and its Lorentz response -/

/-- The oriented continuum Dirac symbol in the gamma frame derived above.
Momentum is data, not a force or a new native field. -/
def orientedCubicalDiracSymbol
    (energy mass : ℂ) (momentum : Fin 3 → ℂ)
    (z : CubicalCell4) : CubicalCell4 :=
  fun component =>
    energy * orientedCubicalGammaTime z component -
      momentum 0 * orientedCubicalGammaSpace 0 z component -
      momentum 1 * orientedCubicalGammaSpace 1 z component -
      momentum 2 * orientedCubicalGammaSpace 2 z component -
      mass * z component

/-- Infinitesimal active rotation of a spatial momentum about a cube axis. -/
def cubicalMomentumRotation
    (axis : Fin 3) (momentum : Fin 3 → ℂ) : Fin 3 → ℂ :=
  match axis with
  | 0 => ![0, -momentum 2, momentum 1]
  | 1 => ![momentum 2, 0, -momentum 0]
  | _ => ![-momentum 1, momentum 0, 0]

/-- The spinor commutator and the momentum rotation give the same variation
of the *whole* Dirac symbol.  This closes more than gamma-matrix algebra: the
four-component operator and its momentum argument transform together. -/
theorem oriented_dirac_symbol_rotation_covariant
    (axis : Fin 3) (energy mass : ℂ) (momentum : Fin 3 → ℂ)
    (z : CubicalCell4) :
    (fun component =>
      standardCubicalSpin axis
          (orientedCubicalDiracSymbol energy mass momentum z) component -
        orientedCubicalDiracSymbol energy mass momentum
          (standardCubicalSpin axis z) component) =
      fun component => I *
        orientedCubicalDiracSymbol 0 0
          (cubicalMomentumRotation axis momentum) z component := by
  funext component
  fin_cases axis <;> fin_cases component <;>
    simp [orientedCubicalDiracSymbol, cubicalMomentumRotation,
      standardCubicalSpin,
      standardCubicalPlaneBivector, orientedCubicalGammaTime,
      orientedCubicalGammaSpace, standardCubicalGamma,
      cubicalStandardBeta, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ] <;>
    ring_nf <;> norm_num [pow_succ, Complex.I_sq] <;> ring

/-- Infinitesimal boost of four-momentum in the selected cube direction. -/
def cubicalMomentumBoostEnergy
    (axis : Fin 3) (momentum : Fin 3 → ℂ) : ℂ := momentum axis

/-- Infinitesimal spatial-momentum change produced by a boost along `axis`. -/
def cubicalMomentumBoostSpace
    (axis : Fin 3) (energy : ℂ) : Fin 3 → ℂ :=
  fun other => if other = axis then energy else 0

theorem oriented_dirac_symbol_boost_covariant
    (axis : Fin 3) (energy mass : ℂ) (momentum : Fin 3 → ℂ)
    (z : CubicalCell4) :
    (fun component =>
      standardCubicalBoost axis
          (orientedCubicalDiracSymbol energy mass momentum z) component -
        orientedCubicalDiracSymbol energy mass momentum
          (standardCubicalBoost axis z) component) =
      fun component => I *
        orientedCubicalDiracSymbol
          (cubicalMomentumBoostEnergy axis momentum) 0
          (cubicalMomentumBoostSpace axis energy) z component := by
  funext component
  fin_cases axis <;> fin_cases component <;>
    simp [orientedCubicalDiracSymbol, cubicalMomentumBoostEnergy,
      cubicalMomentumBoostSpace, standardCubicalBoost,
      orientedCubicalGammaTime, orientedCubicalGammaSpace,
      standardCubicalGamma, cubicalStandardBeta,
      cubicalStandardAlphaX, cubicalStandardAlphaY,
      cubicalStandardAlphaZ] <;>
    ring_nf <;> norm_num [pow_succ, Complex.I_sq] <;> ring

/-! ## Pauli--Lubanski vector from momentum and Lorentz generators -/

/-- Time component of the cubical Pauli--Lubanski operator. -/
def cubicalPauliLubanskiTime
    (momentum : Fin 3 → ℂ) (z : CubicalCell4) : CubicalCell4 :=
  fun component =>
    momentum 0 * standardCubicalSpin 0 z component +
      momentum 1 * standardCubicalSpin 1 z component +
      momentum 2 * standardCubicalSpin 2 z component

/-- Spatial momentum crossed with the cubical boost generators. -/
def cubicalMomentumCrossBoost
    (momentum : Fin 3 → ℂ) (axis : Fin 3)
    (z : CubicalCell4) : CubicalCell4 :=
  match axis with
  | 0 => fun component =>
      momentum 1 * standardCubicalBoost 2 z component -
        momentum 2 * standardCubicalBoost 1 z component
  | 1 => fun component =>
      momentum 2 * standardCubicalBoost 0 z component -
        momentum 0 * standardCubicalBoost 2 z component
  | _ => fun component =>
      momentum 0 * standardCubicalBoost 1 z component -
        momentum 1 * standardCubicalBoost 0 z component

/-- Spatial component of the cubical Pauli--Lubanski operator. -/
def cubicalPauliLubanskiSpace
    (energy : ℂ) (momentum : Fin 3 → ℂ) (axis : Fin 3)
    (z : CubicalCell4) : CubicalCell4 :=
  fun component =>
    energy * standardCubicalSpin axis z component -
      cubicalMomentumCrossBoost momentum axis z component

/-- Infinitesimal momentum contribution to the time component of the
Pauli--Lubanski vector under a boost in `axis`. -/
def cubicalPauliLubanskiBoostVariationTime
    (axis : Fin 3) (energy : ℂ) (z : CubicalCell4) : CubicalCell4 :=
  cubicalPauliLubanskiTime (cubicalMomentumBoostSpace axis energy) z

/-- Infinitesimal momentum contribution to a spatial Pauli--Lubanski
component under a boost in `axis`. -/
def cubicalPauliLubanskiBoostVariationSpace
    (axis : Fin 3) (energy : ℂ) (momentum : Fin 3 → ℂ)
    (other : Fin 3) (z : CubicalCell4) : CubicalCell4 :=
  cubicalPauliLubanskiSpace
    (cubicalMomentumBoostEnergy axis momentum)
    (cubicalMomentumBoostSpace axis energy) other z

/-- In the boost convention already fixed by
`oriented_dirac_symbol_boost_covariant`, the repaired time component obeys
the infinitesimal four-vector law for every boost axis. -/
theorem cubical_pauli_lubanski_boost_covariant_time
    (axis : Fin 3) (energy : ℂ) (momentum : Fin 3 → ℂ)
    (z : CubicalCell4) :
    (fun component =>
      cubicalPauliLubanskiBoostVariationTime axis energy z component +
        I * (standardCubicalBoost axis
            (cubicalPauliLubanskiTime momentum z) component -
          cubicalPauliLubanskiTime momentum
            (standardCubicalBoost axis z) component) -
        cubicalPauliLubanskiSpace energy momentum axis z component) =
      fun _ => 0 := by
  funext component
  fin_cases axis <;> fin_cases component <;>
    simp [cubicalPauliLubanskiBoostVariationTime,
      cubicalPauliLubanskiTime, cubicalPauliLubanskiSpace,
      cubicalMomentumCrossBoost, cubicalMomentumBoostSpace,
      standardCubicalBoost, standardCubicalSpin,
      standardCubicalPlaneBivector, standardCubicalGamma,
      cubicalStandardAlphaX, cubicalStandardAlphaY,
      cubicalStandardAlphaZ] <;>
    ring_nf <;> norm_num [pow_succ, Complex.I_sq]

/-- The three repaired spatial components obey the infinitesimal four-vector
law for every boost axis, including both parallel and transverse cases. -/
theorem cubical_pauli_lubanski_boost_covariant_space
    (axis other : Fin 3) (energy : ℂ) (momentum : Fin 3 → ℂ)
    (z : CubicalCell4) :
    (fun component =>
      cubicalPauliLubanskiBoostVariationSpace
          axis energy momentum other z component +
        I * (standardCubicalBoost axis
            (cubicalPauliLubanskiSpace energy momentum other z) component -
          cubicalPauliLubanskiSpace energy momentum other
            (standardCubicalBoost axis z) component) -
        (if other = axis then
          cubicalPauliLubanskiTime momentum z component
        else 0)) = fun _ => 0 := by
  funext component
  fin_cases axis <;> fin_cases other <;> fin_cases component <;>
    simp [cubicalPauliLubanskiBoostVariationSpace,
      cubicalPauliLubanskiTime, cubicalPauliLubanskiSpace,
      cubicalMomentumCrossBoost, cubicalMomentumBoostEnergy,
      cubicalMomentumBoostSpace, standardCubicalBoost,
      standardCubicalSpin, standardCubicalPlaneBivector,
      standardCubicalGamma, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ] <;>
    ring_nf <;> norm_num [pow_succ, Complex.I_sq]

/-- The Pauli--Lubanski time component is a scalar under the already-derived
infinitesimal spatial rotations, including the simultaneous momentum change. -/
theorem cubical_pauli_lubanski_rotation_covariant_time
    (axis : Fin 3) (momentum : Fin 3 → ℂ) (z : CubicalCell4) :
    (fun component =>
      cubicalPauliLubanskiTime
          (cubicalMomentumRotation axis momentum) z component +
        I * (standardCubicalSpin axis
            (cubicalPauliLubanskiTime momentum z) component -
          cubicalPauliLubanskiTime momentum
            (standardCubicalSpin axis z) component)) =
      fun _ => 0 := by
  funext component
  fin_cases axis <;> fin_cases component <;>
    simp [cubicalPauliLubanskiTime, cubicalMomentumRotation,
      standardCubicalSpin, standardCubicalPlaneBivector,
      standardCubicalGamma, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ] <;>
    ring_nf <;> norm_num [pow_succ, Complex.I_sq]

/-- The repaired spatial components rotate covariantly together with their
momentum argument in the orientation convention fixed by the Dirac symbol. -/
theorem cubical_pauli_lubanski_rotation_covariant_space
    (axis other : Fin 3) (energy : ℂ) (momentum : Fin 3 → ℂ)
    (z : CubicalCell4) :
    (fun component =>
      cubicalPauliLubanskiSpace 0
          (cubicalMomentumRotation axis momentum) other z component +
        I * (standardCubicalSpin axis
            (cubicalPauliLubanskiSpace energy momentum other z) component -
          cubicalPauliLubanskiSpace energy momentum other
            (standardCubicalSpin axis z) component) +
        -cubicalMomentumRotation axis
          (fun spatial =>
            cubicalPauliLubanskiSpace energy momentum spatial z component)
          other) = fun _ => 0 := by
  funext component
  fin_cases axis <;> fin_cases other <;> fin_cases component <;>
    simp [cubicalPauliLubanskiSpace,
      cubicalMomentumCrossBoost, cubicalMomentumRotation,
      standardCubicalBoost, standardCubicalSpin,
      standardCubicalPlaneBivector, standardCubicalGamma,
      cubicalStandardAlphaX, cubicalStandardAlphaY,
      cubicalStandardAlphaZ] <;>
    ring_nf <;> norm_num [pow_succ, Complex.I_sq]

/-- The derived Pauli--Lubanski vector is orthogonal to four-momentum for
arbitrary energy and momentum. -/
theorem cubical_pauli_lubanski_orthogonal
    (energy : ℂ) (momentum : Fin 3 → ℂ) (z : CubicalCell4) :
    (fun component =>
      energy * cubicalPauliLubanskiTime momentum z component -
        momentum 0 * cubicalPauliLubanskiSpace energy momentum 0 z component -
        momentum 1 * cubicalPauliLubanskiSpace energy momentum 1 z component -
        momentum 2 * cubicalPauliLubanskiSpace energy momentum 2 z component) =
      fun _ => 0 := by
  funext component
  fin_cases component <;>
    simp [cubicalPauliLubanskiTime, cubicalPauliLubanskiSpace,
      cubicalMomentumCrossBoost] <;> ring

/-- Minkowski square of the cubical Pauli--Lubanski operator. -/
def cubicalPauliLubanskiSquare
    (energy : ℂ) (momentum : Fin 3 → ℂ)
    (z : CubicalCell4) : CubicalCell4 :=
  fun component =>
    cubicalPauliLubanskiTime momentum
        (cubicalPauliLubanskiTime momentum z) component -
      cubicalPauliLubanskiSpace energy momentum 0
        (cubicalPauliLubanskiSpace energy momentum 0 z) component -
      cubicalPauliLubanskiSpace energy momentum 1
        (cubicalPauliLubanskiSpace energy momentum 1 z) component -
      cubicalPauliLubanskiSpace energy momentum 2
        (cubicalPauliLubanskiSpace energy momentum 2 z) component

theorem standard_spin_component_square
    (axis : Fin 3) (z : CubicalCell4) :
    standardCubicalSpin axis (standardCubicalSpin axis z) =
      fun component => (1 / 4 : ℂ) * z component := by
  funext component
  fin_cases axis <;> fin_cases component <;>
    simp [standardCubicalSpin, standardCubicalPlaneBivector,
      standardCubicalGamma, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ] <;>
    ring_nf <;> norm_num [pow_succ, Complex.I_sq]

theorem rest_pauli_lubanski_spin_half
    (mass : ℂ) (z : CubicalCell4) :
    cubicalPauliLubanskiSquare mass (fun _ => 0) z =
      fun component => -(3 / 4 : ℂ) * mass ^ 2 * z component := by
  funext component
  fin_cases component <;>
    simp [cubicalPauliLubanskiSquare, cubicalPauliLubanskiTime,
      cubicalPauliLubanskiSpace, cubicalMomentumCrossBoost,
      standardCubicalSpin, standardCubicalPlaneBivector,
      standardCubicalGamma, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ] <;>
    ring_nf <;> norm_num [pow_succ, Complex.I_sq] <;> ring

/-! ## Cumulative theorem -/

/-- Cumulative certificate connecting the prior free-Dirac result to the
derived cubical Lorentz and spin-one-half representation. -/
structure LorentzSpinHalfCertificate : Prop where
  priorFreeDirac : CompleteFreeDiracCertificate
  nativePlaneSquare : ∀ axis amplitude,
    cubicalPlaneBivector axis (cubicalPlaneBivector axis amplitude) =
      fun corner => -amplitude corner
  uniqueNonzeroSpinScale :
    ∃! scale : ℝ, admissibleCubicalSpinScale scale
  uniqueOperationalRotationScale :
    ∃! scale : ℝ, cubicalOperationalRotationAtScale scale
  nativeSpinMatchesOperationalRotation :
    cubicalOperationalRotationAtScale nativeCubicalSpinScale
  spinCommutators :
    (∀ amplitude,
      (fun corner =>
        cubicalSpin 0 (cubicalSpin 1 amplitude) corner -
          cubicalSpin 1 (cubicalSpin 0 amplitude) corner) =
        fun corner => I * cubicalSpin 2 amplitude corner) ∧
    (∀ amplitude,
      (fun corner =>
        cubicalSpin 1 (cubicalSpin 2 amplitude) corner -
          cubicalSpin 2 (cubicalSpin 1 amplitude) corner) =
        fun corner => I * cubicalSpin 0 amplitude corner) ∧
    (∀ amplitude,
      (fun corner =>
        cubicalSpin 2 (cubicalSpin 0 amplitude) corner -
          cubicalSpin 0 (cubicalSpin 2 amplitude) corner) =
        fun corner => I * cubicalSpin 1 amplitude corner)
  spinCasimir : ∀ amplitude,
    (fun corner =>
      cubicalSpin 0 (cubicalSpin 0 amplitude) corner +
        cubicalSpin 1 (cubicalSpin 1 amplitude) corner +
        cubicalSpin 2 (cubicalSpin 2 amplitude) corner) =
      fun corner => (3 / 4 : ℂ) * amplitude corner
  bothCopyIntertwining :
    (∀ axis z,
      cubicalSpin axis (cubicalDiracEmbedMinus z) =
        cubicalDiracEmbedMinus (standardCubicalSpin axis z)) ∧
    (∀ axis z,
      cubicalSpin axis (cubicalDiracEmbedPlus z) =
        cubicalDiracEmbedPlus (standardCubicalSpin axis z))
  explicitSpinSpectrum :
    (standardCubicalSpin 0 (standardCell4Basis 0) =
      fun component => (-1 / 2 : ℂ) * standardCell4Basis 0 component) ∧
    (standardCubicalSpin 0 (standardCell4Basis 1) =
      fun component => (1 / 2 : ℂ) * standardCell4Basis 1 component) ∧
    (standardCubicalSpin 0 (standardCell4Basis 2) =
      fun component => (-1 / 2 : ℂ) * standardCell4Basis 2 component) ∧
    (standardCubicalSpin 0 (standardCell4Basis 3) =
      fun component => (1 / 2 : ℂ) * standardCell4Basis 3 component)
  twoPiSign : ∀ axis amplitude,
    cubicalContinuousTurn (2 * Real.pi) axis amplitude =
      fun corner => -amplitude corner
  fourPiReturn : ∀ axis amplitude,
    cubicalContinuousTurn (4 * Real.pi) axis amplitude = amplitude
  finiteRotationIsUnitary : ∀ angle axis z,
    cubicalCell4Density (standardCubicalContinuousTurn angle axis z) =
      cubicalCell4Density z
  spinGeneratorIsHermitian : ∀ axis z w,
    cubicalCell4Inner z (standardCubicalSpin axis w) =
      cubicalCell4Inner (standardCubicalSpin axis z) w
  finiteRotationGroup :
    (∀ axis z, standardCubicalContinuousTurn 0 axis z = z) ∧
    (∀ first second axis z,
      standardCubicalContinuousTurn (first + second) axis z =
        standardCubicalContinuousTurn first axis
          (standardCubicalContinuousTurn second axis z)) ∧
    (∀ angle axis z,
      standardCubicalContinuousTurn (-angle) axis
        (standardCubicalContinuousTurn angle axis z) = z)
  finiteRotationGenerator : ∀ axis z component,
    HasDerivAt
      (fun angle : ℝ =>
        standardCubicalContinuousTurn angle axis z component)
      (-I * standardCubicalSpin axis z component) 0
  finiteRotationBothCopies :
    (∀ angle axis z,
      cubicalContinuousTurn angle axis (cubicalDiracEmbedMinus z) =
        cubicalDiracEmbedMinus
          (standardCubicalContinuousTurn angle axis z)) ∧
    (∀ angle axis z,
      cubicalContinuousTurn angle axis (cubicalDiracEmbedPlus z) =
        cubicalDiracEmbedPlus
          (standardCubicalContinuousTurn angle axis z))
  boostBothCopies :
    (∀ axis z,
      cubicalBoost axis (cubicalDiracEmbedMinus z) =
        cubicalDiracEmbedMinus (standardCubicalBoost axis z)) ∧
    (∀ axis z,
      cubicalBoost axis (cubicalDiracEmbedPlus z) =
        cubicalDiracEmbedPlus (standardCubicalBoost axis z))
  boostCommutators :
    (∀ z, (fun component =>
      standardCubicalBoost 0 (standardCubicalBoost 1 z) component -
        standardCubicalBoost 1 (standardCubicalBoost 0 z) component) =
      fun component => -I * standardCubicalSpin 2 z component) ∧
    (∀ z, (fun component =>
      standardCubicalBoost 1 (standardCubicalBoost 2 z) component -
        standardCubicalBoost 2 (standardCubicalBoost 1 z) component) =
      fun component => -I * standardCubicalSpin 0 z component) ∧
    (∀ z, (fun component =>
      standardCubicalBoost 2 (standardCubicalBoost 0 z) component -
        standardCubicalBoost 0 (standardCubicalBoost 2 z) component) =
      fun component => -I * standardCubicalSpin 1 z component)
  rotationBoostCommutators :
    (∀ z, (fun component =>
      standardCubicalSpin 0 (standardCubicalBoost 1 z) component -
        standardCubicalBoost 1 (standardCubicalSpin 0 z) component) =
      fun component => I * standardCubicalBoost 2 z component) ∧
    (∀ z, (fun component =>
      standardCubicalSpin 1 (standardCubicalBoost 2 z) component -
        standardCubicalBoost 2 (standardCubicalSpin 1 z) component) =
      fun component => I * standardCubicalBoost 0 z component) ∧
    (∀ z, (fun component =>
      standardCubicalSpin 2 (standardCubicalBoost 0 z) component -
        standardCubicalBoost 0 (standardCubicalSpin 2 z) component) =
      fun component => I * standardCubicalBoost 1 z component)
  massInvariantUnderRotations : ∀ axis z,
    cubicalStandardBeta (standardCubicalSpin axis z) =
      standardCubicalSpin axis (cubicalStandardBeta z)
  transportRotatesCovariantly :
    (∀ z, (fun component =>
      standardCubicalSpin 0 (standardCubicalGamma 1 z) component -
        standardCubicalGamma 1 (standardCubicalSpin 0 z) component) =
      fun component => I * standardCubicalGamma 2 z component) ∧
    (∀ z, (fun component =>
      standardCubicalSpin 1 (standardCubicalGamma 2 z) component -
        standardCubicalGamma 2 (standardCubicalSpin 1 z) component) =
      fun component => I * standardCubicalGamma 0 z component) ∧
    (∀ z, (fun component =>
      standardCubicalSpin 2 (standardCubicalGamma 0 z) component -
        standardCubicalGamma 0 (standardCubicalSpin 2 z) component) =
      fun component => I * standardCubicalGamma 1 z component)
  boostsTransformGammaFourVector :
    (∀ axis z, (fun component =>
      standardCubicalBoost axis (orientedCubicalGammaTime z) component -
        orientedCubicalGammaTime
          (standardCubicalBoost axis z) component) =
      fun component => -I * orientedCubicalGammaSpace axis z component) ∧
    (∀ axis z, (fun component =>
      standardCubicalBoost axis
          (orientedCubicalGammaSpace axis z) component -
        orientedCubicalGammaSpace axis
          (standardCubicalBoost axis z) component) =
      fun component => -I * orientedCubicalGammaTime z component) ∧
    (∀ axis other, axis ≠ other → ∀ z,
      standardCubicalBoost axis (orientedCubicalGammaSpace other z) =
        orientedCubicalGammaSpace other (standardCubicalBoost axis z))
  fullDiracSymbolCovariance :
    (∀ axis energy mass momentum z,
      (fun component =>
        standardCubicalSpin axis
            (orientedCubicalDiracSymbol energy mass momentum z) component -
          orientedCubicalDiracSymbol energy mass momentum
            (standardCubicalSpin axis z) component) =
        fun component => I *
          orientedCubicalDiracSymbol 0 0
            (cubicalMomentumRotation axis momentum) z component) ∧
    (∀ axis energy mass momentum z,
      (fun component =>
        standardCubicalBoost axis
            (orientedCubicalDiracSymbol energy mass momentum z) component -
          orientedCubicalDiracSymbol energy mass momentum
            (standardCubicalBoost axis z) component) =
        fun component => I *
          orientedCubicalDiracSymbol
            (cubicalMomentumBoostEnergy axis momentum) 0
            (cubicalMomentumBoostSpace axis energy) z component)
  pauliLubanskiBoostCovariance :
    (∀ axis energy momentum z,
      (fun component =>
        cubicalPauliLubanskiBoostVariationTime axis energy z component +
          I * (standardCubicalBoost axis
              (cubicalPauliLubanskiTime momentum z) component -
            cubicalPauliLubanskiTime momentum
              (standardCubicalBoost axis z) component) -
          cubicalPauliLubanskiSpace energy momentum axis z component) =
        fun _ => 0) ∧
    (∀ axis other energy momentum z,
      (fun component =>
        cubicalPauliLubanskiBoostVariationSpace
            axis energy momentum other z component +
          I * (standardCubicalBoost axis
              (cubicalPauliLubanskiSpace energy momentum other z) component -
            cubicalPauliLubanskiSpace energy momentum other
              (standardCubicalBoost axis z) component) -
          (if other = axis then
            cubicalPauliLubanskiTime momentum z component
          else 0)) = fun _ => 0)
  pauliLubanskiRotationCovariance :
    (∀ axis momentum z,
      (fun component =>
        cubicalPauliLubanskiTime
            (cubicalMomentumRotation axis momentum) z component +
          I * (standardCubicalSpin axis
              (cubicalPauliLubanskiTime momentum z) component -
            cubicalPauliLubanskiTime momentum
              (standardCubicalSpin axis z) component)) =
        fun _ => 0) ∧
    (∀ axis other energy momentum z,
      (fun component =>
        cubicalPauliLubanskiSpace 0
            (cubicalMomentumRotation axis momentum) other z component +
          I * (standardCubicalSpin axis
              (cubicalPauliLubanskiSpace energy momentum other z) component -
            cubicalPauliLubanskiSpace energy momentum other
              (standardCubicalSpin axis z) component) +
          -cubicalMomentumRotation axis
            (fun spatial =>
              cubicalPauliLubanskiSpace energy momentum spatial z component)
            other) = fun _ => 0)
  pauliLubanskiOrthogonal : ∀ energy momentum z,
    (fun component =>
      energy * cubicalPauliLubanskiTime momentum z component -
        momentum 0 * cubicalPauliLubanskiSpace energy momentum 0 z component -
        momentum 1 * cubicalPauliLubanskiSpace energy momentum 1 z component -
        momentum 2 * cubicalPauliLubanskiSpace energy momentum 2 z component) =
      fun _ => 0
  restPauliLubanskiCasimir : ∀ mass z,
    cubicalPauliLubanskiSquare mass (fun _ => 0) z =
      fun component => -(3 / 4 : ℂ) * mass ^ 2 * z component

theorem lorentz_spin_half_from_native_action :
    LorentzSpinHalfCertificate where
  priorFreeDirac := complete_first_principles_free_dirac
  nativePlaneSquare := cubical_plane_bivector_square
  uniqueNonzeroSpinScale := exists_unique_admissible_cubical_spin_scale
  uniqueOperationalRotationScale :=
    exists_unique_cubical_operational_rotation_scale
  nativeSpinMatchesOperationalRotation :=
    native_cubical_spin_is_operational_rotation
  spinCommutators :=
    ⟨cubical_spin_commutator_01, cubical_spin_commutator_12,
      cubical_spin_commutator_20⟩
  spinCasimir := cubical_spin_casimir
  bothCopyIntertwining :=
    ⟨cubical_spin_intertwines_minus, cubical_spin_intertwines_plus⟩
  explicitSpinSpectrum := standard_spin0_basis_spectrum
  twoPiSign := cubical_continuous_turn_two_pi
  fourPiReturn := cubical_continuous_turn_four_pi
  finiteRotationIsUnitary :=
    standard_cubical_continuous_turn_preserves_density
  spinGeneratorIsHermitian := standard_cubical_spin_is_hermitian
  finiteRotationGroup :=
    ⟨standard_cubical_continuous_turn_zero,
      standard_cubical_continuous_turn_add,
      standard_cubical_continuous_turn_inverse⟩
  finiteRotationGenerator :=
    standard_cubical_continuous_turn_has_derivative
  finiteRotationBothCopies :=
    ⟨cubical_continuous_turn_intertwines_minus,
      cubical_continuous_turn_intertwines_plus⟩
  boostBothCopies :=
    ⟨cubical_boost_intertwines_minus,
      cubical_boost_intertwines_plus⟩
  boostCommutators :=
    ⟨cubical_boost_commutator_01, cubical_boost_commutator_12,
      cubical_boost_commutator_20⟩
  rotationBoostCommutators :=
    ⟨cubical_rotation_boost_commutator_01,
      cubical_rotation_boost_commutator_12,
      cubical_rotation_boost_commutator_20⟩
  massInvariantUnderRotations := standard_beta_commutes_spin
  transportRotatesCovariantly :=
    ⟨standard_spin_rotates_transport_01,
      standard_spin_rotates_transport_12,
      standard_spin_rotates_transport_20⟩
  boostsTransformGammaFourVector :=
    ⟨cubical_boost_transforms_gamma_time,
      cubical_boost_transforms_parallel_gamma_space,
      fun axis other haxis z =>
        cubical_boost_commutes_transverse_gamma_space
          axis other haxis z⟩
  fullDiracSymbolCovariance :=
    ⟨oriented_dirac_symbol_rotation_covariant,
      oriented_dirac_symbol_boost_covariant⟩
  pauliLubanskiBoostCovariance :=
    ⟨cubical_pauli_lubanski_boost_covariant_time,
      cubical_pauli_lubanski_boost_covariant_space⟩
  pauliLubanskiRotationCovariance :=
    ⟨cubical_pauli_lubanski_rotation_covariant_time,
      cubical_pauli_lubanski_rotation_covariant_space⟩
  pauliLubanskiOrthogonal := cubical_pauli_lubanski_orthogonal
  restPauliLubanskiCasimir := rest_pauli_lubanski_spin_half

end
end LeanDirac.V2
