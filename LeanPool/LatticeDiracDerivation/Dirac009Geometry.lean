/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac009Geometry.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac008

/-!
# DIRAC-009 research boundary: cubical square-root geometry

DIRAC-006 proves that the action-derived aligned transport has the even C19
symbol and zero first moment.  Therefore that scalar transport channel cannot
itself be renamed as a nonzero first-order Dirac transport generator.

The definitions below construct the signed incidence maps of the oriented
cube directly from its three parity bits.  The signs are not Dirac matrices
supplied as data: they are the usual orientation signs for crossing successive
coordinate directions on a cube.  Their anticommutation follows from the odd
sign around every oriented square face.

This file deliberately does **not** promote DIRAC-009 by itself.  It proves an exact
positive-frequency phase-space intertwiner for the scalar C19 wave symbol,
identifies its cubical Dirac square root, derives the finite-lattice residual,
and bounds that residual by `40 r ^ 4` when every momentum component is bounded
by `r ≤ 1/2`.  It also proves that the prepared running-family equations select
the positive rest frequency `chi0`.

The incidence maps below are a continuum square-root readout of the ordinary
C19 quadratic symbol. They are not inserted into the native action. The exact
finite-lattice difference from that continuum factorization is retained and
bounded rather than hidden in a modified transport law.
-/

@[expose] public section


namespace LeanDirac

variable {Site : Type} {Edge : Type*}

noncomputable section

def cubeIncidenceFlip (axis : Fin 3) : CubeCorner → CubeCorner :=
  match axis with
  | 0 => cellFlip0
  | 1 => cellFlip1
  | _ => cellFlip2

def preparedCubeEdgeOverlap (axis : Fin 3) (corner : CubeCorner) : ℂ :=
  overlap (tetraCorner corner)
    (tetraCorner (cubeIncidenceFlip axis corner))

def preparedCubeExpectedEdgeOverlap
    (axis : Fin 3) (corner : CubeCorner) : ℂ :=
  match axis.val, corner.val with
  | 0, 0 => -tetraA | 0, 1 => -(tetraA * Complex.I)
  | 0, 2 => tetraA * Complex.I | 0, 3 => -tetraA
  | 0, 4 => -tetraA | 0, 5 => tetraA * Complex.I
  | 0, 6 => -(tetraA * Complex.I) | 0, _ => -tetraA
  | 1, 0 => tetraA | 1, 1 => -(tetraA * Complex.I)
  | 1, 2 => tetraA | 1, 3 => tetraA * Complex.I
  | 1, 4 => tetraA * Complex.I | 1, 5 => tetraA
  | 1, 6 => -(tetraA * Complex.I) | 1, _ => tetraA
  | _, 0 => tetraA | _, 1 => tetraA
  | _, 2 => tetraA * Complex.I | _, 3 => -(tetraA * Complex.I)
  | _, 4 => -(tetraA * Complex.I) | _, 5 => tetraA * Complex.I
  | _, 6 => tetraA | _, _ => tetraA

theorem prepared_cube_edge_overlap_values
    (axis : Fin 3) (corner : CubeCorner) :
    preparedCubeEdgeOverlap axis corner =
      preparedCubeExpectedEdgeOverlap axis corner := by
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := overlap_tetra_rays
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := tetra_corner_values
  fin_cases axis <;> fin_cases corner <;>
    simp only [preparedCubeEdgeOverlap, preparedCubeExpectedEdgeOverlap, cubeIncidenceFlip,
      cellFlip0, cellFlip1, cellFlip2, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      c0, c1, c2, c3, c4, c5, c6, c7, overlap_neg_left, overlap_neg_right] <;>
    simp only [overlap_swap tetraRay0 tetraRay1, overlap_swap tetraRay0 tetraRay2,
      overlap_swap tetraRay0 tetraRay3, overlap_swap tetraRay1 tetraRay2,
      overlap_swap tetraRay1 tetraRay3, overlap_swap tetraRay2 tetraRay3,
      h01, h02, h03, h12, h13, h23, star_neg, star_mul', Complex.star_def,
      Complex.conj_ofReal, Complex.conj_I] <;>
    ring

def preparedGaussianPhaseExponent (z : ℂ) : ZMod 4 :=
  if z.im = 0 then
    if 0 < z.re then 0 else 2
  else if 0 < z.im then 1 else 3

def preparedCubeConnection4
    (axis : Fin 3) (corner : CubeCorner) : ZMod 4 :=
  preparedGaussianPhaseExponent (preparedCubeEdgeOverlap axis corner)

def preparedCubeGauge4 (corner : CubeCorner) : ZMod 4 :=
  match corner.val with
  | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 1
  | 4 => 2 | 5 => 1 | 6 => 3 | _ => 3

def cubeIncidenceSign (axis : Fin 3) (corner : CubeCorner) : ℂ :=
  match axis with
  | 0 => 1
  | 1 => if cellBit0 corner = 0 then 1 else -1
  | _ => if (cellBit0 corner + cellBit1 corner) % 2 = 0 then 1 else -1

def cubeIncidenceConnection4
    (axis : Fin 3) (corner : CubeCorner) : ZMod 4 :=
  match axis with
  | 0 => 0
  | 1 => if cellBit0 corner = 0 then 0 else 2
  | _ => if (cellBit0 corner + cellBit1 corner) % 2 = 0 then 0 else 2

theorem prepared_cube_connection_gauge_eq_incidence
    (axis : Fin 3) (corner : CubeCorner) :
    preparedCubeConnection4 axis corner - preparedCubeGauge4 corner +
        preparedCubeGauge4 (cubeIncidenceFlip axis corner) =
      cubeIncidenceConnection4 axis corner := by
  rw [preparedCubeConnection4, prepared_cube_edge_overlap_values]
  have hA : 0 < Real.sqrt 3 / 3 := by positivity
  have hAnot : ¬ Real.sqrt 3 / 3 < 0 := not_lt_of_ge (le_of_lt hA)
  have hfour : (4 : ZMod 4) = 0 := by decide
  have hnegTwo : (-2 : ZMod 4) = 2 := by decide
  fin_cases axis <;> fin_cases corner <;>
    simp only [preparedGaussianPhaseExponent, preparedCubeExpectedEdgeOverlap, tetraA, one_div,
        Complex.ofReal_inv, Complex.neg_im, Complex.inv_im, Complex.ofReal_im, neg_zero,
        Complex.normSq_ofReal, Nat.ofNat_nonneg, Real.mul_self_sqrt, zero_div, ↓reduceIte,
        Complex.neg_re, Complex.inv_re, Complex.ofReal_re, Left.neg_pos_iff, hAnot,
        preparedCubeGauge4, sub_zero, cubeIncidenceFlip, Fin.zero_eta, Fin.isValue, cellFlip0,
        Fin.coe_ofNat_eq_mod, Nat.reduceMod, cubeIncidenceConnection4, Complex.mul_im, Complex.I_im,
        mul_one, Complex.I_re, mul_zero, add_zero, neg_eq_zero, div_eq_zero_iff, Real.sqrt_eq_zero,
        OfNat.ofNat_ne_zero, or_self, Fin.mk_one, hA, Fin.reduceFinMk, Nat.mod_succ, sub_self,
        Nat.zero_mod, Nat.one_mod, cellFlip1, cellBit0, one_ne_zero, zero_sub, zero_add, cellFlip2,
        cellBit1, neg_add_cancel, Nat.reduceAdd, Nat.mod_self]
  all_goals first | exact hfour | exact hnegTwo

def cubeIncidenceGamma (axis : Fin 3) (amplitude : Cell8) : Cell8 :=
  fun corner =>
    cubeIncidenceSign axis corner *
      amplitude (cubeIncidenceFlip axis corner)

def cubeParityBeta (amplitude : Cell8) : Cell8 :=
  fun corner =>
    if (cellBit0 corner + cellBit1 corner + cellBit2 corner) % 2 = 0 then
      amplitude corner
    else
      -amplitude corner

theorem cube_incidence_gamma_square (axis : Fin 3) (amplitude : Cell8) :
    cubeIncidenceGamma axis (cubeIncidenceGamma axis amplitude) = amplitude := by
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubeIncidenceGamma, cubeIncidenceSign, cubeIncidenceFlip,
      cellFlip0, cellFlip1, cellFlip2, cellBit0, cellBit1]

theorem cube_incidence_gamma_anticommute
    (axis other : Fin 3) (haxis : axis ≠ other) (amplitude : Cell8) :
    cubeIncidenceGamma axis (cubeIncidenceGamma other amplitude) =
      fun corner =>
        -cubeIncidenceGamma other (cubeIncidenceGamma axis amplitude) corner := by
  fin_cases axis <;> fin_cases other <;> try { contradiction }
  all_goals
    funext corner
    fin_cases corner <;>
      simp [cubeIncidenceGamma, cubeIncidenceSign, cubeIncidenceFlip,
        cellFlip0, cellFlip1, cellFlip2, cellBit0, cellBit1]

theorem cube_parity_beta_square (amplitude : Cell8) :
    cubeParityBeta (cubeParityBeta amplitude) = amplitude := by
  funext corner
  fin_cases corner <;>
    simp [cubeParityBeta, cellBit0, cellBit1, cellBit2]

theorem cube_parity_beta_anticommutes
    (axis : Fin 3) (amplitude : Cell8) :
    cubeParityBeta (cubeIncidenceGamma axis amplitude) =
      fun corner =>
        -cubeIncidenceGamma axis (cubeParityBeta amplitude) corner := by
  fin_cases axis
  all_goals
    funext corner
    fin_cases corner <;>
      simp [cubeParityBeta, cubeIncidenceGamma, cubeIncidenceSign,
        cubeIncidenceFlip, cellFlip0, cellFlip1, cellFlip2,
        cellBit0, cellBit1, cellBit2]

def cubeIncidenceLinear
    (k0 k1 k2 : ℂ) (amplitude : Cell8) : Cell8 :=
  fun corner =>
    k0 * cubeIncidenceGamma 0 amplitude corner +
    k1 * cubeIncidenceGamma 1 amplitude corner +
    k2 * cubeIncidenceGamma 2 amplitude corner

theorem cube_incidence_linear_square
    (k0 k1 k2 : ℂ) (amplitude : Cell8) :
    cubeIncidenceLinear k0 k1 k2
        (cubeIncidenceLinear k0 k1 k2 amplitude) =
      fun corner => (k0 ^ 2 + k1 ^ 2 + k2 ^ 2) * amplitude corner := by
  funext corner
  fin_cases corner <;>
    simp [cubeIncidenceLinear, cubeIncidenceGamma, cubeIncidenceSign,
      cubeIncidenceFlip, cellFlip0, cellFlip1, cellFlip2,
      cellBit0, cellBit1] <;>
    ring

/-!
The eight cube amplitudes contain two equivalent four-coordinate sectors.
The commuting `cubeFlavor` map is assembled from the same cube translations
and parity bits as the incidence connection; it is not an independent
projector supplied to the dynamics.
-/

abbrev Cell4 := Fin 4 → ℂ

def cubeFlavorSign (corner : CubeCorner) : ℝ :=
  if cellBit2 corner % 2 = 0 then 1 else -1

def cubeFlavor (amplitude : Cell8) : Cell8 := fun corner =>
  Complex.I * (cubeFlavorSign corner : ℂ) *
    amplitude (cellFlip1 (cellFlip2 corner))

theorem cube_flavor_involution (amplitude : Cell8) :
    cubeFlavor (cubeFlavor amplitude) = amplitude := by
  funext corner
  fin_cases corner <;>
    simp [cubeFlavor, cubeFlavorSign, cellFlip1, cellFlip2, cellBit2] <;>
    ring_nf <;> rw [Complex.I_sq] <;> ring

theorem cube_flavor_commutes_gamma
    (axis : Fin 3) (amplitude : Cell8) :
    cubeFlavor (cubeIncidenceGamma axis amplitude) =
      cubeIncidenceGamma axis (cubeFlavor amplitude) := by
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubeFlavor, cubeFlavorSign, cubeIncidenceGamma,
      cubeIncidenceSign, cubeIncidenceFlip, cellFlip0, cellFlip1,
      cellFlip2, cellBit0, cellBit1, cellBit2]

theorem cube_flavor_commutes_beta (amplitude : Cell8) :
    cubeFlavor (cubeParityBeta amplitude) =
      cubeParityBeta (cubeFlavor amplitude) := by
  funext corner
  fin_cases corner <;>
    simp [cubeFlavor, cubeFlavorSign, cubeParityBeta,
      cellFlip1, cellFlip2, cellBit0, cellBit1, cellBit2]

def cubeEmbedMinus (z : Cell4) : Cell8
  | 0 => z 0 | 1 => z 1 | 2 => -Complex.I * z 1 | 3 => Complex.I * z 0
  | 4 => z 2 | 5 => z 3 | 6 => -Complex.I * z 3 | _ => Complex.I * z 2

def cubeEmbedPlus (z : Cell4) : Cell8
  | 0 => z 0 | 1 => z 1 | 2 => Complex.I * z 1 | 3 => -Complex.I * z 0
  | 4 => z 2 | 5 => z 3 | 6 => Complex.I * z 3 | _ => -Complex.I * z 2

theorem cube_embed_minus_injective : Function.Injective cubeEmbedMinus := by
  intro first second h
  funext component
  fin_cases component
  · exact congrFun h 0
  · exact congrFun h 1
  · exact congrFun h 4
  · exact congrFun h 5

theorem cube_embed_plus_injective : Function.Injective cubeEmbedPlus := by
  intro first second h
  funext component
  fin_cases component
  · exact congrFun h 0
  · exact congrFun h 1
  · exact congrFun h 4
  · exact congrFun h 5

theorem cube_embed_minus_has_negative_flavor (z : Cell4) :
    cubeFlavor (cubeEmbedMinus z) = fun corner => -cubeEmbedMinus z corner := by
  funext corner
  fin_cases corner <;>
    simp [cubeFlavor, cubeFlavorSign, cubeEmbedMinus,
      cellFlip1, cellFlip2, cellBit2] <;>
    ring_nf <;> rw [Complex.I_sq] <;> ring

theorem cube_embed_plus_has_positive_flavor (z : Cell4) :
    cubeFlavor (cubeEmbedPlus z) = cubeEmbedPlus z := by
  funext corner
  fin_cases corner <;>
    simp [cubeFlavor, cubeFlavorSign, cubeEmbedPlus,
      cellFlip1, cellFlip2, cellBit2] <;>
    ring_nf <;> rw [Complex.I_sq] <;> ring

def cubeDiracSymbol
    (mass k0 k1 k2 : ℂ) (amplitude : Cell8) : Cell8 := fun corner =>
  mass * cubeParityBeta amplitude corner +
    cubeIncidenceLinear k0 k1 k2 amplitude corner

def cubeScalarSymbol
    (mass k0 k1 k2 : ℂ) (amplitude : Cell8) : Cell8 := fun corner =>
  (mass ^ 2 + k0 ^ 2 + k1 ^ 2 + k2 ^ 2) * amplitude corner

theorem cube_dirac_symbol_square
    (mass k0 k1 k2 : ℂ) (amplitude : Cell8) :
    cubeDiracSymbol mass k0 k1 k2
        (cubeDiracSymbol mass k0 k1 k2 amplitude) =
      cubeScalarSymbol mass k0 k1 k2 amplitude := by
  funext corner
  fin_cases corner <;>
    simp [cubeDiracSymbol, cubeScalarSymbol, cubeParityBeta,
      cubeIncidenceLinear, cubeIncidenceGamma, cubeIncidenceSign,
      cubeIncidenceFlip, cellFlip0, cellFlip1, cellFlip2,
      cellBit0, cellBit1, cellBit2] <;>
    ring

theorem cube_dirac_symbol_scale
    (mass k0 k1 k2 scalar : ℂ) (amplitude : Cell8) :
    cubeDiracSymbol mass k0 k1 k2
        (fun corner => scalar * amplitude corner) =
      fun corner => scalar * cubeDiracSymbol mass k0 k1 k2 amplitude corner := by
  funext corner
  fin_cases corner <;>
    simp [cubeDiracSymbol, cubeParityBeta, cubeIncidenceLinear,
      cubeIncidenceGamma, cubeIncidenceSign, cubeIncidenceFlip,
      cellFlip0, cellFlip1, cellFlip2, cellBit0, cellBit1, cellBit2] <;>
    ring

theorem cube_flavor_commutes_dirac_symbol
    (mass k0 k1 k2 : ℂ) (amplitude : Cell8) :
    cubeFlavor (cubeDiracSymbol mass k0 k1 k2 amplitude) =
      cubeDiracSymbol mass k0 k1 k2 (cubeFlavor amplitude) := by
  funext corner
  fin_cases corner <;>
    simp [cubeFlavor, cubeFlavorSign, cubeDiracSymbol, cubeParityBeta,
      cubeIncidenceLinear, cubeIncidenceGamma, cubeIncidenceSign,
      cubeIncidenceFlip, cellFlip0, cellFlip1, cellFlip2,
      cellBit0, cellBit1, cellBit2] <;>
    ring

theorem cube_dirac_symbol_preserves_minus
    (mass k0 k1 k2 : ℂ) (amplitude : Cell8)
    (h : cubeFlavor amplitude = fun corner => -amplitude corner) :
    cubeFlavor (cubeDiracSymbol mass k0 k1 k2 amplitude) =
      fun corner => -cubeDiracSymbol mass k0 k1 k2 amplitude corner := by
  rw [cube_flavor_commutes_dirac_symbol, h]
  funext corner
  fin_cases corner <;>
    simp [cubeDiracSymbol, cubeParityBeta, cubeIncidenceLinear,
      cubeIncidenceGamma, cubeIncidenceSign, cubeIncidenceFlip,
      cellFlip0, cellFlip1, cellFlip2, cellBit0, cellBit1, cellBit2] <;>
    ring

structure CubeCanonicalState where
  position : Cell8
  velocity : Cell8

@[ext] theorem cube_canonical_state_ext
    (first second : CubeCanonicalState)
    (hposition : first.position = second.position)
    (hvelocity : first.velocity = second.velocity) : first = second := by
  cases first
  cases second
  simp_all

def cubeScalarCanonicalVector
    (mass k0 k1 k2 : ℂ) (state : CubeCanonicalState) : CubeCanonicalState where
  position := state.velocity
  velocity := fun corner => -cubeScalarSymbol mass k0 k1 k2 state.position corner

def cubePositiveFrequencyEmbedding
    (mass k0 k1 k2 : ℂ) (amplitude : Cell8) : CubeCanonicalState where
  position := amplitude
  velocity := fun corner =>
    -Complex.I * cubeDiracSymbol mass k0 k1 k2 amplitude corner

theorem cube_positive_frequency_intertwining
    (mass k0 k1 k2 : ℂ) (amplitude : Cell8) :
    cubeScalarCanonicalVector mass k0 k1 k2
        (cubePositiveFrequencyEmbedding mass k0 k1 k2 amplitude) =
      cubePositiveFrequencyEmbedding mass k0 k1 k2
        (fun corner =>
          -Complex.I * cubeDiracSymbol mass k0 k1 k2 amplitude corner) := by
  apply cube_canonical_state_ext
  · rfl
  · funext corner
    simp only [cubeScalarCanonicalVector, cubePositiveFrequencyEmbedding]
    rw [cube_dirac_symbol_scale, cube_dirac_symbol_square]
    simp [cubeScalarSymbol]
    ring_nf
    rw [Complex.I_sq]
    ring

/-!
The coefficient of the local continuum spatial square is not fitted: it is
the diagonal C19 second moment already proved in DIRAC-006.  The positive
square root supplies the common conversion from continuum wave number to the
three incidence coefficients.
-/

def c19ContinuumSpeed : ℝ := Real.sqrt 12

theorem c19_continuum_speed_square : c19ContinuumSpeed ^ 2 = 12 := by
  norm_num [c19ContinuumSpeed]

/-!
The rest coefficient used below is not an independent Dirac input.  On the
already-running prepared family, the local action equations and total-capacity
condition select the positive rest frequency `chi0`.
-/

theorem prepared_running_rest_frequency_is_chi0
    (A R omega : ℝ) (hA : A ≠ 0)
    (hdensity : A ^ 2 + R ^ 2 = chi0 ^ 2)
    (hpsi : omega ^ 2 * A = (R ^ 2 + A ^ 2) * A)
    (homega : 0 ≤ omega) :
    omega = chi0 := by
  exact running_frequency_is_chi0 A R chi0 omega hA hdensity hpsi
    homega (by norm_num [chi0])

/-!
Why the carved complex-chi track does not yet supply the massive Clifford
sector: on the exact prepared rays, a common pair of amplitudes gives the same
oriented area at every corner.  The complete bond action therefore assigns
zero energy to every bond of that pattern.  Meanwhile the local action sees
only the two field densities.  Thus the current action preserves the track but
does not give its corner orientation a local restoring scale.
-/

def constantAlignedEightSiteState (psiAmplitude chiAmplitude : ℂ) :
    State CubeCorner :=
  alignedEightSiteState (fun _ => psiAmplitude) (fun _ => chiAmplitude)

theorem constant_aligned_wedge_is_corner_independent
    (psiAmplitude chiAmplitude : ℂ) (corner : CubeCorner) :
    wedge ((constantAlignedEightSiteState psiAmplitude chiAmplitude).chi corner)
      ((constantAlignedEightSiteState psiAmplitude chiAmplitude).psi corner) =
      c3ScaleComplex (-(chiAmplitude * psiAmplitude)) unitArea := by
  exact aligned_wedge (fun _ => psiAmplitude) (fun _ => chiAmplitude) corner

theorem constant_aligned_bond_energy_zero
    (chi0 : ℝ) (psiAmplitude chiAmplitude : ℂ)
    (edge : Bond CubeCorner) :
    exteriorAreaBond chi0
      (constantAlignedEightSiteState psiAmplitude chiAmplitude) edge = 0 := by
  apply bond_zero_of_constant_area
  rw [constant_aligned_wedge_is_corner_independent,
    constant_aligned_wedge_is_corner_independent]

theorem site_potential_is_orientation_blind
    (chi0 : ℝ) (first second : State Site) (site : Site)
    (hpsi : density (first.psi site) = density (second.psi site))
    (hchi : density (first.chi site) = density (second.chi site)) :
    sitePotential chi0 first site = sitePotential chi0 second site := by
  simp only [sitePotential]
  rw [hpsi, hchi]

theorem normSq_one_sub_exp_I (angle : ℝ) :
    Complex.normSq
        (1 - Complex.exp (Complex.I * (angle : ℂ))) =
      2 * (1 - Real.cos angle) := by
  rw [mul_comm, Complex.exp_ofReal_mul_I]
  rw [Complex.normSq_apply]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  nlinarith [Real.sin_sq_add_cos_sq angle]

def c19ClosedSymbol (momentum : LatticeMomentum) : ℝ :=
  8 * ((1 - Real.cos (momentum 0)) +
    (1 - Real.cos (momentum 1)) +
    (1 - Real.cos (momentum 2)) +
    (1 - Real.cos (momentum 0) * Real.cos (momentum 1)) +
    (1 - Real.cos (momentum 0) * Real.cos (momentum 2)) +
    (1 - Real.cos (momentum 1) * Real.cos (momentum 2)))

theorem c19_transport_symbol_closed (momentum : LatticeMomentum) :
    c19TransportSymbol momentum = c19ClosedSymbol momentum := by
  unfold c19TransportSymbol c19ClosedSymbol
  simp only [c19Character, normSq_one_sub_exp_I]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, c19PhaseAngle]
  norm_num [c19Weight, c19Coord]
  simp only [Real.cos_neg, Real.cos_add, Real.cos_sub, neg_add_eq_sub, Real.sin_neg]
  ring_nf

def c19QuadraticSymbol (momentum : LatticeMomentum) : ℝ :=
  12 * (momentum 0 ^ 2 + momentum 1 ^ 2 + momentum 2 ^ 2)

theorem c19_quadratic_symbol_is_phase_square_sum
    (momentum : LatticeMomentum) :
    c19QuadraticSymbol momentum =
      ∑ direction,
        c19Weight direction * c19PhaseAngle momentum direction ^ 2 := by
  unfold c19QuadraticSymbol c19PhaseAngle
  simp only [Fin.sum_univ_succ]
  simp [c19Weight, c19Coord]
  ring

def c19SpatialRemainder (momentum : LatticeMomentum) : ℝ :=
  c19TransportSymbol momentum - c19QuadraticSymbol momentum

theorem c19_spatial_remainder_is_bond_error_sum
    (momentum : LatticeMomentum) :
    c19SpatialRemainder momentum =
      ∑ direction, c19Weight direction *
        (2 * (1 - Real.cos (c19PhaseAngle momentum direction)) -
          c19PhaseAngle momentum direction ^ 2) := by
  rw [c19SpatialRemainder, c19_quadratic_symbol_is_phase_square_sum]
  unfold c19TransportSymbol
  simp_rw [c19Character, normSq_one_sub_exp_I]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro direction _
  ring

theorem c19_phase_angle_abs_le_two_mul
    (momentum : LatticeMomentum) (radius : ℝ) (hradius : 0 ≤ radius)
    (hmomentum : ∀ axis, |momentum axis| ≤ radius)
    (direction : C19Neighbor) :
    |c19PhaseAngle momentum direction| ≤ 2 * radius := by
  have hsum : |c19Coord 0 direction| + |c19Coord 1 direction| +
      |c19Coord 2 direction| ≤ 2 := by
    revert direction
    decide
  have hsumReal : |(c19Coord 0 direction : ℝ)| + |(c19Coord 1 direction : ℝ)| +
      |(c19Coord 2 direction : ℝ)| ≤ 2 := by
    simp only [← Int.cast_abs]
    exact_mod_cast hsum
  have hterm : ∀ axis, |momentum axis * (c19Coord axis direction : ℝ)| ≤
      radius * |(c19Coord axis direction : ℝ)| := fun axis => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hmomentum axis) (abs_nonneg _)
  unfold c19PhaseAngle
  rw [Fin.sum_univ_three]
  calc
    _ ≤ |momentum 0 * (c19Coord 0 direction : ℝ)| +
        |momentum 1 * (c19Coord 1 direction : ℝ)| +
        |momentum 2 * (c19Coord 2 direction : ℝ)| := abs_add_three _ _ _
    _ ≤ radius * (|(c19Coord 0 direction : ℝ)| + |(c19Coord 1 direction : ℝ)| +
        |(c19Coord 2 direction : ℝ)|) := by
      linarith [hterm 0, hterm 1, hterm 2]
    _ ≤ 2 * radius := by nlinarith

theorem cosine_phase_error_bound
    (angle radius : ℝ) (_hradius : 0 ≤ radius)
    (hangle : |angle| ≤ 2 * radius) (hsmall : 2 * radius ≤ 1) :
    |2 * (1 - Real.cos angle) - angle ^ 2| ≤ (5/3 : ℝ) * radius ^ 4 := by
  have hunit : |angle| ≤ 1 := hangle.trans hsmall
  have hcos := Real.cos_bound hunit
  have hpow : |angle| ^ 4 ≤ (2 * radius) ^ 4 :=
    pow_le_pow_left₀ (abs_nonneg angle) hangle 4
  calc
    |2 * (1 - Real.cos angle) - angle ^ 2| =
        2 * |Real.cos angle - (1 - angle ^ 2 / 2)| := by
          rw [show 2 * (1 - Real.cos angle) - angle ^ 2 =
            -2 * (Real.cos angle - (1 - angle ^ 2 / 2)) by ring]
          simp
    _ ≤ 2 * (|angle| ^ 4 * (5/96 : ℝ)) := by nlinarith
    _ ≤ 2 * ((2 * radius) ^ 4 * (5/96 : ℝ)) := by nlinarith
    _ = (5/3 : ℝ) * radius ^ 4 := by ring

theorem c19_spatial_remainder_bound
    (momentum : LatticeMomentum) (radius : ℝ) (hradius : 0 ≤ radius)
    (hmomentum : ∀ axis, |momentum axis| ≤ radius)
    (hsmall : 2 * radius ≤ 1) :
    |c19SpatialRemainder momentum| ≤ 40 * radius ^ 4 := by
  rw [c19_spatial_remainder_is_bond_error_sum]
  calc
    |∑ direction, c19Weight direction *
        (2 * (1 - Real.cos (c19PhaseAngle momentum direction)) -
          c19PhaseAngle momentum direction ^ 2)| ≤
      ∑ direction, |c19Weight direction *
        (2 * (1 - Real.cos (c19PhaseAngle momentum direction)) -
          c19PhaseAngle momentum direction ^ 2)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ direction, c19Weight direction * ((5/3 : ℝ) * radius ^ 4) := by
      apply Finset.sum_le_sum
      intro direction _
      rw [abs_mul, abs_of_pos (c19_weight_positive direction)]
      exact mul_le_mul_of_nonneg_left
        (cosine_phase_error_bound
          (c19PhaseAngle momentum direction) radius hradius
          (c19_phase_angle_abs_le_two_mul momentum radius hradius
            hmomentum direction) hsmall)
        (le_of_lt (c19_weight_positive direction))
    _ = 40 * radius ^ 4 := by
      have hweights : ∑ direction, c19Weight direction = 24 := by
        norm_num [c19Weight, Fin.sum_univ_succ]
      rw [← Finset.sum_mul, hweights]
      ring

theorem c19_symbol_exact_quadratic_plus_remainder
    (momentum : LatticeMomentum) :
    c19TransportSymbol momentum =
      c19QuadraticSymbol momentum + c19SpatialRemainder momentum := by
  simp [c19SpatialRemainder]

theorem c19_spatial_remainder_zero_at_origin :
    c19SpatialRemainder (fun _ => 0) = 0 := by
  simp [c19SpatialRemainder, c19QuadraticSymbol,
    c19_transport_symbol_zero]

def c19ContinuumDiracSymbol
    (mass : ℂ) (momentum : Fin 3 → ℝ) (amplitude : Cell8) : Cell8 :=
  cubeDiracSymbol mass
    (c19ContinuumSpeed * momentum 0)
    (c19ContinuumSpeed * momentum 1)
    (c19ContinuumSpeed * momentum 2) amplitude

def c19ContinuumScalarSymbol
    (mass : ℂ) (momentum : Fin 3 → ℝ) (amplitude : Cell8) : Cell8 :=
  fun corner =>
    (mass ^ 2 + (12 : ℂ) *
      ((momentum 0 : ℂ) ^ 2 + (momentum 1 : ℂ) ^ 2 +
        (momentum 2 : ℂ) ^ 2)) * amplitude corner

def c19ExactScalarSymbol
    (mass : ℂ) (momentum : LatticeMomentum) (amplitude : Cell8) : Cell8 :=
  fun corner =>
    (mass ^ 2 + (c19TransportSymbol momentum : ℂ)) * amplitude corner

theorem c19_exact_scalar_symbol_splits
    (mass : ℂ) (momentum : LatticeMomentum) (amplitude : Cell8) :
    c19ExactScalarSymbol mass momentum amplitude = fun corner =>
      c19ContinuumScalarSymbol mass momentum amplitude corner +
        (c19SpatialRemainder momentum : ℂ) * amplitude corner := by
  funext corner
  simp [c19ExactScalarSymbol, c19ContinuumScalarSymbol,
    c19SpatialRemainder, c19QuadraticSymbol]
  ring

theorem cube_scalar_scaled_is_c19_continuum_symbol
    (mass : ℂ) (momentum : Fin 3 → ℝ) (amplitude : Cell8) :
    cubeScalarSymbol mass
        (c19ContinuumSpeed * momentum 0)
        (c19ContinuumSpeed * momentum 1)
        (c19ContinuumSpeed * momentum 2) amplitude =
      c19ContinuumScalarSymbol mass momentum amplitude := by
  funext corner
  change
    (mass ^ 2 + (((c19ContinuumSpeed : ℝ) : ℂ) * momentum 0) ^ 2 +
      (((c19ContinuumSpeed : ℝ) : ℂ) * momentum 1) ^ 2 +
      (((c19ContinuumSpeed : ℝ) : ℂ) * momentum 2) ^ 2) * amplitude corner =
    (mass ^ 2 + (12 : ℂ) *
      ((momentum 0 : ℂ) ^ 2 + (momentum 1 : ℂ) ^ 2 +
        (momentum 2 : ℂ) ^ 2)) * amplitude corner
  have hc : ((c19ContinuumSpeed : ℝ) : ℂ) ^ 2 = 12 := by
    exact_mod_cast c19_continuum_speed_square
  rw [mul_pow, mul_pow, mul_pow, hc]
  ring

theorem c19_continuum_dirac_square_is_native_quadratic_symbol
    (mass : ℂ) (momentum : Fin 3 → ℝ) (amplitude : Cell8) :
    c19ContinuumDiracSymbol mass momentum
        (c19ContinuumDiracSymbol mass momentum amplitude) =
      c19ContinuumScalarSymbol mass momentum amplitude := by
  simp only [c19ContinuumDiracSymbol]
  rw [cube_dirac_symbol_square]
  exact cube_scalar_scaled_is_c19_continuum_symbol mass momentum amplitude

def c19ExactCanonicalVector
    (mass : ℂ) (momentum : LatticeMomentum)
    (state : CubeCanonicalState) : CubeCanonicalState where
  position := state.velocity
  velocity := fun corner =>
    -c19ExactScalarSymbol mass momentum state.position corner

def c19PositiveFrequencyEmbedding
    (mass : ℂ) (momentum : LatticeMomentum)
    (amplitude : Cell8) : CubeCanonicalState where
  position := amplitude
  velocity := fun corner =>
    -Complex.I * c19ContinuumDiracSymbol mass momentum amplitude corner

theorem c19_embedding_position_intertwines_exactly
    (mass : ℂ) (momentum : LatticeMomentum) (amplitude : Cell8) :
    (c19ExactCanonicalVector mass momentum
      (c19PositiveFrequencyEmbedding mass momentum amplitude)).position =
    (c19PositiveFrequencyEmbedding mass momentum
      (fun corner => -Complex.I *
        c19ContinuumDiracSymbol mass momentum amplitude corner)).position := by
  rfl

theorem c19_embedding_velocity_residual_is_spatial_remainder
    (mass : ℂ) (momentum : LatticeMomentum) (amplitude : Cell8) :
    (c19ExactCanonicalVector mass momentum
        (c19PositiveFrequencyEmbedding mass momentum amplitude)).velocity =
      fun corner =>
        (c19PositiveFrequencyEmbedding mass momentum
          (fun site => -Complex.I *
            c19ContinuumDiracSymbol mass momentum amplitude site)).velocity corner -
        (c19SpatialRemainder momentum : ℂ) * amplitude corner := by
  funext corner
  simp only [c19ExactCanonicalVector, c19PositiveFrequencyEmbedding]
  rw [c19_exact_scalar_symbol_splits]
  simp only [c19ContinuumDiracSymbol]
  rw [cube_dirac_symbol_scale, cube_dirac_symbol_square]
  rw [cube_scalar_scaled_is_c19_continuum_symbol]
  change
    -(c19ContinuumScalarSymbol mass momentum amplitude corner +
        (c19SpatialRemainder momentum : ℂ) * amplitude corner) =
      -Complex.I *
          (-Complex.I *
            c19ContinuumScalarSymbol mass momentum amplitude corner) -
        (c19SpatialRemainder momentum : ℂ) * amplitude corner
  ring_nf
  rw [Complex.I_sq]
  ring

theorem c19_native_second_moment_selects_continuum_speed :
    (∀ axis other,
      c19SecondMoment axis other = if axis = other then 12 else 0) ∧
    c19ContinuumSpeed ^ 2 = 12 :=
  ⟨c19_second_moment_isotropic, c19_continuum_speed_square⟩

def cubeIncidenceFaceSign
    (axis other : Fin 3) (corner : CubeCorner) : ℂ :=
  cubeIncidenceSign axis corner *
    cubeIncidenceSign other (cubeIncidenceFlip axis corner) *
    cubeIncidenceSign axis (cubeIncidenceFlip other corner) *
    cubeIncidenceSign other corner

theorem cube_incidence_face_sign_negative
    (axis other : Fin 3) (haxis : axis ≠ other) (corner : CubeCorner) :
    cubeIncidenceFaceSign axis other corner = -1 := by
  fin_cases axis <;> fin_cases other <;> try { contradiction }
  all_goals
    fin_cases corner <;>
      simp [cubeIncidenceFaceSign, cubeIncidenceSign, cubeIncidenceFlip,
        cellFlip0, cellFlip1, cellFlip2, cellBit0, cellBit1]

/-! The native aligned C19 action has no nonzero first spatial moment. -/
theorem aligned_c19_transport_has_zero_first_moment (axis : Fin 3) :
    c19FirstMoment axis = 0 :=
  c19_first_moment_zero axis

/-!
Both independently derived cube structures are in an odd face-sign class:
the prepared tetrahedral overlap has negative product on all six faces, and
the oriented cubical incidence transport has sign `-1` around every face.
This is a geometric readout statement, not an added action term.
-/
theorem prepared_and_incidence_faces_are_odd :
    (faceProduct 0 2 3 1 = (-1/9 : ℂ) ∧
      faceProduct 4 6 7 5 = (-1/9 : ℂ) ∧
      faceProduct 0 4 5 1 = (-1/9 : ℂ) ∧
      faceProduct 2 6 7 3 = (-1/9 : ℂ) ∧
      faceProduct 0 4 6 2 = (-1/9 : ℂ) ∧
      faceProduct 1 5 7 3 = (-1/9 : ℂ)) ∧
    (∀ axis other corner, axis ≠ other →
      cubeIncidenceFaceSign axis other corner = -1) := by
  exact ⟨all_face_products_negative,
    fun axis other corner haxis =>
      cube_incidence_face_sign_negative axis other haxis corner⟩

structure Dirac009NecessaryGeometry : Prop where
  alignedFirstMomentZero : ∀ axis, c19FirstMoment axis = 0
  preparedConnectionSelectsIncidence : ∀ axis corner,
    preparedCubeConnection4 axis corner - preparedCubeGauge4 corner +
        preparedCubeGauge4 (cubeIncidenceFlip axis corner) =
      cubeIncidenceConnection4 axis corner
  gammaSquare : ∀ axis amplitude,
    cubeIncidenceGamma axis (cubeIncidenceGamma axis amplitude) = amplitude
  gammaAnticommutation : ∀ axis other, axis ≠ other → ∀ amplitude,
    cubeIncidenceGamma axis (cubeIncidenceGamma other amplitude) =
      fun corner =>
        -cubeIncidenceGamma other (cubeIncidenceGamma axis amplitude) corner
  betaSquare : ∀ amplitude,
    cubeParityBeta (cubeParityBeta amplitude) = amplitude
  betaAnticommutation : ∀ axis amplitude,
    cubeParityBeta (cubeIncidenceGamma axis amplitude) =
      fun corner =>
        -cubeIncidenceGamma axis (cubeParityBeta amplitude) corner
  linearSquare : ∀ k0 k1 k2 amplitude,
    cubeIncidenceLinear k0 k1 k2
        (cubeIncidenceLinear k0 k1 k2 amplitude) =
      fun corner => (k0 ^ 2 + k1 ^ 2 + k2 ^ 2) * amplitude corner
  flavorInvolution : ∀ amplitude,
    cubeFlavor (cubeFlavor amplitude) = amplitude
  flavorCommutesWithDirac : ∀ mass k0 k1 k2 amplitude,
    cubeFlavor (cubeDiracSymbol mass k0 k1 k2 amplitude) =
      cubeDiracSymbol mass k0 k1 k2 (cubeFlavor amplitude)
  fourCoordinateCopies :
    Function.Injective cubeEmbedMinus ∧ Function.Injective cubeEmbedPlus
  diracSquare : ∀ mass k0 k1 k2 amplitude,
    cubeDiracSymbol mass k0 k1 k2
        (cubeDiracSymbol mass k0 k1 k2 amplitude) =
      cubeScalarSymbol mass k0 k1 k2 amplitude
  phaseSpaceIntertwining : ∀ mass k0 k1 k2 amplitude,
    cubeScalarCanonicalVector mass k0 k1 k2
        (cubePositiveFrequencyEmbedding mass k0 k1 k2 amplitude) =
      cubePositiveFrequencyEmbedding mass k0 k1 k2
        (fun corner =>
          -Complex.I * cubeDiracSymbol mass k0 k1 k2 amplitude corner)
  c19ContinuumSquare : ∀ mass momentum amplitude,
    c19ContinuumDiracSymbol mass momentum
        (c19ContinuumDiracSymbol mass momentum amplitude) =
      c19ContinuumScalarSymbol mass momentum amplitude
  runningMassIsChi0 : ∀ A R omega, A ≠ 0 →
    A ^ 2 + R ^ 2 = chi0 ^ 2 →
    omega ^ 2 * A = (R ^ 2 + A ^ 2) * A →
    0 ≤ omega → omega = chi0
  preparedBondTrackIsFlat : ∀ psiAmplitude chiAmplitude edge,
    exteriorAreaBond chi0
      (constantAlignedEightSiteState psiAmplitude chiAmplitude) edge = 0
  exactFiniteLatticeResidual : ∀ mass momentum amplitude,
    (c19ExactCanonicalVector mass momentum
        (c19PositiveFrequencyEmbedding mass momentum amplitude)).velocity =
      fun corner =>
        (c19PositiveFrequencyEmbedding mass momentum
          (fun site => -Complex.I *
            c19ContinuumDiracSymbol mass momentum amplitude site)).velocity corner -
        (c19SpatialRemainder momentum : ℂ) * amplitude corner
  spatialRemainderBound : ∀ momentum radius, 0 ≤ radius →
    (∀ axis, |momentum axis| ≤ radius) → 2 * radius ≤ 1 →
    |c19SpatialRemainder momentum| ≤ 40 * radius ^ 4
  oddFaceClass : ∀ axis other corner, axis ≠ other →
    cubeIncidenceFaceSign axis other corner = -1

theorem dirac009_necessary_cube_geometry : Dirac009NecessaryGeometry where
  alignedFirstMomentZero := aligned_c19_transport_has_zero_first_moment
  preparedConnectionSelectsIncidence :=
    prepared_cube_connection_gauge_eq_incidence
  gammaSquare := cube_incidence_gamma_square
  gammaAnticommutation := cube_incidence_gamma_anticommute
  betaSquare := cube_parity_beta_square
  betaAnticommutation := cube_parity_beta_anticommutes
  linearSquare := cube_incidence_linear_square
  flavorInvolution := cube_flavor_involution
  flavorCommutesWithDirac := cube_flavor_commutes_dirac_symbol
  fourCoordinateCopies :=
    ⟨cube_embed_minus_injective, cube_embed_plus_injective⟩
  diracSquare := cube_dirac_symbol_square
  phaseSpaceIntertwining := cube_positive_frequency_intertwining
  c19ContinuumSquare :=
    c19_continuum_dirac_square_is_native_quadratic_symbol
  runningMassIsChi0 := prepared_running_rest_frequency_is_chi0
  preparedBondTrackIsFlat :=
    constant_aligned_bond_energy_zero chi0
  exactFiniteLatticeResidual :=
    c19_embedding_velocity_residual_is_spatial_remainder
  spatialRemainderBound := c19_spatial_remainder_bound
  oddFaceClass := fun axis other corner haxis =>
    cube_incidence_face_sign_negative axis other haxis corner

end
end LeanDirac
