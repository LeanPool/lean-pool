/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation at commit e2161e0936f181d4a5a9d49963a666f7cea42502.
Upstream source is dual-licensed under MIT or CC0 1.0; used here under MIT.
-/

module

public import LeanPool.LatticeDiracDerivation.V32GlobalSpectrum

/-!
# V3.2 Stage 4: exact C19 zero audit

The massive branch is gapped, so momentum-space doublers can only arise from
additional zeros of the C19 transport symbol.  This file proves directly from
the positive C19 bond sum that the only zero in the fundamental Brillouin box
is the origin.
-/

@[expose] public section



namespace LeanDirac.V2

noncomputable section
open BigOperators Complex

theorem c19_zero_forces_every_bond_character
    (momentum : LatticeMomentum)
    (hzero : c19TransportSymbol momentum = 0) :
    ∀ direction, c19Character momentum direction = 1 := by
  intro direction
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun d (_ : d ∈ Finset.univ) =>
      mul_nonneg (le_of_lt (c19_weight_positive d))
        (Complex.normSq_nonneg _))).mp hzero
  have hterm := hall direction (Finset.mem_univ direction)
  have hnorm : Complex.normSq (1 - c19Character momentum direction) = 0 := by
    rcases mul_eq_zero.mp hterm with hw | hn
    · exact False.elim ((ne_of_gt (c19_weight_positive direction)) hw)
    · exact hn
  have hsub : 1 - c19Character momentum direction = 0 :=
    Complex.normSq_eq_zero.mp hnorm
  exact (sub_eq_zero.mp hsub).symm

theorem c19_zero_forces_axis_cosines
    (momentum : LatticeMomentum)
    (hzero : c19TransportSymbol momentum = 0) :
    Real.cos (momentum 0) = 1 ∧
      Real.cos (momentum 1) = 1 ∧
      Real.cos (momentum 2) = 1 := by
  have hbond (direction : C19Neighbor) :
      Complex.normSq (1 - c19Character momentum direction) = 0 := by
    rw [c19_zero_forces_every_bond_character momentum hzero direction]
    simp
  have hx := hbond ⟨0, by omega⟩
  have hy := hbond ⟨2, by omega⟩
  have hz := hbond ⟨4, by omega⟩
  rw [c19Character, normSq_one_sub_exp_I] at hx hy hz
  simp [c19PhaseAngle, c19Coord, Fin.sum_univ_succ] at hx hy hz
  constructor
  · nlinarith
  · constructor <;> nlinarith

/-- The V3.2 I nF un da me nt al Br il lo ui nB ox definition used by this stage. -/
def InFundamentalBrillouinBox (momentum : LatticeMomentum) : Prop :=
  ∀ axis, -(Real.pi) ≤ momentum axis ∧ momentum axis < Real.pi

theorem c19_no_momentum_doublers
    (momentum : LatticeMomentum)
    (hbox : InFundamentalBrillouinBox momentum)
    (hzero : c19TransportSymbol momentum = 0) :
    momentum = fun _ => 0 := by
  have hcos := c19_zero_forces_axis_cosines momentum hzero
  funext axis
  fin_cases axis
  · exact (Real.cos_eq_one_iff_of_lt_of_lt
      (by have h := (hbox 0).1; simp at h ⊢; nlinarith [Real.pi_pos])
      (by have h := (hbox 0).2; simp at h ⊢; nlinarith [Real.pi_pos])).mp hcos.1
  · exact (Real.cos_eq_one_iff_of_lt_of_lt
      (by have h := (hbox 1).1; simp at h ⊢; nlinarith [Real.pi_pos])
      (by have h := (hbox 1).2; simp at h ⊢; nlinarith [Real.pi_pos])).mp hcos.2.1
  · exact (Real.cos_eq_one_iff_of_lt_of_lt
      (by have h := (hbox 2).1; simp at h ⊢; nlinarith [Real.pi_pos])
      (by have h := (hbox 2).2; simp at h ⊢; nlinarith [Real.pi_pos])).mp hcos.2.2

/-- The bundled V3.2 B ri ll ou in Zo ne Ce rt if ic at e. -/
structure V32BrillouinZoneCertificate : Prop where
  symbolNonnegative : ∀ momentum, 0 ≤ c19TransportSymbol momentum
  originIsZero : c19TransportSymbol (fun _ => 0) = 0
  originIsOnlyZero : ∀ momentum,
    InFundamentalBrillouinBox momentum →
      c19TransportSymbol momentum = 0 → momentum = fun _ => 0

theorem v32_brillouin_zone_audit : V32BrillouinZoneCertificate where
  symbolNonnegative := c19_transport_symbol_nonnegative
  originIsZero := c19_transport_symbol_zero
  originIsOnlyZero := c19_no_momentum_doublers


end
end LeanDirac.V2
