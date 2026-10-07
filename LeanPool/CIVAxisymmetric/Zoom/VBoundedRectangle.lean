/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.RescaledBounds

/-!
# Uniform finite-axis rescaled field bounds on compact time intervals

The `hbdd` hypothesis shape (uniform boundedness on rectangles of bounded time)
for the finite-axis rescaled radial and vertical fields `V_n`, `W_n` (and the swirl source
`S_n`) of `eq:aniso:zoom:fields`, the companion boundedness input that an eventual
Arzelà–Ascoli extraction of `(V_n, W_n)` in `C¹_loc` (`eq:aniso:zoom:finite:compactness`)
needs alongside the equicontinuity modulus.
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV



/-- For every compact set `J ⊆ (-∞, -1]` and every `C ≥ 0`, the rescaled radial field
`zoomV` is uniformly bounded on `{zoomPoint … ∈ unitCylinder} × J` by a constant `M`
depending only on `C`, `J`, and the exponent `-(1/2)`. -/
theorem exists_forall_abs_zoomV_le_of_isCompact {C h : ℝ} (hC : 0 ≤ C)
    (u : ParabolicPoint → Vec3) (hb : AnisotropicBounds C h u) (zc : ℝ)
    {J : Set ℝ} (hJ : IsCompact J) (hJsub : ∀ τ ∈ J, τ ≤ -1) :
    ∃ M : ℝ, ∀ lam : ℝ, 0 < lam → ∀ p : (ℝ × ℝ) × ℝ,
      zoomPoint lam h zc p ∈ unitCylinder → p.2 ∈ J → |zoomV lam h zc u p| ≤ M := by
  rcases J.eq_empty_or_nonempty with (hne | hne)
  · refine ⟨0, fun lam hlam p hp hmem => ?_⟩
    exfalso
    rw [hne] at hmem
    exact hmem
  · have hpos : ∀ τ ∈ J, (-τ) ≠ 0 := by
      intro τ hτ; linarith only [hJsub τ hτ]
    have h_cont : ContinuousOn (fun τ : ℝ => (-τ) ^ (-(1 / 2 : ℝ))) J :=
      ContinuousOn.rpow_const (continuous_neg.continuousOn) (fun τ hτ => Or.inl (hpos τ hτ))
    obtain ⟨τstar, hτstar, hmax⟩ := hJ.exists_isMaxOn hne h_cont
    refine ⟨C * (-τstar) ^ (-(1 / 2 : ℝ)), fun lam hlam p hp hmem => ?_⟩
    have hbound := abs_zoomV_le C h lam zc hlam u hb p hp
    have hexp : -(1 / 2 : ℝ) - (0 : ℝ) / 2 - ((1 : ℝ) / 2 - h) * (0 : ℝ) = -(1 / 2 : ℝ) := by ring
    rw [hexp] at hbound
    have hpow : (-p.2) ^ (-(1 / 2 : ℝ)) ≤ (-τstar) ^ (-(1 / 2 : ℝ)) :=
      isMaxOn_iff.mp hmax p.2 hmem
    calc
      |zoomV lam h zc u p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) := hbound
      _ ≤ C * (-τstar) ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hpow hC

/-- For every compact set `J ⊆ (-∞, -1]` and every `C ≥ 0`, the sum `|zoomW| + |zoomS|`
is uniformly bounded on `{zoomPoint … ∈ unitCylinder} × J` by a constant `M`
depending only on `C`, `J`, `h`, and the exponent `-(1/2) - h`. -/
theorem exists_forall_abs_zoomW_add_abs_zoomS_le_of_isCompact {C h : ℝ} (hC : 0 ≤ C)
    (u : ParabolicPoint → Vec3) (hb : AnisotropicBounds C h u) (zc : ℝ)
    {J : Set ℝ} (hJ : IsCompact J) (hJsub : ∀ τ ∈ J, τ ≤ -1) :
    ∃ M : ℝ, ∀ lam : ℝ, 0 < lam → ∀ p : (ℝ × ℝ) × ℝ,
      zoomPoint lam h zc p ∈ unitCylinder → p.2 ∈ J →
        |zoomW lam h zc u p| + |zoomS lam h zc u p| ≤ M := by
  rcases J.eq_empty_or_nonempty with (hne | hne)
  · refine ⟨0, fun lam hlam p hp hmem => ?_⟩
    exfalso
    rw [hne] at hmem
    exact hmem
  · have hpos : ∀ τ ∈ J, (-τ) ≠ 0 := by
      intro τ hτ; linarith only [hJsub τ hτ]
    have h_cont : ContinuousOn (fun τ : ℝ => (-τ) ^ (-(1 / 2 : ℝ) - h)) J :=
      ContinuousOn.rpow_const (continuous_neg.continuousOn) (fun τ hτ => Or.inl (hpos τ hτ))
    obtain ⟨τstar, hτstar, hmax⟩ := hJ.exists_isMaxOn hne h_cont
    refine ⟨C * (-τstar) ^ (-(1 / 2 : ℝ) - h), fun lam hlam p hp hmem => ?_⟩
    have hbound := abs_zoomW_add_abs_zoomS_le C h lam zc hlam u hb p hp
    have hexp : -(1 / 2 : ℝ) - h - (0 : ℝ) / 2 - ((1 : ℝ) / 2 - h) * (0 : ℝ) = -(1 / 2 : ℝ) - h
      := by ring
    rw [hexp] at hbound
    have hpow : (-p.2) ^ (-(1 / 2 : ℝ) - h) ≤ (-τstar) ^ (-(1 / 2 : ℝ) - h) :=
      isMaxOn_iff.mp hmax p.2 hmem
    calc
      |zoomW lam h zc u p| + |zoomS lam h zc u p| ≤
          C * (-p.2) ^ (-(1 / 2 : ℝ) - h) := hbound
      _ ≤ C * (-τstar) ^ (-(1 / 2 : ℝ) - h) := mul_le_mul_of_nonneg_left hpow hC

/-- Combined uniform bound for `|zoomV| + |zoomW| + |zoomS|` on
`{zoomPoint … ∈ unitCylinder} × J`. Follows from the two separate bounds above
via additivity. -/
theorem exists_forall_abs_zoomV_add_abs_zoomW_add_abs_zoomS_le_of_isCompact {C h : ℝ} (hC : 0 ≤ C)
    (u : ParabolicPoint → Vec3) (hb : AnisotropicBounds C h u) (zc : ℝ)
    {J : Set ℝ} (hJ : IsCompact J) (hJsub : ∀ τ ∈ J, τ ≤ -1) :
    ∃ M : ℝ, ∀ lam : ℝ, 0 < lam → ∀ p : (ℝ × ℝ) × ℝ,
      zoomPoint lam h zc p ∈ unitCylinder → p.2 ∈ J →
        |zoomV lam h zc u p| + |zoomW lam h zc u p| + |zoomS lam h zc u p| ≤ M := by
  obtain ⟨M1, hM1⟩ := exists_forall_abs_zoomV_le_of_isCompact hC u hb zc hJ hJsub
  obtain ⟨M2, hM2⟩ := exists_forall_abs_zoomW_add_abs_zoomS_le_of_isCompact hC u hb zc hJ hJsub
  refine ⟨M1 + M2, fun lam hlam p hp hmem => ?_⟩
  have hV := hM1 lam hlam p hp hmem
  have hWS := hM2 lam hlam p hp hmem
  linarith only [hV, hWS]

end CIV
