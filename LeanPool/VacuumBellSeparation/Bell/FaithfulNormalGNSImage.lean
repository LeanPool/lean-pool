/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.NormalGNSBoundedWOT
public import LeanPool.VacuumBellSeparation.Bell.GNSFaithfulRange
public import LeanPool.VacuumBellSeparation.Bell.WOTClosedBallVNA

/-!
The faithful normal GNS representation has its LITERAL image as a VNA.
The unit ball is exactly the continuous image of the original compact WOT
unit ball. Faithfulness gives the isometry needed for equality of these
balls; the separately proved closed-ball criterion then supplies the VNA.
No normality, closedness or support equality is assumed for the image.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open scoped Topology ComplexOrder InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance faithfulImage_vna_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := isClosed_vonNeumannAlgebra M

/-- The image of the ORIGINAL WOT unit ball is exactly the LITERAL GNS-range
unit ball. The reverse inclusion uses the genuine faithful C-star isometry. -/
theorem gns_unitBall_image_eq_of_faithful
    (M : VonNeumannAlgebra H) (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hf : ∀ a : M.toStarSubalgebra, φ (star a * a) = 0 → a = 0) :
    Set.range (fun T : vnaWOTBall M 1 =>
      ContinuousLinearMapWOT.ofCLM (φ.gnsStarAlgHom (vnaWOTBallElement T))) =
      {T : φ.GNS →WOT[ℂ] φ.GNS |
        T.toCLM ∈ φ.gnsStarAlgHom.range ∧ ‖T.toCLM‖ ≤ 1} := by
  have hnormMap (a : M.toStarSubalgebra) : ‖φ.gnsStarAlgHom a‖ = ‖a‖ :=
    gnsStarAlgHom_norm_of_faithful φ hf a
  refine Set.ext fun T => ⟨?_, ?_⟩
  · rintro ⟨X, rfl⟩
    exact ⟨⟨vnaWOTBallElement X, rfl⟩, (hnormMap (vnaWOTBallElement X)).trans_le X.2.2⟩
  · rintro ⟨⟨a, ha⟩, hnorm⟩
    have hImage : ‖φ.gnsStarAlgHom a‖ ≤ 1 := (congrArg norm ha).trans_le hnorm
    have hOriginal : ‖a‖ ≤ 1 := (hnormMap a).symm.trans_le hImage
    let X : vnaWOTBall M 1 := ⟨ContinuousLinearMapWOT.ofCLM (a : H →L[ℂ] H), a.2, hOriginal⟩
    exact ⟨X, (congrArg ContinuousLinearMapWOT.ofCLM ha).trans
      (ContinuousLinearMapWOT.ofCLM_toCLM T)⟩

/-- Compactness is in actual GNS WOT, not operator norm or a replacement topology. -/
theorem isCompact_gns_unitBall_wot_of_faithful_normal
    (M : VonNeumannAlgebra H) (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hn : IsNormalFunctional M φ)
    (hf : ∀ a : M.toStarSubalgebra, φ (star a * a) = 0 → a = 0) :
    IsCompact {T : φ.GNS →WOT[ℂ] φ.GNS |
      T.toCLM ∈ φ.gnsStarAlgHom.range ∧ ‖T.toCLM‖ ≤ 1} := by
  let : CompactSpace (vnaWOTBall M 1) :=
    isCompact_iff_compactSpace.mp (isCompact_vna_unitBall_wot M)
  rw [← gns_unitBall_image_eq_of_faithful M φ hf]
  exact isCompact_range (continuous_gns_on_vnaWOTBall M 1 φ hn)

/-- An actual VNA with exactly the faithful normal GNS image carrier. This
is not merely the generated double commutant or the norm closure of the image. -/
theorem exists_vna_eq_gns_range_of_faithful_normal
    (M : VonNeumannAlgebra H) (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hn : IsNormalFunctional M φ)
    (hf : ∀ a : M.toStarSubalgebra, φ (star a * a) = 0 → a = 0) :
    ∃ N : VonNeumannAlgebra φ.GNS, N.toStarSubalgebra = φ.gnsStarAlgHom.range := by
  apply exists_vna_eq_starSubalgebra_of_wot_closed_unitBall φ.gnsStarAlgHom.range
    (gns_range_norm_closed_of_faithful φ hf)
  exact (isCompact_gns_unitBall_wot_of_faithful_normal M φ hn hf).isClosed

end VacuumBellSeparation.Bipartite
