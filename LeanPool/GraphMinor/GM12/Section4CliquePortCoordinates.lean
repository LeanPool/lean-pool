/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4CliquePortMatrix
public import LeanPool.GraphMinor.Surface.CircleMove
public import Mathlib.Analysis.Convex.Segment

/-!
# Matching vertex-pair chords to edge labels

For XII (4.5), page 252, the vertex-pair description used to find
crossings must agree with the finitely indexed edge arcs. The
port bijection and its reversal identity identify both coordinates
of each chord. The unoriented chord is independent of which port
is chosen first.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Both vertex-pair coordinates agree with the two edge-port
coordinates in XII (4.5), page 252. -/
theorem clique_port_matrix_coordinates {p : ℕ}
    (ψ : (Fin (p * (p - 1) / 2) × Bool) ≃ {q : Fin p × Fin p // q.1 ≠ q.2})
    (hψ : ∀ i b, (ψ (i, !b)).val = ((ψ (i, b)).val.2, (ψ (i, b)).val.1))
    (s : Fin (p * (p - 1) / 2) × Bool → ℝ) (F : Fin p → Fin p → ℝ)
    (hF : ∀ v w (hvw : v ≠ w), F v w = s (ψ.symm ⟨(v, w), hvw⟩))
    (i : Fin (p * (p - 1) / 2)) (b : Bool) :
    F (ψ (i, b)).val.1 (ψ (i, b)).val.2 = s (i, b) ∧
      F (ψ (i, b)).val.2 (ψ (i, b)).val.1 = s (i, !b) := by
  have hfirst := hF (ψ (i, b)).val.1 (ψ (i, b)).val.2 (ψ (i, b)).property
  have hsecond := hF (ψ (i, b)).val.2 (ψ (i, b)).val.1 (ψ (i, b)).property.symm
  have hflip : ψ (i, !b) =
      ⟨((ψ (i, b)).val.2, (ψ (i, b)).val.1), (ψ (i, b)).property.symm⟩ :=
    Subtype.ext (hψ i b)
  rw [← hflip, ψ.symm_apply_apply] at hsecond
  refine ⟨?_, hsecond⟩
  simpa only [Subtype.eta, ψ.symm_apply_apply] using hfirst

/-- The chord obtained from vertex-pair coordinates is the actual
edge chord, for either choice of its first port. This keeps the
crossing witnesses aligned with edge labels in XII (4.5), page 252. -/
theorem clique_port_chord_eq_matrix {p : ℕ}
    (ψ : (Fin (p * (p - 1) / 2) × Bool) ≃ {q : Fin p × Fin p // q.1 ≠ q.2})
    (hψ : ∀ i b, (ψ (i, !b)).val = ((ψ (i, b)).val.2, (ψ (i, b)).val.1))
    (s : Fin (p * (p - 1) / 2) × Bool → ℝ) (F : Fin p → Fin p → ℝ)
    (hF : ∀ v w (hvw : v ≠ w), F v w = s (ψ.symm ⟨(v, w), hvw⟩))
    (i : Fin (p * (p - 1) / 2)) (b : Bool) :
    segment ℝ (ee (s (i, false)) : ℂ) (ee (s (i, true)) : ℂ) =
      segment ℝ (ee (F (ψ (i, b)).val.1 (ψ (i, b)).val.2) : ℂ)
        (ee (F (ψ (i, b)).val.2 (ψ (i, b)).val.1) : ℂ) := by
  rw [(clique_port_matrix_coordinates ψ hψ s F hF i b).1,
    (clique_port_matrix_coordinates ψ hψ s F hF i b).2]
  cases b
  · rfl
  · exact segment_symm _ _ _

/-- The endpoints of an edge are the owner and neighbor of either
of its ports. This removes the arbitrary first-port choice in the
source construction for XII (4.5), page 252. -/
theorem clique_port_endpoint_set {p : ℕ}
    (ψ : (Fin (p * (p - 1) / 2) × Bool) ≃ {q : Fin p × Fin p // q.1 ≠ q.2})
    (hψ : ∀ i b, (ψ (i, !b)).val = ((ψ (i, b)).val.2, (ψ (i, b)).val.1))
    (i : Fin (p * (p - 1) / 2)) (b : Bool) :
    ({(ψ (i, false)).val.1, (ψ (i, true)).val.1} : Set (Fin p)) =
      {(ψ (i, b)).val.1, (ψ (i, b)).val.2} := by
  cases b
  · have h := congrArg Prod.fst (hψ i false)
    change (ψ (i, true)).val.1 = (ψ (i, false)).val.2 at h
    rw [h]
  · have h := congrArg Prod.fst (hψ i true)
    change (ψ (i, false)).val.1 = (ψ (i, true)).val.2 at h
    rw [h]
    exact pair_comm _ _

end GraphMinor.GM12
