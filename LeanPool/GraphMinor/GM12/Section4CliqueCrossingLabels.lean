/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4CliquePortCoordinates

/-!
# Crossing witnesses with the original edge labels

For XII (4.5), page 252, a crossing witness found using vertex
pairs must be another edge of the same finite clique. Invert the
port bijection to recover its edge label. Its new endpoint lies
outside the original pair, so the recovered edge label differs
from the original one.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Each labelled clique chord has a differently labelled crossing
chord. This transfers condition (vi) of XII (4.5), page 252, from
vertex pairs to the actual finite edge labels. -/
theorem every_labelled_clique_chord_has_crossing {p : ℕ} (hp : 4 ≤ p)
    (ψ : (Fin (p * (p - 1) / 2) × Bool) ≃ {q : Fin p × Fin p // q.1 ≠ q.2})
    (hψ : ∀ i b, (ψ (i, !b)).val = ((ψ (i, b)).val.2, (ψ (i, b)).val.1))
    (s : Fin (p * (p - 1) / 2) × Bool → ℝ) (F : Fin p → Fin p → ℝ)
    (hF : ∀ v w, F v w ∈ Ioo 0 1)
    (hblocks : ∀ v w i j, v < i → F v w < F i j)
    (hpriority : ∀ v w z, hamiltonPortPriority v w < hamiltonPortPriority v z → F v w < F v z)
    (hcoord : ∀ v w (hvw : v ≠ w), F v w = s (ψ.symm ⟨(v, w), hvw⟩))
    (i : Fin (p * (p - 1) / 2)) :
    ∃ j : Fin (p * (p - 1) / 2), j ≠ i ∧
      (segment ℝ (ee (s (i, false)) : ℂ) (ee (s (i, true)) : ℂ) ∩
        segment ℝ (ee (s (j, false)) : ℂ) (ee (s (j, true)) : ℂ)).Nonempty := by
  let v := (ψ (i, false)).val.1
  let w := (ψ (i, false)).val.2
  obtain ⟨x, y, hxy, hyv, hyw, _, hcross⟩ :=
    every_clique_chord_has_crossing hp F hF hblocks hpriority (ψ (i, false)).property
  let q := ψ.symm ⟨(x, y), hxy⟩
  let j := q.1
  let b := q.2
  have hpair : (ψ (j, b)).val = (x, y) :=
    congrArg Subtype.val (ψ.apply_symm_apply ⟨(x, y), hxy⟩)
  have hji : j ≠ i := by
    intro hji
    rw [hji] at hpair
    cases hb : b
    · rw [hb] at hpair
      exact hyw (congrArg Prod.snd hpair).symm
    · rw [hb] at hpair
      have hflip := congrArg Prod.snd (hψ i false)
      change (ψ (i, true)).val.2 = v at hflip
      exact hyv ((congrArg Prod.snd hpair).symm.trans hflip)
  have hfirst := clique_port_chord_eq_matrix ψ hψ s F hcoord i false
  have hsecond := clique_port_chord_eq_matrix ψ hψ s F hcoord j b
  rw [show (ψ (j, b)).val.1 = x from congrArg Prod.fst hpair,
    show (ψ (j, b)).val.2 = y from congrArg Prod.snd hpair] at hsecond
  exact ⟨j, hji, by rw [hfirst, hsecond]; exact hcross⟩

end GraphMinor.GM12
