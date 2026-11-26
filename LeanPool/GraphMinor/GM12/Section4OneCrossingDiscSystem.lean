/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4ProtectedCrossDiscFamily
public import LeanPool.GraphMinor.GM12.Section4CrossingPoints
public import LeanPool.GraphMinor.GM12.Section4CrossingPairEquiv

/-!
# Discs and edge labels for a one-crossing drawing

For XII (4.5), claim (1), page 253, select the local pair of
edges and straight-line coordinates at each actual crossing.
The absence of a third edge identifies its pair uniquely.
The one-crossing equations then give a bijection from the
two positions at each crossing to the edge set. Choose the
protected discs and express all avoidance and opposite-contact
equations using that bijection.
-/

public section

namespace GraphMinor.GM12

open Set Surface Metric

/-- A finite one-crossing arc configuration supplies its actual
edge-pair bijection and protected coordinate discs, including
the opposite boundary contacts. This is the labelled small-disc
system in XII (4.5), claim (1), page 253. -/
theorem exists_one_crossing_disc_system {V E : Type*} [Finite V] [Finite E]
    (v : V → ℂ) (P : E → Set ℂ) (hP : ∀ e, IsClosed (P e))
    (hM : (edgeMeetingPoints v P).Finite)
    (htriple : ∀ e f g, e ≠ f → f ≠ g → e ≠ g → P e ∩ P f ∩ P g ⊆ range v)
    (hcross : ∀ e, ∃ x ∈ edgeMeetingPoints v P, P e ∩ edgeMeetingPoints v P = {x})
    (hlocal : ∀ x ∈ edgeMeetingPoints v P, ∃ e f, e ≠ f ∧ x ∈ P e ∩ P f ∧
      ∃ (A : ℂ ≃L[ℝ] ℂ) (U : Set ℂ), IsOpen U ∧ x ∈ U ∧
        P e ∩ U = (line[ℝ, x, x + A 1] : Set ℂ) ∩ U ∧
        P f ∩ U = (line[ℝ, x, x + A Complex.I] : Set ℂ) ∩ U) :
    ∃ (σ : (edgeMeetingPoints v P × Bool) ≃ E)
      (A : edgeMeetingPoints v P → ℂ ≃L[ℝ] ℂ)
      (r : edgeMeetingPoints v P → ℝ) (D : edgeMeetingPoints v P → Set ℂ),
      (∀ x, x.val ∈ P (σ (x, false)) ∩ P (σ (x, true))) ∧
      (∀ x, 0 < r x) ∧ (∀ x, IsClosedDisc (D x)) ∧
      (∀ x y, x ≠ y → Disjoint (D x) (D y)) ∧
      (∀ x, x.val ∈ interior (D x)) ∧ (∀ x, Disjoint (D x) (range v)) ∧
      (∀ x e, e ≠ σ (x, false) → e ≠ σ (x, true) → Disjoint (D x) (P e)) ∧
      (∀ x, P (σ (x, false)) ∩ discBd (D x) =
        {x.val + A x (r x • (1 : ℂ)), x.val + A x ((-r x) • (1 : ℂ))}) ∧
      (∀ x, P (σ (x, true)) ∩ discBd (D x) =
        {x.val + A x (r x • Complex.I), x.val + A x ((-r x) • Complex.I)}) ∧
      (∀ x, D x = (fun z => x.val + A x z) '' closedBall 0 (r x)) := by
  classical
  let X := edgeMeetingPoints v P
  let : Fintype X := hM.fintype
  have hloc : ∀ x : X, ∃ e f, e ≠ f ∧ x.val ∈ P e ∩ P f ∧
      ∃ (A : ℂ ≃L[ℝ] ℂ) (U : Set ℂ), IsOpen U ∧ x.val ∈ U ∧
        P e ∩ U = (line[ℝ, x.val, x.val + A 1] : Set ℂ) ∩ U ∧
        P f ∩ U = (line[ℝ, x.val, x.val + A Complex.I] : Set ℂ) ∩ U :=
    fun x => hlocal x.val x.property
  choose left right hne hx A U hU hxU hl hr using hloc
  have hxV : ∀ x : X, x.val ∉ range v := by
    intro x
    obtain ⟨_, _, _, _, hnot⟩ := x.property
    exact hnot
  have honly : ∀ x : X, ∀ e, x.val ∈ P e → e = left x ∨ e = right x := by
    intro x e hxe
    exact edge_eq_of_mem_pair_meeting v P htriple (hne x) ⟨hx x, hxV x⟩ hxe
  have hother : ∀ x : X, ∀ e, e ≠ left x → e ≠ right x → x.val ∉ P e :=
    fun x e hel her hxe => (honly x e hxe).elim hel her
  have hxrange : range (Subtype.val : X → ℂ) = X := by
    ext z
    exact ⟨fun ⟨x, hx⟩ => hx ▸ x.property, fun hz => ⟨⟨z, hz⟩, rfl⟩⟩
  have hsingle : ∀ e, ∃ x : X, P e ∩ range (Subtype.val : X → ℂ) = {x.val} := by
    intro e
    obtain ⟨x, hx, hmeet⟩ := hcross e
    exact ⟨⟨x, hx⟩, by rw [hxrange]; exact hmeet⟩
  obtain ⟨σ, hσ⟩ := exists_crossing_pair_equiv Subtype.val Subtype.val_injective P left right
    hne hx honly hsingle
  obtain ⟨r, D, hpos, hd, -, hdd, hcentre, hDv, hDP, hDL, hDR, hcoord⟩ :=
    exists_protected_cross_disc_family v P hP Subtype.val Subtype.val_injective left right
      hxV hother A U hU hxU hl hr
  refine ⟨σ, A, r, D, ?_, hpos, hd, hdd, hcentre, hDv, ?_, ?_, ?_, hcoord⟩
  · intro x
    rw [(hσ x).1, (hσ x).2]
    exact hx x
  · intro x e hel her
    apply hDP x e
    · exact fun h => hel (h.trans (hσ x).1.symm)
    · exact fun h => her (h.trans (hσ x).2.symm)
  · intro x
    rw [(hσ x).1]
    exact hDL x
  · intro x
    rw [(hσ x).2]
    exact hDR x

end GraphMinor.GM12
