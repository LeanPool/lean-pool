/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4CrossDiscFamily
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# Crossing discs avoiding vertices and unrelated edges

For XII (4.5), claim (1), page 253, a crossing disc must miss
all source vertices and all edges except its crossing pair.
These forbidden points and arcs form a finite closed set which
does not contain the crossing. Shrink its local straight-line
neighborhood by deleting that set before choosing the discs.
The discs retain their opposite boundary contacts and contain
their crossings in their interiors.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Crossing discs can be chosen disjoint from all vertices
and all edges outside their crossing pairs, while retaining
the exact coordinate-disc and opposite-contact equations.
This is the protected disc choice in XII (4.5), claim (1),
page 253. -/
theorem exists_protected_cross_disc_family {V E T : Type*}
    [Finite V] [Finite E] [Finite T]
    (v : V → ℂ) (P : E → Set ℂ) (hP : ∀ e, IsClosed (P e))
    (x : T → ℂ) (hinj : Function.Injective x) (left right : T → E)
    (hxV : ∀ i, x i ∉ range v)
    (hother : ∀ i e, e ≠ left i → e ≠ right i → x i ∉ P e)
    (A : T → ℂ ≃L[ℝ] ℂ) (U : T → Set ℂ)
    (hU : ∀ i, IsOpen (U i)) (hxU : ∀ i, x i ∈ U i)
    (hleft : ∀ i, P (left i) ∩ U i = (line[ℝ, x i, x i + A i 1] : Set ℂ) ∩ U i)
    (hright : ∀ i, P (right i) ∩ U i = (line[ℝ, x i, x i + A i Complex.I] : Set ℂ) ∩ U i) :
    ∃ (r : T → ℝ) (D : T → Set ℂ), (∀ i, 0 < r i) ∧
      (∀ i, IsClosedDisc (D i)) ∧ (∀ i, D i ⊆ U i) ∧
      (∀ i j, i ≠ j → Disjoint (D i) (D j)) ∧
      (∀ i, x i ∈ interior (D i)) ∧
      (∀ i, Disjoint (D i) (range v)) ∧
      (∀ i e, e ≠ left i → e ≠ right i → Disjoint (D i) (P e)) ∧
      (∀ i, P (left i) ∩ discBd (D i) =
        {x i + A i (r i • (1 : ℂ)), x i + A i ((-r i) • (1 : ℂ))}) ∧
      (∀ i, P (right i) ∩ discBd (D i) =
        {x i + A i (r i • Complex.I), x i + A i ((-r i) • Complex.I)}) ∧
      (∀ i, D i = (fun z => x i + A i z) '' Metric.closedBall 0 (r i)) := by
  classical
  let B := fun i => range v ∪ ⋃ e, if e = left i ∨ e = right i then ∅ else P e
  have hB : ∀ i, IsClosed (B i) := by
    intro i
    apply (finite_range v).isClosed.union
    apply isClosed_iUnion_of_finite
    intro e
    split_ifs <;> first | exact isClosed_empty | exact hP e
  have hxB : ∀ i, x i ∉ B i := by
    intro i hx
    rcases hx with hxv | hxedges
    · exact hxV i hxv
    · obtain ⟨e, he⟩ := mem_iUnion.mp hxedges
      by_cases h : e = left i ∨ e = right i
      · simp only [h, ↓reduceIte, mem_empty_iff_false] at he
      · have hxe : x i ∈ P e := by simpa only [h, ↓reduceIte] using he
        exact hother i e (fun hl => h (Or.inl hl)) (fun hr => h (Or.inr hr)) hxe
  let W := fun i => U i ∩ (B i)ᶜ
  have hW : ∀ i, IsOpen (W i) := fun i => (hU i).inter (hB i).isOpen_compl
  have hxW : ∀ i, x i ∈ W i := fun i => ⟨hxU i, hxB i⟩
  have hleftW : ∀ i, P (left i) ∩ W i = (line[ℝ, x i, x i + A i 1] : Set ℂ) ∩ W i := by
    intro i
    rw [show W i = U i ∩ (B i)ᶜ from rfl, ← inter_assoc, hleft i, inter_assoc]
  have hrightW : ∀ i, P (right i) ∩ W i = (line[ℝ, x i, x i + A i Complex.I] : Set ℂ) ∩ W i := by
    intro i
    rw [show W i = U i ∩ (B i)ᶜ from rfl, ← inter_assoc, hright i, inter_assoc]
  obtain ⟨r, hr, D, hd, hsub, hdd, hl, hrt, hcoord⟩ := exists_local_cross_disc_family
    x hinj A (fun i => P (left i)) (fun i => P (right i)) W hW hxW hleftW hrightW
  refine ⟨r, D, hr, hd, (fun i z hz => (hsub i hz).1), hdd, ?_, ?_, ?_, hl, hrt, hcoord⟩
  · intro i
    rw [hcoord i]
    exact cross_disc_center_mem_interior (A i) (x i) (hr i)
  · intro i
    exact disjoint_left.mpr (fun z hz hv => (hsub i hz).2 (Or.inl hv))
  · intro i e hel her
    apply disjoint_left.mpr
    intro z hz hze
    apply (hsub i hz).2
    refine Or.inr (mem_iUnion.mpr ⟨e, ?_⟩)
    simpa only [show ¬ (e = left i ∨ e = right i) from fun h => h.elim hel her,
      ↓reduceIte] using hze

end GraphMinor.GM12
