/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM11.RadialBasics
import LeanPool.GraphMinor.Surface.Disc
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# Locating refined sides in the two cut pieces

After subdividing at the cutting endpoint images in VII (2.6),
page 218, neither cutting endpoint lies in the open part of a
paired side. Each open side therefore misses the cutting line.
Connectedness puts it in one cut piece. Closedness puts its
endpoints in that same piece.
-/

public section
namespace GraphMinor.GM07
open Set Surface

/-- An interval map whose open part misses the overlap of two closed
covering pieces lies wholly in one piece. This locates the refined
paired sides after the cut in VII (2.6), page 218. -/
theorem curve_range_subset_one_piece
    {X : Type*} [TopologicalSpace X] (a : Curve X) {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hAB : A ∪ B = univ)
    (hAvoid : ∀ t ∈ Ioo (0 : unitInterval) 1, a t ∉ A ∩ B) :
    range a ⊆ A ∨ range a ⊆ B := by
  have hConn : IsPreconnected (a '' Ioo (0 : unitInterval) 1) :=
    isPreconnected_Ioo.image a a.continuous.continuousOn
  have hCover : a '' Ioo (0 : unitInterval) 1 ⊆ A ∪ B :=
    fun x _ => hAB.symm ▸ mem_univ x
  have hDisj : ∀ x ∈ a '' Ioo (0 : unitInterval) 1, x ∈ A → x ∉ B := by
    rintro x ⟨t, ht, rfl⟩ hxA hxB
    exact hAvoid t ht ⟨hxA, hxB⟩
  have hClosure : closure (Ioo (0 : unitInterval) 1) = univ := by
    rw [closure_Ioo zero_ne_one]
    apply eq_univ_of_forall
    exact fun t => ⟨unitInterval.nonneg t, unitInterval.le_one t⟩
  have hRange : range a ⊆ closure (a '' Ioo (0 : unitInterval) 1) := by
    rintro x ⟨t, rfl⟩
    exact image_closure_subset_closure_image a.continuous
      ⟨t, hClosure.symm ▸ mem_univ t, rfl⟩
  rcases GM11.subset_or_subset_of_closed hConn hA hB hCover hDisj with h | h
  · exact Or.inl (hRange.trans (hA.closure_subset_iff.mpr h))
  · exact Or.inr (hRange.trans (hB.closure_subset_iff.mpr h))

/-- Once the cutting endpoints miss all open paired sides, every paired side
lies on one side of the cut. Their open parts miss the two cutting endpoints,
so they miss the cutting line. This is the side-location step for the
refined net in VII (2.6), page 218. -/
theorem Net.sides_subset_one_cut_piece
    {S : Type*} [TopologicalSpace S] (N : Net S)
    {A B F : Set N.D} {s t : N.D} (hA : IsClosedDisc A) (hB : IsClosedDisc B)
    (hAB : A ∪ B = univ) (hI : A ∩ B = F)
    (hFbd : F ∩ bd N.D = {s, t}) (hs : ∀ j r, r ∈ Ioo (0 : unitInterval) 1 → N.f j r ≠ s
      ∧ N.g j r ≠ s)
    (ht : ∀ j r, r ∈ Ioo (0 : unitInterval) 1 → N.f j r ≠ t ∧ N.g j r ≠ t) :
    (∀ j, range (N.f j) ⊆ A ∨ range (N.f j) ⊆ B) ∧
      (∀ j, range (N.g j) ⊆ A ∨ range (N.g j) ⊆ B) := by
  let : T2Space N.D := N.isSurface_D.2.1
  constructor
  · intro j
    apply curve_range_subset_one_piece (N.f j) hA.isCompact.isClosed hB.isCompact.isClosed hAB
    intro r hr hx
    have hxF : N.f j r ∈ F := hI ▸ hx
    have hxe := hFbd.subset ⟨hxF, N.range_f_subset_bd j (mem_range_self r)⟩
    rcases hxe with hxs | hxt
    · exact (hs j r hr).1 hxs
    · exact (ht j r hr).1 (mem_singleton_iff.mp hxt)
  · intro j
    apply curve_range_subset_one_piece (N.g j) hA.isCompact.isClosed hB.isCompact.isClosed hAB
    intro r hr hx
    have hxF : N.g j r ∈ F := hI ▸ hx
    have hxe := hFbd.subset ⟨hxF, N.range_g_subset_bd j (mem_range_self r)⟩
    rcases hxe with hxs | hxt
    · exact (hs j r hr).2 hxs
    · exact (ht j r hr).2 (mem_singleton_iff.mp hxt)

/-- Parameterize the cutting line. Its open part misses every old
side, and every old open side misses the whole cutting line once
the cutting endpoints miss all open paired sides. These are the intersections
needed for the inserted pair in VII (2.6), page 218. -/
theorem Net.exists_separating_cut_curve
    {S : Type*} [TopologicalSpace S] (N : Net S)
    {F : Set N.D} {s t : N.D} (hF : IsLineWithEnds F s t)
    (hFbd : F ∩ bd N.D = {s, t}) (hs : ∀ j r, r ∈ Ioo (0 : unitInterval) 1 → N.f j r ≠ s
      ∧ N.g j r ≠ s)
    (ht : ∀ j r, r ∈ Ioo (0 : unitInterval) 1 → N.f j r ≠ t ∧ N.g j r ≠ t) :
    ∃ k : Curve N.D, Function.Injective k ∧ range k = F ∧ k 0 = s ∧ k 1 = t ∧
      (∀ r ∈ Ioo (0 : unitInterval) 1, k r ∉ bd N.D) ∧
      (∀ j, (∀ r ∈ Ioo (0 : unitInterval) 1, k r ∉ range (N.f j)) ∧
        (∀ r ∈ Ioo (0 : unitInterval) 1, N.f j r ∉ range k)) ∧
      (∀ j, (∀ r ∈ Ioo (0 : unitInterval) 1, k r ∉ range (N.g j)) ∧
        (∀ r ∈ Ioo (0 : unitInterval) 1, N.g j r ∉ range k)) := by
  obtain ⟨a, ha, haF, ha0, ha1⟩ := hF.exists_arc
  let k : Curve N.D := ⟨a, ha.1⟩
  have hInterior : ∀ r ∈ Ioo (0 : unitInterval) 1, k r ∉ bd N.D := by
    intro r hr hbd
    have he := hFbd.subset ⟨haF ▸ mem_range_self r, hbd⟩
    rcases he with hrs | hrt
    · exact hr.1.ne' (ha.2 (hrs.trans ha0.symm))
    · exact hr.2.ne (ha.2 ((mem_singleton_iff.mp hrt).trans ha1.symm))
  refine ⟨k, ha.2, haF, ha0, ha1, hInterior, ?_, ?_⟩
  · intro j
    constructor
    · intro r hr hrf
      exact hInterior r hr (N.range_f_subset_bd j hrf)
    · intro r hr hrk
      have hrF : N.f j r ∈ F := haF ▸ hrk
      rcases hFbd.subset ⟨hrF, N.range_f_subset_bd j (mem_range_self r)⟩ with hrs | hrt
      · exact (hs j r hr).1 hrs
      · exact (ht j r hr).1 (mem_singleton_iff.mp hrt)
  · intro j
    constructor
    · intro r hr hrg
      exact hInterior r hr (N.range_g_subset_bd j hrg)
    · intro r hr hrk
      have hrF : N.g j r ∈ F := haF ▸ hrk
      rcases hFbd.subset ⟨hrF, N.range_g_subset_bd j (mem_range_self r)⟩ with hrs | hrt
      · exact (hs j r hr).2 hrs
      · exact (ht j r hr).2 (mem_singleton_iff.mp hrt)

/-- A side lying in one cut piece has a continuous lift to the
pasted disc, with its old parameter unchanged. -/
theorem exists_curve_lift
    {X T : Type*} [TopologicalSpace X] [TopologicalSpace T]
    {A B : Set X} (α : A → T) (β : B → T) (hcα : Continuous α) (hcβ : Continuous β)
    (a : Curve X) (ha : range a ⊆ A ∨ range a ⊆ B) :
    ∃ p : Curve T,
      (∃ h : ∀ t, a t ∈ A, ∀ t, p t = α ⟨a t, h t⟩) ∨
      (∃ h : ∀ t, a t ∈ B, ∀ t, p t = β ⟨a t, h t⟩) := by
  rcases ha with haA | haB
  · let h : ∀ t, a t ∈ A := fun t => haA (mem_range_self t)
    exact ⟨⟨fun t => α ⟨a t, h t⟩, hcα.comp (a.continuous.subtype_mk h)⟩,
      Or.inl ⟨h, fun _ => rfl⟩⟩
  · let h : ∀ t, a t ∈ B := fun t => haB (mem_range_self t)
    exact ⟨⟨fun t => β ⟨a t, h t⟩, hcβ.comp (a.continuous.subtype_mk h)⟩,
      Or.inr ⟨h, fun _ => rfl⟩⟩

/-- A lift of an injective old side into its cut piece stays injective. -/
theorem curve_lift_injective
    {X T : Type*} [TopologicalSpace X] [TopologicalSpace T]
    {A B : Set X} (α : A → T) (β : B → T)
    (hiα : Function.Injective α) (hiβ : Function.Injective β)
    (a : Curve X) (p : Curve T) (ha : Function.Injective a)
    (hp : (∃ h : ∀ t, a t ∈ A, ∀ t, p t = α ⟨a t, h t⟩) ∨
      (∃ h : ∀ t, a t ∈ B, ∀ t, p t = β ⟨a t, h t⟩)) :
    Function.Injective p := by
  intro s t hst
  rcases hp with ⟨hA, hpA⟩ | ⟨hB, hpB⟩
  · rw [hpA s, hpA t] at hst
    exact ha (congrArg Subtype.val (hiα hst))
  · rw [hpB s, hpB t] at hst
    exact ha (congrArg Subtype.val (hiβ hst))

/-- The associated map of a lifted side agrees with the old map
at every parameter, independently of which cut piece contains it. -/
theorem curve_lift_map
    {X T S : Type*} [TopologicalSpace X] [TopologicalSpace T]
    {A B : Set X} (α : A → T) (β : B → T) (φ : T → S) (φ₀ : X → S)
    (hφA : ∀ x : A, φ (α x) = φ₀ x.val) (hφB : ∀ y : B, φ (β y) = φ₀ y.val)
    (a : Curve X) (p : Curve T)
    (hp : (∃ h : ∀ t, a t ∈ A, ∀ t, p t = α ⟨a t, h t⟩) ∨
      (∃ h : ∀ t, a t ∈ B, ∀ t, p t = β ⟨a t, h t⟩)) :
    ∀ t, φ (p t) = φ₀ (a t) := by
  intro t
  rcases hp with ⟨hA, hpA⟩ | ⟨hB, hpB⟩
  · rw [hpA t]
    exact hφA _
  · rw [hpB t]
    exact hφB _

/-- Two old internally disjoint arcs remain internally disjoint
when lifted from their respective cut pieces. A cross-piece meeting
would lie on a pasted side, which the first arc's open part avoids.
This verifies the retained arcs in the new net of VII (2.6), page 218. -/
theorem lifted_curves_internally_disjoint
    {X T : Type*} [TopologicalSpace X] [TopologicalSpace T]
    {A B : Set X} (α : A → T) (β : B → T)
    (hiα : Function.Injective α) (hiβ : Function.Injective β)
    (f g : unitInterval → X)
    (hcross : ∀ (x : A) (y : B), α x = β y ↔ ∃ r, x.val = f r ∧ y.val = g r)
    (a b : Curve X) (p q : Curve T)
    (hpa : (∃ h : ∀ t, a t ∈ A, ∀ t, p t = α ⟨a t, h t⟩) ∨
      (∃ h : ∀ t, a t ∈ B, ∀ t, p t = β ⟨a t, h t⟩))
    (hqb : (∃ h : ∀ t, b t ∈ A, ∀ t, q t = α ⟨b t, h t⟩) ∨
      (∃ h : ∀ t, b t ∈ B, ∀ t, q t = β ⟨b t, h t⟩))
    (hab : ∀ t ∈ Ioo (0 : unitInterval) 1, a t ∉ range b)
    (haf : ∀ t ∈ Ioo (0 : unitInterval) 1, a t ∉ range f)
    (hag : ∀ t ∈ Ioo (0 : unitInterval) 1, a t ∉ range g) :
    ∀ t ∈ Ioo (0 : unitInterval) 1, p t ∉ range q := by
  intro t ht
  rintro ⟨s, hst⟩
  rcases hpa with ⟨haA, hpA⟩ | ⟨haB, hpB⟩
  · rcases hqb with ⟨hbA, hqA⟩ | ⟨hbB, hqB⟩
    · rw [hpA t, hqA s] at hst
      exact hab t ht ⟨s, congrArg Subtype.val (hiα hst)⟩
    · rw [hpA t, hqB s] at hst
      obtain ⟨r, hfr, _⟩ := (hcross ⟨a t, haA t⟩ ⟨b s, hbB s⟩).mp hst.symm
      exact haf t ht ⟨r, hfr.symm⟩
  · rcases hqb with ⟨hbA, hqA⟩ | ⟨hbB, hqB⟩
    · rw [hpB t, hqA s] at hst
      obtain ⟨r, _, hgr⟩ := (hcross ⟨b s, hbA s⟩ ⟨a t, haB t⟩).mp hst
      exact hag t ht ⟨r, hgr.symm⟩
    · rw [hpB t, hqB s] at hst
      exact hab t ht ⟨s, congrArg Subtype.val (hiβ hst)⟩

end GraphMinor.GM07
