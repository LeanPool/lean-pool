/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.GM11.Rotation
public import LeanPool.GraphMinor.GM11.Corners
import LeanPool.GraphMinor.GM11.RadialCorners
import LeanPool.GraphMinor.Surface.DiscArcs
import Mathlib.Topology.Connected.Basic

/-!
# The corner entered by a normal curve

For the omitted entry-edge lemma in XII, page 243, a curve approaching a
vertex stays in one corner near that vertex. The closed sector discs of
XI cover a neighbourhood off the drawing, and distinct sectors meet only
in the drawing. A connected curve segment off the drawing must therefore
stay in one sector. This file proves that local step without assumptions
about a tangle or its inside function.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- In a finite closed cover, a connected set cannot move from one piece
to another when it avoids all intersections between distinct pieces. -/
theorem preconnected_subset_closed_piece {α ι : Type*} [TopologicalSpace α] [Finite ι]
    {A : Set α} (hA : IsPreconnected A) (Q : ι → Set α) (hQ : ∀ i, IsClosed (Q i))
    (hcover : A ⊆ ⋃ i, Q i)
    (hdisj : ∀ i j, i ≠ j → Disjoint A (Q i ∩ Q j))
    {i : ι} (hAi : (A ∩ Q i).Nonempty) : A ⊆ Q i := by
  classical
  let V : Set α := ⋃ j : {j // j ≠ i}, Q j.val
  have hV : IsClosed V := isClosed_iUnion_of_finite (fun j => hQ j.val)
  have hcov : A ⊆ Q i ∪ V := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hx)
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)
  intro y hy
  by_contra hyi
  have hyV : y ∈ V := (hcov hy).resolve_left hyi
  obtain ⟨x, hxA, hxi, hxV⟩ :=
    isPreconnected_closed_iff.mp hA (Q i) V (hQ i) hV hcov hAi ⟨y, hy, hyV⟩
  obtain ⟨j, hxj⟩ := mem_iUnion.mp hxV
  exact Set.disjoint_left.mp (hdisj i j.val (Ne.symm j.property)) hxA ⟨hxi, hxj⟩

universe u
variable {S : Type u} [TopologicalSpace S]

/-- The local corner step for the entry-edge definition of XII, page 243.
If a continuous curve leaves a vertex and immediately stays off the
drawing, some positive initial segment lies in one closed sector disc.
The hypothesis on the number of half-edges is the setting of XI's
rotation-sector lemma. -/
theorem exists_initial_sector (hS : IsClosedSurface S) (Γ : Drawing S)
    {γ : Set S → unitInterval → S} (hγ : EdgePar Γ γ) {v : S}
    (hv : v ∈ Γ.V) (h2 : 2 ≤ Nat.card (halfEdges Γ γ v))
    {g : unitInterval → S} (hg : Continuous g) (hg0 : g 0 = v)
    (hoff : ∀ t, 0 < t → g t ∉ Γ.U) :
    ∃ (Q : halfEdges Γ γ v → Set S), (∀ k, IsClosedDisc (Q k)) ∧
      (∀ k, v ∈ discBd (Q k)) ∧ ∃ (k : halfEdges Γ γ v) (ε : unitInterval),
        0 < ε ∧ ∀ t, t ≤ ε → g t ∈ Q k := by
  have : T2Space S := hS.2.1
  have : Fintype (halfEdges Γ γ v) := (finite_halfEdges Γ γ v).fintype
  obtain ⟨next, P, W, Q, hW, hvW, _, _, _, _, _, _, hcov, _, hQ, hQQ, _, _, _⟩ :=
    exists_rotation_sectors hS Γ hγ hv h2
  obtain ⟨ε, hε, _, hεW⟩ := exists_pos_le hg hW (hg0 ▸ hvW) (a := 1) zero_lt_one
  let A : Set S := g '' Ioc (0 : unitInterval) ε
  have hA : IsPreconnected A := isPreconnected_Ioc.image g hg.continuousOn
  have hAQ : A ⊆ ⋃ k, Q k := by
    rintro x ⟨t, ht, rfl⟩
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hcov ⟨hεW t ht.2, hoff t ht.1⟩)
    exact mem_iUnion.mpr ⟨k, (hQ k).2.2.1 hk⟩
  have hdisj : ∀ i j, i ≠ j → Disjoint A (Q i ∩ Q j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro x ⟨t, ht, rfl⟩ hx
    exact hoff t ht.1 (hQQ i j hij hx)
  have hεA : g ε ∈ A := ⟨ε, ⟨hε, le_rfl⟩, rfl⟩
  obtain ⟨k, hk⟩ := mem_iUnion.mp (hAQ hεA)
  have hsub : A ⊆ Q k := preconnected_subset_closed_piece hA Q
    (fun i => (hQ i).1.isClosed) hAQ hdisj ⟨g ε, hεA, hk⟩
  refine ⟨Q, fun i => (hQ i).1, fun i => (hQ i).2.1, k, ε, hε, ?_⟩
  intro t ht
  by_cases ht0 : t = 0
  · rw [ht0, hg0]
    exact Surface.discBd_subset _ (hQ k).2.1
  · exact hsub ⟨t, ⟨unitInterval.pos_iff_ne_zero.mpr ht0, ht⟩, rfl⟩

/-- Once sectors are fixed, the entering segment determines one of their
corner regions. The extra cover condition is the cover supplied by XI's
rotation construction. The zero endpoint lies on the sector boundary,
while all positive points lie in its corner region. -/
theorem initially_in_given_corner [T2Space S] {Γ : Drawing S}
    {γ : Set S → unitInterval → S} {v : S}
    {next : halfEdges Γ γ v → halfEdges Γ γ v}
    {ρ P Q : halfEdges Γ γ v → Set S} {W : Set S}
    {τ : halfEdges Γ γ v → unitInterval}
    (hsec : IsSectors Γ γ v next ρ P W Q τ)
    (hcover : W \ Γ.U ⊆ ⋃ k, Q k)
    {g : unitInterval → S} (hg : Continuous g) (hg0 : g 0 = v)
    (hoff : ∀ t, 0 < t → g t ∉ Γ.U) :
    ∃ (k : halfEdges Γ γ v) (ε : unitInterval), 0 < ε ∧
      (∀ t, t ≤ ε → g t ∈ Q k) ∧
      ∀ t, 0 < t → t ≤ ε → g t ∈ ρ k := by
  have : Fintype (halfEdges Γ γ v) := (finite_halfEdges Γ γ v).fintype
  obtain ⟨ε, hε, _, hεW⟩ := exists_pos_le hg hsec.isOpen (hg0 ▸ hsec.mem)
    (a := 1) zero_lt_one
  let A : Set S := g '' Ioc (0 : unitInterval) ε
  have hA : IsPreconnected A := isPreconnected_Ioc.image g hg.continuousOn
  have hAQ : A ⊆ ⋃ k, Q k := by
    rintro x ⟨t, ht, rfl⟩
    exact hcover ⟨hεW t ht.2, hoff t ht.1⟩
  have hdisj : ∀ i j, i ≠ j → Disjoint A (Q i ∩ Q j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro x ⟨t, ht, rfl⟩ hx
    exact hoff t ht.1 (hsec.inter i j hij hx)
  have hεA : g ε ∈ A := ⟨ε, ⟨hε, le_rfl⟩, rfl⟩
  obtain ⟨k, hk⟩ := mem_iUnion.mp (hAQ hεA)
  have hsub : A ⊆ Q k := preconnected_subset_closed_piece hA Q
    (fun i => (hsec.disc i).isClosed) hAQ hdisj ⟨g ε, hεA, hk⟩
  have hpos : ∀ t, 0 < t → t ≤ ε → g t ∈ P k := by
    intro t ht htε
    apply hsec.inside k
    refine ⟨⟨hεW t htε, hsub ⟨t, ⟨ht, htε⟩, rfl⟩⟩, ?_⟩
    intro hbd
    exact hoff t ht (hsec.bdU k ⟨hεW t htε, hbd⟩)
  refine ⟨k, ε, hε, ?_, fun t ht htε => hsec.sub k (hpos t ht htε)⟩
  intro t ht
  by_cases ht0 : t = 0
  · rw [ht0, hg0]
    exact Surface.discBd_subset _ (hsec.bd k)
  · exact hsub ⟨t, ⟨unitInterval.pos_iff_ne_zero.mpr ht0, ht⟩, rfl⟩

end GraphMinor.GM12
