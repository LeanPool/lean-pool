/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Disc
public import LeanPool.GraphMinor.GM11.SplitEdge
public import LeanPool.GraphMinor.GM11.RadialAccess
public import LeanPool.GraphMinor.GM12.SurfaceDualCut
public import LeanPool.GraphMinor.GM12.SurfaceDualCurves

/-!
# The faces of a drawing and its radial drawing

Let `H = Γ ∪ K`, for a radial drawing `K` of `Γ`. Each region `p` of `H` has a vertex of `K` from
the
region of `Γ` around `p` on its frontier (`exists_face_hub`), and an edge `e` of `Γ` on its
frontier.
We fix a point `m` of `e` and take a line from `m` to the hub, inside `p` (`exists_face_line`).
-/

@[expose] public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] {Γ K : Drawing S}

omit [T2Space S] [ConnectedSpace S] in
/-- A region of `H` lies in a region `r` of `Γ`, and the vertex of `K` in `r` is on its frontier.
The
region is not all of `r`, so its frontier meets `r`. A point of the frontier in `r` is the hub or
lies
on an edge of `K`. The whole edge is then on the frontier, and so is its end at the hub. -/
theorem exists_face_hub (hrad : PreRad (PaintingOrDrawing.drawing Γ) K) (hS : IsClosedSurface S)
    {p : Set S} (hp : p ∈ (radialUnion hrad).R) :
    ∃ r ∈ Γ.R, p ⊆ r ∧ ∃ c ∈ r, c ∈ K.V ∧ c ∈ closure p := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨r, hr, hpr⟩ := exists_region_of_sub hrad hp
  obtain ⟨c, ⟨hc, hcV⟩, -⟩ := hrad.2.2.2.1 r hr
  have hc' : c ∈ r := hc
  have hcV' : c ∈ K.V := hcV
  refine ⟨r, hr, hpr, c, hc', hcV', ?_⟩
  have hopen : IsOpen p := region_isOpen hp
  have hcU : c ∈ (radialUnion hrad).U := Or.inr (K.V_subset_U hcV')
  have hrc : IsPreconnected r := region_isPreconnected hr
  -- The frontier of `p` meets `r`.
  obtain ⟨y, hyr, hyp⟩ : ∃ y ∈ r, y ∈ closure p \ p := by
    by_contra hno
    push Not at hno
    have hclopen : r ⊆ p ∪ (closure p)ᶜ := fun y hy => by
      by_cases h : y ∈ closure p
      · exact Or.inl (by
          by_contra hn
          exact hno y hy ⟨h, hn⟩ |>.elim)
      · exact Or.inr h
    obtain ⟨z, hz⟩ := region_nonempty hp
    have := hrc.subset_left_of_subset_union hopen isClosed_closure.isOpen_compl
      (disjoint_left.mpr fun x h₁ h₂ => h₂ (subset_closure h₁)) hclopen ⟨z, hpr hz, hz⟩ hc'
    exact region_subset hp this hcU
  by_cases hyc : y = c
  · exact hyc ▸ hyp.1
  have hyU : y ∈ (radialUnion hrad).U := by
    rcases closure_region_subset hp hyp.1 with h | h
    · exact absurd h hyp.2
    · exact h
  have hyK : y ∈ K.U := by
    rcases hyU with h | h
    · exact absurd h (region_subset hr hyr)
    · exact h
  have hyV : y ∉ K.V := fun h => hyc (hub_unique hrad hr hc' hcV' hyr h)
  obtain ⟨g, hg, hyg⟩ := K.exists_edge_of_mem hyK hyV
  have hgH : g ∈ (radialUnion hrad).E := by
    rw [radialUnion_E]
    exact Or.inr hg
  have hgp : g ⊆ closure p :=
    edge_subset_closure_of_incident hS hgH hp ⟨y, hyg, hyp.1⟩
  exact closure_minimal hgp isClosed_closure (spoke_in_region hrad hS hr hc' hcV' hg hyg hyr).1

/-- The objects from which we build the dual. `D` is `Γ` with one new vertex `m e` on each edge `e`,
which cuts `e` into `A e` and `B e`, with ends `x e, m e` and `m e, y e`. Each edge `e` has two
faces
`f (e, b)` beside it, one for each `b`. Each face has a hub `h (e, b)`, and `ℓ (e, b)` is a line
from
`m e` to the hub through the face. -/
structure IsDualLines (hrad : PreRad (PaintingOrDrawing.drawing Γ) K) (D : Drawing S)
    (A B : Set S → Set S) (m x y : Set S → S) (f : Set S × Bool → Set S) (h : Set S × Bool → S)
    (ℓ : Set S × Bool → I → S) : Prop where
  U_eq : D.U = Γ.U
  V_eq : D.V = Γ.V ∪ m '' Γ.E
  split : ∀ e ∈ Γ.E, A e ∈ D.E ∧ B e ∈ D.E ∧ m e ∈ e ∧ m e ∉ A e ∧ m e ∉ B e ∧ Disjoint (A e) (B e)
    ∧
    e = A e ∪ {m e} ∪ B e ∧ x e ∈ Γ.V ∧ y e ∈ Γ.V ∧ closure e ∩ Γ.V = {x e, y e} ∧
    closure (A e) ∩ D.V = {x e, m e} ∧ closure (B e) ∩ D.V = {m e, y e}
  all : ∀ g ∈ D.E, ∃ e ∈ Γ.E, g = A e ∨ g = B e
  face : ∀ e ∈ Γ.E, ∀ b, f (e, b) ∈ (radialUnion hrad).R ∧ e ⊆ closure (f (e, b))
  face_ne : ∀ e ∈ Γ.E, f (e, true) ≠ f (e, false)
  face_all : ∀ e ∈ Γ.E, ∀ p ∈ (radialUnion hrad).R, e ⊆ closure p → ∃ b, p = f (e, b)
  face_unique : ∀ e ∈ Γ.E, ∀ e' ∈ Γ.E, ∀ b b', f (e, b) = f (e', b') → e = e'
  hub : ∀ e ∈ Γ.E, ∀ b, ∃ r ∈ Γ.R, f (e, b) ⊆ r ∧ h (e, b) ∈ r ∧ h (e, b) ∈ K.V
  cont : ∀ e ∈ Γ.E, ∀ b, Continuous (ℓ (e, b))
  inj : ∀ e ∈ Γ.E, ∀ b, Function.Injective (ℓ (e, b))
  zero : ∀ e ∈ Γ.E, ∀ b, ℓ (e, b) 0 = m e
  one : ∀ e ∈ Γ.E, ∀ b, ℓ (e, b) 1 = h (e, b)
  inside : ∀ e ∈ Γ.E, ∀ b, ∀ t, t ≠ 0 → t ≠ 1 → ℓ (e, b) t ∈ f (e, b)

/-- The objects of `IsDualLines` exist. Each face has an edge of `Γ` on its frontier, and a hub by
`exists_face_hub`. The point `m e` and the hub are vertices of `D ∪ K` that have a half-edge, so
`exists_access` gives a path from each of them into the face, and `exists_chord` joins these. -/
theorem exists_dualLines (hrad : PreRad (PaintingOrDrawing.drawing Γ) K) (hS : IsClosedSurface S)
    (hmax : RadMax (PaintingOrDrawing.drawing Γ) K) (hE : Γ.E.Nonempty) :
    ∃ D A B m x y f h ℓ, IsDualLines hrad D A B m x y f h ℓ := by
  classical
  obtain ⟨e₀, he₀⟩ := hE
  obtain ⟨y₀, -⟩ := he₀.1
  have hne : Nonempty S := ⟨y₀⟩
  have hE : Γ.E.Nonempty := ⟨e₀, he₀⟩
  obtain ⟨D, A, B, m, x, y, hU, hV, hsplit, hall⟩ := exists_split Γ
  have hDK : D.U ∩ K.U ⊆ D.V ∩ K.V := by
    rintro z ⟨h₁, h₂⟩
    have hz : z ∈ Γ.V := by
      rw [← radial_inter hrad]
      exact ⟨hU ▸ h₁, h₂⟩
    exact ⟨hV ▸ Or.inl hz, radial_V hrad hz⟩
  let Hs := D.glue K hDK
  have hHsU : Hs.U = (radialUnion hrad).U := by
    change D.U ∪ K.U = Γ.U ∪ K.U
    rw [hU]
  have hHsR : Hs.R = (radialUnion hrad).R := by
    simp only [Drawing.R, hHsU]
  have hHsE : Hs.E = D.E ∪ K.E := Drawing.glue_E _
  obtain ⟨γ, hγ⟩ := exists_edgePar Hs
  have hface : ∀ e ∈ Γ.E, ∃ p q : Set S, p ∈ (radialUnion hrad).R ∧ q ∈ (radialUnion hrad).R
    ∧ p ≠ q ∧
      e ⊆ closure p ∧ e ⊆ closure q ∧
      ∀ p' ∈ (radialUnion hrad).R, e ⊆ closure p' → p' = p ∨ p' = q := fun e he => by
    obtain ⟨p, hp, q, hq, h₁, h₂, h₃, h₄⟩ := exists_two_faces hrad hS hmax hE he
    exact ⟨p, q, hp, hq, h₁, h₂, h₃, h₄⟩
  choose! p q hp hq hpq hep heq hsides using hface
  let f : Set S × Bool → Set S := fun i => if i.2 then p i.1 else q i.1
  have hf : ∀ e ∈ Γ.E, ∀ b, f (e, b) ∈ (radialUnion hrad).R ∧ e ⊆ closure (f (e, b)) := by
    intro e he b
    cases b
    · exact ⟨hq e he, heq e he⟩
    · exact ⟨hp e he, hep e he⟩
  have hline : ∀ i : Set S × Bool, i.1 ∈ Γ.E → ∃ (c : S) (g : I → S), (∃ r ∈ Γ.R, f i ⊆ r ∧ c ∈ r
    ∧ c ∈ K.V) ∧
      Continuous g ∧ Function.Injective g ∧ g 0 = m i.1 ∧ g 1 = c ∧
      ∀ t, t ≠ 0 → t ≠ 1 → g t ∈ f i := by
    rintro ⟨e, b⟩ he
    obtain ⟨hfR, hef⟩ := hf e he b
    obtain ⟨r, hr, hfr, c, hc, hcV, hcl⟩ := exists_face_hub hrad hS hfR
    have hfR' : f (e, b) ∈ Hs.R := hHsR ▸ hfR
    have hfd : IsOpenDisc (f (e, b)) := face_isOpenDisc hrad hS hmax hfR
    obtain ⟨hA, -, hme, -, -, -, -, -, -, -, hcapA, -⟩ := hsplit e he
    have hmcl : m e ∈ closure (A e) ∩ D.V := by rw [hcapA]; simp
    have hAH : A e ∈ Hs.E := hHsE ▸ Or.inl hA
    have hmH : m e ∈ Hs.V := Or.inl hmcl.2
    have hcH : c ∈ Hs.V := Or.inr hcV
    obtain ⟨g₁, hg₁, h₁0, h₁⟩ := exists_access hS Hs hγ hmH
      (by
        obtain ⟨b', hb'⟩ := exists_end_eq hγ hAH hmH hmcl.1
        exact ⟨(A e, b'), hAH, hb'⟩) hfR' (hef hme)
    obtain ⟨s, hs, hcs⟩ := hub_has_spoke hrad hS hmax hr hc hcV
    have hsH : s ∈ Hs.E := hHsE ▸ Or.inr hs
    obtain ⟨g₂, hg₂, h₂0, h₂⟩ := exists_access hS Hs hγ hcH
      (by
        obtain ⟨b', hb'⟩ := exists_end_eq hγ hsH hcH hcs
        exact ⟨(s, b'), hsH, hb'⟩) hfR' hcl
    have hmU : m e ∈ Γ.U := Γ.closure_subset_U he (subset_closure hme)
    have hmc : m e ≠ c := fun h' => region_subset hr hc (h' ▸ hmU)
    have hmf : m e ∉ f (e, b) := fun h' => region_subset hr (hfr h') hmU
    obtain ⟨g, hg, hi, h0, h1, hin, -⟩ := exists_chord (IsOpenDisc.isPathConnected hfd) hmc hmf hg₁
      hg₂ h₁0 h₂0 h₁ h₂
    exact ⟨c, g, ⟨r, hr, hfr, hc, hcV⟩, hg, hi, h0, h1, hin⟩
  choose! h ℓ hhub hcont hinj h0 h1 hin using hline
  refine ⟨D, A, B, m, x, y, f, h, ℓ, ⟨hU, hV, hsplit, hall, hf, fun e he => hpq e he, ?_, ?_,
    fun e he b => hhub (e, b) he, fun e he b => hcont (e, b) he, fun e he b => hinj (e, b) he,
    fun e he b => h0 (e, b) he, fun e he b => h1 (e, b) he, fun e he b => hin (e, b) he⟩⟩
  · intro e he p' hp' hcl
    rcases hsides e he p' hp' hcl with h' | h'
    · exact ⟨true, h'⟩
    · exact ⟨false, h'⟩
  · intro e he e' he' b b' heq'
    obtain ⟨hfR, hef⟩ := hf e he b
    obtain ⟨hfR', hef'⟩ := hf e' he' b'
    obtain ⟨g, -, -, hg, -⟩ := face_edge hrad hS hmax hE hfR
    rw [hg e he hef, hg e' he' (heq' ▸ hef')]

end GraphMinor.GM12
