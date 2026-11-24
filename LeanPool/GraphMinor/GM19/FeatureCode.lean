/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FeatureGenus
public import Mathlib.Data.Set.Finite.List

/-!
# The code of a family of lines

Cut a surface along a family of lines. Each component of the cut surface has a form (`PieceForm`):
its numbers `a` and `b` and the
list of arcs of each cuff. The set of these forms is the code of the family (`HasCode`). Two
families with the same code differ by a
homeomorphism of the surface (`homeo_of_code`). There are finitely many codes for families with a
given index set
(`finite_codes`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Function GraphMinor.Surface

universe u

local notation "𝕀" => unitInterval

variable {I : Type}

/-- The arcs on the boundary of the cut surface: two for each line off the boundary, and one for
each line in the boundary. -/
abbrev ArcIx (inner : I → Prop) : Type := {s : I × Bool // inner s.1 ∨ s.2 = false}

/-- The arc with a given index. -/
def liftArc {Y : Type*} {inner : I → Prop} (ξ η : I → ℝ → Y) (s : ArcIx inner) : ℝ → Y
  := if s.1.2 then η s.1.1 else ξ s.1.1

section form

variable {Y : Type*} [TopologicalSpace Y] {J : Type*}

/-- The form of a part `W` of `Y` with arcs `γ`: the word of `W` with its free sides running through
the arcs in the order of `Ls`. -/
def PieceForm (γ : J → ℝ → Y) (W : Set Y) (a b : ℕ) (Ls : List (List (J × Bool))) : Prop :=
  ∃ f : ℕ × ℂ → W, Presents (sW (ew a b Ls.length)) f ∧
    (∀ i < Ls.length, ∀ (p : ℕ) (s : J) (e : Bool), (Ls.getD i [])[p]? = some (s, e) → ∀ u ∈ Icc
      (0 : ℝ) 1, (holeP a b Ls.length f i (pos (Ls.getD i []).length p u)).1 = γ s (ofs e u)) ∧
    ∀ s, γ s 0 ∈ W ↔ ∃ i < Ls.length, ∃ (p : ℕ) (e : Bool), (Ls.getD i [])[p]? = some (s, e)

/-- Two parts with the same form are homeomorphic, by a map that keeps the arcs. -/
theorem homeo_of_pieceForm [T2Space Y] {Y' : Type*} [TopologicalSpace Y'] [T2Space Y'] {γ : J → ℝ
  → Y} {γ' : J → ℝ → Y'} {W : Set Y} {W' : Set Y'} {a b : ℕ}
    {Ls : List (List (J × Bool))} (h : PieceForm γ W a b Ls) (h' : PieceForm γ' W' a b Ls) :
    ∃ e : W ≃ₜ W', ∀ s, γ s 0 ∈ W → ∀ u ∈ Icc (0 : ℝ) 1, ∀ x : W, x.1 = γ s u → (e x).1 = γ' s u
      := by
  obtain ⟨f, h₁, h₂, h₃⟩ := h
  obtain ⟨f', h₁', h₂', h₃'⟩ := h'
  obtain ⟨e, he⟩ := presents_homeo (finW_sW _) h₁ h₁'
  refine ⟨e, fun s hs u hu x hx ↦ ?_⟩
  obtain ⟨i, hi, p, b', hg⟩ := (h₃ s).mp hs
  have hv := ofs_mem (e := b') hu
  have e₁ := h₂ i hi p s b' hg _ hv
  have e₂ := h₂' i hi p s b' hg _ hv
  rw [ofs_ofs] at e₁ e₂
  have e₃ : x = holeP a b Ls.length f i (pos (Ls.getD i []).length p (ofs b' u)) := Subtype.ext
    (hx.trans e₁.symm)
  rw [e₃, ← e₂]
  exact congrArg Subtype.val (he _ ⟨(ew_mem_dsk _ _ _).1, (norm_per _ _).le⟩)

variable [T2Space Y]

/-- **Each component has a form.** -/
theorem exists_pieceForm [Finite J] {γ : J → ℝ → Y} (hS : IsSurface Y)
  (hγ : BoundaryArcs γ) {W : Set Y} (hW : IsClopen W) (hc : IsConnected W) :
    ∃ (a b : ℕ) (Ls : List (List (J × Bool))), PieceForm γ W a b Ls ∧ Ls.length ≤ Nat.card J
      ∧ ∀ l ∈ Ls, l.length ≤ Nat.card J := by
  classical
  have hSW : IsSurface W := isSurface_sub hS hW
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp hc
  obtain ⟨a, b, c, ⟨e⟩⟩ := classification W hSW inferInstance
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hin : ∀ s, γ s 0 ∈ W → ∀ u ∈ Icc (0 : ℝ) 1, γ s u ∈ W := fun s hs u hu ↦
    (isPreconnected_Icc.image _ (hγ.cont s)).subset_isClopen hW ⟨_, mem_image_of_mem _ h01, hs⟩
      (mem_image_of_mem _ hu)
  have hin' : ∀ s, ∀ u ∈ Icc (0 : ℝ) 1, γ s u ∈ W → γ s 0 ∈ W := fun s u hu hs ↦
    (isPreconnected_Icc.image _ (hγ.cont s)).subset_isClopen hW ⟨_, mem_image_of_mem _ hu, hs⟩
      (mem_image_of_mem _ h01)
  let J' := {s : J // γ s 0 ∈ W}
  let γ' : J' → ℝ → W := fun s u ↦ if h : γ s.1 u ∈ W then ⟨_, h⟩ else ⟨_, s.2⟩
  have hγ' : ∀ (s : J'), ∀ u ∈ Icc (0 : ℝ) 1, (γ' s u).1 = γ s.1 u := fun s u hu ↦ by
    simp only [γ', hin s.1 s.2 u hu, dite_eq_left]
  have hB : BoundaryArcs γ' := by
    refine ⟨fun s ↦ ?_, fun s u hu v hv he ↦ ?_, fun s u hu ↦ ?_, fun s s' u hu v hv he ↦ ?_,
      fun y hy ↦ ?_⟩
    · rw [IsInducing.subtypeVal.continuousOn_iff]
      exact (hγ.cont s.1).congr fun u hu ↦ hγ' s u hu
    · refine hγ.inj s.1 hu hv ?_
      rw [← hγ' s u hu, ← hγ' s v hv, he]
    · refine (mem_bd_sub hW.isOpen).mpr ?_
      rw [hγ' s u hu]
      exact hγ.bd s.1 u hu
    · have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
      have hv' : v ∈ Icc (0 : ℝ) 1 := ⟨hv.1.le, hv.2.le⟩
      obtain ⟨h₁, h₂⟩ := hγ.disj s.1 s'.1 u hu v hv (by rw [← hγ' s u hu', ← hγ' s' v hv', he])
      exact ⟨Subtype.ext h₁, h₂⟩
    · obtain ⟨s, u, hu, hsu⟩ := hγ.cover y.1 ((mem_bd_sub hW.isOpen).mp hy)
      have hs : γ s 0 ∈ W := hin' s u hu (hsu ▸ y.2)
      exact ⟨⟨s, hs⟩, u, hu, Subtype.ext ((hγ' ⟨s, hs⟩ u hu).trans hsu)⟩
  obtain ⟨f, L, hF, hc₁, hc₂⟩ := exists_form hSW e hB
  let L' : ℕ → List (J × Bool) := fun i ↦ (L i).map fun x ↦ (x.1.1, x.2)
  let Ls := (List.range c).map L'
  have hlen : Ls.length = c := by simp [Ls]
  have hget : ∀ i < c, Ls.getD i [] = L' i := fun i hi ↦ by
    simp [Ls, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  have hcard : Nat.card J' ≤ Nat.card J := Nat.card_le_card_of_injective _ Subtype.val_injective
  have hmap : ∀ i p s e, (L' i)[p]? = some (s, e) → ∃ hs : γ s 0 ∈ W, (L i)[p]? = some
    ((⟨s, hs⟩ : J'), e) := fun i p s e h ↦ by
    rw [List.getElem?_map] at h
    obtain ⟨x, hx, he⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact ⟨x.1.2, hx⟩
  refine ⟨a, b, Ls, ⟨f, hlen.symm ▸ hF.pres, fun i hi p s e' hg u hu ↦ ?_, fun s ↦ ⟨fun hs ↦ ?_,
    ?_⟩⟩, hlen.trans_le (hc₁.trans hcard), fun l hl ↦ ?_⟩
  · rw [hlen] at hi ⊢
    rw [hget i hi] at hg ⊢
    obtain ⟨hs, hg'⟩ := hmap i p s e' hg
    have h₁ := hF.side i hi p ⟨s, hs⟩ e' hg' u hu
    have h₂ : (L' i).length = (L i).length := by simp [L']
    rw [h₂, h₁]
    exact hγ' _ _ (ofs_mem hu)
  · obtain ⟨i, hi, p, e', hg⟩ := hF.all ⟨s, hs⟩
    refine ⟨i, by rwa [hlen], p, e', ?_⟩
    rw [hget i hi, List.getElem?_map, hg]
    rfl
  · rintro ⟨i, hi, p, e', hg⟩
    rw [hlen] at hi
    rw [hget i hi] at hg
    exact (hmap i p s e' hg).1
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
    have h₁ : i < c := by simpa using hi
    have h₂ : (L' i).length = (L i).length := by simp [L']
    rw [h₂]
    exact (hc₂ i h₁).trans hcard

end form


section cut

variable {S : Type u} [TopologicalSpace S] [T2Space S] {inner : I → Prop} {b : I → 𝕀 → S}

omit [TopologicalSpace S] [T2Space S] in
theorem liftArc_psi {Y : Type u} {ψ : Y → S} {ξ η : I → ℝ → Y} (hξ : ∀ i, ∀ u ∈ Icc (0 : ℝ) 1, ψ
  (ξ i u) = extI (b i) u) (hη : ∀ i, ∀ u ∈ Icc (0 : ℝ) 1, ψ (η i u) = extI (b i) u)
    (s : ArcIx inner) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : ψ (liftArc ξ η s u) = extI (b s.1.1) u
      := by
  unfold liftArc
  split_ifs
  · exact hη _ u hu
  · exact hξ _ u hu

omit [T2Space S] in
/-- The lifts of a family of lines are arcs on the boundary of the cut surface. -/
theorem boundaryArcs_of_cut {Y : Type u} [TopologicalSpace Y] {ψ : Y → S} {ξ η : I → ℝ → Y}
  (hb : IsLineFamily b inner) (hc : AbstractCut b inner ψ ξ η) :
    BoundaryArcs (liftArc ξ η : ArcIx inner → ℝ → Y) := by
  have hp := fun (s : ArcIx inner) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) ↦ liftArc_psi hc.hξ hc.hη s hu
  refine ⟨fun s ↦ ?_, fun s u hu v hv he ↦ ?_, fun s u hu ↦ ?_, fun s s' u hu v hv he ↦ ?_,
    fun y hy ↦ ?_⟩
  · unfold liftArc
    split_ifs
    · exact hc.cη _
    · exact hc.cξ _
  · have h₁ : extI (b s.1.1) u = extI (b s.1.1) v := by rw [← hp s hu, ← hp s hv, he]
    exact extI_injOn (hb.arc _).2 hu hv h₁
  · unfold liftArc
    split_ifs
    · exact hc.bdη _ u hu
    · exact hc.bdξ _ u hu
  · have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
    have hv' : v ∈ Icc (0 : ℝ) 1 := ⟨hv.1.le, hv.2.le⟩
    have h₁ : extI (b s.1.1) u = extI (b s'.1.1) v := by rw [← hp s hu', ← hp s' hv', he]
    rcases hb.meet _ _ u v hu' hv' h₁ with ⟨h₂, rfl⟩ | ⟨h₂, -⟩
    · refine ⟨?_, rfl⟩
      obtain ⟨⟨i, t⟩, hs⟩ := s
      obtain ⟨⟨j, t'⟩, hs'⟩ := s'
      simp only at h₂
      subst h₂
      refine Subtype.ext (Prod.ext rfl ?_)
      simp only
      by_contra hne
      have hin : inner i := by
        rcases hs with h₄ | h₄
        · exact h₄
        · rcases hs' with h₅ | h₅
          · exact h₅
          · exact absurd (h₄.trans h₅.symm) hne
      have h₃ := hc.ne i hin u hu
      cases t <;> cases t' <;> simp_all [liftArc]
    · rcases h₂ with rfl | rfl
      · exact absurd hu.1 (lt_irrefl _)
      · exact absurd hu.2 (lt_irrefl _)
  · obtain ⟨i, u, hu, h₁ | h₁⟩ := hc.cover y hy
    · exact ⟨⟨(i, false), .inr rfl⟩, u, hu, by simp [liftArc, h₁]⟩
    · by_cases hi : inner i
      · exact ⟨⟨(i, true), .inl hi⟩, u, hu, by simp [liftArc, h₁]⟩
      · exact ⟨⟨(i, false), .inr rfl⟩, u, hu, by simp [liftArc, h₁, hc.eqb i hi u hu]⟩

omit [T2Space S] in
/-- Two points over one point of `S` are equal, or both on the boundary of the cut surface. -/
theorem fib_bd {Y : Type u} [TopologicalSpace Y] {ψ : Y → S} {ξ η : I → ℝ → Y}
    (hc : AbstractCut b inner ψ ξ η) {y y' : Y} (h : ψ y = ψ y') :
    y = y' ∨ (y ∈ bd Y ∧ y' ∈ bd Y) := by
  have key : ∀ y y', Relation.EqvGen (fun p q ↦ ∃ i, ∃ u ∈ Icc (0 : ℝ) 1, p = ξ i u ∧ q
    = η i u) y y' → y = y' ∨ (y ∈ bd Y ∧ y' ∈ bd Y) := by
    intro y y' hr
    induction hr with
    | rel y y' h =>
      obtain ⟨i, u, hu, rfl, rfl⟩ := h
      exact .inr ⟨hc.bdξ i u hu, hc.bdη i u hu⟩
    | refl _ => exact .inl rfl
    | symm _ _ _ ih => exact ih.elim (fun h ↦ .inl h.symm) fun h ↦ .inr h.symm
    | trans x y z _ _ h₁ h₂ =>
      rcases h₁ with rfl | h₁
      · exact h₂
      · rcases h₂ with rfl | h₂
        · exact .inr h₁
        · exact .inr ⟨h₁.1, h₂.2⟩
  exact key _ _ (hc.fib y y' h)

/-- The form data of one component. -/
abbrev PieceCode (inner : I → Prop) : Type := ℕ × ℕ × List (List (ArcIx inner × Bool))

/-- The set `κ` is the code of the family `b` of lines. -/
def HasCode (b : I → 𝕀 → S) (inner : I → Prop) (κ : Set (PieceCode inner)) : Prop :=
  ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : T2Space Y) (ψ : Y → S) (ξ η : I → ℝ
    → Y), IsSurface Y ∧ AbstractCut b inner ψ ξ η ∧
    (∀ x : Y, ∃ k ∈ κ, PieceForm (liftArc ξ η : ArcIx inner → ℝ → Y) (connectedComponent x) k.1
      k.2.1 k.2.2) ∧
    (∀ k ∈ κ, ∃ x : Y, PieceForm (liftArc ξ η : ArcIx inner → ℝ → Y) (connectedComponent x) k.1
      k.2.1 k.2.2) ∧
    ∀ x : Y, ∃ s : ArcIx inner, liftArc ξ η s 0 ∈ connectedComponent x

/-- A homeomorphism of the cut surfaces that keeps the lifts passes to the surface. -/
theorem homeo_of_lifts {b b' : I → 𝕀 → S} {Y Y' : Type u} [TopologicalSpace Y] [TopologicalSpace
  Y'] [CompactSpace Y] [CompactSpace Y'] {ψ : Y → S} {ψ' : Y' → S} {ξ η : I → ℝ → Y}
    {ξ' η' : I → ℝ → Y'} (hc : AbstractCut b inner ψ ξ η) (hc' : AbstractCut b' inner ψ' ξ' η')
      (G : Y ≃ₜ Y') (hξ : ∀ i, ∀ u ∈ Icc (0 : ℝ) 1, G (ξ i u) = ξ' i u)
    (hη : ∀ i, ∀ u ∈ Icc (0 : ℝ) 1, G (η i u) = η' i u) : ∃ e : S ≃ₜ S, ∀ i, ∀ u ∈ Icc (0 : ℝ) 1, e
      (extI (b i) u) = extI (b' i) u := by
  have hξ' : ∀ i, ∀ u ∈ Icc (0 : ℝ) 1, G.symm (ξ' i u) = ξ i u := fun i u hu ↦ by rw [← hξ i u hu,
    G.symm_apply_apply]
  have hη' : ∀ i, ∀ u ∈ Icc (0 : ℝ) 1, G.symm (η' i u) = η i u := fun i u hu ↦ by rw [← hη i u hu,
    G.symm_apply_apply]
  have key : ∀ {Z Z' : Type u} [TopologicalSpace Z] [TopologicalSpace Z'] [CompactSpace Z] {p : Z
    → S} {p' : Z' → S} {x y : I → ℝ → Z} {x' y' : I → ℝ → Z'} {c c' : I → 𝕀 → S}
      (hC : AbstractCut c inner p x y) (hC' : AbstractCut c' inner p' x' y') (K : Z ≃ₜ Z'),
        (∀ i, ∀ u ∈ Icc (0 : ℝ) 1, K (x i u) = x' i u) →
        (∀ i, ∀ u ∈ Icc (0 : ℝ) 1, K (y i u) = y' i u) →
      ∃ E : S → S, Continuous E ∧ ∀ z, E (p z) = p' (K z) := by
    intro Z Z' _ _ _ p p' x y x' y' c c' hC hC' K hx hy
    have hq : IsQuotientMap p := hC.cont.isClosedMap.isQuotientMap hC.cont hC.surj
    choose r hr using hC.surj
    have hfib : ∀ z z', Relation.EqvGen (fun a d ↦ ∃ i, ∃ u ∈ Icc (0 : ℝ) 1, a = x i u ∧ d
      = y i u) z z' → p' (K z) = p' (K z') := by
      intro z z' he
      induction he with
      | rel z z' h =>
        obtain ⟨i, u, hu, rfl, rfl⟩ := h
        rw [hx i u hu, hy i u hu, hC'.hξ i u hu, hC'.hη i u hu]
      | refl _ => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ h₁ h₂ => exact h₁.trans h₂
    have hE : ∀ z, p' (K (r (p z))) = p' (K z) := fun z ↦ hfib _ _ (hC.fib _ _ (hr _))
    refine ⟨fun s ↦ p' (K (r s)), ?_, hE⟩
    rw [hq.continuous_iff]
    have e₁ : (fun s ↦ p' (K (r s))) ∘ p = p' ∘ K := funext hE
    rw [e₁]
    exact hC'.cont.comp K.continuous
  obtain ⟨E, hE₁, hE₂⟩ := key hc hc' G hξ hη
  obtain ⟨E', hE₁', hE₂'⟩ := key hc' hc G.symm hξ' hη'
  have hl : ∀ s, E' (E s) = s := fun s ↦ by
    obtain ⟨z, rfl⟩ := hc.surj s
    rw [hE₂, hE₂', G.symm_apply_apply]
  have hr : ∀ s, E (E' s) = s := fun s ↦ by
    obtain ⟨z, rfl⟩ := hc'.surj s
    rw [hE₂', hE₂, G.apply_symm_apply]
  refine ⟨⟨⟨E, E', hl, hr⟩, hE₁, hE₁'⟩, fun i u hu ↦ ?_⟩
  change E (extI (b i) u) = _
  rw [← hc.hξ i u hu, hE₂, hξ i u hu, hc'.hξ i u hu]

/-- **Two families with the same code differ by a homeomorphism.** -/
theorem homeo_of_code {b b' : I → 𝕀 → S} {κ : Set (PieceCode inner)} (hb : IsLineFamily b inner)
  (hb' : IsLineFamily b' inner) (h : HasCode b inner κ) (h' : HasCode b' inner κ) :
    ∃ e : S ≃ₜ S, ∀ i, ∀ u ∈ Icc (0 : ℝ) 1, e (extI (b i) u) = extI (b' i) u := by
  classical
  obtain ⟨Y, _, _, ψ, ξ, η, hY, hc, h₁, h₂, h₃⟩ := h
  obtain ⟨Y', _, _, ψ', ξ', η', hY', hc', h₁', h₂', h₃'⟩ := h'
  have := hY.1
  have := hY'.1
  have := hY.locallyConnected
  have := hY'.locallyConnected
  set γ : ArcIx inner → ℝ → Y := liftArc ξ η with hγ
  set γ' : ArcIx inner → ℝ → Y' := liftArc ξ' η' with hγ'
  have hA := boundaryArcs_of_cut hb hc
  have hA' := boundaryArcs_of_cut hb' hc'
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have harc : ∀ {Z : Type u} [TopologicalSpace Z] {g : ArcIx inner → ℝ → Z}, BoundaryArcs g → ∀ s
    (x : Z), ∀ u ∈ Icc (0 : ℝ) 1, g s u ∈ connectedComponent x → g s 0 ∈ connectedComponent x := by
    intro Z _ g hg s x u hu hx
    rw [connectedComponent_eq hx] at ⊢
    exact (isPreconnected_Icc.image _ (hg.cont s)).subset_connectedComponent
      (mem_image_of_mem _ hu) (mem_image_of_mem _ h01)
  have hmatch : ∀ x : Y, ∃ (x' : Y') (e : connectedComponent x ≃ₜ connectedComponent x'),
    (∀ s, γ s 0 ∈ connectedComponent x ↔ γ' s 0 ∈ connectedComponent x') ∧
      ∀ s, γ s 0 ∈ connectedComponent x → ∀ u ∈ Icc (0 : ℝ) 1, ∀ z : connectedComponent x, z.1
        = γ s u → (e z).1 = γ' s u := fun x ↦ by
    obtain ⟨k, hk, hf⟩ := h₁ x
    obtain ⟨x', hf'⟩ := h₂' k hk
    obtain ⟨e, he⟩ := homeo_of_pieceForm hf hf'
    refine ⟨x', e, fun s ↦ ?_, he⟩
    obtain ⟨-, -, -, h₄⟩ := hf
    obtain ⟨-, -, -, h₅⟩ := hf'
    rw [h₄ s, h₅ s]
  have hmatch' : ∀ x' : Y', ∃ x : Y, ∀ s, γ s 0 ∈ connectedComponent x ↔ γ' s 0 ∈
    connectedComponent x' := fun x' ↦ by
    obtain ⟨k, hk, hf'⟩ := h₁' x'
    obtain ⟨x, hf⟩ := h₂ k hk
    refine ⟨x, fun s ↦ ?_⟩
    obtain ⟨-, -, -, h₄⟩ := hf
    obtain ⟨-, -, -, h₅⟩ := hf'
    rw [h₄ s, h₅ s]
  choose T E hT hE using hmatch
  let rp : Y → Y := fun x ↦ @Classical.epsilon Y ⟨x⟩ (· ∈ connectedComponent x)
  have hrp : ∀ x, rp x ∈ connectedComponent x := fun x ↦ @Classical.epsilon_spec Y
    (· ∈ connectedComponent x) ⟨x, mem_connectedComponent⟩
  have hrpc : ∀ {x z : Y}, connectedComponent x = connectedComponent z → rp x = rp z
    := fun {x z} he ↦ by
    simp only [rp]
    rw [he]
  have hcp : ∀ x, connectedComponent (rp x) = connectedComponent x := fun x ↦
    (connectedComponent_eq (hrp x)).symm
  have hmem : ∀ x, x ∈ connectedComponent (rp x) := fun x ↦ by
    rw [hcp]
    exact mem_connectedComponent
  let H : Y → Y' := fun x ↦ (E (rp x) ⟨x, hmem x⟩).1
  have hH : ∀ z p (hz : z ∈ connectedComponent p), rp z = p → H z = (E p ⟨z, hz⟩).1 := by
    rintro z _ hz rfl
    rfl
  have hHγ : ∀ s, ∀ u ∈ Icc (0 : ℝ) 1, H (γ s u) = γ' s u := fun s u hu ↦ by
    refine hE _ s ?_ u hu _ rfl
    rw [hcp]
    exact harc hA s _ u hu mem_connectedComponent
  have hHc : Continuous H := by
    rw [continuous_iff_continuousAt]
    intro x₀
    set p := rp x₀ with hp
    have hop : IsOpen (connectedComponent p) := isOpen_connectedComponent
    have hx₀ : x₀ ∈ connectedComponent p := hmem x₀
    have hcont : ContinuousOn H (connectedComponent p) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have e₁ : (connectedComponent p).domRestrict H = Subtype.val ∘ E p := by
        funext z
        refine hH z.1 p z.2 ?_
        exact hrpc ((connectedComponent_eq z.2).symm.trans (hcp x₀))
      rw [e₁]
      exact continuous_subtype_val.comp (E p).continuous
    exact hcont.continuousAt (hop.mem_nhds hx₀)
  have hpick : ∀ x, ∃ s, γ' s 0 ∈ connectedComponent (T (rp x)) ∧ γ s 0 ∈ connectedComponent (rp x)
    := fun x ↦ by
    obtain ⟨s, hs⟩ := h₃ (rp x)
    exact ⟨s, (hT _ s).mp hs, hs⟩
  have hinj : Injective H := fun x z he ↦ by
    have h₄ : connectedComponent (T (rp x)) = connectedComponent (T (rp z)) := by
      have h₅ : H x ∈ connectedComponent (T (rp x)) := (E (rp x) ⟨x, hmem x⟩).2
      have h₆ : H x ∈ connectedComponent (T (rp z)) := he ▸ (E (rp z) ⟨z, hmem z⟩).2
      rw [connectedComponent_eq h₅, connectedComponent_eq h₆]
    obtain ⟨s, hs₁, hs₂⟩ := hpick x
    have hs₃ : γ s 0 ∈ connectedComponent (rp z) := (hT _ s).mpr (h₄ ▸ hs₁)
    have h₅ : connectedComponent (rp x) = connectedComponent (rp z) := by
      rw [connectedComponent_eq hs₂, connectedComponent_eq hs₃]
    have h₆ : rp x = rp z := hrpc (by rw [← hcp x, ← hcp z, h₅])
    have hxz : (E (rp z) ⟨x, h₆ ▸ hmem x⟩).1 = (E (rp z) ⟨z, hmem z⟩).1 := by
      rw [← hH x (rp z) (h₆ ▸ hmem x) h₆]
      exact he
    have := (E (rp z)).injective (Subtype.ext hxz)
    exact congrArg Subtype.val this
  have hsurj : Surjective H := fun y' ↦ by
    obtain ⟨x₀, hx₀⟩ := hmatch' y'
    set p := rp x₀ with hp
    obtain ⟨s, hs₁, hs₂⟩ := hpick x₀
    have hs₃ : γ' s 0 ∈ connectedComponent y' := (hx₀ s).mp (by rw [← hcp x₀]; exact hs₂)
    have h₅ : y' ∈ connectedComponent (T p) := by
      rw [connectedComponent_eq hs₁, ← connectedComponent_eq hs₃]
      exact mem_connectedComponent
    obtain ⟨z, hz⟩ := (E p).surjective ⟨y', h₅⟩
    refine ⟨z.1, ?_⟩
    have h₆ : rp z.1 = p := hrpc ((connectedComponent_eq z.2).symm.trans (hcp x₀))
    rw [hH z.1 p z.2 h₆]
    exact congrArg Subtype.val hz
  let G : Y ≃ₜ Y' := Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective H ⟨hinj, hsurj⟩) hHc
  have hGv : ∀ y, G y = H y := fun _ ↦ rfl
  refine homeo_of_lifts hc hc' G (fun i u hu ↦ ?_) fun i u hu ↦ ?_
  · rw [hGv]
    exact hHγ ⟨(i, false), .inr rfl⟩ u hu
  · rw [hGv]
    by_cases hi : inner i
    · exact hHγ ⟨(i, true), .inl hi⟩ u hu
    · rw [hc.eqb i hi u hu, hc'.eqb i hi u hu]
      exact hHγ ⟨(i, false), .inr rfl⟩ u hu

/-- The piece codes with bounded numbers. -/
def boundedCodes (inner : I → Prop) (B N : ℕ) : Set (PieceCode inner) :=
  {k | k.1 ≤ B ∧ k.2.1 ≤ B ∧ k.2.2.length ≤ N ∧ ∀ l ∈ k.2.2, l.length ≤ N}

theorem finite_boundedCodes [Finite I] (B N : ℕ) : (boundedCodes inner B N).Finite := by
  let T₁ : Set (List (ArcIx inner × Bool)) := {l | l.length ≤ N}
  have hT₁ : T₁.Finite := List.finite_length_le _ N
  have : Finite T₁ := hT₁
  have hT₂ : {l : List T₁ | l.length ≤ N}.Finite := List.finite_length_le _ N
  have hT₃ : ((fun l : List T₁ ↦ l.map Subtype.val) '' {l : List T₁ | l.length ≤ N}).Finite
    := hT₂.image _
  refine ((Set.finite_Iic B).prod ((Set.finite_Iic B).prod hT₃)).subset ?_
  rintro ⟨a, b, Ls⟩ ⟨h₁, h₂, h₃, h₄⟩
  refine ⟨h₁, h₂, Ls.attach.map (fun l ↦ ⟨l.1, h₄ l.1 l.2⟩), by simpa using h₃, ?_⟩
  simp

/-- **Finitely many codes.** -/
theorem finite_codes [Finite I] (hS : IsSurface S) [ConnectedSpace S] (inner : I
  → Prop) [Nonempty I] :
    ∃ 𝒦 : Set (Set (PieceCode inner)), 𝒦.Finite ∧ ∀ b : I → 𝕀 → S, IsLineFamily b inner → ∀
      (V : Set S) (E 𝓕 : Set (Set S)), IsDissection V E 𝓕 → (∀ i, b i 0 ∈ V ∧ b i 1 ∈ V) →
      (∀ i, range (b i) ⊆ gr V E) → ∃ κ ∈ 𝒦, HasCode b inner κ := by
  classical
  obtain ⟨a₀, b₀, c₀, ⟨e₀⟩⟩ := classification S hS inferInstance
  set N := Nat.card (ArcIx inner) with hN
  set B := 2 * a₀ + b₀ with hB
  refine ⟨{κ | κ ⊆ boundedCodes inner B N}, (finite_boundedCodes B N).finite_subsets,
    fun b hb V E 𝓕 hd hV hE ↦ ?_⟩
  obtain ⟨Y, tY, t2, ψ, ξ, η, hY, hc⟩ := exists_abstractCut hS hb hd hV hE
  have := hY.1
  have := hY.locallyConnected
  have hA := boundaryArcs_of_cut hb hc
  have hbdS : ∀ y, ψ y ∈ bd S → y ∈ bd Y := fun y hy ↦ by
    obtain ⟨i, v, hv⟩ := hb.cover _ hy
    have hv' : (v : ℝ) ∈ Icc (0 : ℝ) 1 := v.2
    have h₁ : ψ y = ψ (ξ i v) := by rw [hc.hξ i v hv', extI_coe, hv]
    rcases fib_bd hc h₁ with h₂ | h₂
    · rw [h₂]
      exact hc.bdξ i v hv'
    · exact h₂.1
  let κ : Set (PieceCode inner) := {k | k ∈ boundedCodes inner B N ∧ ∃ x : Y, PieceForm
    (liftArc ξ η : ArcIx inner → ℝ → Y) (connectedComponent x) k.1 k.2.1 k.2.2}
  refine ⟨κ, fun k hk ↦ hk.1, Y, tY, t2, ψ, ξ, η, hY, hc, fun x ↦ ?_, fun k hk ↦ hk.2, fun x ↦ ?_⟩
  · have hW : IsClopen (connectedComponent x) := isClopen_connectedComponent
    obtain ⟨a, b', Ls, hF, h₁, h₂⟩ := exists_pieceForm hY hA hW isConnected_connectedComponent
    obtain ⟨f, hf, -, -⟩ := id hF
    obtain ⟨ht, f₀, hf₀⟩ := presents_ew a b' Ls.length
    obtain ⟨e, -⟩ := presents_homeo (finW_sW _) hf hf₀
    have h₃ := genus_le hc.cont hc.surj (fun y y' h ↦ fib_bd hc h) hbdS hW e e₀
    refine ⟨(a, b', Ls), ⟨⟨?_, ?_, h₁, h₂⟩, x, hF⟩, hF⟩ <;> simp only <;> omega
  · by_contra hcon
    push Not at hcon
    obtain ⟨i⟩ := ‹Nonempty I›
    have hW : IsClopen (connectedComponent x) := isClopen_connectedComponent
    have hnb : ∀ y ∈ connectedComponent x, y ∉ bd Y := fun y hy hb' ↦ by
      obtain ⟨s, u, hu, hsu⟩ := hA.cover y hb'
      have h₀ : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
      refine hcon s ((isPreconnected_Icc.image _ (hA.cont s)).subset_isClopen hW ⟨y, ⟨u, hu,
        hsu⟩, hy⟩ (mem_image_of_mem _ h₀))
    have hcl₁ : IsClosed (ψ '' connectedComponent x) := (hW.1.isCompact.image hc.cont).isClosed
    have hcl₂ : IsClosed (ψ '' (connectedComponent x)ᶜ) := (hW.2.isClosed_compl.isCompact.image
      hc.cont).isClosed
    have hcompl : (ψ '' connectedComponent x)ᶜ = ψ '' (connectedComponent x)ᶜ := by
      ext s
      constructor
      · intro hs
        obtain ⟨y, rfl⟩ := hc.surj s
        exact ⟨y, fun hy ↦ hs (mem_image_of_mem _ hy), rfl⟩
      · rintro ⟨y, hy, rfl⟩ ⟨y', hy', he⟩
        rcases fib_bd hc he with rfl | h₁
        · exact hy hy'
        · exact hnb y' hy' h₁.1
    have hclopen : IsClopen (ψ '' connectedComponent x) := ⟨hcl₁, by
      rw [← isClosed_compl_iff, hcompl]
      exact hcl₂⟩
    have huniv := hclopen.eq_univ ⟨ψ x, mem_image_of_mem _ mem_connectedComponent⟩
    have hempty : (connectedComponent x)ᶜ = ∅ := by
      by_contra hne
      obtain ⟨y, hy⟩ := nonempty_iff_ne_empty.mpr hne
      have hψy : ψ y ∈ ψ '' (connectedComponent x)ᶜ := mem_image_of_mem _ hy
      rw [← hcompl, huniv] at hψy
      exact hψy (mem_univ _)
    have h₁ : liftArc ξ η (⟨(i, false), .inr rfl⟩ : ArcIx inner) 0 ∈ connectedComponent x := by
      by_contra hn
      have : liftArc ξ η (⟨(i, false), .inr rfl⟩ : ArcIx inner) 0 ∈ (connectedComponent x)ᶜ := hn
      rw [hempty] at this
      exact this
    exact hcon _ h₁

end cut

end GraphMinor.GM19
