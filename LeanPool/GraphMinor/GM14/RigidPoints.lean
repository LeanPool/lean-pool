/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Whitney
import LeanPool.GraphMinor.Surface.ArcTools
import LeanPool.GraphMinor.Surface.CutLift
import LeanPool.GraphMinor.Surface.SurfaceGraph
import LeanPool.GraphMinor.GM11.PaintingFacts

/-!
# Moving three points of a circle

Any injective map from at most three points of an `O`-arc to another `O`-arc extends to a
homeomorphism between
the `O`-arcs (`exists_oArc_map`), since three points cut an `O`-arc into three lines and all orders
of
three points on a circle are the same up to reflection. It then extends to a homeomorphism between
closed
discs with these `O`-arcs as boundaries (`exists_disc_points`).
-/

@[expose] public section

namespace GraphMinor.GM14.Whitney

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]

omit [T2Space Y] in
/-- Three points cut an `O`-arc into three lines. -/
theorem exists_three_lines {F : Set X} (hF : IsOArc F) {x y z : X} (hx : x ∈ F) (hy : y ∈ F)
  (hz : z ∈ F)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ L₁ L₂ L₃ : Set X, IsLineWithEnds L₁ x y ∧ IsLineWithEnds L₂ y z ∧ IsLineWithEnds L₃ z x ∧
      L₁ ∪ L₂ ∪ L₃ = F ∧ L₁ ∩ L₂ = {y} ∧ L₂ ∩ L₃ = {z} ∧ L₃ ∩ L₁ = {x} := by
  obtain ⟨A₀, B₀, hA₀, hB₀, hun₀, hcap₀⟩ := IsOArc.lines hF hx hy hxy
  obtain ⟨A, B, hA, hB, hun, hcap, hzB⟩ : ∃ A B : Set X, IsLineWithEnds A x y
    ∧ IsLineWithEnds B x y ∧
      A ∪ B = F ∧ A ∩ B = {x, y} ∧ z ∈ B := by
    have : z ∈ A₀ ∪ B₀ := hun₀ ▸ hz
    rcases this with h | h
    · exact ⟨B₀, A₀, hB₀, hA₀, (union_comm _ _).trans hun₀, (inter_comm _ _).trans hcap₀, h⟩
    · exact ⟨A₀, B₀, hA₀, hB₀, hun₀, hcap₀, h⟩
  obtain ⟨M₁, M₂, hM₁, hM₂, hMu, hMc⟩ := IsLineWithEnds.split hB hzB hxz.symm hyz.symm
  have hxM₁ : x ∈ M₁ := by
    obtain ⟨f, h0, -⟩ := hM₁
    exact h0 ▸ (f 0).2
  have hzM₁ : z ∈ M₁ := by
    obtain ⟨f, -, h1⟩ := hM₁
    exact h1 ▸ (f 1).2
  have hzM₂ : z ∈ M₂ := by
    obtain ⟨f, h0, -⟩ := hM₂
    exact h0 ▸ (f 0).2
  have hyM₂ : y ∈ M₂ := by
    obtain ⟨f, -, h1⟩ := hM₂
    exact h1 ▸ (f 1).2
  have hxA : x ∈ A := by
    have : x ∈ A ∩ B := hcap ▸ mem_insert _ _
    exact this.1
  have hyA : y ∈ A := by
    have : y ∈ A ∩ B := hcap ▸ mem_insert_of_mem _ rfl
    exact this.1
  have hxn : x ∉ M₂ := fun h => hxz (by simpa [hMc] using (show x ∈ M₁ ∩ M₂ from ⟨hxM₁, h⟩))
  have hyn : y ∉ M₁ := fun h => hyz (by simpa [hMc] using (show y ∈ M₁ ∩ M₂ from ⟨h, hyM₂⟩))
  have hAM : ∀ {w}, w ∈ A → w ∈ B → w = x ∨ w = y := fun {w} h₁ h₂ => by
    have : w ∈ A ∩ B := ⟨h₁, h₂⟩
    rw [hcap] at this
    exact this
  refine ⟨A, M₂, M₁, hA, GraphMinor.Surface.IsLineWithEnds.symm hM₂,
    GraphMinor.Surface.IsLineWithEnds.symm hM₁, ?_, ?_, ?_, ?_⟩
  · rw [← hun, ← hMu]
    ext w
    simp only [mem_union]
    tauto
  · apply subset_antisymm
    · rintro w ⟨h₁, h₂⟩
      have h₃ : w ∈ B := hMu ▸ Or.inr h₂
      rcases hAM h₁ h₃ with rfl | h₄
      · exact absurd h₂ hxn
      · exact h₄
    · rintro w rfl
      exact ⟨hyA, hyM₂⟩
  · rw [inter_comm, hMc]
  · apply subset_antisymm
    · rintro w ⟨h₁, h₂⟩
      have h₃ : w ∈ B := hMu ▸ Or.inl h₁
      rcases hAM h₂ h₃ with h₄ | rfl
      · exact h₄
      · exact absurd h₁ hyn
    · rintro w rfl
      exact ⟨hxM₁, hxA⟩

omit [T2Space X] [T2Space Y] in
omit [TopologicalSpace X] [TopologicalSpace Y] in
/-- A map on at most three points of an infinite set into an infinite set extends to three points.
-/
theorem exists_three_pts {F : Set X} {F' : Set Y} (hF : F.Infinite) (hF' : F'.Infinite) {P : Set X}
    (hPf : P.Finite) (hPF : P ⊆ F) (hc : P.ncard ≤ 3) {g : X → Y} (hg : InjOn g P)
    (hgF : MapsTo g P F') :
    ∃ (x y z : X) (g' : X → Y), x ∈ F ∧ y ∈ F ∧ z ∈ F ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ g' x ∈ F'
      ∧ g' y ∈ F' ∧
      g' z ∈ F' ∧ g' x ≠ g' y ∧ g' x ≠ g' z ∧ g' y ≠ g' z ∧
      ∀ p ∈ P, (p = x ∨ p = y ∨ p = z) ∧ g' p = g p := by
  classical
  induction hn : 3 - P.ncard generalizing P g with
  | zero =>
    have h3 : P.ncard = 3 := by omega
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := ncard_eq_three.mp h3
    have hm₁ : x ∈ ({x, y, z} : Set X) := by simp
    have hm₂ : y ∈ ({x, y, z} : Set X) := by simp
    have hm₃ : z ∈ ({x, y, z} : Set X) := by simp
    refine ⟨x, y, z, g, hPF hm₁, hPF hm₂, hPF hm₃, hxy, hxz, hyz, hgF hm₁, hgF hm₂, hgF hm₃,
      fun h => hxy (hg hm₁ hm₂ h), fun h => hxz (hg hm₁ hm₃ h), fun h => hyz (hg hm₂ hm₃ h), ?_⟩
    rintro p hp
    exact ⟨hp, rfl⟩
  | succ n ih =>
    obtain ⟨x, hxF, hxP⟩ := (hF.sdiff hPf).nonempty
    obtain ⟨y, hyF, hyP⟩ := (hF'.sdiff (hPf.image g)).nonempty
    have hcard : (insert x P).ncard = P.ncard + 1 := ncard_insert_of_notMem hxP hPf
    have hupd : ∀ p ∈ P, Function.update g x y p = g p := fun p hp =>
      Function.update_of_ne (fun h : p = x => hxP (by rw [← h]; exact hp)) _ _
    obtain ⟨a, b, c, g', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, hall⟩ :=
      ih (P := insert x P) (g := Function.update g x y) (hPf.insert x) (insert_subset hxF hPF)
      (by omega) (by
        intro p hp q hq he
        rcases hp with rfl | hp <;> rcases hq with rfl | hq
        · rfl
        · rw [Function.update_self, hupd q hq] at he
          exact absurd (he ▸ mem_image_of_mem g hq) hyP
        · rw [Function.update_self, hupd p hp] at he
          exact absurd (he.symm ▸ mem_image_of_mem g hp) hyP
        · rw [hupd p hp, hupd q hq] at he
          exact hg hp hq he) (by
        intro p hp
        rcases hp with rfl | hp
        · rw [Function.update_self]
          exact hyF
        · rw [hupd p hp]
          exact hgF hp) (by omega)
    refine ⟨a, b, c, g', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, fun p hp => ?_⟩
    obtain ⟨h₁₃, h₁₄⟩ := hall p (mem_insert_of_mem _ hp)
    exact ⟨h₁₃, h₁₄.trans (hupd p hp)⟩

/-- An injective map from at most three points of an `O`-arc into an `O`-arc extends to a
homeomorphism. -/
theorem exists_oArc_map {F : Set X} {F' : Set Y} (hF : IsOArc F) (hF' : IsOArc F') {P : Set X}
    (hPf : P.Finite) (hPF : P ⊆ F) (hc : P.ncard ≤ 3) {g : X → Y} (hg : InjOn g P)
    (hgF : MapsTo g P F') : ∃ f f', PH F F' f f' ∧ ∀ p ∈ P, f p = g p := by
  obtain ⟨x, y, z, g', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, hall⟩ :=
    exists_three_pts (infinite_of_isOArc hF) (infinite_of_isOArc hF') hPf hPF hc hg hgF
  obtain ⟨L₁, L₂, L₃, hL₁, hL₂, hL₃, hu, c₁₂, c₂₃, c₃₁⟩ := exists_three_lines hF h₁ h₂ h₃ h₄ h₅ h₆
  obtain ⟨M₁, M₂, M₃, hM₁, hM₂, hM₃, hu', d₁₂, d₂₃, d₃₁⟩ := exists_three_lines hF' h₇ h₈ h₉ h₁₀ h₁₁
    h₁₂
  have : Nonempty X := ⟨x⟩
  have : Nonempty Y := ⟨g' x⟩
  obtain ⟨a₁, a₁', p₁, e₁, e₁'⟩ := exists_line_PH hL₁ hM₁
  obtain ⟨a₂, a₂', p₂, e₂, e₂'⟩ := exists_line_PH hL₂ hM₂
  obtain ⟨a₃, a₃', p₃, e₃, e₃'⟩ := exists_line_PH hL₃ hM₃
  have st : ∀ {L : Set X} {u v : X}, IsLineWithEnds L u v → u ∈ L ∧ v ∈ L := fun {L u v} h => by
    obtain ⟨f, h0, h1⟩ := h
    exact ⟨h0 ▸ (f 0).2, h1 ▸ (f 1).2⟩
  have b₁ : a₁' (g' x) = x := by rw [← e₁]; exact p₁.2.2.1 (st hL₁).1
  have b₂ : a₁' (g' y) = y := by rw [← e₁']; exact p₁.2.2.1 (st hL₁).2
  have b₃ : a₂' (g' y) = y := by rw [← e₂]; exact p₂.2.2.1 (st hL₂).1
  have b₄ : a₂' (g' z) = z := by rw [← e₂']; exact p₂.2.2.1 (st hL₂).2
  have b₅ : a₃' (g' z) = z := by rw [← e₃]; exact p₃.2.2.1 (st hL₃).1
  have b₆ : a₃' (g' x) = x := by rw [← e₃']; exact p₃.2.2.1 (st hL₃).2
  have e₁₂ : ∀ u, u ∈ L₁ → u ∈ L₂ → a₁ u = a₂ u := fun u h h' => by
    have : u ∈ L₁ ∩ L₂ := ⟨h, h'⟩
    rw [c₁₂] at this
    rw [show u = y from this, e₁', e₂]
  have e₂₃ : ∀ u, u ∈ L₂ → u ∈ L₃ → a₂ u = a₃ u := fun u h h' => by
    have : u ∈ L₂ ∩ L₃ := ⟨h, h'⟩
    rw [c₂₃] at this
    rw [show u = z from this, e₂', e₃]
  have e₃₁ : ∀ u, u ∈ L₃ → u ∈ L₁ → a₃ u = a₁ u := fun u h h' => by
    have : u ∈ L₃ ∩ L₁ := ⟨h, h'⟩
    rw [c₃₁] at this
    rw [show u = x from this, e₃', e₁]
  have f₁₂ : ∀ u, u ∈ M₁ → u ∈ M₂ → a₁' u = a₂' u := fun u h h' => by
    have : u ∈ M₁ ∩ M₂ := ⟨h, h'⟩
    rw [d₁₂] at this
    rw [show u = g' y from this, b₂, b₃]
  have f₂₃ : ∀ u, u ∈ M₂ → u ∈ M₃ → a₂' u = a₃' u := fun u h h' => by
    have : u ∈ M₂ ∩ M₃ := ⟨h, h'⟩
    rw [d₂₃] at this
    rw [show u = g' z from this, b₄, b₅]
  have f₃₁ : ∀ u, u ∈ M₃ → u ∈ M₁ → a₃' u = a₁' u := fun u h h' => by
    have : u ∈ M₃ ∩ M₁ := ⟨h, h'⟩
    rw [d₃₁] at this
    rw [show u = g' x from this, b₆, b₁]
  obtain ⟨f, f', hf, hef, -⟩ := exists_glue (ι := Fin 3) (A := ![L₁, L₂, L₃]) (B := ![M₁, M₂, M₃])
    (f := ![a₁, a₂, a₃]) (f' := ![a₁', a₂', a₃'])
    (by
      intro i
      fin_cases i
      · exact hL₁.isCompact.isClosed
      · exact hL₂.isCompact.isClosed
      · exact hL₃.isCompact.isClosed)
    (by
      intro i
      fin_cases i
      · exact hM₁.isCompact.isClosed
      · exact hM₂.isCompact.isClosed
      · exact hM₃.isCompact.isClosed)
    (by
      intro i
      fin_cases i
      · exact p₁
      · exact p₂
      · exact p₃)
    (by
      intro i j u hi hj
      fin_cases i <;> fin_cases j
      · rfl
      · exact e₁₂ u hi hj
      · exact (e₃₁ u hj hi).symm
      · exact (e₁₂ u hj hi).symm
      · rfl
      · exact e₂₃ u hi hj
      · exact e₃₁ u hi hj
      · exact (e₂₃ u hj hi).symm
      · rfl)
    (by
      intro i j u hi hj
      fin_cases i <;> fin_cases j
      · rfl
      · exact f₁₂ u hi hj
      · exact (f₃₁ u hj hi).symm
      · exact (f₁₂ u hj hi).symm
      · rfl
      · exact f₂₃ u hi hj
      · exact f₃₁ u hi hj
      · exact (f₂₃ u hj hi).symm
      · rfl)
  have hUA : (⋃ i, (![L₁, L₂, L₃] : Fin 3 → Set X) i) = F := by
    rw [← hu]
    ext w
    simp [Fin.exists_fin_succ, or_assoc]
  have hUB : (⋃ i, (![M₁, M₂, M₃] : Fin 3 → Set Y) i) = F' := by
    rw [← hu']
    ext w
    simp [Fin.exists_fin_succ, or_assoc]
  rw [hUA, hUB] at hf
  refine ⟨f, f', hf, fun p hp => ?_⟩
  obtain ⟨h₁₃, h₁₄⟩ := hall p hp
  rw [← h₁₄]
  rcases h₁₃ with rfl | rfl | rfl
  · exact (hef 0 (st hL₁).1).trans e₁
  · exact (hef 1 (st hL₂).1).trans e₂
  · exact (hef 2 (st hL₃).1).trans e₃

/-- A homeomorphism between closed discs with a given effect on at most three boundary points. -/
theorem exists_disc_points {E : Set X} {E' : Set Y} (hE : IsClosedDisc E)
  (hE' : IsClosedDisc E') {P : Set X}
    (hPf : P.Finite) (hPF : P ⊆ discBd E) (hc : P.ncard ≤ 3) {g : X → Y} (hg : InjOn g P)
    (hgF : MapsTo g P (discBd E')) :
    ∃ f f', PH E E' f f' ∧ (∀ p ∈ P, f p = g p) ∧ MapsTo f (discBd E) (discBd E') ∧
      MapsTo f' (discBd E') (discBd E) := by
  obtain ⟨k, k', hk, hkg⟩ := exists_oArc_map hE.isOArc_discBd hE'.isOArc_discBd hPf hPF hc hg hgF
  obtain ⟨f, f', hf, he, he'⟩ := exists_disc_PH hE hE' hk
  refine ⟨f, f', hf, fun p hp => (he (hPF hp)).trans (hkg p hp), fun x hx => ?_, fun y hy => ?_⟩
  · rw [he hx]
    exact hk.1 hx
  · rw [he' hy]
    exact hk.2.1 hy

end GraphMinor.GM14.Whitney
