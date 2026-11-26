/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.RegionWalk

/-!
# How often the walk around a region uses an edge

The walk around a region `r` uses an edge once for each side of the edge in `r`. An edge has two
sides in
`r` when `r` together with the edge contains a neighbourhood of a point of the edge (`IsTwoSided`).
`count_collar_walk` is the result.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

/-- Both sides of the edge `e` are in `r`: the set `r ∪ e` contains a neighbourhood of a point of
`e`. -/
def IsTwoSided (r e : Set S) : Prop := (e ∩ interior (r ∪ e)).Nonempty

open Classical in
/-- The number of times a list of edges contains `e`. -/
noncomputable def edgeCount (l : List (Set S)) (e : Set S) : ℕ := l.count e

omit [TopologicalSpace S] in
open Classical in
theorem edgeCount_map_range (F : ℕ → Set S) (e : Set S) (p : ℕ) :
    edgeCount ((List.range' 0 p).map F) e = ((Finset.range p).filter fun j => F j = e).card := by
  induction p with
  | zero => simp [edgeCount]
  | succ p ih =>
    have h₁ : List.range' 0 (p + 1) = List.range' 0 p ++ [p] := by
      simpa using (List.range'_1_concat (s := 0) (n := p))
    rw [Finset.range_add_one, Finset.filter_insert]
    simp only [edgeCount, h₁, List.map_append, List.map_cons, List.map_nil, List.count_append]
    simp only [edgeCount] at ih
    rw [ih]
    by_cases h : F p = e
    · have hnot : p ∉ (Finset.range p).filter fun j => F j = e := by simp
      simp [h, hnot]
    · have h' : ¬ e = F p := fun h' => h h'.symm
      simp [h]

variable [T2Space S] [ConnectedSpace S] {D D₂ Γ' : Drawing S} {A B : Set S → Set S} {m x y : Set S
  → S}
  {r : Set S} {n p : ℕ} {v : ℕ → S} {a s P : ℕ → Set S} {ε : ℕ → I → S} {h : C(Circle × I, S)}
  {F : ℕ → Set S}

open Classical in
/-- The steps of the collar along the edge `g`. -/
noncomputable def stepsOn (n : ℕ) (a : ℕ → Set S) (g : Set S) : Finset ℕ :=
  (Finset.range n).filter fun i => a i = g

omit [TopologicalSpace S] [T2Space S] [ConnectedSpace S] in
theorem mem_stepsOn {g : Set S} {i : ℕ} : i ∈ stepsOn n a g ↔ i < n ∧ a i = g := by
  simp [stepsOn]

section

variable (hrad : PreRad (PaintingOrDrawing.drawing D₂) Γ') (hS : IsClosedSurface S)
  (hmax : RadMax (PaintingOrDrawing.drawing D₂) Γ') (hE : D₂.E.Nonempty)
  (hc : IsHubCollar D₂ Γ' (radialUnion hrad) r n v a s P ε h)
include hrad hS hmax hE hc

open Classical in
/-- The steps along an edge match its two faces inside `r`. -/
theorem card_stepsOn {g f₁ f₂ : Set S} (hg : g ∈ D₂.E) (h₁ : f₁ ∈ (radialUnion hrad).R)
    (h₂ : f₂ ∈ (radialUnion hrad).R) (hne : f₁ ≠ f₂)
    (hall : ∀ p' ∈ (radialUnion hrad).R, g ⊆ closure p' → p' = f₁ ∨ p' = f₂)
    (hc₁ : g ⊆ closure f₁) (hc₂ : g ⊆ closure f₂) :
    (stepsOn n a g).card = (if f₁ ⊆ r then 1 else 0) + (if f₂ ⊆ r then 1 else 0) := by
  have hinj : InjOn P (stepsOn n a g : Set ℕ) := by
    intro i hi j hj heq
    exact hc.inj i j (mem_stepsOn.mp hi).1 (mem_stepsOn.mp hj).1 heq
  have himg : (stepsOn n a g).image P = (({f₁, f₂} : Finset (Set S)).filter fun f => f ⊆ r) := by
    ext f
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨hin, hai⟩ := mem_stepsOn.mp hi
      exact ⟨hall _ (hc.region i) (hai ▸ hc.edge_cl i), hc.region_sub i⟩
    · rintro ⟨hf, hfr⟩
      have hfR : f ∈ (radialUnion hrad).R := by
        rcases hf with rfl | rfl
        · exact h₁
        · exact h₂
      have hgf : g ⊆ closure f := by
        rcases hf with rfl | rfl
        · exact hc₁
        · exact hc₂
      obtain ⟨i, hi, rfl⟩ := hc.all f hfR hfr
      obtain ⟨e₀, -, -, huniq, -⟩ := face_edge hrad hS hmax hE hfR
      exact ⟨i, mem_stepsOn.mpr ⟨hi, (huniq _ (hc.edge i) (hc.edge_cl i)).trans
        (huniq _ hg hgf).symm⟩, rfl⟩
  rw [← Finset.card_image_of_injOn hinj, himg, Finset.filter_insert, Finset.filter_singleton]
  by_cases a₁ : f₁ ⊆ r <;> by_cases a₂ : f₂ ⊆ r <;> simp only [a₁, a₂, ite_true, ite_false] <;>
    simp [hne]

omit hc in
/-- The faces of `e` from the region of `Γ'` around it: the region is the union of the faces and
`e`. -/
theorem exists_faces_region {g : Set S} (hg : g ∈ D₂.E) :
    ∃ t ∈ Γ'.R, ∃ f₁ ∈ (radialUnion hrad).R, ∃ f₂ ∈ (radialUnion hrad).R, f₁ ≠ f₂ ∧
      g ⊆ closure f₁ ∧ g ⊆ closure f₂ ∧ t = f₁ ∪ f₂ ∪ g ∧
      ∀ p' ∈ (radialUnion hrad).R, g ⊆ closure p' → p' = f₁ ∨ p' = f₂ := by
  obtain ⟨z, hz⟩ := hg.1
  have hzU : z ∉ Γ'.U := by
    intro hzU
    have hmem : z ∈ D₂.U ∩ Γ'.U := ⟨(hg.2.1 hz).1, hzU⟩
    rw [radial_inter hrad] at hmem
    exact (hg.2.1 hz).2 hmem
  obtain ⟨t, ht, hzt⟩ := exists_region_of_notMem hzU
  have hdis : Disjoint g Γ'.U := by
    refine disjoint_left.mpr fun w hw hwU => ?_
    have hmem : w ∈ D₂.U ∩ Γ'.U := ⟨(hg.2.1 hw).1, hwU⟩
    rw [radial_inter hrad] at hmem
    exact (hg.2.1 hw).2 hmem
  have hgt : g ⊆ t := subset_region ht hg.2.2.1.isConnected.isPreconnected hdis hz hzt
  obtain ⟨f₁, h₁, f₂, h₂, hne, c₁, c₂, heq⟩ := region_eq_two_faces hrad hS hmax hE ht hg hgt
  obtain ⟨f₃, h₃, f₄, h₄, hne', c₃, c₄, hall⟩ := exists_two_faces hrad hS hmax hE hg
  refine ⟨t, ht, f₁, h₁, f₂, h₂, hne, c₁, c₂, heq, ?_⟩
  intro p' hp' hc'
  have e₁ := hall _ h₁ c₁
  have e₂ := hall _ h₂ c₂
  rcases hall p' hp' hc' with rfl | rfl <;> rcases e₁ with rfl | rfl <;> rcases e₂ with rfl | rfl
  all_goals first | exact Or.inl rfl | exact Or.inr rfl | exact (hne rfl).elim

end

section

variable (hd : SplitData D D₂ A B m x y) (hnp : n = 2 * p)
  (hF : ∀ j, F j ∈ D.E ∧ v (2 * j + 1) = m (F j) ∧
      ((a (2 * j) = A (F j) ∧ a (2 * j + 1) = B (F j) ∧ x (F j) = v (2 * j) ∧
          y (F j) = v (2 * j + 2)) ∨
        (a (2 * j) = B (F j) ∧ a (2 * j + 1) = A (F j) ∧ y (F j) = v (2 * j) ∧
          x (F j) = v (2 * j + 2))))
include hd hnp hF

omit [T2Space S] [ConnectedSpace S] in
open Classical in
/-- A step on one half of `e` lies in a passage along `e`, and each passage has one such step. -/
theorem card_steps_half {e g g' : Set S} (he : e ∈ D.E) (hsub : g ∈ D₂.E) (hne : g ≠ g')
  (hgg : g ⊆ e)
    (hpair : ∀ j, (a (2 * j) = g ∧ a (2 * j + 1) = g') ∨ (a (2 * j) = g' ∧ a (2 * j + 1) = g)
      ∨ F j ≠ e) :
    (stepsOn n a g).card = ((Finset.range p).filter fun j => F j = e).card := by
  have hedge : ∀ j, a (2 * j) ⊆ F j ∧ a (2 * j + 1) ⊆ F j := by
    intro j
    obtain ⟨hf, -, h₁⟩ := hF j
    rcases h₁ with ⟨h₁, h₂, -⟩ | ⟨h₁, h₂, -⟩
    · rw [h₁, h₂]
      exact ⟨hd.A_sub hf, hd.B_sub hf⟩
    · rw [h₁, h₂]
      exact ⟨hd.B_sub hf, hd.A_sub hf⟩
  obtain ⟨z, hz⟩ := hsub.1
  have heq : ∀ {i j}, (i = 2 * j ∨ i = 2 * j + 1) → a i = g → F j = e := by
    rintro i j (rfl | rfl) hi
    · exact D.edge_eq_of_mem (hF j).1 he ((hedge j).1 (hi ▸ hz)) (hgg hz)
    · exact D.edge_eq_of_mem (hF j).1 he ((hedge j).2 (hi ▸ hz)) (hgg hz)
  refine Finset.card_bij (fun i _ => i / 2) ?_ ?_ ?_
  · intro i hi
    obtain ⟨hin, hai⟩ := mem_stepsOn.mp hi
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, heq (by omega) hai⟩
  · intro i hi i' hi' hii
    obtain ⟨-, hai⟩ := mem_stepsOn.mp hi
    obtain ⟨-, hai'⟩ := mem_stepsOn.mp hi'
    set j := i / 2 with hj
    have hFj : F j = e := heq (by omega) hai
    have hc₁ : i = 2 * j ∨ i = 2 * j + 1 := by omega
    have hc₂ : i' = 2 * j ∨ i' = 2 * j + 1 := by omega
    rcases hpair j with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | h₁
    · rcases hc₂ with rfl | rfl
      · rcases hc₁ with h₃ | h₃
        · exact h₃
        · exact (hne (hai.symm.trans (by rw [h₃, h₂]))).elim
      · exact (hne (hai'.symm.trans h₂)).elim
    · rcases hc₁ with h₃ | h₃
      · exact (hne ((by rw [← hai, h₃, h₁]))).elim
      · rcases hc₂ with h₄ | h₄
        · exact (hne ((by rw [← hai', h₄, h₁]))).elim
        · omega
    · exact (h₁ hFj).elim
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    rcases hpair j with ⟨h₁, -⟩ | ⟨-, h₁⟩ | h₁
    · exact ⟨2 * j, mem_stepsOn.mpr ⟨by omega, h₁⟩, by omega⟩
    · exact ⟨2 * j + 1, mem_stepsOn.mpr ⟨by omega, h₁⟩, by omega⟩
    · exact (h₁ hj.2).elim

omit [T2Space S] [ConnectedSpace S] in
open Classical in
theorem card_steps_A {e : Set S} (he : e ∈ D.E) :
    (stepsOn n a (A e)).card = ((Finset.range p).filter fun j => F j = e).card := by
  refine card_steps_half hd hnp hF he (hd.A_mem e he) (hd.ne_AB he) (hd.A_sub he) fun j => ?_
  by_cases hj : F j = e
  · obtain ⟨-, -, h₁⟩ := hF j
    rw [hj] at h₁
    rcases h₁ with ⟨h₁, h₂, -⟩ | ⟨h₁, h₂, -⟩
    · exact Or.inl ⟨h₁, h₂⟩
    · exact Or.inr (Or.inl ⟨h₁, h₂⟩)
  · exact Or.inr (Or.inr hj)

omit [T2Space S] [ConnectedSpace S] in
open Classical in
theorem card_steps_B {e : Set S} (he : e ∈ D.E) :
    (stepsOn n a (B e)).card = ((Finset.range p).filter fun j => F j = e).card := by
  refine card_steps_half hd hnp hF he (hd.B_mem e he) (hd.ne_AB he).symm (hd.B_sub he) fun j => ?_
  by_cases hj : F j = e
  · obtain ⟨-, -, h₁⟩ := hF j
    rw [hj] at h₁
    rcases h₁ with ⟨h₁, h₂, -⟩ | ⟨h₁, h₂, -⟩
    · exact Or.inr (Or.inl ⟨h₁, h₂⟩)
    · exact Or.inl ⟨h₁, h₂⟩
  · exact Or.inr (Or.inr hj)

end

open Classical in
/-- **How often the walk around a region uses an edge**, in terms of the steps of the collar. -/
theorem card_passes (hd : SplitData D D₂ A B m x y)
    (hrad : PreRad (PaintingOrDrawing.drawing D₂) Γ') (hS : IsClosedSurface S)
    (hmax : RadMax (PaintingOrDrawing.drawing D₂) Γ') (hE : D₂.E.Nonempty)
    (hc : IsHubCollar D₂ Γ' (radialUnion hrad) r n v a s P ε h) (hr : r ∈ D₂.R) (hnp : n = 2 * p)
    (hF : ∀ j, F j ∈ D.E ∧ v (2 * j + 1) = m (F j) ∧
      ((a (2 * j) = A (F j) ∧ a (2 * j + 1) = B (F j) ∧ x (F j) = v (2 * j) ∧
          y (F j) = v (2 * j + 2)) ∨
        (a (2 * j) = B (F j) ∧ a (2 * j + 1) = A (F j) ∧ y (F j) = v (2 * j) ∧
          x (F j) = v (2 * j + 2)))) {e : Set S} (he : e ∈ D.E) :
    edgeCount ((List.range' 0 p).map F) e =
      if (e ∩ frontier r).Nonempty then (if IsTwoSided r e then 2 else 1) else 0 := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hcount := edgeCount_map_range F e p
  rw [hcount]
  set c := ((Finset.range p).filter fun j => F j = e).card with hcdef
  have hA := card_steps_A hd hnp hF he
  have hB := card_steps_B hd hnp hF he
  have hU : ∀ f ∈ (radialUnion hrad).R, Disjoint f D₂.U := fun f hf =>
    disjoint_left.mpr fun w hw hwU => region_subset hf hw (Or.inl hwU)
  -- A face either lies in `r` or misses it.
  have hface : ∀ f ∈ (radialUnion hrad).R, (f ∩ r).Nonempty → f ⊆ r := by
    rintro f hf ⟨w, hw, hwr⟩
    obtain ⟨r', hr', hsub⟩ := exists_region_of_sub hrad hf
    obtain rfl := region_eq_of_mem hr' hr (hsub hw) hwr
    exact hsub
  -- Two steps on an edge with a point inside `r ∪ e`.
  have htwo : ∀ {g : Set S}, g ∈ D₂.E → g ⊆ e → (g ∩ interior (r ∪ e)).Nonempty →
      (stepsOn n a g).card = 2 := by
    rintro g hg hge ⟨z, hzg, hzO⟩
    obtain ⟨t, ht, f₁, h₁, f₂, h₂, hne, c₁, c₂, -, hall⟩ := exists_faces_region hrad hS hmax hE hg
    have hin : ∀ f ∈ (radialUnion hrad).R, g ⊆ closure f → f ⊆ r := by
      intro f hf hgf
      obtain ⟨w, hwO, hwf⟩ := mem_closure_iff.mp (hgf hzg) _ isOpen_interior hzO
      refine hface f hf ⟨w, hwf, ?_⟩
      rcases interior_subset hwO with hw | hw
      · exact hw
      · have hwU : w ∈ D₂.U := by
          rw [hd.U_eq]
          exact (he.2.1 hw).1
        exact (disjoint_left.mp (hU f hf) hwf hwU).elim
    rw [card_stepsOn hrad hS hmax hE hc hg h₁ h₂ hne hall c₁ c₂]
    simp [hin f₁ h₁ c₁, hin f₂ h₂ c₂]
  have hcA : c = (stepsOn n a (A e)).card := hA.symm
  have hAe := hd.A_sub he
  have hBe := hd.B_sub he
  have hmA : m e ∈ closure (A e) := by
    have : m e ∈ closure (A e) ∩ D₂.V := by rw [hd.cap_A e he]; simp
    exact this.1
  have htwo₁ : IsTwoSided r e → c = 2 := by
    rintro ⟨w, hw, hwO⟩
    rw [hd.union e he] at hw
    rcases hw with (hw | hw) | hw
    · rw [hcA]
      exact htwo (hd.A_mem e he) hAe ⟨w, hw, hwO⟩
    · have hwm : w = m e := hw
      obtain ⟨w', hw'O, hw'⟩ := mem_closure_iff.mp (hwm ▸ hmA) _ isOpen_interior hwO
      rw [hcA]
      exact htwo (hd.A_mem e he) hAe ⟨w', hw', hw'O⟩
    · rw [hcdef, ← hB]
      exact htwo (hd.B_mem e he) hBe ⟨w, hw, hwO⟩
  have htwo₂ : c = 2 → IsTwoSided r e := by
    intro hc2
    obtain ⟨t, ht, f₁, h₁, f₂, h₂, hne, c₁, c₂, heq, hall⟩ :=
      exists_faces_region hrad hS hmax hE (hd.A_mem e he)
    rw [hcA, card_stepsOn hrad hS hmax hE hc (hd.A_mem e he) h₁ h₂ hne hall c₁ c₂] at hc2
    have hf₁ : f₁ ⊆ r := by
      by_contra h'
      simp only [h', ite_false] at hc2
      split_ifs at hc2
      all_goals omega
    have hf₂ : f₂ ⊆ r := by
      by_contra h'
      simp only [h', ite_false] at hc2
      split_ifs at hc2; omega
    obtain ⟨z, hz⟩ := (hd.A_mem e he).1
    refine ⟨z, hAe hz, ?_⟩
    have hsub : t ⊆ r ∪ e := by
      rw [heq]
      rintro w ((hw | hw) | hw)
      · exact Or.inl (hf₁ hw)
      · exact Or.inl (hf₂ hw)
      · exact Or.inr (hAe hw)
    exact interior_maximal hsub (region_isOpen ht) (heq ▸ Or.inr hz)
  have hfr : (e ∩ frontier r).Nonempty ↔ 0 < c := by
    constructor
    · rintro ⟨z, hze, hzf⟩
      rw [← hc.range_bottom] at hzf
      obtain ⟨w, rfl⟩ := hzf
      obtain ⟨i, hi, u, -, rfl⟩ := exists_circle_param hc.pos w
      have hval : h (Circle.exp (2 * Real.pi * ((i + u.1) / n)), 0) = ε i u := hc.bottom i hi u
      simp only [hval] at hze
      have hcl : ε i u ∈ closure (a i) := hc.ε_range i ▸ mem_range_self u
      obtain ⟨f, hf, hai⟩ := hd.all _ (hc.edge i)
      have hfe : f = e := by
        by_cases hV : ε i u ∈ D₂.V
        · have hVm : ε i u = m e := by
            rw [hd.V_eq] at hV
            rcases hV with hV | ⟨f', hf', hm⟩
            · exact ((he.2.1 hze).2 hV).elim
            · have : f' = e := D.edge_eq_of_mem hf' he (hm ▸ hd.mid f' hf') hze
              rw [← hm, this]
          rcases hai with hai | hai
          · have hmem : ε i u ∈ closure (A f) ∩ D₂.V := ⟨hai ▸ hcl, hd.V_eq ▸ hV⟩
            rw [hd.cap_A f hf, hVm] at hmem
            rcases hmem with h₁ | h₁
            · exact (hd.mid_notMem he (h₁ ▸ hd.x_mem f hf)).elim
            · exact (hd.mid_inj he hf h₁).symm
          · have hmem : ε i u ∈ closure (B f) ∩ D₂.V := ⟨hai ▸ hcl, hd.V_eq ▸ hV⟩
            rw [hd.cap_B f hf, hVm] at hmem
            rcases hmem with h₁ | h₁
            · exact (hd.mid_inj he hf h₁).symm
            · exact (hd.mid_notMem he ((mem_singleton_iff.mp h₁) ▸ hd.y_mem f hf)).elim
        · have hin : ε i u ∈ a i := (D₂.closure_diff_V (hc.edge i)).subset ⟨hcl, hV⟩
          rcases hai with hai | hai
          · exact D.edge_eq_of_mem hf he (hd.A_sub hf (hai ▸ hin)) hze
          · exact D.edge_eq_of_mem hf he (hd.B_sub hf (hai ▸ hin)) hze
      subst hfe
      rcases hai with hai | hai
      · rw [hcA]
        exact Finset.card_pos.mpr ⟨i, mem_stepsOn.mpr ⟨hi, hai⟩⟩
      · rw [hcdef, ← hB]
        exact Finset.card_pos.mpr ⟨i, mem_stepsOn.mpr ⟨hi, hai⟩⟩
    · intro hpos
      rw [hcA] at hpos
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
      obtain ⟨hin, hai⟩ := mem_stepsOn.mp hi
      obtain ⟨z, hz⟩ := (hc.edge i).1
      refine ⟨z, hAe (hai ▸ hz), ?_⟩
      rw [← hc.image_Ioo] at hz
      obtain ⟨u, -, rfl⟩ := hz
      rw [← hc.range_bottom, ← hc.bottom i hin u]
      exact mem_range_self _
  have hle : c ≤ 2 := by
    obtain ⟨t, ht, f₁, h₁, f₂, h₂, hne, c₁, c₂, heq, hall⟩ :=
      exists_faces_region hrad hS hmax hE (hd.A_mem e he)
    rw [hcA, card_stepsOn hrad hS hmax hE hc (hd.A_mem e he) h₁ h₂ hne hall c₁ c₂]
    split_ifs <;> simp
  by_cases h₂ : IsTwoSided r e
  · have h₃ := htwo₁ h₂
    have hnn := hfr.mpr (by omega)
    simp only [h₂, hnn, ite_true]
    exact h₃
  · simp only [h₂, ite_false]
    have hne2 : c ≠ 2 := fun h' => h₂ (htwo₂ h')
    by_cases h₃ : (e ∩ frontier r).Nonempty
    · simp only [h₃, ite_true]
      have := hfr.mp h₃
      omega
    · simp only [h₃, ite_false]
      have := mt hfr.mpr h₃
      omega

omit [T2Space S] [ConnectedSpace S] in
/-- The first vertex of the collar can be taken in the first drawing. -/
theorem exists_start (hd : SplitData D D₂ A B m x y) {H : Drawing S}
    (hc : IsHubCollar D₂ Γ' H r n v a s P ε h) :
    ∃ h', ∃ (v' : ℕ → S) (a' s' P' : ℕ → Set S) (ε' : ℕ → I → S),
      IsHubCollar D₂ Γ' H r n v' a' s' P' ε' h' ∧ v' 0 ∈ D.V ∧
      (range (fun z : Circle => h' (z, 0)) = range fun z : Circle => h (z, 0)) := by
  have hsame : v 0 ∈ D.V ∨ v 1 ∈ D.V := by
    obtain ⟨e, he, hg⟩ := hd.all _ (hc.edge 0)
    have hcap := hc.cap 0
    rcases hg with hg | hg
    · rw [hg, hd.cap_A e he] at hcap
      have : x e ∈ ({v 0, v (0 + 1)} : Set S) := hcap ▸ (by simp)
      rcases this with h₁ | h₁
      · exact Or.inl (h₁ ▸ hd.x_mem e he)
      · exact Or.inr ((mem_singleton_iff.mp h₁) ▸ hd.x_mem e he)
    · rw [hg, hd.cap_B e he] at hcap
      have : y e ∈ ({v 0, v (0 + 1)} : Set S) := hcap ▸ (by simp)
      rcases this with h₁ | h₁
      · exact Or.inl (h₁ ▸ hd.y_mem e he)
      · exact Or.inr ((mem_singleton_iff.mp h₁) ▸ hd.y_mem e he)
  rcases hsame with h₁ | h₁
  · exact ⟨h, v, a, s, P, ε, hc, h₁, rfl⟩
  · obtain ⟨h', hc', hh⟩ := hc.shift
    refine ⟨h', _, _, _, _, _, hc', h₁, ?_⟩
    rw [hc'.range_bottom, hc.range_bottom]

open Classical in
/-- **The walk around a region of a 2-cell drawing in a sphere.** The curve at the bottom of the
collar
`h` runs along a closed walk `W` around the frontier of `r`, which uses each edge once for each of
its
sides in `r`. -/
theorem exists_region_walk (hS : IsClosedSurface S) (hsph : IsSphere S)
    (hT : (PaintingOrDrawing.drawing D).IsTwoCell) (hE : D.E.Nonempty) (hr : r ∈ D.R) :
    ∃ (u : S) (W : GraphWalk D.toGraph u u) (h : C(Circle × I, S)), 0 < W.length ∧
      InjOn h {p | 0 < p.2} ∧ (∀ p : Circle × I, 0 < p.2 → h p ∈ r) ∧
      range (fun z : Circle => h (z, 0)) = frontier r ∧ IsOpen (rᶜ ∪ h '' {p | p.2 < 1}) ∧
      RunsAlongOn D (collarCurve h) 0 1 W ∧
      ∀ e ∈ D.E, edgeCount W.edges e =
        if (e ∩ frontier r).Nonempty then (if IsTwoSided r e then 2 else 1) else 0 := by
  have hne : Nonempty S := ⟨(region_nonempty hr).some⟩
  obtain ⟨D₂, A', B', m', x', y', hU, hV, hall, hevery⟩ := exists_split D
  have hd : SplitData D D₂ A' B' m' x' y' := by
    refine ⟨hU, hV, fun e he => (hall e he).1, fun e he => (hall e he).2.1,
      fun e he => (hall e he).2.2.1, fun e he => (hall e he).2.2.2.1,
      fun e he => (hall e he).2.2.2.2.1, fun e he => (hall e he).2.2.2.2.2.1,
      fun e he => (hall e he).2.2.2.2.2.2.1, fun e he => (hall e he).2.2.2.2.2.2.2.1,
      fun e he => (hall e he).2.2.2.2.2.2.2.2.1, fun e he => (hall e he).2.2.2.2.2.2.2.2.2.1,
      fun e he => (hall e he).2.2.2.2.2.2.2.2.2.2.1, fun e he => (hall e he).2.2.2.2.2.2.2.2.2.2.2,
      hevery⟩
  have hRR : D₂.R = D.R := by
    change componentsIn (univ \ D₂.U) = componentsIn (univ \ D.U)
    rw [hU]
  have hr₂ : r ∈ D₂.R := hRR ▸ hr
  have hT₂ : (PaintingOrDrawing.drawing D₂).IsTwoCell := by
    refine ⟨hT.1, fun q hq => hT.2 q (show q ∈ D.R from hRR ▸ (show q ∈ D₂.R from hq))⟩
  have hE₂ : D₂.E.Nonempty := by
    obtain ⟨e, he⟩ := hE
    exact ⟨_, hd.A_mem e he⟩
  obtain ⟨Γ'', hΓ⟩ := exists_radialDrawing hS hT₂
  have hrad : PreRad (PaintingOrDrawing.drawing D₂) Γ'' := ⟨hΓ.1, hΓ.2.1⟩
  have hmax : RadMax (PaintingOrDrawing.drawing D₂) Γ'' := hΓ.2.2
  obtain ⟨n₀, v₀, a₀, s₀, P₀, ε₀, h₀, hc₀⟩ := exists_hub_collar hrad hS hmax hsph hE₂ hd.noLoop hr₂
  obtain ⟨h₁, v₁, a₁, s₁, P₁, ε₁, hc₁, hv₁, -⟩ := exists_start hd hc₀
  obtain ⟨p', hnp, F, hF⟩ := exists_steps hd hrad hS hmax hE₂ hc₁ hv₁
  obtain ⟨W, hW, hedges⟩ := exists_collar_walk hd hc₁ hv₁ hnp hF
  have hp : 0 < p' := by
    have := hc₁.two_le
    omega
  refine ⟨_, W, h₁, ?_, hc₁.injOn, hc₁.mem_r, hc₁.range_bottom, hc₁.isOpen, hW, ?_⟩
  · simp [GraphWalk.length, hedges, hp]
  · intro e he
    rw [hedges]
    exact card_passes hd hrad hS hmax hE₂ hc₁ hr₂ hnp hF he

end GraphMinor.GM11
