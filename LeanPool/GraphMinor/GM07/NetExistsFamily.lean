/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CellFamily
public import LeanPool.GraphMinor.Surface.WordFold
public import LeanPool.GraphMinor.Surface.CutTwo

/-!
# Polygons of a cut surface

Two facts on families of polygons. A space with disjoint parts, each with a polygon, is presented by
the family of these polygons
(`presents_family`). And a family which presents `Y` also presents a quotient `S` of `Y`, when the
labels of free sides are renamed
so that sides pasted in `S` have the same label (`presents_paste`). In `GM07/NetExists.lean`, `Y` is
`S` cut along a drawing.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Metric GraphMinor.Surface

section family

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] {r : ℕ} {Z : ℕ → Set Y} {w : ℕ
  → List Letter} {g : ℕ → ℕ × ℂ → Y}

omit [T2Space Y] in
/-- **Disjoint parts.** If `Y` is the disjoint union of `Z j`, and the word `w j` presents `Z j` by
`g j`, with no label in two
words, then the family of the words presents `Y`. -/
theorem presents_family (hdisj : ∀ i j, i < r → j < r → i ≠ j → Disjoint (Z i) (Z j))
  (hcov : ∀ y, ∃ j < r, y ∈ Z j)
    (hne : ∀ j < r, w j ≠ []) (hl : ∀ i j, i < r → j < r → i ≠ j → ∀ l ∈ w i, ∀ l' ∈ w j, l.1 ≠
      l'.1)
    (hc : ∀ j < r, ContinuousOn (g j) (Dsk (sW (w j)))) (hs : ∀ j < r, g j '' Dsk (sW (w j)) = Z j)
    (he : ∀ j < r, ∀ a ∈ Dsk (sW (w j)), ∀ b ∈ Dsk (sW (w j)), g j a = g j b ↔ PRel (sW
      (w j)) a b) :
    Presents (fun i => if i < r then w i else []) (fun a => g a.1 (0, a.2)) := by
  set W : ℕ → List Letter := fun i => if i < r then w i else [] with hW
  have hWi : ∀ {i}, i < r → W i = w i := fun h => ite_eq_left h
  have hWn : ∀ {i}, W i ≠ [] → i < r := fun {i} h => by
    by_contra hi
    exact h (ite_eq_right hi)
  have hmem : ∀ {j z}, j < r → ‖z‖ ≤ 1 → ((0, z) : ℕ × ℂ) ∈ Dsk (sW (w j)) := fun {j z} hj hz =>
    ⟨by rw [sW_zero]; exact hne j hj, hz⟩
  have hmemZ : ∀ {j z}, j < r → ‖z‖ ≤ 1 → g j (0, z) ∈ Z j := fun hj hz
    => hs _ hj ▸ mem_image_of_mem _ (hmem hj hz)
  have up : ∀ {j a b}, j < r → Stp (sW (w j)) a b → Stp W (j, a.2) (j, b.2) := by
    rintro j _ _ hj ⟨i, i', p, q, k, ε, ε', t, h1, h2, h3, ht, rfl, rfl⟩
    obtain ⟨rfl, h4⟩ := sW_get h1
    obtain ⟨rfl, h5⟩ := sW_get h2
    refine ⟨j, j, p, q, k, ε, ε', t, by rw [hWi hj]; exact h4, by rw [hWi hj]; exact h5, ?_, ht,
      ?_, ?_⟩
    · intro h
      exact h3 (by rw [(Prod.mk.inj h).2])
    · simp only [sW_zero, hWi hj]
    · simp only [sW_zero, hWi hj]
  have upR : ∀ {j a b}, j < r → PRel (sW (w j)) a b → PRel W (j, a.2) (j, b.2) := by
    intro j a b hj h
    induction h with
    | rel _ _ h => exact .rel _ _ (up hj h)
    | refl _ => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ h1 h2 => exact .trans _ _ _ h1 h2
  have down : ∀ {a b}, Stp W a b → g a.1 (0, a.2) = g b.1 (0, b.2) := by
    rintro _ _ ⟨i, j, p, q, k, ε, ε', t, h1, h2, h3, ht, rfl, rfl⟩
    have hi : i < r := hWn fun h => by simp [h] at h1
    have hj : j < r := hWn fun h => by simp [h] at h2
    rw [hWi hi] at h1
    rw [hWi hj] at h2
    obtain rfl : i = j := by
      by_contra hij
      exact hl i j hi hj hij _ (List.mem_of_getElem? h1) _ (List.mem_of_getElem? h2) rfl
    have h4 : Stp (sW (w i)) (0, sdPt (w i).length p ε t) (0, sdPt (w i).length q ε' t) :=
      ⟨0, 0, p, q, k, ε, ε', t, by rw [sW_zero]; exact h1, by rw [sW_zero]; exact h2, fun h => h3
        (by rw [(Prod.mk.inj h).2]), ht,
        by simp only [sW_zero], by simp only [sW_zero]⟩
    simp only [hWi hi]
    exact (he i hi _ h4.mem_Dsk.1 _ h4.mem_Dsk.2).mpr (.rel _ _ h4)
  have downR : ∀ {a b}, PRel W a b → g a.1 (0, a.2) = g b.1 (0, b.2) := by
    intro a b h
    induction h with
    | rel _ _ h => exact down h
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ h1 h2 => exact h1.trans h2
  refine ⟨continuousOn_slots fun i hi => ?_, ?_, fun a ha b hb => ⟨fun hab => ?_, downR⟩⟩
  · have hi' := hWn hi
    refine (hc i hi').comp (f := fun z : ℂ => ((0 : ℕ), z)) (by fun_prop) fun z hz => hmem hi'
      (by simpa using hz)
  · refine eq_univ_of_forall fun y => ?_
    obtain ⟨j, hj, hy⟩ := hcov y
    rw [← hs j hj] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨h1, -, h3⟩ := mem_Dsk_sW ha
    refine ⟨(j, a.2), ⟨by simp only [hWi hj]; exact hne j hj, h3⟩, ?_⟩
    have : a = (0, a.2) := Prod.ext h1 rfl
    simp only
    rw [← this]
  · obtain ⟨i, z⟩ := a
    obtain ⟨i', z'⟩ := b
    have hi := hWn ha.1
    have hi' := hWn hb.1
    have h1 := hmemZ hi ha.2
    have h2 := hmemZ hi' hb.2
    simp only at hab
    obtain rfl : i = i' := by
      by_contra hne'
      exact Set.disjoint_left.mp (hdisj i i' hi hi' hne') h1 (hab ▸ h2)
    exact upR (a := (0, z)) (b := (0, z')) hi ((he i hi _ (hmem hi ha.2) _ (hmem hi hb.2)).mp hab)

end family

/-- A letter under a change of sign `s`. -/
def netFl (s ε : Bool) : Bool := if s then ε else !ε

theorem sdPt_netFl (n p : ℕ) (s ε : Bool) (t : ℝ) : sdPt n p (netFl s ε) t = sdPt n p ε (ofs s t)
  := by
  cases s <;> cases ε <;> simp [netFl, sdPt, ofs]

/-- Rename each label `k` to `(R k).1` and change its sign by `(R k).2`. -/
def netW (R : ℕ → ℕ × Bool) (W : ℕ → List Letter) : ℕ → List Letter :=
  fun i => (W i).map fun l => ((R l.1).1, netFl (R l.1).2 l.2)

theorem netW_length (R : ℕ → ℕ × Bool) (W : ℕ → List Letter) (i : ℕ) : (netW R W i).length =
  (W i).length := by
  simp [netW]

theorem dsk_netW (R : ℕ → ℕ × Bool) (W : ℕ → List Letter) : Dsk (netW R W) = Dsk W := by
  ext a
  simp [Dsk, netW]

theorem netW_get {R : ℕ → ℕ × Bool} {W : ℕ → List Letter} {i p k : ℕ} {e : Bool} (h : (W i)[p]?
  = some (k, e)) :
    (netW R W i)[p]? = some ((R k).1, netFl (R k).2 e) := by
  simp [netW, h]

theorem netW_get' {R : ℕ → ℕ × Bool} {W : ℕ → List Letter} {i p K : ℕ} {ε : Bool} (h :
  (netW R W i)[p]? = some (K, ε)) :
    ∃ k e, (W i)[p]? = some (k, e) ∧ (R k).1 = K ∧ netFl (R k).2 e = ε := by
  simp only [netW, List.getElem?_map, Option.map_eq_some_iff, Prod.mk.injEq, Prod.exists] at h
  obtain ⟨k, e, h1, h2, h3⟩ := h
  exact ⟨k, e, h1, h2, h3⟩

section paste

variable {Y S : Type*} [TopologicalSpace Y] [TopologicalSpace S] {W : ℕ → List Letter} {g : ℕ × ℂ
  → Y} {ψ : Y → S} {R : ℕ → ℕ × Bool}

/-- **Pasting free sides.** Let `W` present `Y`, and let `ψ` be a quotient map onto `S`. Rename
labels so that two different labels get
one new label only if their sides agree in `S`, and suppose that the new steps and the points of `Y`
generate all fibres of `ψ`. Then the
new family presents `S`. -/
theorem presents_paste (hg : Presents W g) (hψ : Continuous ψ) (hsurj : Function.Surjective ψ)
    (hmatch : ∀ i j p q k k' e e' (t : ℝ), (W i)[p]? = some (k, e) → (W j)[q]? = some (k', e')
      → k ≠ k' → (R k).1 = (R k').1 → t ∈ Icc (0 : ℝ) 1 →
      ψ (g (i, sdPt (W i).length p (netFl (R k).2 e) t)) = ψ (g (j, sdPt (W j).length q (netFl
        (R k').2 e') t)))
    (hfib : ∀ y y', ψ y = ψ y' → Relation.EqvGen (fun u v => u = v ∨ ∃ a b, g a = u ∧ g b = v ∧ Stp
      (netW R W) a b) y y') :
    Presents (netW R W) (ψ ∘ g) := by
  have hDs := dsk_netW R W
  have hSt : ∀ a b, Stp W a b → Stp (netW R W) a b := by
    rintro _ _ ⟨i, j, p, q, k, ε, ε', t, h1, h2, h3, ht, rfl, rfl⟩
    have ht' : ofs (R k).2 t ∈ Icc (0 : ℝ) 1 := ofs_mem ht
    refine ⟨i, j, p, q, _, _, _, ofs (R k).2 t, netW_get h1, netW_get h2, h3, ht', ?_, ?_⟩
    · rw [netW_length, sdPt_netFl, ofs_ofs]
    · rw [netW_length, sdPt_netFl, ofs_ofs]
  have hPR : ∀ a b, PRel W a b → PRel (netW R W) a b := by
    intro a b h
    induction h with
    | rel _ _ h => exact .rel _ _ (hSt _ _ h)
    | refl _ => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ h1 h2 => exact .trans _ _ _ h1 h2
  have hSt' : ∀ a b, Stp (netW R W) a b → ψ (g a) = ψ (g b) := by
    rintro _ _ ⟨i, j, p, q, K, ε, ε', t, h1, h2, h3, ht, rfl, rfl⟩
    obtain ⟨k, e, h4, h5, rfl⟩ := netW_get' h1
    obtain ⟨k', e', h6, h7, rfl⟩ := netW_get' h2
    rw [netW_length, netW_length]
    by_cases hk : k = k'
    · subst hk
      have h8 : Stp W (i, sdPt (W i).length p e (ofs (R k).2 t)) (j, sdPt (W j).length q e' (ofs
        (R k).2 t)) :=
        ⟨i, j, p, q, k, e, e', _, h4, h6, h3, ofs_mem ht, rfl, rfl⟩
      rw [sdPt_netFl, sdPt_netFl]
      exact congrArg ψ ((hg.2.2 _ h8.mem_Dsk.1 _ h8.mem_Dsk.2).mpr (.rel _ _ h8))
    · exact hmatch i j p q k k' e e' t h4 h6 hk (h5.trans h7.symm) ht
  have hdown : ∀ a b, PRel (netW R W) a b → ψ (g a) = ψ (g b) := by
    intro a b h
    induction h with
    | rel _ _ h => exact hSt' _ _ h
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ h1 h2 => exact h1.trans h2
  have key : ∀ y y', Relation.EqvGen (fun u v => u = v ∨ ∃ a b, g a = u ∧ g b = v ∧ Stp
    (netW R W) a b) y y' →
      ∀ a ∈ Dsk W, ∀ b ∈ Dsk W, g a = y → g b = y' → PRel (netW R W) a b := by
    intro y y' h
    induction h with
    | rel y y' h =>
      intro a ha b hb hay hby
      rcases h with rfl | ⟨a', b', h1, h2, h3⟩
      · exact hPR _ _ ((hg.2.2 a ha b hb).mp (hay.trans hby.symm))
      · have h4 := h3.mem_Dsk
        rw [hDs] at h4
        exact .trans _ _ _ (hPR _ _ ((hg.2.2 a ha a' h4.1).mp (hay.trans h1.symm)))
          (.trans _ _ _ (.rel _ _ h3) (hPR _ _ ((hg.2.2 b' h4.2 b hb).mp (h2.trans hby.symm))))
    | refl y =>
      intro a ha b hb hay hby
      exact hPR _ _ ((hg.2.2 a ha b hb).mp (hay.trans hby.symm))
    | symm y y' _ ih =>
      intro a ha b hb hay hby
      exact .symm _ _ (ih b hb a ha hby hay)
    | trans y y' y'' _ _ h1 h2 =>
      intro a ha b hb hay hby
      obtain ⟨c, hc, rfl⟩ : y' ∈ g '' Dsk W := by
        rw [hg.2.1]
        exact mem_univ _
      exact .trans _ _ _ (h1 a ha c hc hay rfl) (h2 c hc b hb rfl hby)
  refine ⟨?_, ?_, fun a ha b hb => ?_⟩
  · rw [hDs]
    exact hψ.comp_continuousOn hg.1
  · rw [hDs, image_comp, hg.2.1, image_univ, hsurj.range_eq]
  · rw [hDs] at ha hb
    exact ⟨fun h => key _ _ (hfib _ _ h) a ha b hb rfl rfl, hdown a b⟩

end paste

end GraphMinor.GM07
