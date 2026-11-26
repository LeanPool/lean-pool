/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.ModelHomeo
public import LeanPool.GraphMinor.Surface.WordSurface

/-!
# The normal word of a model surface

`ew a b c` is the normal form word of the model surface $\Sigma(a, b, c)$ with two more sides `x
x⁻¹` at the end. So it
is never empty. We give its letters by a formula (`ew_get`), and each model surface is presented by
this word
(`presents_ew`). So the model surfaces are surfaces (`isSurface_model`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Function

/-- The label of the side `j`. -/
def lab (a b c j : ℕ) : ℕ :=
  if j < 4 * a then 2 * (j / 4) + (j % 4) % 2
  else if j < 4 * a + 2 * b then 2 * a + (j - 4 * a) / 2
  else if j < 4 * a + 2 * b + 3 * c then
    2 * a + b + 2 * ((j - (4 * a + 2 * b)) / 3) + ((j - (4 * a + 2 * b)) % 3) % 2
  else 2 * a + b + 2 * c

/-- The sign of the side `j`. -/
def sgn (a b c j : ℕ) : Bool :=
  if j < 4 * a then decide (j % 4 < 2)
  else if j < 4 * a + 2 * b then true
  else if j < 4 * a + 2 * b + 3 * c then decide ((j - (4 * a + 2 * b)) % 3 < 2)
  else decide (j = 4 * a + 2 * b + 3 * c)

/-- The normal word with two more sides. -/
def ew (a b c : ℕ) : List Letter := nfW a b c ++ [(2 * a + b + 2 * c, true),
  (2 * a + b + 2 * c, false)]

theorem hW_length (k a : ℕ) : (hW k a).length = 4 * a := by
  induction a generalizing k with
  | zero => rfl
  | succ a ih => simp [hW, hndB, ih]; omega

theorem cW_length (k a : ℕ) : (cW k a).length = 2 * a := by
  induction a generalizing k with
  | zero => rfl
  | succ a ih => simp [cW, ih]; omega

theorem tW_length (k a : ℕ) : (tW k a).length = 3 * a := by
  induction a generalizing k with
  | zero => rfl
  | succ a ih => simp [tW, holB, ih]; omega

theorem hW_get (a : ℕ) : ∀ k j, j < 4 * a → (hW k a)[j]? = some (k + 2 * (j / 4) +
  (j % 4) % 2, decide (j % 4 < 2)) := by
  induction a with
  | zero => intro k j h; omega
  | succ a ih =>
    intro k j hj
    by_cases h : j < 4
    · interval_cases j <;> simp [hW, hndB, linv]
    · have hlen : (hndB (k, true) (k + 1, true)).length = 4 := rfl
      rw [hW, List.getElem?_append_right (by rw [hlen]; omega), hlen, ih _ _ (by omega)]
      have e1 : k + 2 + 2 * ((j - 4) / 4) + (j - 4) % 4 % 2 = k + 2 * (j / 4) + j % 4 % 2 := by
        omega
      have e2 : ((j - 4) % 4 < 2) ↔ (j % 4 < 2) := by omega
      rw [e1, decide_eq_decide.mpr e2]

theorem cW_get (a : ℕ) : ∀ k j, j < 2 * a → (cW k a)[j]? = some (k + j / 2, true) := by
  induction a with
  | zero => intro k j h; omega
  | succ a ih =>
    intro k j hj
    by_cases h : j < 2
    · interval_cases j <;> simp [cW]
    · have hlen : ([(k, true), (k, true)] : List Letter).length = 2 := rfl
      rw [cW, List.getElem?_append_right (by rw [hlen]; omega), hlen, ih _ _ (by omega)]
      congr 2
      omega

theorem tW_get (a : ℕ) : ∀ k j, j < 3 * a → (tW k a)[j]? = some (k + 2 * (j / 3) +
  (j % 3) % 2, decide (j % 3 < 2)) := by
  induction a with
  | zero => intro k j h; omega
  | succ a ih =>
    intro k j hj
    by_cases h : j < 3
    · interval_cases j <;> simp [tW, holB, linv]
    · have hlen : (holB (k, true) (k + 1, true)).length = 3 := rfl
      rw [tW, List.getElem?_append_right (by rw [hlen]; omega), hlen, ih _ _ (by omega)]
      have e1 : k + 2 + 2 * ((j - 3) / 3) + (j - 3) % 3 % 2 = k + 2 * (j / 3) + j % 3 % 2 := by
        omega
      have e2 : ((j - 3) % 3 < 2) ↔ (j % 3 < 2) := by omega
      rw [e1, decide_eq_decide.mpr e2]

theorem ew_length (a b c : ℕ) : (ew a b c).length = 4 * a + 2 * b + 3 * c + 2 := by
  simp [ew, nfW, hW_length, cW_length, tW_length]
  omega

theorem ew_get (a b c : ℕ) {j : ℕ} (hj : j < 4 * a + 2 * b + 3 * c + 2) : (ew a b c)[j]? = some
  (lab a b c j, sgn a b c j) := by
  have h1 := hW_length 0 a
  have h2 := cW_length (2 * a) b
  have h3 := tW_length (2 * a + b) c
  unfold ew nfW lab sgn
  simp only [List.append_assoc]
  by_cases j1 : j < 4 * a
  · rw [List.getElem?_append_left (by omega), hW_get a 0 j j1]
    simp [j1]
  rw [List.getElem?_append_right (by omega), h1, ite_eq_right j1, ite_eq_right j1]
  by_cases j2 : j < 4 * a + 2 * b
  · rw [List.getElem?_append_left (by omega), cW_get b _ _ (by omega)]
    simp [j2]
  rw [List.getElem?_append_right (by omega), h2, ite_eq_right j2, ite_eq_right j2]
  by_cases j3 : j < 4 * a + 2 * b + 3 * c
  · rw [List.getElem?_append_left (by omega), tW_get c _ _ (by omega)]
    simp only [j3, ite_true]
    have e1 : j - 4 * a - 2 * b = j - (4 * a + 2 * b) := by omega
    rw [e1]
  rw [List.getElem?_append_right (by omega), h3, ite_eq_right j3, ite_eq_right j3]
  have e : j = 4 * a + 2 * b + 3 * c ∨ j = 4 * a + 2 * b + 3 * c + 1 := by omega
  rcases e with rfl | rfl
  · have e1 : 4 * a + 2 * b + 3 * c - 4 * a - 2 * b - 3 * c = 0 := by omega
    simp [e1]
  · have e1 : 4 * a + 2 * b + 3 * c + 1 - 4 * a - 2 * b - 3 * c = 1 := by omega
    simp [e1]

theorem ew_get_iff (a b c p k : ℕ) (e : Bool) : (ew a b c)[p]? = some (k, e) ↔
    p < 4 * a + 2 * b + 3 * c + 2 ∧ lab a b c p = k ∧ sgn a b c p = e := by
  constructor
  · intro h
    have hp : p < (ew a b c).length := (List.getElem?_eq_some_iff.mp h).1
    rw [ew_length] at hp
    rw [ew_get a b c hp] at h
    obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨hp, h1, h2⟩
  · rintro ⟨h1, rfl, rfl⟩
    exact ew_get a b c h1

/-- The other side with the same label. A free side is its own twin. -/
def twin (a b c p : ℕ) : ℕ :=
  if p < 4 * a then (if p % 4 < 2 then p + 2 else p - 2)
  else if p < 4 * a + 2 * b then (if (p - 4 * a) % 2 = 0 then p + 1 else p - 1)
  else if p < 4 * a + 2 * b + 3 * c then
    (if (p - (4 * a + 2 * b)) % 3 = 0 then p + 2 else if (p - (4 * a + 2 * b)) % 3
      = 2 then p - 2 else p)
  else if p = 4 * a + 2 * b + 3 * c then p + 1 else p - 1

theorem lab_two {a b c p q : ℕ} (hp : p < 4 * a + 2 * b + 3 * c + 2) (hq : q < 4 * a + 2 * b + 3 *
  c + 2)
    (h1 : lab a b c p = lab a b c q) : q = p ∨ q = twin a b c p := by
  unfold lab at h1
  unfold twin
  by_cases h2 : p < 4 * a
  · have h3 : q < 4 * a := by
      by_contra hc
      split_ifs at h1 <;> omega
    simp only [h2, h3, ite_true] at h1 ⊢
    split_ifs <;> omega
  by_cases h4 : p < 4 * a + 2 * b
  · have h3 : ¬ q < 4 * a := by
      intro hc
      split_ifs at h1; omega
    have h5 : q < 4 * a + 2 * b := by
      by_contra hc
      split_ifs at h1 <;> omega
    simp only [h2, h3, h4, h5, ite_true, ite_false] at h1 ⊢
    split_ifs <;> omega
  by_cases h6 : p < 4 * a + 2 * b + 3 * c
  · have h3 : ¬ q < 4 * a := by
      intro hc
      split_ifs at h1; omega
    have h5 : ¬ q < 4 * a + 2 * b := by
      intro hc
      split_ifs at h1; omega
    have h7 : q < 4 * a + 2 * b + 3 * c := by
      by_contra hc
      simp only [h2, h3, h4, h5, h6, hc, ite_true, ite_false] at h1
      omega
    simp only [h2, h3, h4, h5, h6, h7, ite_true, ite_false] at h1 ⊢
    obtain ⟨x, rfl⟩ : ∃ x, p = 4 * a + 2 * b + x := ⟨p - (4 * a + 2 * b), by omega⟩
    obtain ⟨y, rfl⟩ : ∃ y, q = 4 * a + 2 * b + y := ⟨q - (4 * a + 2 * b), by omega⟩
    simp only [Nat.add_sub_cancel_left] at h1 ⊢
    split_ifs <;> omega
  · have h3 : ¬ q < 4 * a := by
      intro hc
      split_ifs at h1; omega
    have h5 : ¬ q < 4 * a + 2 * b := by
      intro hc
      split_ifs at h1; omega
    have h7 : ¬ q < 4 * a + 2 * b + 3 * c := by
      intro hc
      simp only [h2, h3, h4, h5, h6, hc, ite_true, ite_false] at h1
      obtain ⟨y, rfl⟩ : ∃ y, q = 4 * a + 2 * b + y := ⟨q - (4 * a + 2 * b), by omega⟩
      simp only [Nat.add_sub_cancel_left] at h1
      omega
    simp only [h2, h4, h6, ite_false]
    split_ifs <;> omega

theorem twin_lt {a b c p : ℕ} (hp : p < 4 * a + 2 * b + 3 * c + 2) : twin a b c p < 4 * a + 2 * b +
  3 * c + 2 := by
  unfold twin
  split_ifs <;> omega

theorem lab_twin {a b c p : ℕ} (hp : p < 4 * a + 2 * b + 3 * c + 2) : lab a b c (twin a b c p)
  = lab a b c p := by
  unfold twin lab
  split_ifs <;> first | rfl | omega

theorem lab_three {a b c p q r : ℕ} (hp : p < 4 * a + 2 * b + 3 * c + 2)
  (hq : q < 4 * a + 2 * b + 3 * c + 2)
    (hr : r < 4 * a + 2 * b + 3 * c + 2) (h1 : lab a b c p = lab a b c q) (h2 : lab a b c q
      = lab a b c r) :
    p = q ∨ q = r ∨ p = r := by
  rcases lab_two hp hq h1 with h3 | h3
  · exact .inl h3.symm
  · rcases lab_two hp hr (h1.trans h2) with h4 | h4
    · exact .inr (.inr h4.symm)
    · exact .inr (.inl (h3.trans h4.symm))

theorem encard_le_two_of {α : Type*} {S : Set α} (h : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x = y ∨ y = z ∨ x
  = z) :
    S.encard ≤ 2 := by
  classical
  by_cases h0 : S = ∅
  · simp [h0]
  obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr h0
  by_cases h1 : S ⊆ {x}
  · refine (encard_le_encard h1).trans ?_
    rw [encard_singleton]
    norm_num
  obtain ⟨y, hy, hne⟩ := not_subset.mp h1
  have hs : S ⊆ {x, y} := fun z hz => by
    rcases h x hx y hy z hz with h2 | h2 | h2
    · exact absurd h2.symm hne
    · exact .inr h2.symm
    · exact .inl h2.symm
  refine (encard_le_encard hs).trans ((encard_insert_le _ _).trans ?_)
  rw [encard_singleton]
  norm_num

theorem sW_get {w : List Letter} {i p : ℕ} {l : Letter} (h : (sW w i)[p]? = some l) : i = 0 ∧ w[p]?
  = some l := by
  by_cases hi : i = 0
  · subst hi
    simpa [sW] using h
  · simp [sW, hi, nW] at h

theorem sW_zero (w : List Letter) : sW w 0 = w := by simp [sW]

theorem isPaired_ew (a b c : ℕ) : IsPaired (sW (ew a b c)) := by
  intro k
  refine encard_le_two_of ?_
  rintro ⟨i, p⟩ ⟨e, hp⟩ ⟨i', q⟩ ⟨e', hq⟩ ⟨i'', r⟩ ⟨e'', hr⟩
  obtain ⟨rfl, h1⟩ := sW_get hp
  obtain ⟨rfl, h2⟩ := sW_get hq
  obtain ⟨rfl, h3⟩ := sW_get hr
  obtain ⟨h4, h5, -⟩ := (ew_get_iff _ _ _ _ _ _).mp h1
  obtain ⟨h6, h7, -⟩ := (ew_get_iff _ _ _ _ _ _).mp h2
  obtain ⟨h8, h9, -⟩ := (ew_get_iff _ _ _ _ _ _).mp h3
  rcases lab_three h4 h6 h8 (h5.trans h7.symm) (h7.trans h9.symm) with rfl | rfl | rfl <;> simp

theorem presents_comp {W : ℕ → List Letter} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {f : ℕ × ℂ → X}
    (hf : Presents W f) (e : X ≃ₜ Y) : Presents W (e ∘ f) := by
  refine ⟨e.continuous.comp_continuousOn hf.1, ?_, fun a ha b hb => ?_⟩
  · rw [image_comp, hf.2.1]
    exact e.surjective.range_eq ▸ image_univ
  · simp only [Function.comp, e.injective.eq_iff]
    exact hf.2.2 a ha b hb

theorem nfW_noLab (a b c : ℕ) : NoLab (nfW a b c) (2 * a + b + 2 * c) := by
  intro l hl
  simp only [nfW, List.mem_append] at hl
  rcases hl with (hl | hl) | hl
  · have := hW_labels _ _ l hl
    omega
  · have := cW_labels _ _ l hl
    omega
  · have := tW_labels _ _ l hl
    omega

theorem nfW_length (a b c : ℕ) : (nfW a b c).length = 4 * a + 2 * b + 3 * c := by
  simp [nfW, hW_length, cW_length, tW_length]
  omega

theorem peq_modelW_ew (a b c : ℕ) : PEq.{0} (modelW a b (2 * a + b + c)) (sW (ew a b c)) := by
  obtain ⟨w, h1, h2⟩ := exists_modelW_nf.{0} a b c
  rcases h2 with ⟨h2, hne⟩ | ⟨hn, rfl⟩
  · have h3 : WEq.{0} w (nfW a b c) := nf_eq h2 (isNF_nfW a b c)
    have hne' : nfW a b c ≠ [] := by
      intro he
      have := nfW_length a b c
      rw [he] at this
      simp only [List.length_nil] at this
      omega
    have h4 : WEq.{0} (nfW a b c) ([(2 * a + b + 2 * c, true), (2 * a + b + 2 * c, false)] ++ nfW a
      b c) :=
      peq_fold finW_nW true hne' (freshIn_sW (nfW_noLab a b c))
    exact h1.trans (h3.trans (h4.trans (WEq.rot _ _)))
  · have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    have hc : c = 0 := by omega
    subst ha hb hc
    refine h1.trans ?_
    exact WEq.rot [linv (segL 0)] [segL 0]

theorem ew_mem_dsk (a b c : ℕ) : ((0 : ℕ), (0 : ℂ)) ∈ Dsk (sW (ew a b c)) := by
  refine ⟨?_, by simp⟩
  rw [sW_zero]
  intro he
  have := ew_length a b c
  rw [he] at this
  simp at this

/-- A model surface is Hausdorff and presented by the word `ew`. -/
theorem presents_ew (a b c : ℕ) : T2Space (SurfaceModel a b c) ∧
    ∃ f : ℕ × ℂ → SurfaceModel a b c, Presents (sW (ew a b c)) f := by
  have h0 : (Dsk (sW (ew a b c))).Nonempty := ⟨_, ew_mem_dsk a b c⟩
  have ht := t2Space_wordSpace (finW_sW (ew a b c)) (isPaired_ew a b c)
  have hp := presents_wordMap h0
  obtain ⟨g, hg⟩ := (peq_modelW_ew a b c (WordSpace (sW (ew a b c)))).mpr ⟨wordMap h0, hp⟩
  obtain ⟨e⟩ := model_homeo a b c hg
  refine ⟨e.symm.isEmbedding.t2Space, e ∘ wordMap h0, presents_comp hp e⟩

/-- The model surfaces are connected surfaces. -/
theorem isSurface_model (a b c : ℕ) : IsSurface (SurfaceModel a b c) ∧ ConnectedSpace
  (SurfaceModel a b c) := by
  obtain ⟨ht, f, hf⟩ := presents_ew a b c
  have := ht
  refine ⟨(surface_of_presents (finW_sW _) (isPaired_ew a b c) hf).1, ?_⟩
  have hsub : ∀ z : ℂ, z ∈ Metric.closedBall (0 : ℂ) 1 → ((0 : ℕ), z) ∈ Dsk (sW (ew a b c))
    := fun z hz =>
    ⟨(ew_mem_dsk a b c).1, by simpa using hz⟩
  have hc : ContinuousOn (fun z : ℂ => f (0, z)) (Metric.closedBall 0 1) := hf.1.comp
    (by fun_prop) hsub
  have himg : (fun z : ℂ => f (0, z)) '' Metric.closedBall 0 1 = univ := by
    refine eq_univ_of_forall fun y => ?_
    have h1 : y ∈ f '' Dsk (sW (ew a b c)) := by
      rw [hf.2.1]
      exact mem_univ y
    obtain ⟨⟨i, z⟩, hz, rfl⟩ := h1
    have hi : i = 0 := by
      by_contra hi
      exact hz.1 (by simp [sW, hi, nW])
    subst hi
    exact ⟨z, by simpa using hz.2, rfl⟩
  have h3 : IsPreconnected (univ : Set (SurfaceModel a b c)) := by
    rw [← himg]
    exact (convex_closedBall (0 : ℂ) 1).isPreconnected.image _ hc
  exact { toPreconnectedSpace := ⟨h3⟩, toNonempty := ⟨f (0, 0)⟩ }

end GraphMinor.Surface
