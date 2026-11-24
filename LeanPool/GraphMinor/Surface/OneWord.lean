/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CellFamily

/-!
# From a family of words to one word

A connected space presented by a family of words, with each label used at most twice, is presented
by one word
(`exists_one_word`). While there is more than one word, connectedness gives a label shared by the
first word and
another one, and we glue the two polygons along that label.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Function

universe u uu

theorem peq_self_rot {W : ℕ → List Letter} (hW : FinW W) (i : ℕ) {a b : List Letter} (h : W i
  = a ++ b) :
    PEq.{uu} W (update W i (b ++ a)) := by
  have := peq_rot.{uu} hW i a b
  rwa [← h, update_eq_self] at this

theorem merge_opp {W : ℕ → List Letter} (hW : FinW W) {j k : ℕ} (hj : j ≠ 0) {e : Bool} {a b c d :
  List Letter}
    (h0 : W 0 = a ++ (k, e) :: b) (h1 : W j = c ++ (k, !e) :: d) (hu : b ++ a ≠ [])
      (hv : d ++ c ≠ [])
    (hab : NoLab (b ++ a) k) (hcd : NoLab (d ++ c) k) (hoth : ∀ i, i ≠ 0 → i ≠ j → NoLab (W i) k) :
    PEq.{uu} W (update (update W j []) 0 (d ++ c ++ (b ++ a))) := by
  have s1 : PEq.{uu} W (update W 0 ((k, e) :: b ++ a)) := by
    simpa using peq_self_rot.{uu} hW 0 h0
  have hW1 : FinW (update W 0 ((k, e) :: b ++ a)) := hW.update _ _
  have s2 : PEq.{uu} (update W 0 ((k, e) :: b ++ a))
      (update (update W 0 ((k, e) :: b ++ a)) j ((k, !e) :: d ++ c)) := by
    have h1' : update W 0 ((k, e) :: b ++ a) j = c ++ (k, !e) :: d := by rw [update_of_ne hj, h1]
    simpa using peq_self_rot.{uu} hW1 j h1'
  have hW0 : FinW (update W j []) := hW.update _ _
  have e2 : update (update W 0 ((k, e) :: b ++ a)) j ((k, !e) :: d ++ c) =
      update (update (update W j []) 0 ((k, e) :: (b ++ a))) j ((k, !e) :: (d ++ c)) := by
    funext i
    by_cases hi : i = j
    · subst hi
      simp
    · by_cases hi0 : i = 0
      · subst hi0
        simp [update_of_ne hi]
      · simp [update_of_ne hi, update_of_ne hi0]
  have s3 := peq_cut.{uu} (W := update W j []) (i := 0) (j := j) (y := k) (u := b ++ a) (v
    := d ++ c) hW0 e hj
    (by simp) hu hv (by
      intro i l hl
      by_cases hi0 : i = 0
      · subst hi0
        rw [update_self] at hl
        exact (noLab_append.mpr ⟨hcd, hab⟩) l hl
      · rw [update_of_ne hi0] at hl
        by_cases hi : i = j
        · subst hi
          simp at hl
        · rw [update_of_ne hi] at hl
          exact hoth i hi0 hi l hl)
  rw [e2] at s2
  exact s1.trans (s2.trans s3.symm)

theorem noLab_of_cnt {w : List Letter} {c : ℕ} (h : cnt w c = 0) : NoLab w c := by
  intro l hl he
  have := cnt_pos (w := w) (l := l) hl
  rw [he, h] at this
  exact lt_irrefl _ this

/-- Glue the word at `j` to the first word along the label `k`. -/
theorem merge_step {W : ℕ → List Letter} (hW : FinW W) {j k : ℕ} (hj : j ≠ 0) {e e' : Bool}
    (h0 : (k, e) ∈ W 0) (h1 : (k, e') ∈ W j) (c0 : cnt (W 0) k = 1) (c1 : cnt (W j) k = 1)
    (hoth : ∀ i, i ≠ 0 → i ≠ j → cnt (W i) k = 0) (l0 : 2 ≤ (W 0).length) (l1 : 2 ≤ (W j).length) :
    ∃ w, PEq.{uu} W (update (update W j []) 0 w) ∧ 2 ≤ w.length ∧ ∀ c, cnt w c ≤ cnt (W 0) c + cnt
      (W j) c := by
  have key : ∀ (W : ℕ → List Letter), FinW W → (k, !e) ∈ W j → (k, e) ∈ W 0 → cnt (W 0) k = 1 → cnt
    (W j) k = 1 →
      (∀ i, i ≠ 0 → i ≠ j → cnt (W i) k = 0) → 2 ≤ (W 0).length → 2 ≤ (W j).length →
      ∃ w, PEq.{uu} W (update (update W j []) 0 w) ∧ 2 ≤ w.length ∧ ∀ c, cnt w c ≤ cnt
        (W 0) c + cnt (W j) c := by
    intro W hW h1 h0 c0 c1 hoth l0 l1
    obtain ⟨a, b, ha⟩ := List.append_of_mem h0
    obtain ⟨c, d, hc⟩ := List.append_of_mem h1
    have hc0 : cnt (b ++ a) k = 0 := by
      have h2 : cnt a k + (1 + cnt b k) = 1 := by simpa [ha, cnt_append, cnt_cons] using c0
      rw [cnt_append]
      omega
    have hc1 : cnt (d ++ c) k = 0 := by
      have h2 : cnt c k + (1 + cnt d k) = 1 := by simpa [hc, cnt_append, cnt_cons] using c1
      rw [cnt_append]
      omega
    have hl0 : 1 ≤ (b ++ a).length := by
      rw [ha] at l0
      simp at l0 ⊢
      omega
    have hl1 : 1 ≤ (d ++ c).length := by
      rw [hc] at l1
      simp at l1 ⊢
      omega
    refine ⟨d ++ c ++ (b ++ a), merge_opp hW hj ha hc (fun h => by simp [h] at hl0)
      (fun h => by simp [h] at hl1) (noLab_of_cnt hc0) (noLab_of_cnt hc1) (fun i h h'
        => noLab_of_cnt (hoth i h h')),
      ?_, fun x => ?_⟩
    · simp only [List.length_append] at hl0 hl1 ⊢
      omega
    · rw [ha, hc]
      simp only [cnt_append, cnt_cons]
      split_ifs <;> omega
  by_cases he : e' = !e
  · subst he
    exact key W hW h1 h0 c0 c1 hoth l0 l1
  · have he' : e' = e := by
      cases e <;> cases e' <;> simp_all
    subst he'
    have s0 : PEq.{uu} W (update W j (winv (W j))) := by
      have := peq_rev.{uu} hW j (W j)
      rwa [update_eq_self] at this
    have hmem : (k, !e') ∈ winv (W j) := by
      have : linv (k, e') ∈ winv (W j) := by
        simp only [winv, List.mem_reverse, List.mem_map]
        exact ⟨_, h1, rfl⟩
      simpa [linv] using this
    obtain ⟨w, h2, h3, h4⟩ := key (update W j (winv (W j))) (hW.update _ _) (by simpa using hmem)
      (by rwa [update_of_ne hj.symm]) (by rwa [update_of_ne hj.symm]) (by simpa [cnt_winv] using c1)
      (fun i h h' => by rw [update_of_ne h']; exact hoth i h h') (by rwa [update_of_ne hj.symm])
      (by simpa [winv] using l1)
    refine ⟨w, s0.trans ?_, h3, fun c => ?_⟩
    · simpa using h2
    · have := h4 c
      simpa [update_of_ne hj.symm, cnt_winv] using this

variable {X : Type u} [TopologicalSpace X] [T2Space X]

/-- A connected space gives a label shared by the first word and another word. -/
theorem exists_shared [ConnectedSpace X] {W : ℕ → List Letter} {f : ℕ × ℂ → X} (hW : FinW W)
  (hf : Presents W f)
    (h0 : W 0 ≠ []) {j₀ : ℕ} (hj₀ : j₀ ≠ 0) (hne : W j₀ ≠ []) :
    ∃ j k e e', j ≠ 0 ∧ (k, e) ∈ W 0 ∧ (k, e') ∈ W j := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hc, hs, hrel⟩ := hf
  have hDc : IsCompact (Dsk W) := isCompact_Dsk hW
  let P : Set (ℕ × ℂ) := {a | a.1 = 0}
  have hPo : IsClopen P := (isClopen_discrete ({0} : Set ℕ)).preimage continuous_fst
  have hF0 : IsClosed (f '' (Dsk W ∩ P)) :=
    ((hDc.inter_right hPo.isClosed).image_of_continuousOn (hc.mono inter_subset_left)).isClosed
  have hF1 : IsClosed (f '' (Dsk W \ P)) :=
    ((hDc.diff hPo.isOpen).image_of_continuousOn (hc.mono sdiff_subset)).isClosed
  have hcov : (univ : Set X) ⊆ f '' (Dsk W ∩ P) ∪ f '' (Dsk W \ P) := by
    intro x _
    have h1 : x ∈ f '' Dsk W := hs ▸ mem_univ x
    obtain ⟨a, ha, rfl⟩ := h1
    by_cases hp : a ∈ P
    · exact .inl ⟨a, ⟨ha, hp⟩, rfl⟩
    · exact .inr ⟨a, ⟨ha, hp⟩, rfl⟩
  have hn0 : (0, (0 : ℂ)) ∈ Dsk W := ⟨h0, by simp⟩
  have hn1 : (j₀, (0 : ℂ)) ∈ Dsk W := ⟨hne, by simp⟩
  obtain ⟨x, -, ⟨a, ⟨ha, hap⟩, rfl⟩, ⟨b, ⟨hb, hbp⟩, he⟩⟩ := isPreconnected_closed_iff.mp
    (isPreconnected_univ (α := X)) _ _ hF0 hF1 hcov ⟨_, mem_univ _, _, ⟨hn0, rfl⟩, rfl⟩
    ⟨_, mem_univ _, _, ⟨hn1, hj₀⟩, rfl⟩
  have hr : PRel W a b := (hrel a ha b hb).mp he.symm
  have key : ∀ x y, PRel W x y → (x.1 = 0 ↔ y.1 = 0) := by
    intro x y h
    induction h with
    | rel x y hs =>
      obtain ⟨i, j, p, q, k, e, e', t, h1, h2, -, -, rfl, rfl⟩ := hs
      have m1 : (k, e) ∈ W i := List.mem_of_getElem? h1
      have m2 : (k, e') ∈ W j := List.mem_of_getElem? h2
      constructor
      · intro hi
        by_contra hj
        have hi' : i = 0 := hi
        subst hi'
        exact hcon j k e e' hj m1 m2
      · intro hj
        by_contra hi
        have hj' : j = 0 := hj
        subst hj'
        exact hcon i k e' e hi m2 m1
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ h1 h2 => exact h1.trans h2
  exact hbp ((key a b hr).mp hap)

theorem exists_one_word [ConnectedSpace X] (n : ℕ) : ∀ (S : Finset ℕ) (W : ℕ → List Letter)
  (f : ℕ × ℂ → X),
    S.card = n → FinW W → W 0 ≠ [] → Presents W f → (∀ i, W i ≠ [] → 2 ≤ (W i).length) →
      (∀ i, i ∉ S → W i = []) →
    (∀ c, ∑ i ∈ S, cnt (W i) c ≤ 2) → ∃ (w : List Letter) (g : ℕ × ℂ → X), w ≠ [] ∧ Good w
      ∧ Presents (sW w) g := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S W f hn hW h0 hf hlen hS hsum
  have h0S : 0 ∈ S := by
    by_contra h
    exact h0 (hS 0 h)
  by_cases hall : ∀ j, j ≠ 0 → W j = []
  · have e : W = sW (W 0) := by
      funext i
      by_cases hi : i = 0
      · subst hi
        simp [sW]
      · simp [sW, nW, update_of_ne hi, hall i hi]
    refine ⟨W 0, f, h0, fun c => ?_, e ▸ hf⟩
    exact (Finset.single_le_sum (f := fun i => cnt (W i) c) (fun _ _ => Nat.zero_le _) h0S).trans
      (hsum c)
  push Not at hall
  obtain ⟨j₀, hj₀, hne⟩ := hall
  obtain ⟨j, k, e, e', hj, m0, m1⟩ := exists_shared hW hf h0 hj₀ hne
  have hjne : W j ≠ [] := fun he => by simp [he] at m1
  have hjS : j ∈ S := by
    by_contra h
    exact hjne (hS j h)
  have split : ∀ c, cnt (W j) c + (cnt (W 0) c + ∑ i ∈ (S.erase j).erase 0, cnt (W i) c) ≤ 2
    := fun c => by
    have h1 := Finset.add_sum_erase S (fun i => cnt (W i) c) hjS
    have h2 := Finset.add_sum_erase (S.erase j) (fun i => cnt (W i) c)
      (Finset.mem_erase.mpr ⟨hj.symm, h0S⟩)
    have h3 := hsum c
    omega
  have p0 : 0 < cnt (W 0) k := cnt_pos (w := W 0) (l := (k, e)) m0
  have p1 : 0 < cnt (W j) k := cnt_pos (w := W j) (l := (k, e')) m1
  have hk := split k
  have hrest : ∀ i, i ≠ 0 → i ≠ j → cnt (W i) k = 0 := by
    intro i hi0 hij
    by_cases hiS : i ∈ S
    · have h1 : i ∈ (S.erase j).erase 0 := Finset.mem_erase.mpr ⟨hi0, Finset.mem_erase.mpr ⟨hij,
      hiS⟩⟩
      have h2 := Finset.single_le_sum (f := fun i => cnt (W i) k) (fun _ _ => Nat.zero_le _) h1
      omega
    · rw [hS i hiS]
      rfl
  obtain ⟨w, hpe, hwl, hwc⟩ := merge_step.{u} hW hj m0 m1 (by omega) (by omega) hrest (hlen 0 h0)
    (hlen j hjne)
  obtain ⟨g, hg⟩ := (hpe X).mp ⟨f, hf⟩
  have hwne : w ≠ [] := fun he => by simp [he] at hwl
  refine ih (S.erase j).card ?_ (S.erase j) _ g rfl ((hW.update _ _).update _ _)
    (by simpa using hwne) hg ?_ ?_ ?_
  · rw [← hn]
    exact Finset.card_erase_lt_of_mem hjS
  · intro i hi
    by_cases hi0 : i = 0
    · subst hi0
      simpa using hwl
    · rw [update_of_ne hi0] at hi ⊢
      by_cases hij : i = j
      · subst hij
        simp at hi
      · rw [update_of_ne hij] at hi ⊢
        exact hlen i hi
  · intro i hi
    have hi0 : i ≠ 0 := fun h => hi (Finset.mem_erase.mpr ⟨h ▸ hj.symm, h ▸ h0S⟩)
    rw [update_of_ne hi0]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [update_of_ne hij]
      exact hS i fun h => hi (Finset.mem_erase.mpr ⟨hij, h⟩)
  · intro c
    have h1 := Finset.add_sum_erase (S.erase j) (fun i => cnt (update (update W j []) 0 w i) c)
      (Finset.mem_erase.mpr ⟨hj.symm, h0S⟩)
    have h2 : ∑ i ∈ (S.erase j).erase 0, cnt (update (update W j []) 0 w i) c =
        ∑ i ∈ (S.erase j).erase 0, cnt (W i) c := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi0 := (Finset.mem_erase.mp hi).1
      have hij := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      rw [update_of_ne hi0, update_of_ne hij]
    simp only [update_self] at h1
    have h3 := hwc c
    have h4 := split c
    omega

end GraphMinor.Surface
