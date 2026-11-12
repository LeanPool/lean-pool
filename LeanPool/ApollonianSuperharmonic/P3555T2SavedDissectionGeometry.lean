/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3555T2ParabolaChordCuts
public import LeanPool.ApollonianSuperharmonic.P3511T1CyclicDissection
public import Mathlib.Analysis.Convex.Combination
public import LeanPool.ApollonianSuperharmonic.P3555T2ParabolaSupporting

-- [TABLET NODE: P3555T2SavedDissectionGeometry]

/-!
# P3555T2SavedDissectionGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace SavedDissectionProof

private theorem hsetAt164 :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3
        : ℕ))), ∀ (c : Fin (n + (3 : ℕ))), ([a, b, c].Nodup) → ((∃ (k : ℕ), [a, b, c].Sublist
        ((List.ofFn fun (i : Fin (n + (3 : ℕ))) => i).rotate k)) → (([a, b, c].Nodup) → ((∃ (k :
        ℕ), [a, b, c].Sublist ((List.ofFn fun (i : Fin (n + (3 : ℕ))) => i).rotate k)) → (((a ≠ b
        ∧ a ≠ c) ∧ b ≠ c) → (
    let f : Fin 3 → Fin (n + 3) := ![a, b, c]
    (Function.Injective f) → ((P3381T1TriangleDeterminant (q ∘ f) ≠ 0) → (q '' {i | i ∈ [a, b,
        c]} = Set.range (q ∘ f)))))))) := by
  classical
  intro n q a b c hboundary hcyclic hnd hcyc hnd' f hfi hdet
  ext x
  change (∃ i, i ∈ [a, b, c] ∧ q i = x) ↔ ∃ j : Fin 3, q (f j) = x
  constructor
  · rintro ⟨i, hi, hix⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨0, by simpa [f] using hix⟩
    · exact ⟨1, by simpa [f] using hix⟩
    · exact ⟨2, by simpa [f] using hix⟩
  · rintro ⟨j, hj⟩
    fin_cases j
    · exact ⟨a, by simp, by simpa [f] using hj⟩
    · exact ⟨b, by simp, by simpa [f] using hj⟩
    · exact ⟨c, by simp, by simpa [f] using hj⟩

private theorem hDaffine :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3
        : ℕ))),
    let D : Real × Real → Real := fun z =>
      P3381T1TriangleDeterminant ![q a, q b, z]
    ∀ (w : Fin 3 → Real), ∀ (p : Fin 3 → Real × Real), ((∑ i, w i) = 1) → (D (∑ i, w i • p i) = ∑
        i, w i * D (p i)) := by
  classical
  intro n q a b D w p hw
  have hform (z : Real × Real) :
      D z = ((q b).1 - (q a).1) * (z.2 - (q a).2) -
        (z.1 - (q a).1) * ((q b).2 - (q a).2) := by
    simp [D, P3381T1TriangleDeterminant]
  rw [hform]
  have hfst : (∑ i, w i • p i).1 = ∑ i, w i * (p i).1 := by
    rw [Prod.fst_sum]
    simp only [Prod.smul_fst, smul_eq_mul]
  have hsnd : (∑ i, w i • p i).2 = ∑ i, w i * (p i).2 := by
    rw [Prod.snd_sum]
    simp only [Prod.smul_snd, smul_eq_mul]
  rw [hfst, hsnd]
  simp_rw [hform]
  simp only [Fin.sum_univ_three] at hw ⊢
  have hw2 : w 2 = 1 - w 0 - w 1 := by linarith
  rw [hw2]
  ring

private theorem faceChord :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3
        : ℕ))), ∀ (f : Fin 3 → Fin (n + 3)), ∀ (φ : (Real × Real) → Real), (∀ (w : Fin 3 → Real),
        ∀ (p : Fin 3 → Real × Real), (∑ i, w i) = 1 → φ (∑ i, w i • p i) = ∑ i, w i * φ (p i)) →
        ((∀ i, φ (q (f i)) ≤ 0) → ((∀ i, f i ≠ a → f i ≠ b → φ (q (f i)) < 0) → (∀ (z : Real ×
        Real), (z ∈ convexHull Real (Set.range (q ∘ f))) → ((φ z = 0) → (z ∈ convexHull Real (q
        '' (Set.range f ∩ ({a, b} : Set (Fin (n + 3)))))))))) := by
  classical
  intro n q a b f φ hφ hweak hstrict z hz hzφ
  classical
  obtain ⟨ι, inst, w, y, hw0, hw1, hy, hyz⟩ :=
    mem_convexHull_iff_exists_fintype.mp hz
  let _ := inst
  choose j hj using hy
  let W : Fin 3 → Real := fun i => ∑ r, if j r = i then w r else 0
  have hW0 : ∀ i, 0 ≤ W i := by
    intro i
    exact Finset.sum_nonneg fun r _ => by
      split_ifs
      · exact hw0 r
      · exact le_rfl
  have hWsum : (∑ i, W i) = 1 := by
    simpa [W, Finset.sum_comm] using hw1
  have hWz : (∑ i, W i • q (f i)) = z := by
    calc
      (∑ i, W i • q (f i)) = ∑ r, w r • q (f (j r)) := by
        simp [W, Finset.sum_smul, Finset.sum_comm, ite_smul]
      _ = ∑ r, w r • y r := by
        apply Finset.sum_congr rfl
        intro r hr
        simpa [Function.comp_apply] using
          congrArg (fun x => w r • x) (hj r)
      _ = z := hyz
  have hsumφ : (∑ i, W i * φ (q (f i))) = 0 := by
    calc
      (∑ i, W i * φ (q (f i))) = φ (∑ i, W i • q (f i)) :=
        (hφ W (fun i => q (f i)) hWsum).symm
      _ = φ z := congrArg φ hWz
      _ = 0 := hzφ
  have hterm : ∀ i, W i * φ (q (f i)) ≤ 0 := by
    intro i
    exact mul_nonpos_of_nonneg_of_nonpos (hW0 i) (hweak i)
  have hWzero : ∀ i, f i ≠ a → f i ≠ b → W i = 0 := by
    intro i hia hib
    have hzeroTerms :=
      (Finset.sum_eq_zero_iff_of_nonpos (fun j _ => hterm j)).mp hsumφ
    have ht := hzeroTerms i (Finset.mem_univ i)
    rcases mul_eq_zero.mp ht with hzero | hzero
    · exact hzero
    · exact False.elim ((hstrict i hia hib).ne' hzero.symm)
  by_cases hS : (Set.range f ∩ ({a, b} : Set (Fin (n + 3)))).Nonempty
  · obtain ⟨c, hc⟩ := hS
    let g : Fin 3 → Fin (n + 3) :=
      fun i => if f i ∈ ({a, b} : Set (Fin (n + 3))) then f i else c
    have hg : ∀ i, g i ∈ Set.range f ∩ ({a, b} : Set (Fin (n + 3))) := by
      intro i
      by_cases hi : f i ∈ ({a, b} : Set (Fin (n + 3)))
      · have hi' : f i = a ∨ f i = b := by simpa using hi
        refine ⟨⟨i, ?_⟩, ?_⟩
        · simp [g, hi']
        · simp [g, hi']
      · have hne : f i ≠ a ∧ f i ≠ b := by simpa using hi
        exact by simpa [g, hne] using hc
    have hvec : (∑ i, W i • q (g i)) = z := by
      rw [← hWz]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases he : f i ∈ ({a, b} : Set (Fin (n + 3)))
      · have he' : f i = a ∨ f i = b := by simpa using he
        simp [g, he']
      · have hne : f i ≠ a ∧ f i ≠ b := by simpa using he
        simp [g, hWzero i hne.1 hne.2]
    exact mem_convexHull_of_exists_fintype W (fun i => q (g i)) hW0 hWsum
      (fun i => Set.mem_image_of_mem q (hg i)) hvec
  · have hna : ∀ i, f i ≠ a := by
      intro i hi
      apply hS
      exact ⟨a, ⟨i, hi⟩, by simp⟩
    have hnb : ∀ i, f i ≠ b := by
      intro i hi
      apply hS
      exact ⟨b, ⟨i, hi⟩, by simp⟩
    have hzero : ∀ i, W i = 0 := fun i => hWzero i (hna i) (hnb i)
    have : (∑ i, W i) = 0 := by simp [hzero]
    rw [hWsum] at this
    norm_num at this

private theorem hAparent :
    ∀ (n : Nat), ∀ (a : Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3 : ℕ))), ∀ (u : List (Fin (n + (3 :
        ℕ)))), ∀ (v : List (Fin (n + (3 : ℕ)))), ∀ i, i ∈ a :: (u ++ [b]) → i ∈ a :: (u ++ b ::
        v) := by
  classical
  intro n a b u v i hi
  simp only [List.mem_cons, List.mem_append,
    List.not_mem_nil] at hi
  simp only [or_false] at hi
  simp only [List.mem_cons, List.mem_append]
  rcases hi with ha | hu | hb
  · exact Or.inl ha
  · exact Or.inr (Or.inl hu)
  · exact Or.inr (Or.inr (Or.inl hb))

private theorem hBparent :
    ∀ (n : Nat), ∀ (a : Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3 : ℕ))), ∀ (u : List (Fin (n + (3 :
        ℕ)))), ∀ (v : List (Fin (n + (3 : ℕ)))), ∀ i, i ∈ b :: (v ++ [a]) → i ∈ a :: (u ++ b ::
        v) := by
  classical
  intro n a b u v i hi
  simp only [List.mem_cons, List.mem_append,
    List.not_mem_nil] at hi
  simp only [or_false] at hi
  simp only [List.mem_cons, List.mem_append]
  rcases hi with hb | hv | ha
  · exact Or.inr (Or.inr (Or.inl hb))
  · exact Or.inr (Or.inr (Or.inr hv))
  · exact Or.inl ha

private theorem hcross :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3
        : ℕ))), ∀ (u : List (Fin (n + (3 : ℕ)))), ∀ (v : List (Fin (n + (3 : ℕ)))), ∀ (left :
        List (Fin (3 : ℕ) → Fin (n + (3 : ℕ)))), ∀ (right : List (Fin (3 : ℕ) → Fin (n + (3 :
        ℕ)))), ({i : Fin (n + (3 : ℕ)) | i ∈ a :: (u ++ [b])} ∩ {i : Fin (n + (3 : ℕ)) | i ∈ b ::
        (v ++ [a])} = {a, b}) → ((∀ f ∈ left, Function.Injective f ∧ Set.range f ⊆ {i : Fin (n +
        (3 : ℕ)) | i ∈ a :: (u ++ [b])} ∧ P3381T1TriangleDeterminant (q ∘ f) ≠ (0 : ℝ)) → ((∀ f
        ∈ right, Function.Injective f ∧ Set.range f ⊆ {i : Fin (n + (3 : ℕ)) | i ∈ b :: (v ++
        [a])} ∧ P3381T1TriangleDeterminant (q ∘ f) ≠ (0 : ℝ)) → (∀ f ∈ left, ∀ g ∈ right,
      Set.range f ≠ Set.range g))) := by
  classical
  intro n q a b u v left right hAB hfaceA hfaceB f hf g hg heq
  have hfi := (hfaceA f hf).1
  have hgi := (hfaceB g hg).1
  have hsubA := (hfaceA f hf).2.1
  have hsubB := (hfaceB g hg).2.1
  have hsmall : Set.range f ⊆ ({a, b} : Set (Fin (n + 3))) := by
    intro x hx
    have hxA : x ∈ a :: (u ++ [b]) := hsubA hx
    have hxg : x ∈ Set.range g := by rw [← heq]; exact hx
    have hxB : x ∈ b :: (v ++ [a]) := hsubB hxg
    have hxAB : x ∈ {i | i ∈ a :: (u ++ [b])} ∩
        {i | i ∈ b :: (v ++ [a])} := ⟨hxA, hxB⟩
    rw [hAB] at hxAB
    simpa using hxAB
  have h0 : f 0 = a ∨ f 0 = b := by
    have := hsmall ⟨0, rfl⟩
    simpa using this
  have h1 : f 1 = a ∨ f 1 = b := by
    have := hsmall ⟨1, rfl⟩
    simpa using this
  have h2 : f 2 = a ∨ f 2 = b := by
    have := hsmall ⟨2, rfl⟩
    simpa using this
  have hn01 : f 0 ≠ f 1 := hfi.ne (by decide)
  have hn02 : f 0 ≠ f 2 := hfi.ne (by decide)
  have hn12 : f 1 ≠ f 2 := hfi.ne (by decide)
  rcases h0 with h0a | h0b
  · rcases h1 with h1a | h1b
    · exact hn01 (h0a.trans h1a.symm)
    · rcases h2 with h2a | h2b
      · exact hn02 (h0a.trans h2a.symm)
      · exact hn12 (h1b.trans h2b.symm)
  · rcases h1 with h1a | h1b
    · rcases h2 with h2a | h2b
      · exact hn12 (h1a.trans h2a.symm)
      · exact hn02 (h0b.trans h2b.symm)
    · exact hn01 (h0b.trans h1b.symm)

private theorem hsignA :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3
        : ℕ))), ∀ (u : List (Fin (n + (3 : ℕ)))), ∀ (left : List (Fin (3 : ℕ) → Fin (n + (3 :
        ℕ)))), (∀ i ∈ u, (fun (z : ℝ × ℝ) => P3381T1TriangleDeterminant ![q a, q b, z]) (q i) <
        (0 : ℝ)) → ((∀ f ∈ left, Function.Injective f ∧ Set.range f ⊆ {i : Fin (n + (3 : ℕ)) | i
        ∈ a :: (u ++ [b])} ∧ P3381T1TriangleDeterminant (q ∘ f) ≠ (0 : ℝ)) → (
    let D : Real × Real → Real := fun z =>
      P3381T1TriangleDeterminant ![q a, q b, z]
    (D (q a) = 0) → ((D (q b) = 0) → (∀ (f : Fin 3 → Fin (n + 3)), (f ∈ left) → ((∀ i, D (q (f
        i)) ≤ 0) ∧
      (∀ i, f i ≠ a → f i ≠ b → D (q (f i)) < 0)))))) := by
  classical
  intro n q a b u left hU hfaceA D hDa hDb f hf
  have hlabels := (hfaceA f hf).2.1
  constructor
  · intro i
    have hi := hlabels ⟨i, rfl⟩
    simp only [List.mem_cons, List.mem_append,
      List.not_mem_nil, or_false] at hi
    rcases hi with ha | hu | hb
    · rw [ha, hDa]
    · exact (hU (f i) hu).le
    · rw [hb]
      simp [hDb]
  · intro i hia hib
    have hi := hlabels ⟨i, rfl⟩
    simp only [List.mem_cons, List.mem_append,
      List.not_mem_nil, or_false] at hi
    rcases hi with ha | hu | hb
    · exact (hia ha).elim
    · exact hU (f i) hu
    · exact (hib hb).elim

private theorem hsignB :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3
        : ℕ))), ∀ (v : List (Fin (n + (3 : ℕ)))), ∀ (right : List (Fin (3 : ℕ) → Fin (n + (3 :
        ℕ)))), (∀ i ∈ v, (0 : ℝ) < (fun (z : ℝ × ℝ) => P3381T1TriangleDeterminant ![q a, q b,
        z]) (q i)) → ((∀ f ∈ right, Function.Injective f ∧ Set.range f ⊆ {i : Fin (n + (3 : ℕ)) |
        i ∈ b :: (v ++ [a])} ∧ P3381T1TriangleDeterminant (q ∘ f) ≠ (0 : ℝ)) → (
    let D : Real × Real → Real := fun z =>
      P3381T1TriangleDeterminant ![q a, q b, z]
    (D (q a) = 0) → ((D (q b) = 0) → (∀ (f : Fin 3 → Fin (n + 3)), (f ∈ right) → ((∀ i, (-D) (q
        (f i)) ≤ 0) ∧
      (∀ i, f i ≠ a → f i ≠ b → (-D) (q (f i)) < 0)))))) := by
  classical
  intro n q a b v right hV hfaceB D hDa hDb f hf
  have hlabels := (hfaceB f hf).2.1
  constructor
  · intro i
    have hi := hlabels ⟨i, rfl⟩
    simp only [List.mem_cons, List.mem_append,
      List.not_mem_nil, or_false] at hi
    rcases hi with hb | hv | ha
    · rw [hb]
      simp [hDb]
    · exact (neg_nonpos.mpr (hV (f i) hv).le)
    · rw [ha]
      simp [hDa]
  · intro i hia hib
    have hi := hlabels ⟨i, rfl⟩
    simp only [List.mem_cons, List.mem_append,
      List.not_mem_nil, or_false] at hi
    rcases hi with hb | hv | ha
    · exact (hib hb).elim
    · exact neg_neg_of_pos (hV (f i) hv)
    · exact (hia ha).elim

private theorem hendpoint_intersection :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), (Function.Injective q ∧ (∀ (f : Fin (3 : ℕ) →
        Fin (n + (3 : ℕ))), Function.Injective f → P3381T1TriangleDeterminant (q ∘ f) ≠ (0 :
        ℝ)) ∧ ∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3 : ℕ))), j ≠ i → j ≠ i + (1 : Fin (n +
        (3 : ℕ))) → (0 : ℝ) < P3381T1TriangleDeterminant ![q i, q (i + (1 : Fin (n + (3 :
        ℕ)))), q j]) → (∀ (a : Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3 : ℕ))), (a ≠ b) → (∀ (S :
        Set (Fin (n + 3))), ∀ (T : Set (Fin (n + 3))), (S ⊆ ({a, b} : Set (Fin (n + 3)))) → ((T ⊆
        ({a, b} : Set (Fin (n + 3)))) → (∀ (z : Real × Real), (z ∈ convexHull Real (q '' S)) →
        ((z ∈ convexHull Real (q '' T)) → (z ∈ convexHull Real (q '' (S ∩ T)))))))) := by
  classical
  intro n q hsupport a b hab S T hS hT z hzS hzT
  classical
  have hqa_ne_hqb : q a ≠ q b := fun h => hab (hsupport.1 h)
  by_cases haS : a ∈ S <;> by_cases hbS : b ∈ S <;>
    by_cases haT : a ∈ T <;> by_cases hbT : b ∈ T
  all_goals
    have hSform : S = if a ∈ S then if b ∈ S then {a, b} else {a} else if b ∈ S then {b} else ∅
        := by
      ext x
      constructor
      · intro hx
        rcases hS hx with hx' | hx'
        · subst x; simp [haS, hbS, hab] at hx ⊢
        · subst x; simp [haS, hbS, hab.symm] at hx ⊢
      · intro hx
        by_cases hxa : x = a
        · subst x; simp [haS, hbS, hab] at hx ⊢
        · by_cases hxb : x = b
          · subst x; simp [haS, hbS, hab.symm] at hx ⊢
          · simp [hxa, hxb, haS, hbS] at hx
    have hTform : T = if a ∈ T then if b ∈ T then {a, b} else {a} else if b ∈ T then {b} else ∅
        := by
      ext x
      constructor
      · intro hx
        rcases hT hx with hx' | hx'
        · subst x; simp [haT, hbT, hab] at hx ⊢
        · subst x; simp [haT, hbT, hab.symm] at hx ⊢
      · intro hx
        by_cases hxa : x = a
        · subst x; simp [haT, hbT, hab] at hx ⊢
        · by_cases hxb : x = b
          · subst x; simp [haT, hbT, hab.symm] at hx ⊢
          · simp [hxa, hxb, haT, hbT] at hx
    rw [hSform] at hzS ⊢
    rw [hTform] at hzT ⊢
    simp only [haS, ↓reduceIte, hbS, Set.image_empty, convexHull_empty,
        Set.mem_empty_iff_false, Set.image_insert_eq, Set.image_singleton, convexHull_pair,
        haT, hbT, Set.inter_self, convexHull_singleton, Set.mem_singleton_iff,
        Set.mem_insert_iff, or_true, Set.inter_singleton_of_mem, true_or,
        Set.singleton_inter_of_mem] at hzS hzT ⊢
    all_goals
      first
      | exact hzS
      | exact hzT
      | exact False.elim (hqa_ne_hqb (hzS.symm.trans hzT))
      | exact False.elim (hqa_ne_hqb (hzT.symm.trans hzS))

private theorem hcrossInter :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (a : Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3
        : ℕ))), ∀ (u : List (Fin (n + (3 : ℕ)))), ∀ (v : List (Fin (n + (3 : ℕ)))), ∀ (left :
        List (Fin (3 : ℕ) → Fin (n + (3 : ℕ)))), ∀ (right : List (Fin (3 : ℕ) → Fin (n + (3 :
        ℕ)))), ({i : Fin (n + (3 : ℕ)) | i ∈ a :: (u ++ [b])} ∩ {i : Fin (n + (3 : ℕ)) | i ∈ b ::
        (v ++ [a])} = {a, b}) → (((convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (q '' {i : Fin (n +
        (3 : ℕ)) | i ∈ a :: (u ++ [b])}) ∩ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (q '' {i :
        Fin (n + (3 : ℕ)) | i ∈ b :: (v ++ [a])}) = segment ℝ (q a) (q b)) → ((∀ f ∈ left,
        Function.Injective f ∧ Set.range f ⊆ {i : Fin (n + (3 : ℕ)) | i ∈ a :: (u ++ [b])} ∧
        P3381T1TriangleDeterminant (q ∘ f) ≠ (0 : ℝ)) → ((∀ f ∈ right, Function.Injective f ∧
        Set.range f ⊆ {i : Fin (n + (3 : ℕ)) | i ∈ b :: (v ++ [a])} ∧
        P3381T1TriangleDeterminant (q ∘ f) ≠ (0 : ℝ)) → (
    let D : Real × Real → Real := fun z =>
      P3381T1TriangleDeterminant ![q a, q b, z]
    (D (q a) = 0) → ((D (q b) = 0) → ((∀ (w : Fin 3 → Real), ∀ (p : Fin 3 → Real × Real), ((∑ i,
        w i) = 1) → (D (∑ i, w i • p i) = ∑ i, w i * D (p i))) → ((∀ (f : Fin 3 → Fin (n + 3)), ∀
        (φ : (Real × Real) → Real), (∀ (w : Fin 3 → Real), ∀ (p : Fin 3 → Real × Real), (∑ i, w
        i) = 1 → φ (∑ i, w i • p i) = ∑ i, w i * φ (p i)) → ((∀ i, φ (q (f i)) ≤ 0) → ((∀ i, f i
        ≠ a → f i ≠ b → φ (q (f i)) < 0) → (∀ (z : Real × Real), (z ∈ convexHull Real (Set.range
        (q ∘ f))) → ((φ z = 0) → (z ∈ convexHull Real (q '' (Set.range f ∩ ({a, b} : Set (Fin (n
        + 3))))))))))) → ((∀ (w : Fin 3 → Real), ∀ (p : Fin 3 → Real × Real), ((∑ i, w i) = 1) →
        (-D (∑ i, w i • p i) = ∑ i, w i * (-D (p i)))) → ((∀ (f : Fin 3 → Fin (n + 3)), (f ∈
        left) → ((∀ i, D (q (f i)) ≤ 0) ∧ (∀ i, f i ≠ a → f i ≠ b → D (q (f i)) < 0))) → ((∀ (f :
        Fin 3 → Fin (n + 3)), (f ∈ right) → ((∀ i, (-D) (q (f i)) ≤ 0) ∧ (∀ i, f i ≠ a → f i ≠ b
        → (-D) (q (f i)) < 0))) → ((∀ (S : Set (Fin (n + 3))), ∀ (T : Set (Fin (n + 3))), (S ⊆
        ({a, b} : Set (Fin (n + 3)))) → ((T ⊆ ({a, b} : Set (Fin (n + 3)))) → (∀ (z : Real ×
        Real), (z ∈ convexHull Real (q '' S)) → ((z ∈ convexHull Real (q '' T)) → (z ∈ convexHull
        Real (q '' (S ∩ T))))))) → (∀ (f : Fin 3 → Fin (n + 3)), (f ∈ left) → (∀ (g : Fin 3 → Fin
        (n + 3)), (g ∈ right) → (convexHull Real (Set.range (q ∘ f)) ∩ convexHull Real (Set.range
        (q ∘ g)) =
        convexHull Real (q '' (Set.range f ∩ Set.range g)))))))))))))))) := by
  classical
  intro n q a b u v left right hAB hinter hfaceA hfaceB D hDa hDb hDaffine faceChord hDnegAffine
      hsignA hsignB hendpoint_intersection f hf g hg
  have hrangeA : Set.range (q ∘ f) ⊆
      q '' {i | i ∈ a :: (u ++ [b])} := by
    rintro z ⟨i, rfl⟩
    exact ⟨f i, (hfaceA f hf).2.1 ⟨i, rfl⟩, rfl⟩
  have hrangeB : Set.range (q ∘ g) ⊆
      q '' {i | i ∈ b :: (v ++ [a])} := by
    rintro z ⟨i, rfl⟩
    exact ⟨g i, (hfaceB g hg).2.1 ⟨i, rfl⟩, rfl⟩
  have hshared : Set.range f ∩ Set.range g ⊆ ({a, b} : Set (Fin (n + 3))) := by
    intro x hx
    have hxA : x ∈ a :: (u ++ [b]) := (hfaceA f hf).2.1 hx.1
    have hxB : x ∈ b :: (v ++ [a]) := (hfaceB g hg).2.1 hx.2
    have hxAB : x ∈ {i | i ∈ a :: (u ++ [b])} ∩
        {i | i ∈ b :: (v ++ [a])} := ⟨hxA, hxB⟩
    rw [hAB] at hxAB
    simpa using hxAB
  have hendpointSet :
      (Set.range f ∩ ({a, b} : Set (Fin (n + 3)))) ∩
          (Set.range g ∩ ({a, b} : Set (Fin (n + 3)))) =
        Set.range f ∩ Set.range g := by
    ext x
    simp only [Set.mem_inter_iff]
    constructor
    · rintro ⟨⟨hxf, hxAB⟩, ⟨hxg, _⟩⟩
      exact ⟨hxf, hxg⟩
    · rintro ⟨hxf, hxg⟩
      exact ⟨⟨hxf, hshared ⟨hxf, hxg⟩⟩, ⟨hxg, hshared ⟨hxf, hxg⟩⟩⟩
  have hDzero (z : Real × Real)
      (hz : z ∈ segment Real (q a) (q b)) : D z = 0 := by
    rw [segment_eq_image] at hz
    rcases hz with ⟨t, ht, htz⟩
    let w : Fin 3 → Real := ![1 - t, t, 0]
    let p : Fin 3 → Real × Real := ![q a, q b, (0, 0)]
    have hw : (∑ i, w i) = 1 := by simp [w, Fin.sum_univ_three]
    have hp : (∑ i, w i • p i) = (1 - t) • q a + t • q b := by
      simp [w, p, Fin.sum_univ_three]
    calc
      D z = D ((1 - t) • q a + t • q b) := by rw [← htz]
      _ = D (∑ i, w i • p i) := by rw [hp]
      _ = ∑ i, w i * D (p i) := hDaffine w p hw
      _ = 0 := by simp [w, p, Fin.sum_univ_three, hDa, hDb]
  have hleftHull :
      convexHull Real (Set.range (q ∘ f)) ⊆
        convexHull Real (q '' {i | i ∈ a :: (u ++ [b])}) :=
    convexHull_mono hrangeA
  have hrightHull :
      convexHull Real (Set.range (q ∘ g)) ⊆
        convexHull Real (q '' {i | i ∈ b :: (v ++ [a])}) :=
    convexHull_mono hrangeB
  ext z
  constructor
  · intro hz
    have hzA : z ∈ convexHull Real (q '' {i | i ∈ a :: (u ++ [b])}) :=
      hleftHull hz.1
    have hzB : z ∈ convexHull Real (q '' {i | i ∈ b :: (v ++ [a])}) :=
      hrightHull hz.2
    have hzChord : z ∈ segment Real (q a) (q b) := by
      have : z ∈ convexHull Real (q '' {i | i ∈ a :: (u ++ [b])}) ∩
          convexHull Real (q '' {i | i ∈ b :: (v ++ [a])}) := ⟨hzA, hzB⟩
      rw [hinter] at this
      exact this
    have hzero := hDzero z hzChord
    have hzfa : z ∈ convexHull Real (q ''
        (Set.range f ∩ ({a, b} : Set (Fin (n + 3))))) :=
      faceChord f D hDaffine (hsignA f hf).1 (hsignA f hf).2 z hz.1 hzero
    have hzg : (-D) z = 0 := by simp [hzero]
    have hzgb : z ∈ convexHull Real (q ''
        (Set.range g ∩ ({a, b} : Set (Fin (n + 3))))) :=
      faceChord g (-D) hDnegAffine (hsignB g hg).1 (hsignB g hg).2 z hz.2 hzg
    have hzBoth : z ∈ convexHull Real (q ''
        ((Set.range f ∩ ({a, b} : Set (Fin (n + 3)))) ∩
          (Set.range g ∩ ({a, b} : Set (Fin (n + 3)))))) :=
      hendpoint_intersection _ _ (by intro x hx; exact hx.2)
        (by intro x hx; exact hx.2) z hzfa hzgb
    simpa only [hendpointSet] using hzBoth
  · intro hz
    have hmonoA : q '' (Set.range f ∩ Set.range g) ⊆ Set.range (q ∘ f) := by
      rintro z ⟨x, ⟨hxf, hxg⟩, rfl⟩
      rcases hxf with ⟨i, rfl⟩
      exact ⟨i, rfl⟩
    have hmonoB : q '' (Set.range f ∩ Set.range g) ⊆ Set.range (q ∘ g) := by
      rintro z ⟨x, ⟨hxf, hxg⟩, rfl⟩
      rcases hxg with ⟨i, rfl⟩
      exact ⟨i, rfl⟩
    exact ⟨convexHull_mono hmonoA hz, convexHull_mono hmonoB hz⟩

private theorem hAget :
    ∀ (n : Nat), ∀ (a : Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3 : ℕ))), ∀ (u : List (Fin (n + (3 :
        ℕ)))), ∀ (v : List (Fin (n + (3 : ℕ)))), ∀ (i : Fin (a :: (u ++ b :: v)).length), ∀ (hi :
        i.val ≤ u.length + 1), (a :: (u ++ b :: v)).get i =
        (a :: (u ++ [b])).get ⟨i.val, by
          have hlen : (a :: (u ++ [b])).length = u.length + 2 := by simp
          rw [hlen]
          omega⟩ := by
  classical
  intro n a b u v i hi
  by_cases hprefix : i.val ≤ u.length
  · rw [List.get_eq_getElem, List.get_eq_getElem]
    have hip : i.val < (a :: u).length := by simp; omega
    have hiA : i.val < (a :: (u ++ [b])).length := by
      have hlen : (a :: (u ++ [b])).length = u.length + 2 := by simp
      rw [hlen]
      omega
    change ((a :: u) ++ (b :: v))[i.val] = ((a :: u) ++ [b])[i.val]
    rw [List.getElem_append_left hip, List.getElem_append_left hip]
  · have hlast : i.val = u.length + 1 := by omega
    have hpar : (a :: (u ++ b :: v)).get i = b := by
      rw [List.get_eq_getElem]
      simp [hlast, List.getElem_append_right]
    have hchild : (a :: (u ++ [b])).get
        ⟨i.val, by
          have hlen : (a :: (u ++ [b])).length = u.length + 2 := by simp
          rw [hlen]
          omega⟩ = b := by
      rw [List.get_eq_getElem]
      simp [hlast]
    exact hpar.trans hchild.symm

private theorem hBget :
    ∀ (n : Nat), ∀ (a : Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3 : ℕ))), ∀ (u : List (Fin (n + (3 :
        ℕ)))), ∀ (v : List (Fin (n + (3 : ℕ)))), ∀ (j : Fin (a :: (u ++ b :: v)).length), ∀ (hj :
        u.length + 1 ≤ j.val), (a :: (u ++ b :: v)).get j =
        (b :: (v ++ [a])).get ⟨j.val - (u.length + 1), by
          have hlenL : (a :: (u ++ b :: v)).length = u.length + v.length + 2 := by
            simp; omega
          have hlenB : (b :: (v ++ [a])).length = v.length + 2 := by simp
          rw [hlenB]
          omega⟩ := by
  classical
  intro n a b u v j hj
  have hlenL : (a :: (u ++ b :: v)).length = u.length + v.length + 2 := by
    simp; omega
  have hlenB : (b :: (v ++ [a])).length = v.length + 2 := by simp
  have hip : (a :: u).length ≤ j.val := by simp; omega
  have hj' : j.val < u.length + v.length + 2 := by simpa [hlenL] using j.isLt
  let jB : Fin (b :: (v ++ [a])).length :=
    ⟨j.val - (u.length + 1), by rw [hlenB]; omega⟩
  have hpre : (a :: u).length = u.length + 1 := by simp
  have hjBval : jB.val = j.val - (u.length + 1) := rfl
  have htail : j.val - (a :: u).length < (b :: v).length := by
    rw [hpre]
    simp only [List.length_cons]
    omega
  have htailB : jB.val < (b :: v).length := by
    rw [hjBval]
    simp only [List.length_cons]
    omega
  have hresult : (a :: (u ++ b :: v)).get j = (b :: (v ++ [a])).get jB := by
    rw [List.get_eq_getElem, List.get_eq_getElem]
    change ((a :: u) ++ (b :: v))[j.val] = ((b :: v) ++ [a])[jB.val]
    rw [List.getElem_append_right hip, List.getElem_append_left htailB]
    have hidx : j.val - (a :: u).length = jB.val := by rw [hpre, hjBval]
    have hfin : (⟨j.val - (a :: u).length, htail⟩ : Fin (b :: v).length) =
        ⟨jB.val, htailB⟩ := Fin.ext hidx
    simpa only [List.get_eq_getElem] using congrArg (List.get (b :: v)) hfin
  simpa [jB] using hresult

private theorem hNoAEndpoints :
    ∀ (n : Nat), ∀ (a : Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3 : ℕ))), ∀ (u : List (Fin (n + (3 :
        ℕ)))), (List (Fin (n + (3 : ℕ)))) → (((0 : ℕ) < u.length) → (((a :: (u ++ [b])).Nodup) →
        (∀ (i : Fin (a :: (u ++ [b])).length), ∀ (j : Fin (a :: (u ++ [b])).length), (i.val + 1 =
        j.val) → (((a :: (u ++ [b])).get i ∈ ({a, b} : Set (Fin (n + 3)))) → (((a :: (u ++
        [b])).get j ∈ ({a, b} : Set (Fin (n + 3)))) → (False)))))) := by
  classical
  intro n a b u v hu hndA i j hij hia hja
  have hzero : (a :: (u ++ [b])).get ⟨0, by simp⟩ = a := by simp
  have hend : (a :: (u ++ [b])).get ⟨u.length + 1, by simp⟩ = b := by
    simp [List.get_eq_getElem]
  have hne : (a :: (u ++ [b])).get i ≠ (a :: (u ++ [b])).get j := by
    intro heq
    have hij' := (hndA.get_inj_iff).mp heq
    have hv := congrArg Fin.val hij'
    omega
  have hia' : (a :: (u ++ [b])).get i = a ∨
      (a :: (u ++ [b])).get i = b := by simpa using hia
  have hja' : (a :: (u ++ [b])).get j = a ∨
      (a :: (u ++ [b])).get j = b := by simpa using hja
  rcases hia' with hia' | hia'
  · have hi0 : i = 0 := (hndA.get_inj_iff).mp (hia'.trans hzero.symm)
    rcases hja' with hja' | hja'
    · have hj0 : j = 0 := (hndA.get_inj_iff).mp (hja'.trans hzero.symm)
      exact hne (by rw [hi0, hj0])
    · have hjend : j = ⟨u.length + 1, by simp⟩ :=
        (hndA.get_inj_iff).mp (hja'.trans hend.symm)
      have hi0v : i.val = 0 := congrArg Fin.val hi0
      have hjendv : j.val = u.length + 1 := congrArg Fin.val hjend
      have hm : u.length = 0 := by omega
      exact (Nat.ne_of_gt hu) hm
  · have hiend : i = ⟨u.length + 1, by simp⟩ :=
      (hndA.get_inj_iff).mp (hia'.trans hend.symm)
    rcases hja' with hja' | hja'
    · have hj0 : j = 0 := (hndA.get_inj_iff).mp (hja'.trans hzero.symm)
      have hiendv : i.val = u.length + 1 := congrArg Fin.val hiend
      have hj0v : j.val = 0 := congrArg Fin.val hj0
      omega
    · have hjend : j = ⟨u.length + 1, by simp⟩ :=
        (hndA.get_inj_iff).mp (hja'.trans hend.symm)
      exact hne (by rw [hiend, hjend])

private theorem hNoBEndpoints :
    ∀ (n : Nat), ∀ (a : Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3 : ℕ))), (List (Fin (n + (3 : ℕ))))
        → (∀ (v : List (Fin (n + (3 : ℕ)))), ((0 : ℕ) < v.length) → (((b :: (v ++ [a])).Nodup) →
        (∀ (i : Fin (b :: (v ++ [a])).length), ∀ (j : Fin (b :: (v ++ [a])).length), (i.val + 1 =
        j.val) → (((b :: (v ++ [a])).get i ∈ ({a, b} : Set (Fin (n + 3)))) → (((b :: (v ++
        [a])).get j ∈ ({a, b} : Set (Fin (n + 3)))) → (False)))))) := by
  classical
  intro n a b u v hv hndB i j hij hia hja
  have hzero : (b :: (v ++ [a])).get ⟨0, by simp⟩ = b := by simp
  have hend : (b :: (v ++ [a])).get ⟨v.length + 1, by simp⟩ = a := by
    simp [List.get_eq_getElem]
  have hne : (b :: (v ++ [a])).get i ≠ (b :: (v ++ [a])).get j := by
    intro heq
    have hij' := (hndB.get_inj_iff).mp heq
    have hv := congrArg Fin.val hij'
    omega
  have hia' : (b :: (v ++ [a])).get i = a ∨
      (b :: (v ++ [a])).get i = b := by simpa [or_comm] using hia
  have hja' : (b :: (v ++ [a])).get j = a ∨
      (b :: (v ++ [a])).get j = b := by simpa [or_comm] using hja
  rcases hia' with hia' | hia'
  · have hiend : i = ⟨v.length + 1, by simp⟩ :=
      (hndB.get_inj_iff).mp (hia'.trans hend.symm)
    have hv := congrArg Fin.val hiend
    simp at hv
    rcases hja' with hja' | hja'
    · have hjend : j = ⟨v.length + 1, by simp⟩ :=
        (hndB.get_inj_iff).mp (hja'.trans hend.symm)
      exact hne (by rw [hiend, hjend])
    · have hj0 : j = 0 := (hndB.get_inj_iff).mp (hja'.trans hzero.symm)
      have hiendv : i.val = v.length + 1 := congrArg Fin.val hiend
      have hj0v : j.val = 0 := congrArg Fin.val hj0
      omega
  · have hi0 : i = 0 := (hndB.get_inj_iff).mp (hia'.trans hzero.symm)
    rcases hja' with hja' | hja'
    · have hjend : j = ⟨v.length + 1, by simp⟩ :=
        (hndB.get_inj_iff).mp (hja'.trans hend.symm)
      have hi0v : i.val = 0 := congrArg Fin.val hi0
      have hjendv : j.val = v.length + 1 := congrArg Fin.val hjend
      have hm : v.length = 0 := by omega
      exact (Nat.ne_of_gt hv) hm
    · have hj0 : j = 0 := (hndB.get_inj_iff).mp (hja'.trans hzero.symm)
      exact hne (by rw [hi0, hj0])

private theorem hfaces :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (left : List (Fin (3 : ℕ) → Fin (n + (3 :
        ℕ)))), ∀ (right : List (Fin (3 : ℕ) → Fin (n + (3 : ℕ)))), (⋃ f ∈ left ++ right,
        convexHull Real (Set.range (q ∘ f))) =
        (⋃ f ∈ left, convexHull Real (Set.range (q ∘ f))) ∪
          (⋃ f ∈ right, convexHull Real (Set.range (q ∘ f))) := by
  classical
  intro n q left right
  ext x
  simp only [Set.mem_union, Set.mem_iUnion, List.mem_append]
  constructor
  · rintro ⟨f, hf, hx⟩
    rcases hf with hf | hf
    · exact Or.inl ⟨f, hf, hx⟩
    · exact Or.inr ⟨f, hf, hx⟩
  · rintro (⟨f, hf, hx⟩ | ⟨f, hf, hx⟩)
    · exact ⟨f, Or.inl hf, hx⟩
    · exact ⟨f, Or.inr hf, hx⟩

private theorem hchildNextAt805 :
    ∀ (n : Nat), ∀ (a : Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3 : ℕ))), ∀ (u : List (Fin (n + (3 :
        ℕ)))), ∀ (v : List (Fin (n + (3 : ℕ)))), ∀ (k : Fin (a :: (u ++ b :: v)).length),  ∀ (hkA
            : (↑k : ℕ) ≤
        u.length),
    let iA : Fin (a :: (u ++ [b])).length :=
      ⟨k.val, by have hlen : (a :: (u ++ [b])).length = u.length + 2 := by simp
                 rw [hlen]; omega⟩
    let iA1 : Fin (a :: (u ++ [b])).length :=
      ⟨k.val + 1, by have hlen : (a :: (u ++ [b])).length = u.length + 2 := by simp
                     rw [hlen]; omega⟩
    (k.val + 1 < (a :: (u ++ b :: v)).length) → ((a :: (u ++ [b])).get
          ⟨(iA.val + 1) % (a :: (u ++ [b])).length,
            Nat.mod_lt _ (Nat.zero_lt_of_lt iA.isLt)⟩ =
        (a :: (u ++ [b])).get iA1) := by
  classical
  intro n a b u v k hkA iA iA1 hk1Lt
  apply congrArg
  apply Fin.ext
  have hlen : (a :: (u ++ [b])).length = u.length + 2 := by simp
  have hiLt : iA.val + 1 < (a :: (u ++ [b])).length := by
    simp only [List.length_cons, List.length_append]
    dsimp [iA]
    omega
  exact Nat.mod_eq_of_lt hiLt

private theorem hsecondAt889 :
    ∀ (n : Nat), ∀ (a : Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3 : ℕ))), ∀ (u : List (Fin (n + (3 :
        ℕ)))), ∀ (v : List (Fin (n + (3 : ℕ)))), ∀ (hv : (0 : ℕ) < v.length), ∀ (hBget : ∀ (j :
            Fin (a :: (u ++ b :: v)).length), ∀ (hj : u.length + 1 ≤ j.val), (a :: (u ++ b ::
            v)).get
        j =
        (b :: (v ++ [a])).get ⟨j.val - (u.length + 1), by
          have hlenL : (a :: (u ++ b :: v)).length = u.length + v.length + 2 := by
            simp; omega
          have hlenB : (b :: (v ++ [a])).length = v.length + 2 := by simp
          rw [hlenB]
          omega⟩), ∀ (k : Fin (a :: (u ++ b :: v)).length), ∀ (hlenL : (a :: (u ++ b ::
              v)).length = u.length + v.length + 2), ∀ (hkA : ¬(↑k : ℕ) ≤ u.length), ∀ (hjval :
                  k.val - (u.length + 1) ≤ v.length),
    let iB : Fin (b :: (v ++ [a])).length :=
      ⟨k.val - (u.length + 1), by
        have hlen : (b :: (v ++ [a])).length = v.length + 2 := by simp
        rw [hlen]
        omega⟩
    ∀ (hjlast : (↑iB : ℕ) < v.length),
    let k1 : Fin (a :: (u ++ b :: v)).length :=
      ⟨k.val + 1, by
        have hks : k.val + 1 < u.length + v.length + 2 := by dsimp [iB] at hjlast; omega
        simpa [hlenL] using hks⟩
    let nextParent : Fin (a :: (u ++ b :: v)).length :=
      ⟨(k.val + 1) % (a :: (u ++ b :: v)).length,
        Nat.mod_lt _ (Nat.zero_lt_of_lt k.isLt)⟩
    ∀ (hk1mod : (k.val + 1) % (a :: (u ++ b :: v)).length = k.val + 1), (nextParent = k1) → (
    let iB1 : Fin (b :: (v ++ [a])).length :=
      ⟨k1.val - (u.length + 1), by
        have hlen : (b :: (v ++ [a])).length = v.length + 2 := by simp
        rw [hlen]
        have hks : k.val + 1 < u.length + v.length + 2 := by dsimp [iB] at hjlast; omega
        dsimp [k1]
        omega⟩
    (a :: (u ++ b :: v)).get nextParent = (b :: (v ++ [a])).get iB1) := by
  classical
  intro n a b u v hv hBget k hlenL hkA hjval iB hjlast k1 nextParent hk1mod hnextIndex iB1
  calc
    (a :: (u ++ b :: v)).get nextParent = (a :: (u ++ b :: v)).get k1 := by
      rw [hnextIndex]
    _ = (b :: (v ++ [a])).get iB1 := by
      have hkB1 : u.length + 1 ≤ k1.val := by dsimp [k1]; omega
      have htemp := hBget k1 hkB1
      have hidx : (k1.val - (u.length + 1)) = iB1.val := by rfl
      have hfin : (⟨k1.val - (u.length + 1), (show _ by
          have hlen : (b :: (v ++ [a])).length = v.length + 2 := by simp
          rw [hlen]
          have hkv : k.val < u.length + v.length + 2 := by simpa [hlenL] using k.isLt
          have hks : k.val + 1 < u.length + v.length + 2 := by dsimp [iB] at hjlast; omega
          dsimp [k1]
          omega)⟩ : Fin (b :: (v ++ [a])).length) = iB1 := Fin.ext hidx
      rw [← hfin]
      exact htemp

private theorem hchildNextAt907 :
    ∀ (n : Nat), ∀ (a : Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3 : ℕ))), ∀ (u : List (Fin (n + (3 :
        ℕ)))), ∀ (v : List (Fin (n + (3 : ℕ)))), ∀ (hv : (0 : ℕ) < v.length), ∀ (k : Fin (a :: (u
        ++ b :: v)).length), ∀ (hlenL : (a :: (u ++ b :: v)).length = u.length + v.length + 2), ∀
        (hkA : ¬(↑k : ℕ) ≤ u.length), ∀ (hjval : k.val - (u.length + 1) ≤ v.length),
    let iB : Fin (b :: (v ++ [a])).length :=
      ⟨k.val - (u.length + 1), by
        have hlen : (b :: (v ++ [a])).length = v.length + 2 := by simp
        rw [hlen]
        omega⟩
    ∀ (hjlast : (↑iB : ℕ) < v.length),
    let k1 : Fin (a :: (u ++ b :: v)).length :=
      ⟨k.val + 1, by
        have hks : k.val + 1 < u.length + v.length + 2 := by dsimp [iB] at hjlast; omega
        simpa [hlenL] using hks⟩
    ∀ (hk1mod : (k.val + 1) % (a :: (u ++ b :: v)).length = k.val + 1),
    let iB1 : Fin (b :: (v ++ [a])).length :=
      ⟨k1.val - (u.length + 1), by
        have hlen : (b :: (v ++ [a])).length = v.length + 2 := by simp
        rw [hlen]
        have hks : k.val + 1 < u.length + v.length + 2 := by dsimp [iB] at hjlast; omega
        dsimp [k1]
        omega⟩
    (b :: (v ++ [a])).get
          ⟨(iB.val + 1) % (b :: (v ++ [a])).length,
            Nat.mod_lt _ (Nat.zero_lt_of_lt iB.isLt)⟩ =
        (b :: (v ++ [a])).get iB1 := by
  classical
  intro n a b u v hv k hlenL hkA hjval iB hjlast k1 hk1mod iB1
  apply congrArg
  apply Fin.ext
  have hlen : (b :: (v ++ [a])).length = v.length + 2 := by simp
  have hstep : iB.val + 1 < (b :: (v ++ [a])).length := by
    have hvlen : v.length < (b :: (v ++ [a])).length := by omega
    omega
  have hiB1 : iB1.val = iB.val + 1 := by dsimp [iB, iB1, k1]; omega
  exact (Nat.mod_eq_of_lt hstep).trans hiB1.symm

private theorem hchildNextAt975 :
    ∀ (n : Nat), ∀ (a : Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3 : ℕ))), ∀ (u : List (Fin (n + (3 :
        ℕ)))), ∀ (v : List (Fin (n + (3 : ℕ)))), ∀ (k : Fin (a :: (u ++ b :: v)).length), ∀
            (hjval : k.val - (u.length + 1) ≤ v.length),
    let iB : Fin (b :: (v ++ [a])).length :=
      ⟨k.val - (u.length + 1), by
        have hlen : (b :: (v ++ [a])).length = v.length + 2 := by simp
        rw [hlen]
        omega⟩
    (iB.val = v.length) → (
    let iB1 : Fin (b :: (v ++ [a])).length := ⟨v.length + 1, by simp⟩
    (b :: (v ++ [a])).get
          ⟨(iB.val + 1) % (b :: (v ++ [a])).length,
            Nat.mod_lt _ (Nat.zero_lt_of_lt iB.isLt)⟩ =
        (b :: (v ++ [a])).get iB1) := by
  classical
  intro n a b u v k hjval iB hjEq iB1
  apply congrArg
  apply Fin.ext
  have hiEq : iB.val + 1 = v.length + 1 := by omega
  have hstep : iB.val + 1 < (b :: (v ++ [a])).length := by
    have hstep' : iB.val + 1 < v.length + 2 := by rw [hiEq]; omega
    have hlen : v.length + 2 = (b :: (v ++ [a])).length := by simp
    exact Nat.lt_of_lt_of_eq hstep' hlen
  exact (Nat.mod_eq_of_lt hstep).trans (by rw [hiEq])

private theorem hcycR :
    ∀ (n : Nat), ∀ (L : List (Fin (n + (3 : ℕ)))), ∀ (k : ℕ), (∃ (k : ℕ), L.Sublist ((List.ofFn
        fun (i : Fin (n + (3 : ℕ))) => i).rotate k)) → (∃ m : Nat, (L.rotate k).Sublist
      ((List.ofFn (fun i : Fin (n + 3) => i)).rotate m)) := by
  classical
  intro n L k hcyc
  obtain ⟨r, hr⟩ := hcyc
  have hrotateSublist (h : L.Sublist
      ((List.ofFn (fun i : Fin (n + 3) => i)).rotate r)) :
      ∃ s, (L.rotate k).Sublist
        (((List.ofFn (fun i : Fin (n + 3) => i)).rotate r).rotate s) := by
    have hs : (L.take (k % L.length) ++ L.drop (k % L.length)).Sublist
        ((List.ofFn (fun i : Fin (n + 3) => i)).rotate r) := by
      simpa only [List.take_append_drop] using h
    obtain ⟨A, B, hroot, htake, hdrop⟩ := List.append_sublist_iff.mp hs
    refine ⟨A.length, ?_⟩
    rw [hroot, List.rotate_append_length_eq, List.rotate_eq_drop_append_take_mod]
    exact hdrop.append htake
  obtain ⟨s, hs⟩ := hrotateSublist hr
  exact ⟨r + s, by simpa only [List.rotate_rotate] using hs⟩

end SavedDissectionProof

namespace SavedDissectionCases

private theorem triangleCase :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), (Function.Injective q ∧ (∀ (f : Fin (3 : ℕ) →
        Fin (n + (3 : ℕ))), Function.Injective f → P3381T1TriangleDeterminant (q ∘ f) ≠ (0 :
        ℝ)) ∧ ∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3 : ℕ))), j ≠ i → j ≠ i + (1 : Fin (n +
        (3 : ℕ))) → (0 : ℝ) < P3381T1TriangleDeterminant ![q i, q (i + (1 : Fin (n + (3 :
        ℕ)))), q j]) → (
    let Good : List (Fin (n + 3)) → List (Fin 3 → Fin (n + 3)) → Prop := fun L F =>
      L.Nodup →
      (∃ k : Nat, L.Sublist
        ((List.ofFn (fun i : Fin (n + 3) => i)).rotate k)) →
      (∀ f ∈ F, Function.Injective f ∧
        Set.range f ⊆ {i | i ∈ L} ∧
        P3381T1TriangleDeterminant (q ∘ f) ≠ 0) ∧
      F.Pairwise (fun f g => Set.range f ≠ Set.range g) ∧
      convexHull Real (q '' {i | i ∈ L}) =
        ⋃ (f : Fin 3 → Fin (n + 3)) (_ : f ∈ F),
          convexHull Real (Set.range (q ∘ f)) ∧
      (∀ f ∈ F, ∀ g ∈ F,
        convexHull Real (Set.range (q ∘ f)) ∩
          convexHull Real (Set.range (q ∘ g)) =
          convexHull Real (q '' (Set.range f ∩ Set.range g))) ∧
      (∀ k : Fin L.length,
        ∃! f : Fin 3 → Fin (n + 3), f ∈ F ∧
          L.get k ∈ Set.range f ∧
          L.get ⟨(k.val + 1) % L.length,
            Nat.mod_lt _ (Nat.zero_lt_of_lt k.isLt)⟩ ∈ Set.range f)
    ∀ (a : Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3 : ℕ))), ∀ (c : Fin (n + (3 : ℕ))), ([a, b,
        c].Nodup) → ((∃ (k : ℕ), [a, b, c].Sublist ((List.ofFn fun (i : Fin (n + (3 : ℕ))) =>
        i).rotate k)) → (Good [a, b, c] [![a, b, c]]))) := by
  classical
  intro n q hsupport Good a b c hboundary hcyclic hnd hcyc
  have hnd' : (a ≠ b ∧ a ≠ c) ∧ b ≠ c := by simpa using hnd
  let f : Fin 3 → Fin (n + 3) := ![a, b, c]
  have hfi : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hdet : P3381T1TriangleDeterminant (q ∘ f) ≠ 0 :=
    hsupport.2.1 f hfi
  have hset := SavedDissectionProof.hsetAt164
      n q a b c hboundary hcyclic hnd hcyc hnd' hfi hdet
  refine ⟨?_, by simp, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_singleton] at hg
    subst g
    refine ⟨hfi, ?_, hdet⟩
    intro x hx
    rcases hx with ⟨i, rfl⟩
    fin_cases i <;> simp []
  · calc
      convexHull Real (q '' {i | i ∈ [a, b, c]}) =
          convexHull Real (Set.range (q ∘ f)) := congrArg (convexHull Real) hset
      _ = ⋃ g ∈ [f], convexHull Real (Set.range (q ∘ g)) := by simp
  · intro g hg j hj
    simp only [List.mem_singleton] at hg hj
    subst g
    subst j
    simp [Set.range_comp]
  · intro k
    fin_cases k
    · refine ⟨f, ?_, ?_⟩
      · simp [f]
      · intro g hg
        exact List.mem_singleton.mp hg.1
    · refine ⟨f, ?_, ?_⟩
      · simp [f]
      · intro g hg
        exact List.mem_singleton.mp hg.1
    · refine ⟨f, ?_, ?_⟩
      · simp [f]
      · intro g hg
        exact List.mem_singleton.mp hg.1

private theorem leftBoundaryCase :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real),
    let Good : List (Fin (n + 3)) → List (Fin 3 → Fin (n + 3)) → Prop := fun L F =>
      L.Nodup →
      (∃ k : Nat, L.Sublist
        ((List.ofFn (fun i : Fin (n + 3) => i)).rotate k)) →
      (∀ f ∈ F, Function.Injective f ∧
        Set.range f ⊆ {i | i ∈ L} ∧
        P3381T1TriangleDeterminant (q ∘ f) ≠ 0) ∧
      F.Pairwise (fun f g => Set.range f ≠ Set.range g) ∧
      convexHull Real (q '' {i | i ∈ L}) =
        ⋃ (f : Fin 3 → Fin (n + 3)) (_ : f ∈ F),
          convexHull Real (Set.range (q ∘ f)) ∧
      (∀ f ∈ F, ∀ g ∈ F,
        convexHull Real (Set.range (q ∘ f)) ∩
          convexHull Real (Set.range (q ∘ g)) =
          convexHull Real (q '' (Set.range f ∩ Set.range g))) ∧
      (∀ k : Fin L.length,
        ∃! f : Fin 3 → Fin (n + 3), f ∈ F ∧
          L.get k ∈ Set.range f ∧
          L.get ⟨(k.val + 1) % L.length,
            Nat.mod_lt _ (Nat.zero_lt_of_lt k.isLt)⟩ ∈ Set.range f)
    ∀ (a : Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3 : ℕ))), ∀ (u : List (Fin (n + (3 : ℕ)))), ∀ (v
        : List (Fin (n + (3 : ℕ)))), ∀ (left : List (Fin (3 : ℕ) → Fin (n + (3 : ℕ)))), ∀ (right
        : List (Fin (3 : ℕ) → Fin (n + (3 : ℕ)))), ∀ (hv : (0 : ℕ) < v.length), ∀ (hndA : (a ::
        (u ++ [b])).Nodup), ∀ (hcycA : ∃ (k : ℕ), (a :: (u ++ [b])).Sublist ((List.ofFn fun (i :
        Fin (n + (3 : ℕ))) => i).rotate k)), ∀ (hgoodA : Good (a :: (u ++ [b])) left), ∀ (hfaceB
        : ∀ f ∈ right, Function.Injective f ∧ Set.range f ⊆ {i : Fin (n + (3 : ℕ)) | i ∈ b :: (v
        ++ [a])} ∧ P3381T1TriangleDeterminant (q ∘ f) ≠ (0 : ℝ)), (∀ (i : Fin (a :: (u ++ b ::
        v)).length), ∀ (hi : i.val ≤ u.length + 1), (a :: (u ++ b :: v)).get i =
        (a :: (u ++ [b])).get ⟨i.val, by
          have hlen : (a :: (u ++ [b])).length = u.length + 2 := by simp
          rw [hlen]
          omega⟩) → ((∀ (i : Fin (a :: (u ++ [b])).length), ∀ (j : Fin (a :: (u ++ [b])).length),
              (i.val + 1 = j.val) → (((a :: (u ++ [b])).get i ∈ ({a, b} : Set (Fin (n + 3)))) →
              (((a :: (u ++ [b])).get j ∈ ({a, b} : Set (Fin (n + 3)))) → (False)))) → (∀ (k :
              Fin (a :: (u ++ b :: v)).length), ((a :: (u ++ b :: v)).length = u.length +
              v.length + 2) → ((∀ (x : Fin (n + 3)), (x ∈ a :: (u ++ [b])) → ((x ∈ b :: (v ++
              [a])) → (x ∈ ({a, b} : Set (Fin (n + 3)))))) → (((↑k : ℕ) ≤ u.length) → (∃! f : Fin
              3 → Fin (n + 3), f ∈ left ++ right ∧ (a :: (u ++ b :: v)).get k ∈ Set.range f ∧ (a
              :: (u ++ b :: v)).get ⟨(k.val + 1) % (a :: (u ++ b :: v)).length, Nat.mod_lt _
              (Nat.zero_lt_of_lt k.isLt)⟩ ∈ Set.range f))))) := by
  classical
  intro n q Good a b u v left right hv hndA hcycA hgoodA hfaceB hAget hNoAEndpoints k hlenL
      hABpoint hkA
  let iA : Fin (a :: (u ++ [b])).length :=
    ⟨k.val, by have hlen : (a :: (u ++ [b])).length = u.length + 2 := by simp
               rw [hlen]; omega⟩
  let iA1 : Fin (a :: (u ++ [b])).length :=
    ⟨k.val + 1, by have hlen : (a :: (u ++ [b])).length = u.length + 2 := by simp
                   rw [hlen]; omega⟩
  have hk1Lt : k.val + 1 < (a :: (u ++ b :: v)).length := by
    have hk1 : k.val + 1 < u.length + v.length + 2 := by omega
    simpa [hlenL] using hk1
  let k1 : Fin (a :: (u ++ b :: v)).length := ⟨k.val + 1, hk1Lt⟩
  let nextParent : Fin (a :: (u ++ b :: v)).length :=
    ⟨(k.val + 1) % (a :: (u ++ b :: v)).length,
      Nat.mod_lt _ (Nat.zero_lt_of_lt k.isLt)⟩
  have hnextIndex : nextParent = k1 := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt hk1Lt
  have hfirst : (a :: (u ++ b :: v)).get k = (a :: (u ++ [b])).get iA := by
    exact hAget k (by omega)
  have hsecond :
      (a :: (u ++ b :: v)).get nextParent = (a :: (u ++ [b])).get iA1 := by
    calc
      (a :: (u ++ b :: v)).get nextParent = (a :: (u ++ b :: v)).get k1 := by
        rw [hnextIndex]
      _ = (a :: (u ++ [b])).get iA1 := by
        exact hAget k1 (by dsimp [k1]; omega)
  have hchildNext := SavedDissectionProof.hchildNextAt805 n a b u v k hkA hk1Lt
  have hincA := (hgoodA hndA hcycA).2.2.2.2 iA
  rcases hincA with ⟨f, hfA, huniqA⟩
  have hfAfirst : (a :: (u ++ [b])).get iA ∈ Set.range f := hfA.2.1
  have hfAsecond : (a :: (u ++ [b])).get iA1 ∈ Set.range f := by
    rw [← hchildNext]
    exact hfA.2.2
  refine ⟨f, ?_, ?_⟩
  · refine ⟨List.mem_append_left _ hfA.1, ?_, ?_⟩
    · rw [hfirst]; exact hfAfirst
    · change (a :: (u ++ b :: v)).get nextParent ∈ Set.range f
      rw [hsecond]
      exact hfAsecond
  · intro g hg
    rcases List.mem_append.mp hg.1 with hgA | hgB
    · apply huniqA g
      refine ⟨hgA, ?_, ?_⟩
      · rw [← hfirst]; exact hg.2.1
      · have hgSecond := hg.2.2
        change (a :: (u ++ b :: v)).get nextParent ∈ Set.range g at hgSecond
        rw [hsecond] at hgSecond
        rw [← hchildNext] at hgSecond
        exact hgSecond
    · have hxgA : (a :: (u ++ [b])).get iA ∈ Set.range g := by
        rw [← hfirst]; exact hg.2.1
      have hygA : (a :: (u ++ [b])).get iA1 ∈ Set.range g := by
        have hgSecond := hg.2.2
        change (a :: (u ++ b :: v)).get nextParent ∈ Set.range g at hgSecond
        rw [hsecond] at hgSecond
        exact hgSecond
      have hsmallA : (a :: (u ++ [b])).get iA ∈ ({a, b} : Set _) :=
        hABpoint _ (List.get_mem _ iA)
          ((hfaceB g hgB).2.1 hxgA)
      have hsmallA1 : (a :: (u ++ [b])).get iA1 ∈ ({a, b} : Set _) :=
        hABpoint _ (List.get_mem _ iA1)
          ((hfaceB g hgB).2.1 hygA)
      exact False.elim (hNoAEndpoints iA iA1 (by dsimp [iA, iA1]) hsmallA hsmallA1)

private theorem rightBoundaryCase :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real),
    let Good : List (Fin (n + 3)) → List (Fin 3 → Fin (n + 3)) → Prop := fun L F =>
      L.Nodup →
      (∃ k : Nat, L.Sublist
        ((List.ofFn (fun i : Fin (n + 3) => i)).rotate k)) →
      (∀ f ∈ F, Function.Injective f ∧
        Set.range f ⊆ {i | i ∈ L} ∧
        P3381T1TriangleDeterminant (q ∘ f) ≠ 0) ∧
      F.Pairwise (fun f g => Set.range f ≠ Set.range g) ∧
      convexHull Real (q '' {i | i ∈ L}) =
        ⋃ (f : Fin 3 → Fin (n + 3)) (_ : f ∈ F),
          convexHull Real (Set.range (q ∘ f)) ∧
      (∀ f ∈ F, ∀ g ∈ F,
        convexHull Real (Set.range (q ∘ f)) ∩
          convexHull Real (Set.range (q ∘ g)) =
          convexHull Real (q '' (Set.range f ∩ Set.range g))) ∧
      (∀ k : Fin L.length,
        ∃! f : Fin 3 → Fin (n + 3), f ∈ F ∧
          L.get k ∈ Set.range f ∧
          L.get ⟨(k.val + 1) % L.length,
            Nat.mod_lt _ (Nat.zero_lt_of_lt k.isLt)⟩ ∈ Set.range f)
    ∀ (a : Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3 : ℕ))), ∀ (u : List (Fin (n + (3 : ℕ)))), ∀ (v
        : List (Fin (n + (3 : ℕ)))), ∀ (left : List (Fin (3 : ℕ) → Fin (n + (3 : ℕ)))), ∀ (right
        : List (Fin (3 : ℕ) → Fin (n + (3 : ℕ)))), ∀ (hv : (0 : ℕ) < v.length), ∀ (hndB : (b ::
        (v ++ [a])).Nodup), ∀ (hcycB : ∃ (k : ℕ), (b :: (v ++ [a])).Sublist ((List.ofFn fun (i :
        Fin (n + (3 : ℕ))) => i).rotate k)), ∀ (hgoodB : Good (b :: (v ++ [a])) right), ∀ (hfaceA
        : ∀ f ∈ left, Function.Injective f ∧ Set.range f ⊆ {i : Fin (n + (3 : ℕ)) | i ∈ a :: (u
        ++ [b])} ∧ P3381T1TriangleDeterminant (q ∘ f) ≠ (0 : ℝ)), ∀ (hlenL : (a :: (u ++ b ::
        v)).length = u.length + v.length + 2), (∀ (j : Fin (a :: (u ++ b :: v)).length), ∀ (hj :
        u.length + 1 ≤ j.val), (a :: (u ++ b :: v)).get j =
        (b :: (v ++ [a])).get ⟨j.val - (u.length + 1), by
          have hlenB : (b :: (v ++ [a])).length = v.length + 2 := by simp
          rw [hlenB]
          omega⟩) → ((∀ (i : Fin (b :: (v ++ [a])).length), ∀ (j : Fin (b :: (v ++ [a])).length),
              (i.val + 1 = j.val) → (((b :: (v ++ [a])).get i ∈ ({a, b} : Set (Fin (n + 3)))) →
              (((b :: (v ++ [a])).get j ∈ ({a, b} : Set (Fin (n + 3)))) → (False)))) → (∀ (k :
              Fin (a :: (u ++ b :: v)).length), (∀ (x : Fin (n + 3)), (x ∈ a :: (u ++ [b])) → ((x
              ∈ b :: (v ++ [a])) → (x ∈ ({a, b} : Set (Fin (n + 3)))))) → ((¬(↑k : ℕ) ≤ u.length)
              → (∃! f : Fin 3 → Fin (n + 3), f ∈ left ++ right ∧ (a :: (u ++ b :: v)).get k ∈
              Set.range f ∧ (a :: (u ++ b :: v)).get ⟨(k.val + 1) % (a :: (u ++ b :: v)).length,
              Nat.mod_lt _ (Nat.zero_lt_of_lt k.isLt)⟩ ∈ Set.range f)))) := by
  classical
  intro n q Good a b u v left right hv hndB hcycB hgoodB hfaceA hlenL hBget hNoBEndpoints k
      hABpoint hkA
  have hkB : u.length + 1 ≤ k.val := by omega
  have hjval : k.val - (u.length + 1) ≤ v.length := by
    have hkv : k.val < u.length + v.length + 2 := by simpa [hlenL] using k.isLt
    omega
  let iB : Fin (b :: (v ++ [a])).length :=
    ⟨k.val - (u.length + 1), by
      have hlen : (b :: (v ++ [a])).length = v.length + 2 := by simp
      rw [hlen]
      omega⟩
  have hfirst : (a :: (u ++ b :: v)).get k = (b :: (v ++ [a])).get iB := by
    simpa [iB] using hBget k hkB
  by_cases hjlast : iB.val < v.length
  · let k1 : Fin (a :: (u ++ b :: v)).length :=
      ⟨k.val + 1, by
        have hkv : k.val < u.length + v.length + 2 := by simpa [hlenL] using k.isLt
        have hks : k.val + 1 < u.length + v.length + 2 := by dsimp [iB] at hjlast; omega
        simpa [hlenL] using hks⟩
    let nextParent : Fin (a :: (u ++ b :: v)).length :=
      ⟨(k.val + 1) % (a :: (u ++ b :: v)).length,
        Nat.mod_lt _ (Nat.zero_lt_of_lt k.isLt)⟩
    have hk1mod : (k.val + 1) % (a :: (u ++ b :: v)).length = k.val + 1 := by
      have hkv : k.val < u.length + v.length + 2 := by simpa [hlenL] using k.isLt
      have hks : k.val + 1 < u.length + v.length + 2 := by dsimp [iB] at hjlast; omega
      simpa [hlenL] using Nat.mod_eq_of_lt hks
    have hnextIndex : nextParent = k1 := by
      apply Fin.ext
      exact hk1mod
    let iB1 : Fin (b :: (v ++ [a])).length :=
      ⟨k1.val - (u.length + 1), by
        have hlen : (b :: (v ++ [a])).length = v.length + 2 := by simp
        rw [hlen]
        have hkv : k.val < u.length + v.length + 2 := by simpa [hlenL] using k.isLt
        have hks : k.val + 1 < u.length + v.length + 2 := by dsimp [iB] at hjlast; omega
        dsimp [k1]
        omega⟩
    have hsecond := SavedDissectionProof.hsecondAt889 n a b u v hv hBget k hlenL hkA hjval hjlast
            hk1mod hnextIndex
    have hchildNext := SavedDissectionProof.hchildNextAt907 n a b u v hv
              k hlenL hkA hjval hjlast hk1mod
    have hincB := (hgoodB hndB hcycB).2.2.2.2 iB
    rcases hincB with ⟨f, hfB, huniqB⟩
    have hfBfirst : (b :: (v ++ [a])).get iB ∈ Set.range f := hfB.2.1
    have hfBsecond : (b :: (v ++ [a])).get iB1 ∈ Set.range f := by
      rw [← hchildNext]
      exact hfB.2.2
    refine ⟨f, ?_, ?_⟩
    · refine ⟨List.mem_append_right _ hfB.1, ?_, ?_⟩
      · rw [hfirst]; exact hfBfirst
      · change (a :: (u ++ b :: v)).get nextParent ∈ Set.range f
        rw [hsecond]
        exact hfBsecond
    · intro g hg
      rcases List.mem_append.mp hg.1 with hgA | hgB
      · have hxgB : (b :: (v ++ [a])).get iB ∈ Set.range g := by
          rw [← hfirst]; exact hg.2.1
        have hygB : (b :: (v ++ [a])).get iB1 ∈ Set.range g := by
          have hgSecond := hg.2.2
          change (a :: (u ++ b :: v)).get nextParent ∈ Set.range g at hgSecond
          rw [hsecond] at hgSecond
          exact hgSecond
        have hsmallB : (b :: (v ++ [a])).get iB ∈ ({a, b} : Set _) :=
          hABpoint _ ((hfaceA g hgA).2.1 hxgB) (List.get_mem _ iB)
        have hsmallB1 : (b :: (v ++ [a])).get iB1 ∈ ({a, b} : Set _) :=
          hABpoint _ ((hfaceA g hgA).2.1 hygB) (List.get_mem _ iB1)
        exact False.elim (hNoBEndpoints iB iB1 (by dsimp [iB, iB1, k1]; omega)
          hsmallB hsmallB1)
      · apply huniqB g
        refine ⟨hgB, ?_, ?_⟩
        · rw [← hfirst]; exact hg.2.1
        · have hgSecond := hg.2.2
          change (a :: (u ++ b :: v)).get nextParent ∈ Set.range g at hgSecond
          rw [hsecond] at hgSecond
          rw [← hchildNext] at hgSecond
          exact hgSecond
  · have hjEq : iB.val = v.length := by
      have hival : iB.val = k.val - (u.length + 1) := rfl
      omega
    have hkLast : k.val + 1 = (a :: (u ++ b :: v)).length := by
      have hkv : k.val < u.length + v.length + 2 := by simpa [hlenL] using k.isLt
      dsimp [iB] at hjEq
      omega
    let nextParent : Fin (a :: (u ++ b :: v)).length :=
      ⟨(k.val + 1) % (a :: (u ++ b :: v)).length,
        Nat.mod_lt _ (Nat.zero_lt_of_lt k.isLt)⟩
    have hnextZero : nextParent = 0 := by
      apply Fin.ext
      change (k.val + 1) % (a :: (u ++ b :: v)).length = 0
      rw [hkLast]
      exact Nat.mod_self _
    let iB1 : Fin (b :: (v ++ [a])).length := ⟨v.length + 1, by simp⟩
    have hsecond :
        (a :: (u ++ b :: v)).get nextParent = (b :: (v ++ [a])).get iB1 := by
      rw [hnextZero]
      simp [iB1, List.get_eq_getElem]
    have hchildNext := SavedDissectionProof.hchildNextAt975 n a b u v k
              hjval hjEq
    have hincB := (hgoodB hndB hcycB).2.2.2.2 iB
    rcases hincB with ⟨f, hfB, huniqB⟩
    have hfBfirst : (b :: (v ++ [a])).get iB ∈ Set.range f := hfB.2.1
    have hfBsecond : (b :: (v ++ [a])).get iB1 ∈ Set.range f := by
      rw [← hchildNext]
      exact hfB.2.2
    refine ⟨f, ?_, ?_⟩
    · refine ⟨List.mem_append_right _ hfB.1, ?_, ?_⟩
      · rw [hfirst]; exact hfBfirst
      · change (a :: (u ++ b :: v)).get nextParent ∈ Set.range f
        rw [hsecond]
        exact hfBsecond
    · intro g hg
      rcases List.mem_append.mp hg.1 with hgA | hgB
      · have hxgB : (b :: (v ++ [a])).get iB ∈ Set.range g := by
          rw [← hfirst]; exact hg.2.1
        have hygB : (b :: (v ++ [a])).get iB1 ∈ Set.range g := by
          have hgSecond := hg.2.2
          change (a :: (u ++ b :: v)).get nextParent ∈ Set.range g at hgSecond
          rw [hsecond] at hgSecond
          exact hgSecond
        have hsmallB : (b :: (v ++ [a])).get iB ∈ ({a, b} : Set _) :=
          hABpoint _ ((hfaceA g hgA).2.1 hxgB) (List.get_mem _ iB)
        have hsmallB1 : (b :: (v ++ [a])).get iB1 ∈ ({a, b} : Set _) :=
          hABpoint _ ((hfaceA g hgA).2.1 hygB) (List.get_mem _ iB1)
        exact False.elim (hNoBEndpoints iB iB1 (by dsimp [iB, iB1]; omega)
          hsmallB hsmallB1)
      · apply huniqB g
        refine ⟨hgB, ?_, ?_⟩
        · rw [← hfirst]; exact hg.2.1
        · have hgSecond := hg.2.2
          change (a :: (u ++ b :: v)).get nextParent ∈ Set.range g at hgSecond
          rw [hsecond] at hgSecond
          rw [← hchildNext] at hgSecond
          exact hgSecond

private theorem rotationCase :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real),
    let Good : List (Fin (n + 3)) → List (Fin 3 → Fin (n + 3)) → Prop := fun L F =>
      L.Nodup →
      (∃ k : Nat, L.Sublist
        ((List.ofFn (fun i : Fin (n + 3) => i)).rotate k)) →
      (∀ f ∈ F, Function.Injective f ∧
        Set.range f ⊆ {i | i ∈ L} ∧
        P3381T1TriangleDeterminant (q ∘ f) ≠ 0) ∧
      F.Pairwise (fun f g => Set.range f ≠ Set.range g) ∧
      convexHull Real (q '' {i | i ∈ L}) =
        ⋃ (f : Fin 3 → Fin (n + 3)) (_ : f ∈ F),
          convexHull Real (Set.range (q ∘ f)) ∧
      (∀ f ∈ F, ∀ g ∈ F,
        convexHull Real (Set.range (q ∘ f)) ∩
          convexHull Real (Set.range (q ∘ g)) =
          convexHull Real (q '' (Set.range f ∩ Set.range g))) ∧
      (∀ k : Fin L.length,
        ∃! f : Fin 3 → Fin (n + 3), f ∈ F ∧
          L.get k ∈ Set.range f ∧
          L.get ⟨(k.val + 1) % L.length,
            Nat.mod_lt _ (Nat.zero_lt_of_lt k.isLt)⟩ ∈ Set.range f)
    ∀ (L : List (Fin (n + (3 : ℕ)))), ∀ (F : List (Fin (3 : ℕ) → Fin (n + (3 : ℕ)))), ∀ (k : ℕ),
        (P3511T1CyclicDissection (Fin (n + (3 : ℕ))) (L.rotate k) F) → (((L.rotate k).Nodup →
        (∃ (k_1 : ℕ), (L.rotate k).Sublist ((List.ofFn fun (i : Fin (n + (3 : ℕ))) => i).rotate
        k_1)) → Good (L.rotate k) F) → (Good L F)) := by
  classical
  intro n q Good L F k d ih hnd hcyc
  have hndR : (L.rotate k).Nodup := by simpa using hnd
  have hcycR := SavedDissectionProof.hcycR n L k hcyc
  have hR : Good (L.rotate k) F := ih hndR hcycR
  have hRfacts := hR hndR hcycR
  have hset : q '' {i | i ∈ L} = q '' {i | i ∈ L.rotate k} := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, (List.mem_rotate).2 hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, (List.mem_rotate).1 hi, rfl⟩
  have hreplaceMod (N x y : Nat) : (x + y % N) % N = (x + y) % N := by
    rw [Nat.add_mod, Nat.add_mod]
    simp
  have hsuccMod (N x : Nat) : ((x % N) + 1) % N = (x + 1) % N := by
    rw [Nat.add_mod, Nat.add_mod]
    simp
  have hrotateSuccMod (N r i : Nat) :
      (N - r + ((i + 1) % N)) % N = (((N - r + i) % N) + 1) % N := by
    calc
      (N - r + ((i + 1) % N)) % N = (N - r + (i + 1)) % N :=
        hreplaceMod N (N - r) (i + 1)
      _ = ((N - r + i) % N + 1) % N := (hsuccMod N (N - r + i)).symm
  refine ⟨?_, hRfacts.2.1, ?_, hRfacts.2.2.2.1, ?_⟩
  · intro f hf
    rcases hRfacts.1 f hf with ⟨hfi, hsub, hdet⟩
    refine ⟨hfi, ?_, hdet⟩
    intro x hx
    exact (List.mem_rotate).1 (hsub hx)
  · calc
      convexHull Real (q '' {i | i ∈ L}) =
          convexHull Real (q '' {i | i ∈ L.rotate k}) :=
        congrArg (convexHull Real) hset
      _ = ⋃ (f : Fin 3 → Fin (n + 3)) (_ : f ∈ F),
            convexHull Real (Set.range (q ∘ f)) := hRfacts.2.2.1
  · intro i
    let offset := L.length - k % L.length
    let j : Fin (L.rotate k).length :=
      ⟨(offset + i.val) % L.length, by
        simp only [List.length_rotate]
        exact Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
    let nextI : Fin L.length :=
      ⟨(i.val + 1) % L.length, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
    let jNext : Fin (L.rotate k).length :=
      ⟨(offset + nextI.val) % L.length, by
        simp only [List.length_rotate]
        exact Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
    let jSucc : Fin (L.rotate k).length :=
      ⟨(j.val + 1) % (L.rotate k).length,
        Nat.mod_lt _ (Nat.zero_lt_of_lt j.isLt)⟩
    have hjEq : jNext = jSucc := by
      apply Fin.ext
      change (offset + nextI.val) % L.length = (j.val + 1) % (L.rotate k).length
      simp only [List.length_rotate]
      dsimp [nextI, jNext, jSucc, j, offset]
      exact hrotateSuccMod L.length (k % L.length) i.val
    have hfirst : L.get i = (L.rotate k).get j := by
      simpa [j, offset] using List.get_eq_get_rotate L k i
    have hsecond : L.get nextI = (L.rotate k).get jSucc := by
      have h := List.get_eq_get_rotate L k nextI
      simpa [jNext, offset, hjEq] using h
    obtain ⟨f, hfR, huniqR⟩ := hRfacts.2.2.2.2 j
    refine ⟨f, ?_, ?_⟩
    · refine ⟨hfR.1, ?_, ?_⟩
      · rw [hfirst]
        exact hfR.2.1
      · rw [hsecond]
        exact hfR.2.2
    · intro g hg
      apply huniqR g
      refine ⟨hg.1, ?_, ?_⟩
      · rw [← hfirst]
        exact hg.2.1
      · rw [← hsecond]
        exact hg.2.2

end SavedDissectionCases

theorem P3555T2SavedDissectionGeometry {n : Nat}
    (q : Fin (n + 3) → Real × Real)
    (hq : ∀ i, q i = ((i.val : Real), (i.val : Real) ^ 2))
    (boundary : List (Fin (n + 3)))
    (faces : List (Fin 3 → Fin (n + 3)))
    (hboundary : boundary.Nodup)
    (hcyclic : ∃ k : Nat, boundary.Sublist
      ((List.ofFn (fun i : Fin (n + 3) => i)).rotate k))
    (hd : P3511T1CyclicDissection (Fin (n + 3)) boundary faces) :
    (∀ f ∈ faces, Function.Injective f ∧
      Set.range f ⊆ {i | i ∈ boundary} ∧
      P3381T1TriangleDeterminant (q ∘ f) ≠ 0) ∧
    faces.Pairwise (fun f g => Set.range f ≠ Set.range g) ∧
    convexHull Real (q '' {i | i ∈ boundary}) =
      ⋃ (f : Fin 3 → Fin (n + 3)) (_ : f ∈ faces),
        convexHull Real (Set.range (q ∘ f)) ∧
    (∀ f ∈ faces, ∀ g ∈ faces,
      convexHull Real (Set.range (q ∘ f)) ∩
        convexHull Real (Set.range (q ∘ g)) =
        convexHull Real (q '' (Set.range f ∩ Set.range g))) ∧
    (∀ k : Fin boundary.length,
      ∃! f : Fin 3 → Fin (n + 3), f ∈ faces ∧
        boundary.get k ∈ Set.range f ∧
        boundary.get ⟨(k.val + 1) % boundary.length,
          Nat.mod_lt _ (Nat.zero_lt_of_lt k.isLt)⟩ ∈ Set.range f) := by
-- BODY
  classical
  have hsupport := P3555T2ParabolaSupporting q hq
  let Good : List (Fin (n + 3)) → List (Fin 3 → Fin (n + 3)) → Prop := fun L F =>
    L.Nodup →
    (∃ k : Nat, L.Sublist
      ((List.ofFn (fun i : Fin (n + 3) => i)).rotate k)) →
    (∀ f ∈ F, Function.Injective f ∧
      Set.range f ⊆ {i | i ∈ L} ∧
      P3381T1TriangleDeterminant (q ∘ f) ≠ 0) ∧
    F.Pairwise (fun f g => Set.range f ≠ Set.range g) ∧
    convexHull Real (q '' {i | i ∈ L}) =
      ⋃ (f : Fin 3 → Fin (n + 3)) (_ : f ∈ F),
        convexHull Real (Set.range (q ∘ f)) ∧
    (∀ f ∈ F, ∀ g ∈ F,
      convexHull Real (Set.range (q ∘ f)) ∩
        convexHull Real (Set.range (q ∘ g)) =
        convexHull Real (q '' (Set.range f ∩ Set.range g))) ∧
    (∀ k : Fin L.length,
      ∃! f : Fin 3 → Fin (n + 3), f ∈ F ∧
        L.get k ∈ Set.range f ∧
        L.get ⟨(k.val + 1) % L.length,
          Nat.mod_lt _ (Nat.zero_lt_of_lt k.isLt)⟩ ∈ Set.range f)
  have hgood : Good boundary faces := by
    induction hd with
    | triangle a b c =>
      have triangleCase : Good [a, b, c] [![a, b, c]] := SavedDissectionCases.triangleCase n q
          hsupport a b c hboundary hcyclic
      exact triangleCase
    | split a b u v left right hu hv hleft hright ihleft ihright =>
      intro hnd hcyc
      have hcuts := P3555T2ParabolaChordCuts q hq a b u v hv hnd hcyc
      rcases hcuts with ⟨hab, hndA, hndB, hcycA, hcycB, hAB, hU, hV,
        hcutA, hcutB, hunion, hinter⟩
      have hgoodA : Good (a :: (u ++ [b])) left := ihleft hndA hcycA
      have hgoodB : Good (b :: (v ++ [a])) right := ihright hndB hcycB
      have hfaceA := (hgoodA hndA hcycA).1
      have hpairA := (hgoodA hndA hcycA).2.1
      have hfaceB := (hgoodB hndB hcycB).1
      have hpairB := (hgoodB hndB hcycB).2.1
      have hcoverA := (hgoodA hndA hcycA).2.2.1
      have hcoverB := (hgoodB hndB hcycB).2.2.1
      have hinterA := (hgoodA hndA hcycA).2.2.2.1
      have hinterB := (hgoodB hndB hcycB).2.2.2.1
      let D : Real × Real → Real := fun z =>
        P3381T1TriangleDeterminant ![q a, q b, z]
      have hDa : D (q a) = 0 := by simp [D, P3381T1TriangleDeterminant]
      have hDb : D (q b) = 0 := by simp [D, P3381T1TriangleDeterminant]
      have hDaffine (w : Fin 3 → Real) (p : Fin 3 → Real × Real)
          (hw : (∑ i, w i) = 1) :
          D (∑ i, w i • p i) = ∑ i, w i * D (p i) := SavedDissectionProof.hDaffine n q a b w p hw
      have faceChord (f : Fin 3 → Fin (n + 3))
          (φ : (Real × Real) → Real)
          (hφ : ∀ (w : Fin 3 → Real) (p : Fin 3 → Real × Real),
            (∑ i, w i) = 1 → φ (∑ i, w i • p i) = ∑ i, w i * φ (p i))
          (hweak : ∀ i, φ (q (f i)) ≤ 0)
          (hstrict : ∀ i, f i ≠ a → f i ≠ b → φ (q (f i)) < 0)
          (z : Real × Real) (hz : z ∈ convexHull Real (Set.range (q ∘ f)))
          (hzφ : φ z = 0) := SavedDissectionProof.faceChord n q a b f φ hφ hweak hstrict z hz hzφ
      have hAparent := SavedDissectionProof.hAparent n a b u v
      have hBparent := SavedDissectionProof.hBparent n a b u v
      have hcross := SavedDissectionProof.hcross n q a b u v left right hAB
              hfaceA hfaceB
      have hDnegAffine (w : Fin 3 → Real) (p : Fin 3 → Real × Real)
          (hw : (∑ i, w i) = 1) :
          -D (∑ i, w i • p i) = ∑ i, w i * (-D (p i)) := by
        rw [hDaffine w p hw]
        simp
      have hsignA (f : Fin 3 → Fin (n + 3)) (hf : f ∈ left) := SavedDissectionProof.hsignA n q a b u
              left hU hfaceA hDa hDb f hf
      have hsignB (f : Fin 3 → Fin (n + 3)) (hf : f ∈ right) := SavedDissectionProof.hsignB n q a
          b v
              right hV hfaceB hDa hDb f hf
      have hendpoint_intersection (S T : Set (Fin (n + 3)))
          (hS : S ⊆ ({a, b} : Set (Fin (n + 3))))
          (hT : T ⊆ ({a, b} : Set (Fin (n + 3))))
          (z : Real × Real)
          (hzS : z ∈ convexHull Real (q '' S))
          (hzT : z ∈ convexHull Real (q '' T)) := SavedDissectionProof.hendpoint_intersection n q
              hsupport a b hab S T hS hT z hzS hzT
      have hcrossInter (f : Fin 3 → Fin (n + 3)) (hf : f ∈ left)
          (g : Fin 3 → Fin (n + 3)) (hg : g ∈ right) := SavedDissectionProof.hcrossInter n q a b
              u v left right hAB hinter hfaceA hfaceB
                hDa hDb hDaffine faceChord hDnegAffine hsignA hsignB hendpoint_intersection f hf
                g hg
      have hAget (i : Fin (a :: (u ++ b :: v)).length) (hi : i.val ≤ u.length + 1) :
          (a :: (u ++ b :: v)).get i =
            (a :: (u ++ [b])).get ⟨i.val, by
              have hlen : (a :: (u ++ [b])).length = u.length + 2 := by simp
              rw [hlen]
              omega⟩ := SavedDissectionProof.hAget n a b u v i hi
      have hBget (j : Fin (a :: (u ++ b :: v)).length) (hj : u.length + 1 ≤ j.val) :
          (a :: (u ++ b :: v)).get j =
            (b :: (v ++ [a])).get ⟨j.val - (u.length + 1), by
              have hlenL : (a :: (u ++ b :: v)).length = u.length + v.length + 2 := by
                simp; omega
              have hlenB : (b :: (v ++ [a])).length = v.length + 2 := by simp
              have hj' : j.val < u.length + v.length + 2 := by simpa [hlenL] using j.isLt
              rw [hlenB]
              omega⟩ := SavedDissectionProof.hBget n a b u v j hj
      have hNoAEndpoints (i j : Fin (a :: (u ++ [b])).length)
          (hij : i.val + 1 = j.val)
          (hia : (a :: (u ++ [b])).get i ∈ ({a, b} : Set (Fin (n + 3))))
          (hja : (a :: (u ++ [b])).get j ∈ ({a, b} : Set (Fin (n + 3)))) : False :=
              SavedDissectionProof.hNoAEndpoints n a b u v hu hndA i j hij hia hja
      have hNoBEndpoints (i j : Fin (b :: (v ++ [a])).length)
          (hij : i.val + 1 = j.val)
          (hia : (b :: (v ++ [a])).get i ∈ ({a, b} : Set (Fin (n + 3))))
          (hja : (b :: (v ++ [a])).get j ∈ ({a, b} : Set (Fin (n + 3)))) : False :=
              SavedDissectionProof.hNoBEndpoints n a b u v hv hndB i j hij hia hja
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro f hf
        rcases List.mem_append.mp hf with hf | hf
        · rcases hfaceA f hf with ⟨hfi, hsub, hdet⟩
          refine ⟨hfi, ?_, hdet⟩
          intro x hx
          exact hAparent x (hsub hx)
        · rcases hfaceB f hf with ⟨hfi, hsub, hdet⟩
          refine ⟨hfi, ?_, hdet⟩
          intro x hx
          exact hBparent x (hsub hx)
      · apply List.pairwise_append.mpr
        refine ⟨hpairA, hpairB, ?_⟩
        intro f hf g hg
        exact hcross f hf g hg
      · have hfaces := SavedDissectionProof.hfaces
                    n q left right
        calc
          convexHull Real (q '' {i | i ∈ a :: (u ++ b :: v)}) =
              convexHull Real (q '' {i | i ∈ a :: (u ++ [b])}) ∪
                convexHull Real (q '' {i | i ∈ b :: (v ++ [a])}) := hunion.symm
          _ = (⋃ f ∈ left, convexHull Real (Set.range (q ∘ f))) ∪
                (⋃ f ∈ right, convexHull Real (Set.range (q ∘ f))) := by
            rw [hcoverA, hcoverB]
          _ = ⋃ f ∈ left ++ right, convexHull Real (Set.range (q ∘ f)) := hfaces.symm
      · intro f hf g hg
        rcases List.mem_append.mp hf with hfA | hfB
        · rcases List.mem_append.mp hg with hgA | hgB
          · exact hinterA f hfA g hgA
          · exact hcrossInter f hfA g hgB
        · rcases List.mem_append.mp hg with hgA | hgB
          · simpa [Set.inter_comm] using hcrossInter g hgA f hfB
          · exact hinterB f hfB g hgB
      · intro k
        have hlenL : (a :: (u ++ b :: v)).length = u.length + v.length + 2 := by
          simp; omega
        have hABpoint (x : Fin (n + 3))
            (hxA : x ∈ a :: (u ++ [b])) (hxB : x ∈ b :: (v ++ [a])) :
            x ∈ ({a, b} : Set (Fin (n + 3))) := by
          have hx : x ∈ {i | i ∈ a :: (u ++ [b])} ∩
              {i | i ∈ b :: (v ++ [a])} := ⟨hxA, hxB⟩
          rw [hAB] at hx
          simpa using hx
        by_cases hkA : k.val ≤ u.length
        · have leftBoundaryCase :
            ∃! f : Fin 3 → Fin (n + 3), f ∈ left ++ right ∧
            (a :: (u ++ b :: v)).get k ∈ Set.range f ∧
            (a :: (u ++ b :: v)).get
              ⟨(k.val + 1) % (a :: (u ++ b :: v)).length,
                Nat.mod_lt _ (Nat.zero_lt_of_lt k.isLt)⟩ ∈ Set.range f :=
                    SavedDissectionCases.leftBoundaryCase n q a b u v left right hv hndA hcycA
                    hgoodA hfaceB hAget hNoAEndpoints k hlenL hABpoint hkA
          exact leftBoundaryCase
        · have rightBoundaryCase :
            ∃! f : Fin 3 → Fin (n + 3), f ∈ left ++ right ∧
            (a :: (u ++ b :: v)).get k ∈ Set.range f ∧
            (a :: (u ++ b :: v)).get
              ⟨(k.val + 1) % (a :: (u ++ b :: v)).length,
                Nat.mod_lt _ (Nat.zero_lt_of_lt k.isLt)⟩ ∈ Set.range f :=
                    SavedDissectionCases.rightBoundaryCase n q a b u v left right hv hndB hcycB
                    hgoodB hfaceA hlenL hBget hNoBEndpoints k hABpoint hkA
          exact rightBoundaryCase
    | rotate L F k d ih =>
      have rotationCase : Good L F := SavedDissectionCases.rotationCase n q L F k d ih
      exact rotationCase
  exact hgood hboundary hcyclic

end ApollonianSuperharmonic

end
