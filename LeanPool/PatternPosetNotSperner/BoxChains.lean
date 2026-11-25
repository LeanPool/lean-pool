/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler B. Hughes
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Prod

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Zify

/-!
# Symmetric Chain Decomposition and Exact Slice Counts of the 3D Box

Formalizes the 3D integer box
`Box(k) = { (x, y, z) : 0 ≤ x ≤ 2k + 1, 0 ≤ y ≤ 2k + 1, 0 ≤ z ≤ 2k }`,
its exact slice cardinality formula
`B(3k + 1 + t) = 3k^2 + 5k + 2 - t^2` (`0 ≤ t ≤ k`),
and an explicit closed-form symmetric chain decomposition (`boxId` / `boxRecon`)
yielding both:
1. Exactly `3k^2 + 5k + 2` chains partitioning `Box(k)` in the coordinatewise order;
2. Unimodality of the slice sizes `B(s)`.
-/

@[expose] public section

namespace PatternPoset

/-! ### 2D Rectangle Symmetric Chain (Hook) Decomposition -/

/-- Hook index of `(i, j)` in `[0, A] × [0, B]`. -/
def rectId (A i j : ℕ) : ℕ := min (A - i) j

/-- Position along the hook `rectId A i j`. -/
def rectPos (A i j : ℕ) : ℕ := i + j - rectId A i j

/-- Reconstruct `(i, j)` in `[0, A] × [0, B]` from hook index `d` and hook position `u`. -/
def rectRecon (A d u : ℕ) : ℕ × ℕ :=
  if u ≤ A - d then (u, d) else (A - d, u + 2 * d - A)

theorem rectId_bounds {A B i j : ℕ} (hi : i ≤ A) (hj : j ≤ B) :
    rectId A i j ≤ A ∧ rectId A i j ≤ B ∧
    rectId A i j ≤ i + j ∧
    rectPos A i j ≤ A + B - 2 * rectId A i j := by
  simp only [rectPos, rectId]
  omega

theorem rectRecon_mem {A B d u : ℕ} (hdA : d ≤ A) (hdB : d ≤ B) (hu : u ≤ A + B - 2 * d) :
    (rectRecon A d u).1 ≤ A ∧ (rectRecon A d u).2 ≤ B := by
  unfold rectRecon
  split_ifs <;> omega

theorem rectId_rectRecon {A B d u : ℕ} (hdA : d ≤ A) (_hdB : d ≤ B)
    (_hu : u ≤ A + B - 2 * d) :
    rectId A (rectRecon A d u).1 (rectRecon A d u).2 = d ∧
    rectPos A (rectRecon A d u).1 (rectRecon A d u).2 = u ∧
    (rectRecon A d u).1 + (rectRecon A d u).2 = u + d := by
  simp only [rectPos, rectId, rectRecon]
  split_ifs <;> dsimp <;> omega

theorem rectRecon_rectId_rectPos {A B i j : ℕ} (hi : i ≤ A) (_hj : j ≤ B) :
    rectRecon A (rectId A i j) (rectPos A i j) = (i, j) := by
  simp only [rectRecon, rectPos, rectId]
  by_cases h : i + j - min (A - i) j ≤ A - min (A - i) j
  · simp only [h, ↓reduceIte]
    apply Prod.ext <;> dsimp <;> omega
  · simp only [h, ↓reduceIte]
    apply Prod.ext <;> dsimp <;> omega

theorem rectRecon_mono {A d u₁ u₂ : ℕ} (hdA : d ≤ A) (h : u₁ ≤ u₂) :
    (rectRecon A d u₁).1 ≤ (rectRecon A d u₂).1 ∧
    (rectRecon A d u₁).2 ≤ (rectRecon A d u₂).2 := by
  unfold rectRecon
  split_ifs <;> dsimp <;> omega

/-! ### 3D Box `Box(k)` and Iterated Symmetric Chain Decomposition -/

/-- The 3D box `[0, 2k+1] × [0, 2k+1] × [0, 2k]` as a `Finset`. -/
def boxFinset (k : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (2 * k + 2)) ×ˢ ((Finset.range (2 * k + 2)) ×ˢ (Finset.range (2 * k + 1)))

theorem mem_boxFinset {k : ℕ} {t : ℕ × ℕ × ℕ} :
    t ∈ boxFinset k ↔ t.1 ≤ 2 * k + 1 ∧ t.2.1 ≤ 2 * k + 1 ∧ t.2.2 ≤ 2 * k := by
  simp only [boxFinset, Finset.mem_product, Finset.mem_range]
  omega

/-- The slice of `Box(k)` of triples with coordinate sum `s`. -/
def boxSlice (k s : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (boxFinset k).filter (fun t => t.1 + t.2.1 + t.2.2 = s)

theorem mem_boxSlice {k s : ℕ} {t : ℕ × ℕ × ℕ} :
    t ∈ boxSlice k s ↔
      t.1 ≤ 2 * k + 1 ∧ t.2.1 ≤ 2 * k + 1 ∧ t.2.2 ≤ 2 * k ∧
      t.1 + t.2.1 + t.2.2 = s := by
  rw [boxSlice, Finset.mem_filter, mem_boxFinset]
  tauto

/-- Symmetric chain identifier `(d₁, d₂)` for a triple `(x, y, z) ∈ Box(k)`. -/
def boxId (k : ℕ) (t : ℕ × ℕ × ℕ) : ℕ × ℕ :=
  let M := 2 * k + 1
  let d₁ := rectId M t.1 t.2.1
  let u := rectPos M t.1 t.2.1
  (d₁, rectId (2 * M - 2 * d₁) u t.2.2)

/-- Reconstruct the unique triple on chain `(d₁, d₂)` in `Box(k)` with sum `s`. -/
def boxRecon (k d₁ d₂ s : ℕ) : ℕ × ℕ × ℕ :=
  let M := 2 * k + 1
  let uz := rectRecon (2 * M - 2 * d₁) d₂ (s - d₁ - d₂)
  let xy := rectRecon M d₁ uz.1
  (xy.1, xy.2, uz.2)

theorem boxId_bounds {k : ℕ} {t : ℕ × ℕ × ℕ} (ht : t ∈ boxFinset k) :
    let id := boxId k t
    id.1 ≤ 2 * k + 1 ∧
    id.2 ≤ 4 * k + 2 - 2 * id.1 ∧
    id.2 ≤ 2 * k ∧
    id.1 + id.2 ≤ 3 * k + 1 ∧
    id.1 + id.2 ≤ t.1 + t.2.1 + t.2.2 ∧
    t.1 + t.2.1 + t.2.2 ≤ 6 * k + 2 - (id.1 + id.2) := by
  rw [mem_boxFinset] at ht
  rcases ht with ⟨hx, hy, hz⟩
  have h1 := rectId_bounds (A := 2 * k + 1) (B := 2 * k + 1) hx hy
  have h2 := rectId_bounds (A := 2 * (2 * k + 1) - 2 * rectId (2 * k + 1) t.1 t.2.1)
    (B := 2 * k) (by omega : rectPos (2 * k + 1) t.1 t.2.1 ≤ _) hz
  dsimp only [boxId]
  have hpos1 : rectPos (2 * k + 1) t.1 t.2.1 = t.1 + t.2.1 - rectId (2 * k + 1) t.1 t.2.1 := rfl
  have hpos2 : rectPos (2 * (2 * k + 1) - 2 * rectId (2 * k + 1) t.1 t.2.1)
      (rectPos (2 * k + 1) t.1 t.2.1) t.2.2 =
      rectPos (2 * k + 1) t.1 t.2.1 + t.2.2 -
      rectId (2 * (2 * k + 1) - 2 * rectId (2 * k + 1) t.1 t.2.1)
        (rectPos (2 * k + 1) t.1 t.2.1) t.2.2 := rfl
  omega

theorem boxRecon_mem_slice {k d₁ d₂ s : ℕ}
    (hd1 : d₁ ≤ 2 * k + 1)
    (hd2a : d₂ ≤ 4 * k + 2 - 2 * d₁)
    (hd2b : d₂ ≤ 2 * k)
    (hs1 : d₁ + d₂ ≤ s)
    (hs2 : s ≤ 6 * k + 2 - (d₁ + d₂)) :
    boxRecon k d₁ d₂ s ∈ boxSlice k s ∧
      boxId k (boxRecon k d₁ d₂ s) = (d₁, d₂) := by
  set M := 2 * k + 1
  have hA : 2 * M - 2 * d₁ = 4 * k + 2 - 2 * d₁ := by omega
  have hv : s - d₁ - d₂ ≤ (2 * M - 2 * d₁) + 2 * k - 2 * d₂ := by omega
  have huz_mem := rectRecon_mem (A := 2 * M - 2 * d₁) (B := 2 * k) (by omega) hd2b hv
  have huz_id := rectId_rectRecon (A := 2 * M - 2 * d₁) (B := 2 * k) (by omega) hd2b hv
  set uz := rectRecon (2 * M - 2 * d₁) d₂ (s - d₁ - d₂)
  have hu : uz.1 ≤ M + M - 2 * d₁ := by omega
  have hxy_mem := rectRecon_mem (A := M) (B := M) hd1 hd1 hu
  have hxy_id := rectId_rectRecon (A := M) (B := M) hd1 hd1 hu
  set xy := rectRecon M d₁ uz.1
  constructor
  · rw [mem_boxSlice]
    refine ⟨hxy_mem.1, hxy_mem.2, huz_mem.2, ?_⟩
    change xy.1 + xy.2 + uz.2 = s
    omega
  · change (rectId M xy.1 xy.2,
      rectId (2 * M - 2 * rectId M xy.1 xy.2) (rectPos M xy.1 xy.2) uz.2) = (d₁, d₂)
    rw [hxy_id.1, hxy_id.2.1, huz_id.1]

theorem boxRecon_boxId {k : ℕ} {t : ℕ × ℕ × ℕ} (ht : t ∈ boxFinset k) :
    boxRecon k (boxId k t).1 (boxId k t).2 (t.1 + t.2.1 + t.2.2) = t := by
  have hb := boxId_bounds ht
  rw [mem_boxFinset] at ht
  rcases ht with ⟨hx, hy, hz⟩
  set M := 2 * k + 1
  set d₁ := rectId M t.1 t.2.1
  set u := rectPos M t.1 t.2.1
  set d₂ := rectId (2 * M - 2 * d₁) u t.2.2
  have h1 := rectId_bounds (A := M) (B := M) hx hy
  have hu_le : u ≤ 2 * M - 2 * d₁ := by omega
  have hsum_eq : t.1 + t.2.1 + t.2.2 - d₁ - d₂ = rectPos (2 * M - 2 * d₁) u t.2.2 := by
    change t.1 + t.2.1 + t.2.2 - d₁ - d₂ = (t.1 + t.2.1 - d₁) + t.2.2 - d₂
    omega
  have huz :
      rectRecon (2 * M - 2 * d₁) d₂ (t.1 + t.2.1 + t.2.2 - d₁ - d₂) = (u, t.2.2) := by
    rw [hsum_eq]
    exact rectRecon_rectId_rectPos hu_le hz
  have hxy : rectRecon M d₁ u = (t.1, t.2.1) := rectRecon_rectId_rectPos hx hy
  change (let uz := rectRecon (2 * M - 2 * d₁) d₂ (t.1 + t.2.1 + t.2.2 - d₁ - d₂)
    let xy := rectRecon M d₁ uz.1
    (xy.1, xy.2, uz.2)) = t
  rw [huz]
  dsimp only
  rw [hxy]

/-- Any two triples in `Box(k)` with the same `boxId` are coordinatewise comparable. -/
theorem box_chain_comparable {k : ℕ} {t₁ t₂ : ℕ × ℕ × ℕ}
    (h1 : t₁ ∈ boxFinset k) (h2 : t₂ ∈ boxFinset k) (hid : boxId k t₁ = boxId k t₂) :
    (t₁.1 ≤ t₂.1 ∧ t₁.2.1 ≤ t₂.2.1 ∧ t₁.2.2 ≤ t₂.2.2) ∨
    (t₂.1 ≤ t₁.1 ∧ t₂.2.1 ≤ t₁.2.1 ∧ t₂.2.2 ≤ t₁.2.2) := by
  have mono_step : ∀ {a b : ℕ × ℕ × ℕ}, a ∈ boxFinset k → b ∈ boxFinset k →
      boxId k a = boxId k b → a.1 + a.2.1 + a.2.2 ≤ b.1 + b.2.1 + b.2.2 →
      a.1 ≤ b.1 ∧ a.2.1 ≤ b.2.1 ∧ a.2.2 ≤ b.2.2 := by
    intro a b ha hb hab hle
    have hba := boxId_bounds ha
    set M := 2 * k + 1
    set d₁ := (boxId k a).1
    set d₂ := (boxId k a).2
    have ha_eq := (boxRecon_boxId ha).symm
    have hb_eq := (boxRecon_boxId hb).symm
    rw [← hab] at hb_eq
    have hv : a.1 + a.2.1 + a.2.2 - d₁ - d₂ ≤ b.1 + b.2.1 + b.2.2 - d₁ - d₂ := by omega
    have huz := rectRecon_mono (A := 2 * M - 2 * d₁) (d := d₂) (by omega) hv
    have hxy := rectRecon_mono (A := M) (d := d₁) (by omega) huz.1
    rw [ha_eq, hb_eq]
    exact ⟨hxy.1, hxy.2, huz.2⟩
  rcases le_total (t₁.1 + t₁.2.1 + t₁.2.2) (t₂.1 + t₂.2.1 + t₂.2.2) with hle | hle
  · exact Or.inl (mono_step h1 h2 hid hle)
  · exact Or.inr (mono_step h2 h1 hid.symm hle)

/-- `boxId k` is injective on every fixed slice `boxSlice k s`. -/
theorem boxId_injOn_slice (k s : ℕ) :
    Set.InjOn (boxId k) (boxSlice k s : Set (ℕ × ℕ × ℕ)) := by
  intro t₁ h1 t₂ h2 heq
  rw [Finset.mem_coe, boxSlice, Finset.mem_filter] at h1 h2
  have hr1 := boxRecon_boxId h1.1
  have hr2 := boxRecon_boxId h2.1
  rw [h1.2] at hr1
  rw [h2.2, ← heq] at hr2
  exact hr1.symm.trans hr2

/-- Every chain in `Box(k)` crosses the middle slice `s = 3k + 1`. -/
theorem boxId_image_eq_mid (k : ℕ) :
    (boxFinset k).image (boxId k) = (boxSlice k (3 * k + 1)).image (boxId k) := by
  ext id
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    have hb := boxId_bounds ht
    have hrec := boxRecon_mem_slice (s := 3 * k + 1) hb.1 hb.2.1 hb.2.2.1
      hb.2.2.2.1 (by omega)
    exact ⟨boxRecon k (boxId k t).1 (boxId k t).2 (3 * k + 1), hrec.1, hrec.2⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, (Finset.mem_filter.mp ht).1, rfl⟩

/-- The number of chains in the symmetric chain decomposition of `Box(k)` equals `B(3k + 1)`. -/
theorem boxId_image_card (k : ℕ) :
    ((boxFinset k).image (boxId k)).card = (boxSlice k (3 * k + 1)).card := by
  rw [boxId_image_eq_mid]
  exact Finset.card_image_of_injOn (boxId_injOn_slice k (3 * k + 1))

/-- Every slice has cardinality at most the middle slice `B(3k + 1)`. -/
theorem boxSlice_card_le_mid (k s : ℕ) :
    (boxSlice k s).card ≤ (boxSlice k (3 * k + 1)).card := by
  rw [← boxId_image_card]
  calc
    (boxSlice k s).card = ((boxSlice k s).image (boxId k)).card :=
      (Finset.card_image_of_injOn (boxId_injOn_slice k s)).symm
    _ ≤ ((boxFinset k).image (boxId k)).card :=
      Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))

/-- Unimodality on the upper half: for `3k + 1 ≤ s₁ ≤ s₂`, `B(s₂) ≤ B(s₁)`. -/
theorem boxSlice_card_antitone {k s₁ s₂ : ℕ} (h1 : 3 * k + 1 ≤ s₁) (h2 : s₁ ≤ s₂) :
    (boxSlice k s₂).card ≤ (boxSlice k s₁).card := by
  have hsub : (boxSlice k s₂).image (boxId k) ⊆ (boxSlice k s₁).image (boxId k) := by
    intro id hid
    rcases Finset.mem_image.mp hid with ⟨t, ht, rfl⟩
    rw [boxSlice, Finset.mem_filter] at ht
    have hb := boxId_bounds ht.1
    have hrec := boxRecon_mem_slice (s := s₁) hb.1 hb.2.1 hb.2.2.1
      (by omega) (by omega)
    exact Finset.mem_image.mpr ⟨boxRecon k (boxId k t).1 (boxId k t).2 s₁, hrec.1, hrec.2⟩
  rw [← Finset.card_image_of_injOn (boxId_injOn_slice k s₂),
      ← Finset.card_image_of_injOn (boxId_injOn_slice k s₁)]
  exact Finset.card_le_card hsub

/-! ### Exact Slice Cardinality Formula `B(3k + 1 + t) = 3k^2 + 5k + 2 - t^2` -/

private theorem two_mul_sum_range_add (a n : ℕ) :
    2 * ∑ i ∈ Finset.range n, (a + i) = n * (2 * a + n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    cases n with
    | zero => simp
    | succ m =>
      have h1 : 2 * a + (m + 1) - 1 = 2 * a + m := by omega
      have h2 : 2 * a + (m + 1 + 1) - 1 = 2 * a + m + 1 := by omega
      rw [h1, h2]
      ring

private theorem two_mul_sum_range_sub (b n : ℕ) (h : n ≤ b + 1) :
    2 * ∑ i ∈ Finset.range n, (b - i) = n * (2 * b + 1 - n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih (by omega)]
    have h1 : n ≤ b := by omega
    have h2 : n ≤ 2 * b + 1 := by omega
    have h3 : n + 1 ≤ 2 * b + 1 := by omega
    zify [h1, h2, h3]
    ring

/-- Number of pairs `(x, y) ∈ [0, M]^2` with `x + y = m`. -/
private theorem card_pair_sum (M m : ℕ) (hm : m ≤ 2 * M) :
    (((Finset.range (M + 1)) ×ˢ (Finset.range (M + 1))).filter
      (fun p => p.1 + p.2 = m)).card =
    if m ≤ M then m + 1 else 2 * M + 1 - m := by
  split_ifs with hle
  · have hbij :
        (((Finset.range (M + 1)) ×ˢ (Finset.range (M + 1))).filter
          (fun p => p.1 + p.2 = m)).card = (Finset.range (m + 1)).card := by
      refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
        omega
      · intro p₁ hp₁ p₂ hp₂ heq
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp₁ hp₂
        ext
        · exact heq
        · omega
      · intro x hx
        rw [Finset.mem_range] at hx
        refine ⟨(x, m - x), ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        omega
    rw [hbij, Finset.card_range]
  · have hbij :
        (((Finset.range (M + 1)) ×ˢ (Finset.range (M + 1))).filter
          (fun p => p.1 + p.2 = m)).card = (Finset.range (2 * M + 1 - m)).card := by
      refine Finset.card_bij (fun p _ => p.1 - (m - M)) ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
        omega
      · intro p₁ hp₁ p₂ hp₂ heq
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp₁ hp₂
        ext <;> omega
      · intro u hu
        rw [Finset.mem_range] at hu
        refine ⟨(m - M + u, M - u), ?_, by dsimp; omega⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        omega
    rw [hbij, Finset.card_range]

/-- Exact slice cardinality formula: for `0 ≤ t ≤ k`,
`B(3k + 1 + t) = 3k^2 + 5k + 2 - t^2`. -/
theorem boxSlice_card (k t : ℕ) (ht : t ≤ k) :
    (boxSlice k (3 * k + 1 + t)).card = 3 * k ^ 2 + 5 * k + 2 - t ^ 2 := by
  have hfiber :
      (boxSlice k (3 * k + 1 + t)).card =
      ∑ z ∈ Finset.range (2 * k + 1),
        (((Finset.range (2 * k + 2)) ×ˢ (Finset.range (2 * k + 2))).filter
          (fun p => p.1 + p.2 = 3 * k + 1 + t - z)).card := by
    rw [← Finset.card_sigma]
    refine Finset.card_bij (fun tr _ => ⟨tr.2.2, (tr.1, tr.2.1)⟩) ?_ ?_ ?_
    · intro tr htr
      rw [mem_boxSlice] at htr
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      omega
    · intro tr₁ _ tr₂ _ heq
      rcases tr₁ with ⟨x₁, y₁, z₁⟩
      rcases tr₂ with ⟨x₂, y₂, z₂⟩
      simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq] at heq
      rcases heq with ⟨hz, hx, hy⟩
      subst hx; subst hy; subst hz; rfl
    · rintro ⟨z, x, y⟩ h
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h
      refine ⟨(x, y, z), ?_, rfl⟩
      rw [mem_boxSlice]
      dsimp
      omega
  rw [hfiber]
  have hrew : ∀ z ∈ Finset.range (2 * k + 1),
      (((Finset.range (2 * k + 2)) ×ˢ (Finset.range (2 * k + 2))).filter
        (fun p => p.1 + p.2 = 3 * k + 1 + t - z)).card =
      if z < k + t then k + 2 - t + z else 3 * k + 2 + t - z := by
    intro z hz
    rw [Finset.mem_range] at hz
    rw [card_pair_sum (2 * k + 1) (3 * k + 1 + t - z) (by omega)]
    split_ifs <;> omega
  rw [Finset.sum_congr rfl hrew]
  -- Split `range (2*k + 1)` at `k + t`
  have hsplit :
      ∑ z ∈ Finset.range (2 * k + 1),
        (if z < k + t then k + 2 - t + z else 3 * k + 2 + t - z) =
      (∑ z ∈ Finset.range (k + t), (k + 2 - t + z)) +
      (∑ u ∈ Finset.range (k + 1 - t), (2 * k + 2 - u)) := by
    have hdecomp : 2 * k + 1 = (k + t) + (k + 1 - t) := by omega
    conv_lhs => rw [hdecomp, Finset.sum_range_add]
    congr 1
    · apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.mem_range] at hz
      simp [hz]
    · apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.mem_range] at hu
      have hnot : ¬ (k + t + u < k + t) := by omega
      simp only [hnot, ↓reduceIte]
      omega
  rw [hsplit]
  have hs1 := two_mul_sum_range_add (k + 2 - t) (k + t)
  have hs2 := two_mul_sum_range_sub (2 * k + 2) (k + 1 - t) (by omega)
  have hsq : t ^ 2 ≤ 3 * k ^ 2 + 5 * k + 2 := by nlinarith
  have h2eq :
      2 * ((∑ z ∈ Finset.range (k + t), (k + 2 - t + z)) +
           (∑ u ∈ Finset.range (k + 1 - t), (2 * k + 2 - u))) =
      2 * (3 * k ^ 2 + 5 * k + 2 - t ^ 2) := by
    rw [mul_add, hs1, hs2]
    have h1 : t ≤ k + 2 := by omega
    have h2 : 1 ≤ 2 * (k + 2 - t) + (k + t) := by omega
    have h3 : t ≤ k + 1 := by omega
    have h4 : k + 1 - t ≤ 2 * (2 * k + 2) + 1 := by omega
    zify [h1, h2, h3, h4, hsq]
    ring
  omega

/-- Middle slice cardinality: `B(3k + 1) = 3k^2 + 5k + 2`. -/
theorem boxSlice_mid_card (k : ℕ) :
    (boxSlice k (3 * k + 1)).card = 3 * k ^ 2 + 5 * k + 2 := by
  simpa using boxSlice_card k 0 (Nat.zero_le k)

/-- Exact number of symmetric chains covering `Box(k)`: `3k^2 + 5k + 2`. -/
theorem boxId_image_card_eq (k : ℕ) :
    ((boxFinset k).image (boxId k)).card = 3 * k ^ 2 + 5 * k + 2 := by
  rw [boxId_image_card, boxSlice_mid_card]

end PatternPoset
