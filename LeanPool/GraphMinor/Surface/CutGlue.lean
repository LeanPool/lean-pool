/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CutPieces
public import LeanPool.GraphMinor.Surface.WordCases

/-!
# Gluing the sides of a word

`ArcLift ψ F a ξ η` says that `ξ` and `η` are the two lifts of the path `a` around `F` to the
surface `S'` that arises by
cutting along `F`. If a word of `S'` has `ξ` and `η` as free sides, then the word with these two
sides pasted is a word of
the surface before cutting (`glue_word`). The rest of the file has the facts on labels and lifts
that all cases share.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Function

universe uu

/-- `ξ` and `η` are the two lifts of the path `a` through the fibres of `ψ`. -/
structure ArcLift {S' S : Type*} [TopologicalSpace S'] [TopologicalSpace S] (ψ : S' → S)
  (F : Set S) (a : ℝ → S)
    (ξ η : ℝ → S') : Prop where
  cξ : ContinuousOn ξ (Icc 0 1)
  cη : ContinuousOn η (Icc 0 1)
  hξ : ∀ u ∈ Icc (0 : ℝ) 1, ψ (ξ u) = a u
  hη : ∀ u ∈ Icc (0 : ℝ) 1, ψ (η u) = a u
  img : a '' Icc 0 1 = F
  fib : ∀ y y', ψ y = ψ y' → y ≠ y' → ∃ u ∈ Icc (0 : ℝ) 1, (y = ξ u ∧ y' = η u) ∨ (y' = ξ u ∧ y
    = η u)

theorem ArcLift.swap {S' S : Type*} [TopologicalSpace S'] [TopologicalSpace S] {ψ : S'
  → S} {F : Set S} {a : ℝ → S}
    {ξ η : ℝ → S'} (h : ArcLift ψ F a ξ η) : ArcLift ψ F a η ξ :=
  ⟨h.cη, h.cξ, h.hη, h.hξ, h.img, fun y y' h1 h2 => by
    obtain ⟨u, hu, h3⟩ := h.fib y y' h1 h2
    exact ⟨u, hu, h3.elim (fun h4 => .inr h4.symm) fun h4 => .inl h4.symm⟩⟩

theorem rev_mem {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : 1 - u ∈ Icc (0 : ℝ) 1
  := ⟨by linarith [hu.2], by linarith [hu.1]⟩

/-- The same lifts, run backwards. -/
theorem ArcLift.rev {S' S : Type*} [TopologicalSpace S'] [TopologicalSpace S] {ψ : S'
  → S} {F : Set S} {a : ℝ → S}
    {ξ η : ℝ → S'} (h : ArcLift ψ F a ξ η) : ArcLift ψ F (fun u => a (1 - u)) (fun u => ξ (1 - u))
      (fun u => η (1 - u)) := by
  have hc : ContinuousOn (fun u : ℝ => 1 - u) (Icc 0 1) := by fun_prop
  refine ⟨h.cξ.comp hc fun u hu => rev_mem hu, h.cη.comp hc fun u hu => rev_mem hu,
    fun u hu => h.hξ _ (rev_mem hu),
    fun u hu => h.hη _ (rev_mem hu), ?_, fun y y' h1 h2 => ?_⟩
  · rw [← h.img]
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, rev_mem hu, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨1 - u, rev_mem hu, by simp⟩
  · obtain ⟨u, hu, h3⟩ := h.fib y y' h1 h2
    refine ⟨1 - u, rev_mem hu, ?_⟩
    simpa using h3

theorem unique_of_cnt {w : List Letter} {k p q : ℕ} {e e' : Bool} (hc : cnt w k = 1) (h1 : w[p]?
  = some (k, e))
    (h2 : w[q]? = some (k, e')) : p = q := by
  induction w generalizing p q with
  | nil => simp at h1
  | cons x w ih =>
    rw [cnt_cons] at hc
    cases p with
    | zero =>
      cases q with
      | zero => rfl
      | succ q =>
        have h3 : x = (k, e) := by simpa using h1
        rw [List.getElem?_cons_succ] at h2
        have h4 : 0 < cnt w k := by
          have := cnt_pos (List.mem_of_getElem? h2)
          simpa using this
        rw [ite_eq_left (by rw [h3])] at hc
        omega
    | succ p =>
      cases q with
      | zero =>
        have h3 : x = (k, e') := by simpa using h2
        rw [List.getElem?_cons_succ] at h1
        have h4 : 0 < cnt w k := by
          have := cnt_pos (List.mem_of_getElem? h1)
          simpa using this
        rw [ite_eq_left (by rw [h3])] at hc
        omega
      | succ q =>
        rw [List.getElem?_cons_succ] at h1 h2
        have h5 : 0 < cnt w k := by
          have := cnt_pos (List.mem_of_getElem? h1)
          simpa using this
        have hx : (if x.1 = k then 1 else 0) = 0 := by omega
        rw [hx, zero_add] at hc
        rw [ih hc h1 h2]

theorem SideVal.at_word {T : Type*} {w : List Letter} {g : ℕ × ℂ → T} {k p : ℕ} {ρ : ℝ → T}
  (h : SideVal (sW w) g k ρ)
    (hw : w[p]? = some (k, true)) (hc : cnt w k = 1) : ∀ u ∈ Icc (0 : ℝ) 1, g
      (0, sdPt w.length p true u) = ρ u := by
  obtain ⟨i, q, h1, h2⟩ := h
  obtain ⟨rfl, h3⟩ := sW_get h1
  obtain rfl := unique_of_cnt hc hw h3
  rw [sW_zero] at h2
  exact h2

theorem sdPt_ofs (n p : ℕ) (σ : Bool) (t : ℝ) : sdPt n p σ t = sdPt n p true (ofs σ t) := by
  cases σ <;> simp [sdPt, ofs]

/-- The word with two free sides pasted presents the surface before cutting. -/
theorem glue_word {S' S : Type*} [TopologicalSpace S'] [TopologicalSpace S] {ψ : S'
  → S} {F : Set S} {a : ℝ → S}
    {ξ η : ℝ → S'} (L : ArcLift ψ F a ξ η) (hψ : Continuous ψ) (hsurj : Surjective ψ) {A B : List
      Letter} {p q p₁ : ℕ} {σ : Bool}
    (hp1 : (A ++ (q, true) :: B)[p₁]? = some (p, true)) (hne : p₁ ≠ A.length)
    (hc1 : cnt (A ++ (q, true) :: B) q = 1) (hc2 : cnt (A ++ (q, true) :: B) p = 1)
      (_hpq : p ≠ q) {g : ℕ × ℂ → S'}
    (hg : Presents (sW (A ++ (q, true) :: B)) g) (hsξ : SideVal (sW (A ++
      (q, true) :: B)) g p ξ) {ζ : ℝ → S'}
    (hsη : SideVal (sW (A ++ (q, true) :: B)) g q ζ) (hζ : ∀ u ∈ Icc (0 : ℝ) 1, ζ (ofs σ u) = η u) :
    Presents (sW (A ++ (p, σ) :: B)) (ψ ∘ g) ∧ SideVal (sW (A ++ (p, σ) :: B)) (ψ ∘ g) p a := by
  set w := A ++ (q, true) :: B with hw
  set w₁ := A ++ (p, σ) :: B with hw₁
  have hl : w₁.length = w.length := by simp [hw, hw₁]
  have hget : ∀ n, n ≠ A.length → w₁[n]? = w[n]? := by
    intro n hn
    rw [hw, hw₁]
    by_cases h1 : n < A.length
    · rw [List.getElem?_append_left h1, List.getElem?_append_left h1]
    · have h2 : A.length ≤ n := not_lt.mp h1
      rw [List.getElem?_append_right h2, List.getElem?_append_right h2]
      obtain ⟨m, hm⟩ : ∃ m, n - A.length = m + 1 := ⟨n - A.length - 1, by omega⟩
      rw [hm]
      simp
  have hq0 : w[A.length]? = some (q, true) := by simp [hw]
  have hq1 : w₁[A.length]? = some (p, σ) := by simp [hw₁]
  have h3 := hsξ.at_word hp1 hc2
  have h4 := hsη.at_word hq0 hc1
  have h5 : ∀ t ∈ Icc (0 : ℝ) 1, g (0, sdPt w.length A.length σ t) = η t := fun t ht => by
    rw [sdPt_ofs, h4 _ (ofs_mem ht), hζ t ht]
  have hsW : ∀ {v : List Letter}, (sW v 0) = v := fun {v} => sW_zero v
  refine ⟨presents_glue (W := sW w) (W₁ := sW w₁) (i₀ := 0) (q₀ := A.length) (i₁ := 0) (p₁ := p₁)
    (p := p) (q := q)
    (σ := σ) (ε₀ := true) (ε₁ := true) hg hψ hsurj ?_ (by rw [hsW]; exact hq0)
      (by rw [hsW]; exact hq1)
    (by rw [hsW]; exact hp1) (by simp [hne]) ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro i n hn
    by_cases hi : i = 0
    · subst hi
      rw [hsW, hsW]
      exact hget n fun e => hn (by rw [e])
    · simp [sW, update_of_ne hi, nW]
  · intro i
    by_cases hi : i = 0
    · subst hi
      rw [hsW, hsW, hl]
    · simp [sW, update_of_ne hi, nW]
  · intro j m e h
    obtain ⟨rfl, h6⟩ := sW_get h
    rw [unique_of_cnt hc1 h6 hq0]
  · intro j m e h
    obtain ⟨rfl, h6⟩ := sW_get h
    rw [unique_of_cnt hc2 h6 hp1]
  · intro t ht
    rw [hsW, h3 t ht, h5 t ht, L.hξ t ht, L.hη t ht]
  · intro x _ y _ h6 h7
    obtain ⟨t, ht, h8⟩ := L.fib _ _ h6 h7
    refine ⟨t, ht, ?_⟩
    rw [hsW, h3 t ht, h5 t ht]
    exact h8
  · refine ⟨0, p₁, ?_, fun u hu => ?_⟩
    · rw [hsW, hget p₁ hne]
      exact hp1
    · simp only [Function.comp_apply, hsW, hl]
      rw [h3 u hu, L.hξ u hu]

/-! ### Labels of the rest of the word -/

theorem noLab_rW {a b c k : ℕ} {L : List ℕ} (h1 : 2 * a + b ≤ k) (h2 : k ≠ 2 * a + b + 2 * c)
    (h3 : ∀ m ∈ L, k ≠ 2 * a + b + 2 * m ∧ k ≠ 2 * a + b + 2 * m + 1) : NoLab (rW a b c L) k := by
  refine noLab_append.mpr ⟨noLab_append.mpr ⟨noLab_append.mpr ⟨fun l hl he => ?_,
    fun l hl he => ?_⟩, noLab_hlW h3⟩, ?_⟩
  · have := (hW_labels 0 a l hl).2
    omega
  · have := (cW_labels (2 * a) b l hl).2
    omega
  · intro l hl he
    simp only [eW, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> exact h2 he.symm

/-- The state of a word that starts with `R`. -/
theorem inv_of_model {a b : ℕ} {L : List ℕ} (hL : L.Nodup) {R : List Letter} (hG : Good R)
    (hR : ∀ l ∈ R, 2 * a + b ≤ l.1 ∧ ∀ m ∈ L, l.1 ≠ 2 * a + b + 2 * m
      ∧ l.1 ≠ 2 * a + b + 2 * m + 1) :
    Inv R (hW 0 a) (cW (2 * a) b) (hlW (2 * a + b) L) a b L.length := by
  refine ⟨hL_hW _ _, cL_cW _ _, tL_hlW _ hL, ?_, ?_, ?_, ?_, ?_, ?_, hG⟩
  · intro l hl m hm he
    have h1 := (hW_labels _ _ l hl).2
    have h2 := (cW_labels _ _ m hm).1
    omega
  · intro l hl
    have h1 := (hW_labels _ _ l hl).2
    exact noLab_hlW fun m _ => by omega
  · intro l hl
    have h1 := (cW_labels _ _ l hl).2
    exact noLab_hlW fun m _ => by omega
  · intro l hl m hm he
    have h1 := (hW_labels _ _ l hl).2
    have h2 := (hR m hm).1
    omega
  · intro l hl m hm he
    have h1 := (cW_labels _ _ l hl).2
    have h2 := (hR m hm).1
    omega
  · intro l hl m hm he
    obtain ⟨n, h1, h2⟩ := hlW_labels l hl
    have h3 := (hR m hm).2 n h1
    omega

/-- The word with a block in front is equivalent to the word with `E` and the block in front. -/
theorem weq_front (a b c : ℕ) (L : List ℕ) (R : List Letter) :
    WEq.{uu} (R ++ rW a b c L) (eW a b c ++ R ++ hW 0 a ++ cW (2 * a) b ++ hlW (2 * a + b) L) := by
  refine WEq.rot' (R ++ hW 0 a ++ cW (2 * a) b ++ hlW (2 * a + b) L) (eW a b c) (by simp [rW])
    (by simp)

/-! ### Lifts on the real line -/

/-- The linear map from `p` to `q`. -/
def lin (p q u : ℝ) : ℝ := p + (q - p) * u

theorem continuousOn_lin (p q : ℝ) : ContinuousOn (lin p q) (Icc 0 1) := by
  unfold lin
  fun_prop

theorem strictMonoOn_lin {p q : ℝ} (h : p < q) : StrictMonoOn (lin p q) (Icc 0 1)
  := fun x _ y _ hxy => by
  unfold lin
  nlinarith

theorem lin_zero (p q : ℝ) : lin p q 0 = p := by simp [lin]

theorem lin_one (p q : ℝ) : lin p q 1 = q := by simp [lin]

theorem lin_mem {p q u : ℝ} (_h : p ≤ q) (hu : u ∈ Ioo (0 : ℝ) 1) (hlt : p < q) : lin p q u ∈ Ioo p
  q := by
  unfold lin
  constructor <;> nlinarith [hu.1, hu.2]

/-- A lift of an injective path stays below a full turn. -/
theorem lift_lt_add_one {m : ℝ → ℝ} (hc : ContinuousOn m (Icc 0 1)) (_hm : StrictMonoOn m (Icc 0 1))
    (hi : InjOn (fun u => ee (m u)) (Icc 0 1)) : m 1 < m 0 + 1 := by
  by_contra h
  push Not at h
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  obtain ⟨v, hv, he⟩ := intermediate_value_Icc zero_le_one hc (show m 0 + 1 ∈ Icc (m 0)
    (m 1) from ⟨by linarith, h⟩)
  have h1 : ee (m v) = ee (m 0) := by
    rw [he]
    exact ee_add_one _
  have h2 := hi hv h0 h1
  rw [h2] at he
  linarith

/-- The two lifts of disjoint paths fit into one turn, after a shift by an integer. -/
theorem exists_shift {m n : ℝ → ℝ} (hc : ContinuousOn m (Icc 0 1)) (hn : ContinuousOn n (Icc 0 1))
  (_hm : m 0 ≤ m 1)
    (_hmn : n 0 ≤ n 1) (hd : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, ee (m u) ≠ ee (n v)) :
    ∃ k : ℤ, m 1 < n 0 + k ∧ n 1 + k < m 0 + 1 := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  set k := ⌈m 0 - n 0⌉ with hk
  have h2 : m 0 ≤ n 0 + k := by
    have := Int.le_ceil (m 0 - n 0)
    linarith
  have h3 : n 0 + k < m 0 + 1 := by
    have := Int.ceil_lt_add_one (m 0 - n 0)
    linarith
  refine ⟨k, ?_, ?_⟩
  · by_contra h
    push Not at h
    obtain ⟨v, hv, he⟩ := intermediate_value_Icc zero_le_one hc (show n 0 + k ∈ Icc (m 0)
      (m 1) from ⟨h2, h⟩)
    exact hd v hv 0 h0 (by rw [he, ee_add_int])
  · by_contra h
    push Not at h
    have hc' : ContinuousOn (fun u => n u + (k : ℝ)) (Icc 0 1) := hn.add continuousOn_const
    obtain ⟨v, hv, he⟩ := intermediate_value_Icc zero_le_one hc'
      (show m 0 + 1 ∈ Icc (n 0 + k) (n 1 + k) from ⟨h3.le, h⟩)
    have h4 : ee (n v) = ee (m 0) := by
      rw [← ee_add_int (n v) k]
      simp only at he
      rw [he, ee_add_one]
    exact hd 0 h0 v hv h4.symm

end GraphMinor.Surface
