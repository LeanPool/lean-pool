/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CutSimilar
public import LeanPool.GraphMinor.Surface.VoltWord

/-!
# O-arcs that are not null-homotopic

We use `volt_zero` on the words of a surface that have an `O`-arc as a side.

An `O`-arc that does not separate gets a value of order two. If an `O`-arc separates and neither
side is a disc, then we need a
group that is not commutative, since the two sides of a separating curve cancel in every commutative
group. We take the group
`S₃` and give the `O`-arc a 3-cycle. A 3-cycle is a commutator, it is a square, and a free side of a
hole can have any value, so
each of the two sides of the `O`-arc can close up (`exists_close`). This is the same idea as the
standard fact that surface groups
are residually finite: see P. Scott, *Subgroups of surface groups are almost geometric*, J. London
Math. Soc. 17 (1978) 555–565.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology

universe u

/-- The symmetric group on three letters, written additively. -/
abbrev S3 : Type := Additive (Equiv.Perm (Fin 3))

/-- A value of order three. -/
def T3 (v : S3) : Prop := v ≠ 0 ∧ v + v + v = 0

instance : DecidablePred T3 := fun v => by
  unfold T3
  infer_instance

theorem t3_exists : ∃ v, T3 v := by decide

theorem T3.neg : ∀ {v : S3}, T3 v → T3 (-v) := by decide

theorem T3.square : ∀ {v : S3}, T3 v → ∃ x : S3, x + x = v := by decide

theorem T3.comm : ∀ {v : S3}, T3 v → ∃ x y : S3, x + y + -x + -y = v := by decide

theorem order_two_exists : ∃ v : S3, v ≠ 0 ∧ v + v = 0 := by decide

section counts

/-- A label occurs at most `cnt w k` times, as positions of the word. -/
theorem idx_encard_le (w : List Letter) (k : ℕ) : {p : ℕ | ∃ e, w[p]? = some (k, e)}.encard
  ≤ cnt w k := by
  induction w with
  | nil => simp [cnt_nil]
  | cons l w ih =>
    have himg : {p : ℕ | ∃ e, w[p]? = some (k, e)}.encard = (Nat.succ '' {p : ℕ | ∃ e, w[p]? = some
      (k, e)}).encard :=
      (Nat.succ_injective.injOn.encard_image).symm
    rw [cnt_cons]
    by_cases h : l.1 = k
    · have hs : {p : ℕ | ∃ e, (l :: w)[p]? = some (k, e)} ⊆ insert 0 (Nat.succ '' {p : ℕ | ∃ e,
        w[p]? = some (k, e)}) := by
        rintro (_ | p) ⟨e, he⟩
        · exact .inl rfl
        · exact .inr ⟨p, ⟨e, by simpa using he⟩, rfl⟩
      refine (encard_le_encard hs).trans ((encard_insert_le _ _).trans ?_)
      rw [← himg, ite_eq_left h]
      push_cast
      rw [add_comm]
      gcongr
    · have hs : {p : ℕ | ∃ e, (l :: w)[p]? = some (k, e)} ⊆ Nat.succ '' {p : ℕ | ∃ e, w[p]? = some
        (k, e)} := by
        rintro (_ | p) ⟨e, he⟩
        · simp only [List.getElem?_cons_zero, Option.some.injEq] at he
          exact absurd (by rw [he]) h
        · exact ⟨p, ⟨e, by simpa using he⟩, rfl⟩
      refine (encard_le_encard hs).trans ?_
      rw [← himg, ite_eq_right h, zero_add]
      exact ih

theorem isPaired_sW {w : List Letter} (h : Good w) : IsPaired (sW w) := by
  intro k
  have hs : {s : ℕ × ℕ | ∃ e, (sW w s.1)[s.2]? = some (k, e)} ⊆ (fun p =>
    ((0 : ℕ), p)) '' {p : ℕ | ∃ e, w[p]? = some (k, e)} := by
    rintro ⟨i, p⟩ ⟨e, he⟩
    obtain ⟨rfl, h2⟩ := sW_get he
    exact ⟨p, ⟨e, h2⟩, rfl⟩
  refine (encard_le_encard hs).trans ((encard_image_le _ _).trans ((idx_encard_le w k).trans ?_))
  exact_mod_cast h k

theorem isPaired_dW {u v : List Letter} (h : ∀ k, cnt u k + cnt v k ≤ 2) : IsPaired (dW u v) := by
  intro k
  have hs : {s : ℕ × ℕ | ∃ e, (dW u v s.1)[s.2]? = some (k, e)} ⊆
      (fun p => ((0 : ℕ), p)) '' {p : ℕ | ∃ e, u[p]? = some (k, e)} ∪ (fun p =>
        ((1 : ℕ), p)) '' {p : ℕ | ∃ e, v[p]? = some (k, e)} := by
    rintro ⟨i, p⟩ ⟨e, he⟩
    rcases dW_cases u v i with ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | h2
    · rw [h2] at he
      exact .inl ⟨p, ⟨e, he⟩, rfl⟩
    · rw [h2] at he
      exact .inr ⟨p, ⟨e, he⟩, rfl⟩
    · rw [h2] at he
      simp at he
  refine (encard_le_encard hs).trans ((encard_union_le _ _).trans ?_)
  have h1 := (encard_image_le (fun p => ((0 : ℕ), p)) {p : ℕ | ∃ e, u[p]? = some (k, e)}).trans
    (idx_encard_le u k)
  have h2 := (encard_image_le (fun p => ((1 : ℕ), p)) {p : ℕ | ∃ e, v[p]? = some (k, e)}).trans
    (idx_encard_le v k)
  refine (add_le_add h1 h2).trans ?_
  exact_mod_cast h k

theorem finW_dW (u v : List Letter) : FinW (dW u v) := by
  refine (finite_le_nat 1).subset fun k hk => ?_
  rcases dW_cases u v k with ⟨rfl, -⟩ | ⟨rfl, -⟩ | e
  · simp
  · simp
  · exact absurd e hk

theorem good_append {A B : List Letter} (hA : Good A) (hB : Good B) (hX : DisjL A B) : Good
  (A ++ B) := by
  intro k
  rw [cnt_append]
  by_cases h : ∃ l ∈ A, l.1 = k
  · obtain ⟨l, hl, rfl⟩ := h
    rw [noLab_iff_cnt.mp (hX l hl)]
    exact hA _
  · have : NoLab A k := fun l hl he => h ⟨l, hl, he⟩
    rw [noLab_iff_cnt.mp this, zero_add]
    exact hB k

theorem BC.good {H : List Letter} {a b c : ℕ} (h : BC H a b c) : Good H := by
  induction h with
  | nil => exact fun k => by simp [cnt_nil]
  | @hnd H a b c u v huv hX _ ih =>
    refine good_append (fun k => ?_) ih hX
    simp only [hndB, linv, cnt_cons, cnt_nil]
    split_ifs <;> omega
  | @cap H a b c y hX _ ih =>
    refine good_append (fun k => ?_) ih hX
    simp only [cnt_cons, cnt_nil]
    split_ifs <;> omega
  | @hole H a b c t r htr hX _ ih =>
    refine good_append (fun k => ?_) ih hX
    simp only [holB, linv, cnt_cons, cnt_nil]
    split_ifs <;> omega

theorem good_rW {a b c : ℕ} {L : List ℕ} (hL : L.Nodup) (hc : ∀ m ∈ L, m < c) : Good (rW a b c L)
  := by
  rw [rW_eq]
  refine good_append (bc_hH a b hL).good (fun k => ?_) (DisjL.symm ?_)
  · simp only [eW, cnt_cons, cnt_nil]
    split_ifs <;> omega
  · intro l hl
    simp only [eW, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;>
    · exact noLab_hH (by simp only; omega) fun m hm => by
        have := hc m hm
        simp only
        omega

theorem wv_shW {A : Type} [AddGroup A] (V : ℕ → A) (M : ℕ) (w : List Letter) : wv V (shW M w) = wv
  (fun k => V (k + M)) w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    have e : shW M (l :: w) = (l.1 + M, l.2) :: shW M w := rfl
    rw [e, wv_cons, wv_cons, ih]
    rfl

theorem cnt_shW (M : ℕ) (w : List Letter) (k : ℕ) : cnt (shW M w) (k + M) = cnt w k := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    have e : shW M (l :: w) = (l.1 + M, l.2) :: shW M w := rfl
    rw [e, cnt_cons, cnt_cons, ih]
    simp only [add_left_inj]

theorem hlW_mem {k : ℕ} {L : List ℕ} {l : Letter} (h : l ∈ hlW k L) : ∃ m ∈ L, l.1 = k + 2 * m
  ∨ l.1 = k + 2 * m + 1 := by
  obtain ⟨m, hm, h1⟩ := List.mem_flatMap.mp h
  simp only [holB, linv, List.mem_cons, List.not_mem_nil, or_false] at h1
  refine ⟨m, hm, ?_⟩
  rcases h1 with rfl | rfl | rfl <;> simp

end counts

section close

/-- The word of the rest of a surface can have any 3-cycle as its value, unless the surface is a
disc. -/
theorem exists_close {a b c : ℕ} {L : List ℕ} {v : S3} (hv : T3 v) (hL : L.Nodup) (h : 0 < a
  ∨ 0 < b ∨ L ≠ []) :
    ∃ V : ℕ → S3, wv V (rW a b c L) = v := by
  have hrest : ∀ {K : ℕ} {V : ℕ → S3}, (∀ k ≥ K, V k = 0) → K ≤ 2 * a + b → ∀ l ∈ hlW
    (2 * a + b) L ++ eW a b c, V l.1 = 0 := by
    intro K V hV hK l hl
    rcases List.mem_append.mp hl with hl | hl
    · obtain ⟨m, -, h1⟩ := hlW_mem hl
      exact hV _ (by omega)
    · simp only [eW, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> exact hV _ (by simp only; omega)
  have hE : ∀ {K : ℕ} {V : ℕ → S3}, (∀ k ≥ K, V k = 0) → K ≤ 2 * a + b → wv V (hlW
    (2 * a + b) L ++ eW a b c) = 0 :=
    fun hV hK => wv_zero (hrest hV hK)
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rcases Nat.eq_zero_or_pos b with rfl | hb
    · obtain ⟨m, L', rfl⟩ : ∃ m L', L = m :: L' := by
        rcases L with _ | ⟨m, L'⟩
        · simp at h
        · exact ⟨m, L', rfl⟩
      refine ⟨Function.update 0 (2 * m + 1) v, ?_⟩
      have hm : m ∉ L' := (List.nodup_cons.mp hL).1
      have e1 : rW 0 0 c (m :: L') = holB (2 * m, true) (2 * m + 1, true) ++ (hlW 0 L' ++ eW 0 0 c)
        := by
        simp [rW, hW, cW, hlW]
      rw [e1, wv_append]
      have e2 : wv (Function.update 0 (2 * m + 1) v : ℕ → S3) (hlW 0 L' ++ eW 0 0 c) = 0 := by
        refine wv_zero fun l hl => Function.update_of_ne ?_ _ _
        rcases List.mem_append.mp hl with hl | hl
        · obtain ⟨m', hm', h1⟩ := hlW_mem hl
          have : m' ≠ m := fun he => hm (he ▸ hm')
          omega
        · simp only [eW, List.mem_cons, List.not_mem_nil, or_false] at hl
          rcases hl with rfl | rfl <;> simp only <;> omega
      rw [e2]
      simp only [holB, linv, wv_cons, wv_nil, lVal, add_zero, Function.update_self]
      simp
    · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      obtain ⟨x, hx⟩ := hv.square
      refine ⟨Function.update 0 0 x, ?_⟩
      have e1 : rW 0 (b' + 1) c L = [(0, true), (0, true)] ++ (cW 1 b' ++ (hlW (2 * 0 +
        (b' + 1)) L ++ eW 0 (b' + 1) c)) := by
        simp [rW, hW, cW]
      have hV : ∀ k ≥ 1, (Function.update 0 0 x : ℕ → S3) k = 0 := fun k hk => by
        rw [Function.update_of_ne (by omega)]
        rfl
      have e2 : wv (Function.update 0 0 x : ℕ → S3) (cW 1 b') = 0 :=
        wv_zero fun l hl => hV _ (cW_labels 1 b' l hl).1
      rw [e1, wv_append, wv_append, e2, hE hV (by omega)]
      simp [lVal, hx]
  · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    obtain ⟨x, y, hxy⟩ := hv.comm
    refine ⟨Function.update (Function.update 0 0 x) 1 y, ?_⟩
    have e1 : rW (a' + 1) b c L = hndB (0, true) (1, true) ++ (hW 2 a' ++ cW (2 * (a' + 1)) b ++
        (hlW (2 * (a' + 1) + b) L ++ eW (a' + 1) b c)) := by
      simp [rW, hW]
    have hV : ∀ k ≥ 2, (Function.update (Function.update 0 0 x) 1 y : ℕ → S3) k = 0 := fun k hk
      => by
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      rfl
    have e2 : wv (Function.update (Function.update 0 0 x) 1 y : ℕ → S3) (hW 2 a' ++ cW (2 *
      (a' + 1)) b) = 0 :=
      wv_zero fun l hl => by
        rcases List.mem_append.mp hl with hl | hl
        · exact hV _ (hW_labels 2 a' l hl).1
        · exact hV _ (by have := (cW_labels _ _ l hl).1; omega)
    rw [e1, wv_append, wv_append, e2, hE hV (by omega)]
    simp only [hndB, linv, wv_cons, wv_nil, lVal, Bool.not_true, Bool.false_eq_true, ite_false,
      ite_true, add_zero]
    rw [Function.update_self, Function.update_of_ne (show (0 : ℕ) ≠ 1 by omega),
      Function.update_self]
    rw [← hxy]
    simp only [add_assoc]

end close

section sides

variable {Y : Type u} [TopologicalSpace Y]

/-- `F` is an `O`-arc that is null-homotopic in the whole space. -/
def NullIn (F : Set Y) : Prop :=
  ∃ (φ₀ : Circle ≃ₜ F) (H : C(Circle × unitInterval, Y)) (c₀ : Y), (∀ x, H (x, 0) = (φ₀ x).1)
    ∧ ∀ x, H (x, 1) = c₀

/-- A side that goes around a null-homotopic `O`-arc has value zero. -/
theorem side_null {A : Type} [AddGroup A] [Finite A] [T2Space Y] {W : ℕ → List Letter} {f : ℕ × ℂ
  → Y} {V : ℕ → A} (hW : FinW W) (hP : IsPaired W)
    (hf : Presents W f) (h0 : W 0 ≠ []) (hV : ∀ i, wv V (W i) = 0) {F : Set Y}
      (hN : NullIn F) {p k : ℕ} (hp : (W 0)[p]? = some (k, true))
    {ρ : ℝ → Y} (cρ : ContinuousOn ρ (Icc 0 1)) (hc : ρ 1 = ρ 0) (hρ : ∀ u ∈ Icc (0 : ℝ) 1, ρ u ∈ F)
    (hs : ∀ u ∈ Icc (0 : ℝ) 1, f (0, per (W 0).length (p + u)) = ρ u) : V k = 0 := by
  obtain ⟨φ₀, H, c₀, h1, h2⟩ := hN
  obtain ⟨m, cm, hm⟩ := exists_lift φ₀ cρ hρ
  have m0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have m1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  exact volt_zero hW hP hf h0 hV H (c := fun x => (φ₀ x).1) h1 h2 hp cm
    (φ₀.injective (Subtype.ext ((hm 1 m1).trans (hc.trans (hm 0 m0).symm))))
    fun u hu => (hs u hu).trans (hm u hu).symm

omit [TopologicalSpace Y] in
/-- A side of a single word, at its position. -/
theorem side_sW {w : List Letter} {f : ℕ × ℂ → Y} {k : ℕ} {ρ : ℝ → Y} (h : SideVal (sW w) f k ρ) :
    ∃ p : ℕ, w[p]? = some (k, true) ∧ ∀ u ∈ Icc (0 : ℝ) 1, f (0, per w.length (p + u)) = ρ u := by
  obtain ⟨i, p, h1, h2⟩ := h
  obtain ⟨rfl, h3⟩ := sW_get h1
  rw [sW_zero] at h2
  refine ⟨p, h3, fun u hu => ?_⟩
  have := h2 u hu
  simpa [sdPt] using this

variable [T2Space Y] {a b c i j : ℕ} {L : List ℕ} {f : ℕ × ℂ → Y} {F : Set Y} {ρ : ℝ → Y}

/-- Two lifts on two holes of one word: the `O`-arc does not separate. -/
theorem not_null_E (hij : i ≠ j) (hi : i < c) (hj : j < c) (hL : L.Nodup) (hc : ∀ m ∈ L, m < c
  ∧ m ≠ i ∧ m ≠ j) {σ : Bool}
    (hf : Presents (sW (blkE a b i j σ ++ rW a b c L)) f) (hs : SideVal (sW
      (blkE a b i j σ ++ rW a b c L)) f (rL a b i).1 ρ)
    (hN : NullIn F) (cρ : ContinuousOn ρ (Icc 0 1)) (hcl : ρ 1 = ρ 0) (hρ : ∀ u ∈ Icc
      (0 : ℝ) 1, ρ u ∈ F) : False := by
  obtain ⟨x, hx0, hx⟩ := order_two_exists
  set r := 2 * a + b + 2 * i + 1 with hr
  have hzero : ∀ k, 2 * a + b ≤ k → k ≠ 2 * a + b + 2 * c → (∀ m ∈ L, k ≠ 2 * a + b + 2 * m
    ∧ k ≠ 2 * a + b + 2 * m + 1) →
      cnt (rW a b c L) k = 0 := fun k h1 h2 h3 => cnt_rW_zero h1 h2 h3
  have hgood : Good (blkE a b i j σ ++ rW a b c L) := by
    refine good_append (fun k => ?_) (good_rW hL fun m hm => (hc m hm).1) fun l hl
      => noLab_iff_cnt.mpr ?_
    · cases σ <;> simp only [blkE, tL, rL, linv, cnt_cons, cnt_nil] <;> split_ifs <;> omega
    · cases σ <;> simp only [blkE, tL, rL, linv, List.mem_cons, List.not_mem_nil, or_false] at hl
        <;>
      · rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;>
        · refine hzero _ (by simp only; omega) (by simp only; omega) fun m hm => ?_
          have := hc m hm
          simp only
          omega
  have hne : (blkE a b i j σ ++ rW a b c L) ≠ [] := by simp [blkE]
  have hV0 : ∀ l ∈ rW a b c L, (Function.update 0 r x : ℕ → S3) l.1 = 0 := fun l hl =>
    Function.update_of_ne (fun he => (noLab_iff_cnt.mpr (hzero r (by omega) (by omega) fun m hm
      => by
      have := hc m hm
      omega)) l hl he) _ _
  have ht : (Function.update 0 r x : ℕ → S3) (2 * a + b + 2 * i) = 0 := Function.update_of_ne
    (by omega) _ _
  have ht' : (Function.update 0 r x : ℕ → S3) (2 * a + b + 2 * j) = 0 := Function.update_of_ne
    (by omega) _ _
  have hr1 : (Function.update 0 r x : ℕ → S3) r = x := Function.update_self _ _ _
  have hV : ∀ d, wv (Function.update 0 r x : ℕ → S3) (sW (blkE a b i j σ ++ rW a b c L) d) = 0 := by
    intro d
    by_cases hd : d = 0
    · subst hd
      rw [sW_zero, wv_append, wv_zero hV0, add_zero]
      cases σ <;> simp [blkE, tL, rL, linv, lVal, ht, ht', ← hr, hx]
    · have : sW (blkE a b i j σ ++ rW a b c L) d = [] := by simp [sW, hd, nW]
      rw [this]
      rfl
  obtain ⟨p, hp, h1⟩ := side_sW hs
  have := side_null (finW_sW _) (isPaired_sW hgood) hf (by rw [sW_zero]; exact hne) hV hN (p := p)
    (by rw [sW_zero]; exact hp) cρ hcl hρ
    (fun u hu => by rw [sW_zero]; exact h1 u hu)
  rw [show (rL a b i).1 = r from rfl, hr1] at this
  exact hx0 this

/-- One lift that runs twice around a hole: the `O`-arc does not separate. -/
theorem not_null_D (hi : i < c) (hL : L.Nodup) (hc : ∀ m ∈ L, m < c ∧ m ≠ i)
    (hf : Presents (sW (blkD a b i ++ rW a b c L)) f) (hs : SideVal (sW
      (blkD a b i ++ rW a b c L)) f (rL a b i).1 ρ)
    (hN : NullIn F) (cρ : ContinuousOn ρ (Icc 0 1)) (hcl : ρ 1 = ρ 0) (hρ : ∀ u ∈ Icc
      (0 : ℝ) 1, ρ u ∈ F) : False := by
  obtain ⟨x, hx0, hx⟩ := order_two_exists
  set r := 2 * a + b + 2 * i + 1 with hr
  have hzero : ∀ k, 2 * a + b ≤ k → k ≠ 2 * a + b + 2 * c → (∀ m ∈ L, k ≠ 2 * a + b + 2 * m
    ∧ k ≠ 2 * a + b + 2 * m + 1) →
      cnt (rW a b c L) k = 0 := fun k h1 h2 h3 => cnt_rW_zero h1 h2 h3
  have hgood : Good (blkD a b i ++ rW a b c L) := by
    refine good_append (fun k => ?_) (good_rW hL fun m hm => (hc m hm).1) fun l hl
      => noLab_iff_cnt.mpr ?_
    · simp only [blkD, tL, rL, linv, cnt_cons, cnt_nil]
      split_ifs <;> omega
    · simp only [blkD, tL, rL, linv, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl | rfl <;>
      · refine hzero _ (by simp only; omega) (by simp only; omega) fun m hm => ?_
        have := hc m hm
        simp only
        omega
  have hne : (blkD a b i ++ rW a b c L) ≠ [] := by simp [blkD]
  have hV0 : ∀ l ∈ rW a b c L, (Function.update 0 r x : ℕ → S3) l.1 = 0 := fun l hl =>
    Function.update_of_ne (fun he => (noLab_iff_cnt.mpr (hzero r (by omega) (by omega) fun m hm
      => by
      have := hc m hm
      omega)) l hl he) _ _
  have ht : (Function.update 0 r x : ℕ → S3) (2 * a + b + 2 * i) = 0 := Function.update_of_ne
    (by omega) _ _
  have hr1 : (Function.update 0 r x : ℕ → S3) r = x := Function.update_self _ _ _
  have hV : ∀ d, wv (Function.update 0 r x : ℕ → S3) (sW (blkD a b i ++ rW a b c L) d) = 0 := by
    intro d
    by_cases hd : d = 0
    · subst hd
      rw [sW_zero, wv_append, wv_zero hV0, add_zero]
      simp [blkD, tL, rL, linv, lVal, ht, ← hr, hx]
    · have : sW (blkD a b i ++ rW a b c L) d = [] := by simp [sW, hd, nW]
      rw [this]
      rfl
  obtain ⟨p, hp, h1⟩ := side_sW hs
  have := side_null (finW_sW _) (isPaired_sW hgood) hf (by rw [sW_zero]; exact hne) hV hN (p := p)
    (by rw [sW_zero]; exact hp) cρ hcl hρ
    (fun u hu => by rw [sW_zero]; exact h1 u hu)
  rw [show (rL a b i).1 = r from rfl, hr1] at this
  exact hx0 this

/-- A cuff of a surface that is not a disc is not null-homotopic. -/
theorem not_null_C (hi : i < c) (hL : L.Nodup) (hc : ∀ m ∈ L, m < c ∧ m ≠ i) (hne' : 0 < a ∨ 0 < b
  ∨ L ≠ [])
    (hf : Presents (sW (hB a b i ++ rW a b c L)) f) (hs : SideVal (sW (hB a b i ++ rW a b c L)) f
      (rL a b i).1 ρ)
    (hN : NullIn F) (cρ : ContinuousOn ρ (Icc 0 1)) (hcl : ρ 1 = ρ 0) (hρ : ∀ u ∈ Icc
      (0 : ℝ) 1, ρ u ∈ F) : False := by
  obtain ⟨v, hv⟩ := t3_exists
  obtain ⟨V₁, hV₁⟩ := exists_close (a := a) (b := b) (c := c) hv.neg hL hne'
  set r := 2 * a + b + 2 * i + 1 with hr
  set t := 2 * a + b + 2 * i with ht
  have hzero : ∀ k, 2 * a + b ≤ k → k ≠ 2 * a + b + 2 * c → (∀ m ∈ L, k ≠ 2 * a + b + 2 * m
    ∧ k ≠ 2 * a + b + 2 * m + 1) →
      cnt (rW a b c L) k = 0 := fun k h1 h2 h3 => cnt_rW_zero h1 h2 h3
  have hgood : Good (hB a b i ++ rW a b c L) := by
    refine good_append (fun k => ?_) (good_rW hL fun m hm => (hc m hm).1) fun l hl
      => noLab_iff_cnt.mpr ?_
    · simp only [hB, holB, tL, rL, linv, cnt_cons, cnt_nil]
      split_ifs <;> omega
    · simp only [hB, holB, tL, rL, linv, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl <;>
      · refine hzero _ (by simp only; omega) (by simp only; omega) fun m hm => ?_
        have := hc m hm
        simp only
        omega
  have hne : (hB a b i ++ rW a b c L) ≠ [] := by simp [hB, holB]
  set V : ℕ → S3 := Function.update (Function.update V₁ r v) t 0 with hVdef
  have hVr : V r = v := by
    rw [hVdef, Function.update_of_ne (by omega), Function.update_self]
  have hVt : V t = 0 := Function.update_self _ _ _
  have hrr : NoLab (rW a b c L) r := noLab_iff_cnt.mpr (hzero r (by omega) (by omega) fun m hm => by
    have := hc m hm
    omega)
  have hrt : NoLab (rW a b c L) t := noLab_iff_cnt.mpr (hzero t (by omega) (by omega) fun m hm => by
    have := hc m hm
    omega)
  have e1 : wv V (rW a b c L) = -v := by
    rw [← hV₁]
    exact wv_congr fun l hl => by
      rw [hVdef, Function.update_of_ne (hrt l hl), Function.update_of_ne (hrr l hl)]
  have hV : ∀ d, wv V (sW (hB a b i ++ rW a b c L) d) = 0 := by
    intro d
    by_cases hd : d = 0
    · subst hd
      rw [sW_zero, wv_append, e1]
      simp [hB, holB, tL, rL, linv, lVal, ← hr, ← ht, hVr, hVt]
    · have : sW (hB a b i ++ rW a b c L) d = [] := by simp [sW, hd, nW]
      rw [this]
      rfl
  obtain ⟨p, hp, h1⟩ := side_sW hs
  have := side_null (finW_sW _) (isPaired_sW hgood) hf (by rw [sW_zero]; exact hne) hV hN (p := p)
    (by rw [sW_zero]; exact hp) cρ hcl hρ
    (fun u hu => by rw [sW_zero]; exact h1 u hu)
  rw [show (rL a b i).1 = r from rfl, hVr] at this
  exact hv.1 this

/-- A separating `O`-arc with neither side a disc is not null-homotopic. -/
theorem not_null_B {a₁ b₁ c₁ a₂ b₂ c₂ i j : ℕ} {L₁ L₂ : List ℕ} {σ : Bool} (hi : i < c₁)
  (hj : j < c₂) (hN₁ : L₁.Nodup) (hN₂ : L₂.Nodup)
    (hL₁ : ∀ m ∈ L₁, m < c₁ ∧ m ≠ i) (hL₂ : ∀ m ∈ L₂, m < c₂ ∧ m ≠ j) (h₁ : 0 < a₁ ∨ 0 < b₁
      ∨ L₁ ≠ []) (h₂ : 0 < a₂ ∨ 0 < b₂ ∨ L₂ ≠ [])
    (hf : Presents (dW (wLoop₁ a₁ b₁ c₁ i L₁) (wLoop₂ a₂ b₂ c₂ j L₂ (frL a₁ b₁ c₁ + 1)
      ((rL a₁ b₁ i).1, σ))) f) {q : ℕ}
    (hq : (wLoop₁ a₁ b₁ c₁ i L₁)[q]? = some ((rL a₁ b₁ i).1, true))
    (hs : ∀ u ∈ Icc (0 : ℝ) 1, f (0, per (wLoop₁ a₁ b₁ c₁ i L₁).length (q + u)) = ρ u)
    (hN : NullIn F) (cρ : ContinuousOn ρ (Icc 0 1)) (hcl : ρ 1 = ρ 0) (hρ : ∀ u ∈ Icc
      (0 : ℝ) 1, ρ u ∈ F) : False := by
  obtain ⟨v, hv⟩ := t3_exists
  have hv₂ : T3 (-(if σ then v else -v)) := by
    cases σ
    · simpa using hv.neg.neg
    · simpa using hv.neg
  obtain ⟨V₁, hV₁⟩ := exists_close (a := a₁) (b := b₁) (c := c₁) hv.neg hN₁ h₁
  obtain ⟨V₂, hV₂⟩ := exists_close (a := a₂) (b := b₂) (c := c₂) hv₂ hN₂ h₂
  obtain ⟨M, hM⟩ : ∃ M, M = 2 * a₁ + b₁ + 2 * c₁ + 2 := ⟨_, rfl⟩
  have hMe : frL a₁ b₁ c₁ + 1 = M := by
    rw [hM]
    rfl
  rw [hMe] at hf
  obtain ⟨r, hr⟩ : ∃ r, r = 2 * a₁ + b₁ + 2 * i + 1 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = 2 * a₁ + b₁ + 2 * i := ⟨_, rfl⟩
  obtain ⟨t₂, ht₂⟩ : ∃ t₂, t₂ = 2 * a₂ + b₂ + 2 * j := ⟨_, rfl⟩
  have er : (rL a₁ b₁ i).1 = r := hr.symm
  rw [er] at hf hq
  have e₁ : wLoop₁ a₁ b₁ c₁ i L₁ = (t, true) :: (r, true) :: (t, false) :: rW a₁ b₁ c₁ L₁ := by
    subst hr ht
    simp [wLoop₁, hB, holB, tL, rL, linv]
  have e₂ : wLoop₂ a₂ b₂ c₂ j L₂ M (r, σ) = (t₂ + M, true) :: (r, σ) :: (t₂ + M, false) :: shW M
    (rW a₂ b₂ c₂ L₂) := by
    subst ht₂
    simp [wLoop₂, tL]
  rw [e₁, e₂] at hf
  rw [e₁] at hq hs
  have l₁ := rW_labels_lt (a := a₁) (b := b₁) (c := c₁) (L := L₁) fun m hm => (hL₁ m hm).1
  have hfr : frL a₁ b₁ c₁ + 1 = M := hMe
  have zr : NoLab (rW a₁ b₁ c₁ L₁) r := noLab_iff_cnt.mpr (cnt_rW_zero (by omega)
    (by omega) fun m hm => by
    have := hL₁ m hm
    omega)
  have zt : NoLab (rW a₁ b₁ c₁ L₁) t := noLab_iff_cnt.mpr (cnt_rW_zero (by omega)
    (by omega) fun m hm => by
    have := hL₁ m hm
    omega)
  have zt₂ : NoLab (rW a₂ b₂ c₂ L₂) t₂ := noLab_iff_cnt.mpr (cnt_rW_zero (by omega)
    (by omega) fun m hm => by
    have := hL₂ m hm
    omega)
  have hrM : r < M := by omega
  have htM : t < M := by omega
  let V : ℕ → S3 := fun k => if k < M then Function.update (Function.update V₁ r v) t 0 k else if k
    = t₂ + M then 0 else V₂ (k - M)
  have hVr : V r = v := by
    simp only [V, ite_eq_left hrM]
    rw [Function.update_of_ne (by omega), Function.update_self]
  have hVt : V t = 0 := by
    simp only [V, ite_eq_left htM]
    exact Function.update_self _ _ _
  have hVt₂ : V (t₂ + M) = 0 := by
    have : ¬ t₂ + M < M := by omega
    simp only [V, ite_eq_right this, ite_true]
  have e3 : wv V (rW a₁ b₁ c₁ L₁) = -v := by
    rw [← hV₁]
    refine wv_congr fun l hl => ?_
    have h3 : l.1 < M := by
      have := l₁ l hl
      omega
    simp only [V, ite_eq_left h3]
    rw [Function.update_of_ne (zt l hl), Function.update_of_ne (zr l hl)]
  have e4 : wv V (shW M (rW a₂ b₂ c₂ L₂)) = -(if σ then v else -v) := by
    rw [wv_shW, ← hV₂]
    refine wv_congr fun l hl => ?_
    have h3 : ¬ l.1 + M < M := by omega
    have h4 : l.1 + M ≠ t₂ + M := fun he => zt₂ l hl (by omega)
    simp only [V, ite_eq_right h3, ite_eq_right h4, Nat.add_sub_cancel]
  have hV : ∀ d, wv V (dW ((t, true) :: (r, true) :: (t, false) :: rW a₁ b₁ c₁ L₁)
      ((t₂ + M, true) :: (r, σ) :: (t₂ + M, false) :: shW M (rW a₂ b₂ c₂ L₂)) d) = 0 := by
    intro d
    rcases dW_cases ((t, true) :: (r, true) :: (t, false) :: rW a₁ b₁ c₁ L₁)
      ((t₂ + M, true) :: (r, σ) :: (t₂ + M, false) :: shW M (rW a₂ b₂ c₂ L₂)) d with ⟨-, h3⟩ | ⟨-,
        h3⟩ | h3
    · rw [h3]
      simp [lVal, hVr, hVt, e3]
    · rw [h3]
      cases σ <;> simp [lVal, hVr, hVt₂, e4]
    · rw [h3]
      rfl
  have hg₁ := good_rW (a := a₁) (b := b₁) hN₁ fun m hm => (hL₁ m hm).1
  have hg₂ := good_rW (a := a₂) (b := b₂) hN₂ fun m hm => (hL₂ m hm).1
  have hP : ∀ k, cnt ((t, true) :: (r, true) :: (t, false) :: rW a₁ b₁ c₁ L₁) k +
      cnt ((t₂ + M, true) :: (r, σ) :: (t₂ + M, false) :: shW M (rW a₂ b₂ c₂ L₂)) k ≤ 2 := by
    intro k
    by_cases hk : k < M
    · have s0 : cnt (shW M (rW a₂ b₂ c₂ L₂)) k = 0 := noLab_iff_cnt.mp (noLab_shW_of fun k' he
        => by omega)
      have g := hg₁ k
      have c1 : k = r → cnt (rW a₁ b₁ c₁ L₁) k = 0 := fun h => h ▸ noLab_iff_cnt.mp zr
      have c2 : k = t → cnt (rW a₁ b₁ c₁ L₁) k = 0 := fun h => h ▸ noLab_iff_cnt.mp zt
      simp only [cnt_cons, s0]
      split_ifs <;> omega
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + M := ⟨k - M, by omega⟩
      have s0 : cnt (rW a₁ b₁ c₁ L₁) (k' + M) = 0 := noLab_iff_cnt.mp fun l hl he => by
        have := l₁ l hl
        omega
      have g := hg₂ k'
      have c1 : k' = t₂ → cnt (rW a₂ b₂ c₂ L₂) k' = 0 := fun h => h ▸ noLab_iff_cnt.mp zt₂
      simp only [cnt_cons, s0, cnt_shW]
      split_ifs <;> omega
  have := side_null (finW_dW _ _) (isPaired_dW hP) hf (by rw [dW_zero]; simp) hV hN (p := q)
    (by rw [dW_zero]; exact hq) cρ hcl hρ
    (fun u hu => by rw [dW_zero]; exact hs u hu)
  rw [hVr] at this
  exact hv.1 this

end sides

end GraphMinor.Surface
