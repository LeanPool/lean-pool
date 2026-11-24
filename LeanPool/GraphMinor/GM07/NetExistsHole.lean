/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.NetExistsCycle
public import LeanPool.GraphMinor.Surface.CohCount
public import LeanPool.GraphMinor.Surface.CutNull
public import LeanPool.GraphMinor.Surface.Classification

/-!
# A polygon whose free sides are given arcs

This is the step "augment" of Graph Minors VII, page 216, for one component of the surface cut along
the drawing. A connected surface
is a model surface, so it is a polygon with one free side around each cuff (`presents_ew`). The
other sides are the added edges. We
move each free side along its cuff and split it, so that its parts are the arcs on this cuff
(`exists_hole_word`).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface

universe u

/-- Maps of `[0, 1]`, one after the other, as a list. -/
noncomputable def concF {κ : Type*} (m : κ → ℝ → ℝ) : List κ → ℝ → ℝ
  | [] => id
  | [x] => m x
  | x :: y :: L => conc2 (m x) (concF m (y :: L))

theorem concF_zero {κ : Type*} (m : κ → ℝ → ℝ) (L : List κ) (x : κ) : concF m (x :: L) 0 = m x 0
  := by
  cases L with
  | nil => rfl
  | cons y L => exact conc2_zero

theorem concF_props {κ : Type*} {m : κ → ℝ → ℝ} (L : List κ) : ∀ x, (x :: L).IsChain (fun α β
  => m α 1 = m β 0) →
    (∀ y ∈ x :: L, ContinuousOn (m y) (Icc 0 1) ∧ StrictMonoOn (m y) (Icc 0 1)) →
    ContinuousOn (concF m (x :: L)) (Icc 0 1) ∧ StrictMonoOn (concF m (x :: L)) (Icc 0 1) ∧ ∃ ω ∈
      (x :: L).getLast?, concF m (x :: L) 1 = m ω 1 := by
  induction L with
  | nil =>
    intro x _ h
    exact ⟨(h x (by simp)).1, (h x (by simp)).2, x, by simp, rfl⟩
  | cons y L ih =>
    intro x hc h
    rw [List.isChain_cons_cons] at hc
    obtain ⟨h1, h2, ω, h3, h4⟩ := ih y hc.2 fun z hz => h z (List.mem_cons_of_mem _ hz)
    have h5 : m x 1 = concF m (y :: L) 0 := by rw [concF_zero]; exact hc.1
    refine ⟨continuousOn_conc2 (h x (by simp)).1 h1 h5, strictMonoOn_conc2 (h x
      (by simp)).2 h2 h5, ω, ?_, ?_⟩
    · rw [List.getLast?_cons_cons]
      exact h3
    · rw [concF]
      rw [conc2_one h5, h4]

theorem exists_fresh_cnt (w : List Letter) : ∃ q, cnt w q = 0 := by
  obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset (w.map Prod.fst).toFinset
  refine ⟨q, noLab_iff_cnt.mp fun l hl => ?_⟩
  intro he
  exact hq (List.mem_toFinset.mpr (List.mem_map.mpr ⟨l, hl, he⟩))

section

variable {T : Type u} [TopologicalSpace T] [T2Space T]

/-- `exists_split`, stated with counts of labels. -/
theorem exists_split_cnt {w : List Letter} {p q : ℕ} {f : ℕ × ℂ → T} (hf : Presents
  (sW w) f) {ρ : ℝ → T} (hρ : SideVal (sW w) f p ρ)
    (hp : cnt w p = 1) (hq : cnt w q = 0) :
    ∃ w' f', Presents (sW w') f' ∧ SideVal (sW w') f' p (fun u => ρ (u / 2)) ∧ SideVal (sW w') f' q
      (fun u => ρ ((1 + u) / 2)) ∧
      w'.length = w.length + 1 ∧ (∀ k, k ≠ q → cnt w' k = cnt w k) ∧ cnt w' q = 1 ∧
      ∀ k, k ≠ p → k ≠ q → ∀ ρ', SideVal (sW w) f k ρ' → SideVal (sW w') f' k ρ' := by
  have hpq : p ≠ q := by
    rintro rfl
    omega
  obtain ⟨i, r, h1, -⟩ := id hρ
  obtain ⟨-, h2⟩ := sW_get h1
  obtain ⟨hr, h3⟩ := List.getElem?_eq_some_iff.mp h2
  have hw : w = w.take r ++ (p, true) :: w.drop (r + 1) := by
    conv_lhs => rw [← List.take_append_drop r w, List.drop_eq_getElem_cons hr, h3]
  set A := w.take r with hA
  set B := w.drop (r + 1) with hB
  have hc : ∀ k, cnt w k = cnt (B ++ A) k + if p = k then 1 else 0 := fun k => by
    rw [hw, cnt_append, cnt_cons, cnt_append]
    simp only
    omega
  have hn1 : NoLab (B ++ A) p := noLab_iff_cnt.mpr (by
    have := hc p
    simp only [ite_true] at this
    omega)
  have hn2 : NoLab (B ++ A) q := noLab_iff_cnt.mpr (by have := hc q; omega)
  rw [hw] at hf hρ
  obtain ⟨f', h4, h5, h6, h7⟩ := exists_split hpq hn1 hn2 hf hρ
  have hc' : ∀ k, cnt (A ++ (p, true) :: (q, true) :: B) k = cnt w k + if q = k then 1 else 0
    := fun k => by
    rw [hw, cnt_append, cnt_cons, cnt_cons, cnt_append, cnt_cons]
    simp only
    omega
  refine ⟨_, f', h4, h5, h6, ?_, fun k hk => ?_, ?_, fun k h8 h9 ρ' h10 => h7 k h8 h9 ρ' (hw ▸ h10)⟩
  · have hlen : w.length = A.length + (B.length + 1) := by
      have := congrArg List.length hw
      rwa [List.length_append, List.length_cons] at this
    rw [hlen]
    simp only [List.length_append, List.length_cons]
    omega
  · rw [hc' k, ite_eq_right (Ne.symm hk), add_zero]
  · rw [hc' q, hq]
    simp

/-- A free side which runs through a list of paths is split into one side for each path. -/
theorem exists_split_list {κ : Type*} (F : ℝ → T) (m : κ → ℝ → ℝ) (L : List κ) : ∀ (x : κ) (p : ℕ)
  (w : List Letter) (f : ℕ × ℂ → T),
    (x :: L).IsChain (fun α β => m α 1 = m β 0) → Presents (sW w) f → cnt w p = 1 → Good w
      → SideVal (sW w) f p (fun u => F (concF m (x :: L) u)) →
    ∃ w' f', Presents (sW w') f' ∧ Good w' ∧ w.length ≤ w'.length ∧
      (∀ y ∈ x :: L, ∃ k, (k = p ∨ cnt w k = 0) ∧ cnt w' k = 1 ∧ SideVal (sW w') f' k (fun u => F
        (m y u))) ∧
      ∀ k, cnt w k ≠ 0 → k ≠ p → cnt w' k = cnt w k ∧ ∀ ρ', SideVal (sW w) f k ρ' → SideVal
        (sW w') f' k ρ' := by
  induction L with
  | nil =>
    intro x p w f _ hf hp hG hs
    refine ⟨w, f, hf, hG, le_rfl, fun y hy => ?_, fun k _ _ => ⟨rfl, fun _ h => h⟩⟩
    obtain rfl : y = x := by simpa using hy
    exact ⟨p, .inl rfl, hp, hs⟩
  | cons y L ih =>
    intro x p w f hc hf hp hG hs
    rw [List.isChain_cons_cons] at hc
    obtain ⟨q, hq⟩ := exists_fresh_cnt w
    have hpq : p ≠ q := by
      rintro rfl
      omega
    have hrw : concF m (x :: y :: L) = conc2 (m x) (concF m (y :: L)) := rfl
    have h5 : m x 1 = concF m (y :: L) 0 := by rw [concF_zero]; exact hc.1
    obtain ⟨w₁, f₁, h1, h2, h3, h4, h6, h7, h8⟩ := exists_split_cnt hf hs hp hq
    have s1 : SideVal (sW w₁) f₁ p (fun u => F (m x u)) := h2.congr fun u hu
      => by rw [hrw, conc2_left hu]
    have s2 : SideVal (sW w₁) f₁ q (fun u => F (concF m (y :: L) u)) := h3.congr fun u hu
      => by rw [hrw, conc2_right h5 hu]
    have hG1 : Good w₁ := fun k => by
      by_cases hk : k = q
      · subst hk
        omega
      · rw [h6 k hk]
        exact hG k
    obtain ⟨w', f', a1, a2, a3, a4, a5⟩ := ih y q w₁ f₁ hc.2 h1 h7 hG1 s2
    have hp1 : cnt w₁ p = 1 := by rw [h6 p hpq, hp]
    refine ⟨w', f', a1, a2, by omega, fun z hz => ?_, fun k hk1 hk2 => ?_⟩
    · rcases List.mem_cons.mp hz with rfl | hz
      · have := a5 p (by omega) hpq
        exact ⟨p, .inl rfl, by rw [this.1, hp1], this.2 _ s1⟩
      · obtain ⟨k, b1, b2, b3⟩ := a4 z hz
        refine ⟨k, .inr ?_, b2, b3⟩
        rcases b1 with rfl | b1
        · exact hq
        · have hkq : k ≠ q := by
            rintro rfl
            omega
          rw [← h6 k hkq]
          exact b1
    · have hkq : k ≠ q := by
        rintro rfl
        exact hk1 hq
      have h9 := a5 k (by rw [h6 k hkq]; exact hk1) hkq
      exact ⟨by rw [h9.1, h6 k hkq], fun ρ' h10 => h9.2 _ (h8 k hk2 hkq ρ' h10)⟩

end

section

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] {ι : Type*} [Finite ι] {ℓ : ι → ℝ → Z}

/-- Move the free sides around the cuffs one at a time, and split them into the arcs on these cuffs.
-/
theorem exists_holes (hS : IsSurface Z) (hfam : IsArcFamily ℓ) {c : ℕ} {p : ℕ
  → ℕ} {ρ : ℕ → ℝ → Z} (hp : ∀ i j, i < c → j < c → p i = p j → i = j)
    (hρ : ∀ i < c, ContinuousOn (ρ i) (Icc 0 1) ∧ InjOn (ρ i) (Ico 0 1) ∧ ρ i 0 = ρ i 1)
      (hcuff : ∀ i < c, ρ i '' Icc 0 1 ∈ cuffs Z)
    (hne : ∀ i j, i < c → j < c → i ≠ j → ρ i '' Icc 0 1 ≠ ρ j '' Icc 0 1) {w₀ : List Letter} {g₀ :
      ℕ × ℂ → Z} (hw : Presents (sW w₀) g₀) (hG : Good w₀)
    (hside : ∀ i < c, cnt w₀ (p i) = 1 ∧ SideVal (sW w₀) g₀ (p i) (ρ i)) (e : ℕ) : e ≤ c
      → ∃ w g, Presents (sW w) g ∧ Good w ∧ w₀.length ≤ w.length ∧
      (∀ i, e ≤ i → i < c → cnt w (p i) = 1 ∧ SideVal (sW w) g (p i) (ρ i)) ∧
      ∀ i < e, ∀ α, ℓ α 0 ∈ ρ i '' Icc 0 1 → ∃ k σ, cnt w k = 1 ∧ (∀ j, e ≤ j → j < c → k ≠ p j)
        ∧ SideVal (sW w) g k (fun u => ℓ α (ofs σ u)) := by
  classical
  induction e with
  | zero =>
    intro _
    exact ⟨w₀, g₀, hw, hG, le_rfl, fun i _ hi => hside i hi, fun i hi => absurd hi (by omega)⟩
  | succ e ih =>
    intro he
    obtain ⟨w, g, h1, h2, h3, h4, h5⟩ := ih (by omega)
    have hec : e < c := he
    obtain ⟨hc, hi, hl⟩ := hρ e hec
    have hC := hcuff e hec
    have hcl : ∀ j < c, IsClosed (ρ j '' Icc 0 1) := fun j hj =>
      (isCompact_Icc.image_of_continuousOn (hρ j hj).1).isClosed
    set C := ρ e '' Icc 0 1 with hCdef
    obtain ⟨φ, hφ⟩ : ∃ φ : Circle ≃ₜ C, ∀ u ∈ Icc (0 : ℝ) 1, (φ (ee u)).1 = ρ e u
      := exists_circle_param hc hi hl
    set U : Set Z := (⋃ j ∈ {j | j < c ∧ j ≠ e}, ρ j '' Icc 0 1)ᶜ with hU
    have hfinite : {j | j < c ∧ j ≠ e}.Finite :=
      (Set.finite_lt_nat c).subset fun _ hj => hj.1
    have hUo : IsOpen U :=
      (hfinite.isClosed_biUnion fun j hj => hcl j hj.1).isOpen_compl
    have hCU : C ⊆ U := by
      intro x hx hmem
      obtain ⟨j, ⟨hj, hj'⟩, hxj⟩ := mem_iUnion₂.mp hmem
      exact Set.disjoint_left.mp (cuffs_disjoint hC (hcuff j hj) (hne e j hec hj hj'.symm)) hx hxj
    have hoff : ∀ j < c, j ≠ e → ∀ x ∈ ρ j '' Icc 0 1, x ∉ U := fun j hj hj' x hx h =>
      h (mem_iUnion₂.mpr ⟨j, ⟨hj, hj'⟩, hx⟩)
    obtain ⟨A, a1, a2, a3⟩ := exists_arcs_on hfam hC
    obtain ⟨L, σ, n, b1, b2, b3, b4, ⟨a₀, ha₀, ω, hω, b5⟩, -, -, -⟩ := exists_cuff_order hfam φ A
      a1 a3
    obtain ⟨L', rfl⟩ : ∃ L', L = a₀ :: L' := by
      cases L with
      | nil => simp at ha₀
      | cons x L' =>
        obtain rfl : x = a₀ := by simpa using ha₀
        exact ⟨L', rfl⟩
    obtain ⟨c1, c2, ω', hω', c3⟩ := concF_props (m := n) L' a₀ b4 fun y hy => ⟨(b3 y
      ((b2 y).mp hy)).1, (b3 y ((b2 y).mp hy)).2.1⟩
    obtain rfl := Option.mem_unique hω' hω
    have s0 : SideVal (sW w) g (p e) (fun u => (φ (ee u)).1) := (h4 e le_rfl hec).2.congr fun u hu
      => (hφ u hu).symm
    obtain ⟨g₁, d1, d2, d3⟩ := exists_pieces1 hS hC hUo hCU φ h1 s0 c1 c2
      (by rw [c3, concF_zero, b5])
    have hcnt := (h4 e le_rfl hec).1
    obtain ⟨w₂, g₂, f1, f2, f3, f4, f5⟩ := exists_split_list (fun x => (φ (ee x)).1) n L' a₀
      (p e) w g₁ b4 d1 hcnt h2 d2
    refine ⟨w₂, g₂, f1, f2, h3.trans f3, fun i hi1 hi2 => ?_, fun i hi α hα => ?_⟩
    · have q1 := h4 i (by omega) hi2
      have hne' : p i ≠ p e := fun h => by
        have := hp i e hi2 hec h
        omega
      have q2 := f5 (p i) (by omega) hne'
      refine ⟨by rw [q2.1, q1.1], q2.2 _ (d3 _ _ q1.2 fun u hu => hoff i hi2 (by omega) _ ⟨u, hu,
        rfl⟩)⟩
    · obtain ⟨⟨u₀, hu₀, hα'⟩⟩ : Nonempty (∃ u₀ ∈ Icc (0 : ℝ) 1, ρ i u₀ = ℓ α 0) := by
        obtain ⟨u₀, h6, h7⟩ := hα
        exact ⟨⟨u₀, h6, h7⟩⟩
      have hic : i < c := by omega
      by_cases hie : i = e
      · subst hie
        have hαA : α ∈ A := a2 α 0 (by simp) hα
        obtain ⟨k, g1, g2, g3⟩ := f4 α ((b2 α).mpr hαA)
        refine ⟨k, σ α, g2, fun j hj1 hj2 => ?_, g3.congr fun u hu => (b3 α hαA).2.2 u hu⟩
        have q1 := h4 j (by omega) hj2
        rcases g1 with rfl | g1
        · intro he'
          have := hp i j hec hj2 he'
          omega
        · rintro rfl
          omega
      · have hi' : i < e := by omega
        obtain ⟨k, σ', g1, g2, g3⟩ := h5 i hi' α hα
        have hke : k ≠ p e := g2 e le_rfl hec
        have q2 := f5 k (by omega) hke
        refine ⟨k, σ', by rw [q2.1, g1], fun j hj1 hj2 => g2 j (by omega) hj2,
          q2.2 _ (d3 _ _ g3 fun u hu => ?_)⟩
        exact hoff i hic hie _ (arc_sub_cuff hfam (hcuff i hic) (by simp) hα _ (ofs_mem hu))

theorem cnt_eq_one_of_free {w : List Letter} {r k : ℕ} {e : Bool} (h : w[r]? = some (k, e))
  (hf : FreeSide (sW w) 0 r) : cnt w k = 1 := by
  obtain ⟨hr, h3⟩ := List.getElem?_eq_some_iff.mp h
  have hw : w = w.take r ++ (k, e) :: w.drop (r + 1) := by
    conv_lhs => rw [← List.take_append_drop r w, List.drop_eq_getElem_cons hr, h3]
  have h1 : cnt (w.take r) k = 0 := noLab_iff_cnt.mp fun l hl he => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hl
    obtain ⟨l₁, l₂⟩ := l
    obtain rfl : l₁ = k := he
    have hlt : q < r := by
      have := (List.getElem?_eq_some_iff.mp hq).1
      simp at this
      omega
    rw [List.getElem?_take_of_lt hlt] at hq
    have := hf 0 q _ e l₂ (by rw [sW_zero]; exact h) (by rw [sW_zero]; exact hq)
    simp at this
    omega
  have h2 : cnt (w.drop (r + 1)) k = 0 := noLab_iff_cnt.mp fun l hl he => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hl
    obtain ⟨l₁, l₂⟩ := l
    obtain rfl : l₁ = k := he
    rw [List.getElem?_drop] at hq
    have := hf 0 (r + 1 + q) _ e l₂ (by rw [sW_zero]; exact h) (by rw [sW_zero]; exact hq)
    simp at this
    omega
  rw [hw, cnt_append, cnt_cons, h1, h2]
  simp

/-- **A polygon for a connected surface.** A connected surface with a family of arcs on its boundary
has a polygon in which each arc
is one free side, up to reversal. The other sides are the edges that the sketch of page 216 adds. -/
theorem exists_hole_word [ConnectedSpace Z] (hS : IsSurface Z) (hfam : IsArcFamily ℓ) :
    ∃ (w : List Letter) (g : ℕ × ℂ → Z), 2 ≤ w.length ∧ Good w ∧ Presents (sW w) g ∧
      ∀ α, ∃ k σ, cnt w k = 1 ∧ SideVal (sW w) g k (fun u => ℓ α (ofs σ u)) := by
  classical
  obtain ⟨a, b, c, ⟨e⟩⟩ := classification Z hS inferInstance
  obtain ⟨-, f₀, hf₀⟩ := presents_ew a b c
  have hf := presents_comp hf₀ e.symm
  set f := e.symm ∘ f₀ with hfdef
  have hne : ∀ i j, i < c → j < c → i ≠ j → holeC a b c f i ≠ holeC a b c f j
    := fun i j hi hj hij he => by
    have h1 : Set.InjOn (holeC a b c f) {i | i < c} := by
      have h2 := ncard_cuffs hf
      rw [cuffs_eq_holeC hf] at h2
      have h3 : Set.ncard {i | i < c} = c := by
        have : {i | i < c} = ((Finset.range c : Finset ℕ) : Set ℕ) := by
          ext i
          simp
        rw [this, ncard_coe_finset, Finset.card_range]
      exact (Set.ncard_image_iff (by exact Set.finite_lt_nat c)).mp (h2.trans h3.symm)
    exact hij (h1 hi hj he)
  have hcuff : ∀ i < c, holeC a b c f i ∈ cuffs Z := fun i hi => by
    rw [cuffs_eq_holeC hf]
    exact ⟨i, hi, rfl⟩
  have hw0 : (ew a b c).length ≠ 0 := by simp [ew]
  have hgood : Good (ew a b c) := by
    rw [ew_eq_rW]
    exact good_rW (List.nodup_range' ..) fun m hm => by
      have := (List.mem_range'_1.mp hm).2
      omega
  have hside : ∀ i < c, cnt (ew a b c) (rL a b i).1 = 1 ∧ SideVal (sW (ew a b c)) f (rL a b i).1
    (holeP a b c f i) := fun i hi => by
    have h1 := sideVal_hole hf hi
    rw [← ew_eq_rW] at h1
    refine ⟨?_, h1⟩
    refine cnt_eq_one_of_free (r := 4 * a + 2 * b + 3 * i + 1) (e := true) ?_ (freeSide_hole hi)
    rw [ew_get a b c (by omega), lab_t (δ := 1) hi (by norm_num), sgn_t (δ := 1) hi (by norm_num)]
    simp [rL]
  obtain ⟨w, g, h1, h2, h3, -, h5⟩ := exists_holes hS hfam (p := fun i => (rL a b i).1) (ρ
    := holeP a b c f) (c := c) (fun i j _ _ h => by simpa [rL] using h)
    (fun i hi => hole_loop hf hi) (fun i hi => hcuff i hi) hne hf hgood hside c le_rfl
  refine ⟨w, g, ?_, h2, h1, fun α => ?_⟩
  · have : (ew a b c).length = (nfW a b c).length + 2 := by simp [ew]
    omega
  · have hmem := hfam.mem α 0 (by simp)
    rw [← sUnion_cuffs, cuffs_eq_holeC hf] at hmem
    obtain ⟨_, ⟨i, hi, rfl⟩, h6⟩ := hmem
    obtain ⟨k, σ, h7, -, h8⟩ := h5 i hi α h6
    exact ⟨k, σ, h7, h8⟩

end

end GraphMinor.GM07
