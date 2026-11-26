/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CohPrim

/-!
# The classes of the normal word

Let `Y` be presented by the word `ew a b c`. A class in `KCl Y A` is given by the values of its
primitive on the labels
of the handles and of the cross-caps. These values are free, except that twice the sum on the
cross-caps vanishes
(`card_kCl`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

universe u

variable {a b c : ℕ} {Y : Type u} [TopologicalSpace Y] {f : ℕ × ℂ → Y} {A : Type} [AddCommGroup A]

theorem pmap_cont (hf : Presents (sW (ew a b c)) f) : ContinuousOn (pmap f) (closedBall 0 1) :=
  hf.1.comp (by fun_prop) fun z hz => ⟨(ew_mem_dsk a b c).1, by simpa using hz⟩

theorem mem_dsk_ew {x : ℕ × ℂ} (h : x ∈ Dsk (sW (ew a b c))) : x.1 = 0 ∧ x.2 ∈ closedBall (0 : ℂ) 1
  := by
  obtain ⟨i, z⟩ := x
  refine ⟨?_, by simpa using h.2⟩
  by_contra hi
  exact h.1 (by simp [sW, show i ≠ 0 from hi, nW])

theorem pmap_image (hf : Presents (sW (ew a b c)) f) : pmap f '' closedBall 0 1 = univ := by
  refine eq_univ_of_forall fun y => ?_
  have h1 : y ∈ f '' Dsk (sW (ew a b c)) := by
    rw [hf.2.1]
    exact mem_univ y
  obtain ⟨⟨i, z⟩, hz, rfl⟩ := h1
  obtain ⟨h2, h3⟩ := mem_dsk_ew hz
  simp only at h2 h3
  subst h2
  exact ⟨z, h3, rfl⟩

theorem freeSide_hole {i : ℕ} (hi : i < c) : FreeSide (sW (ew a b c)) 0 (4 * a + 2 * b + 3 * i + 1)
  := by
  intro j q k e e' h1 h2
  obtain ⟨rfl, h3⟩ := sW_get h2
  rw [sW_zero] at h1
  obtain ⟨hp, hl, -⟩ := (ew_get_iff _ _ _ _ _ _).mp h1
  obtain ⟨hq, hl', -⟩ := (ew_get_iff _ _ _ _ _ _).mp h3
  have ht := (twin_eq_iff hp).mpr ⟨i, hi, rfl⟩
  rcases lab_two hp hq (hl.trans hl'.symm) with h4 | h4
  · rw [h4]
  · rw [h4, ht]

theorem twin_of_free {p : ℕ} (hp : p < 4 * a + 2 * b + 3 * c + 2) (hfr : FreeSide (sW
  (ew a b c)) 0 p) :
    twin a b c p = p := by
  have h1 := hfr 0 (twin a b c p) (lab a b c p) (sgn a b c p) (sgn a b c (twin a b c p))
    (by rw [sW_zero]; exact ew_get a b c hp) (by
      rw [sW_zero, ← lab_twin hp]
      exact ew_get a b c (twin_lt hp))
  exact (Prod.mk.inj h1).2.symm

/-- On a free side, the change of a primitive of a class that vanishes on the boundary is zero. -/
theorem volt_free [T2Space Y] {φ : Y → Y → A} {g : ℂ → A} (hf : Presents (sW (ew a b c)) f)
  (hφ : BdTriv φ)
    (hg : IsPrim φ (pmap f) g) {i : ℕ} (hi : i < c) : volt a b c g (4 * a + 2 * b + 3 * i + 1) = 0
      := by
  obtain ⟨h, N, hN, hbd⟩ := hφ
  obtain ⟨ε, h0, h1⟩ := hg
  simp only [neg_add_eq_sub] at hbd h1
  obtain ⟨ε', h0', h2⟩ := exists_eps (isCompact_closedBall 0 1) (pmap_cont hf) hN
  have hs := (surface_of_presents (finW_sW _) (isPaired_ew a b c) hf).2
  set r := 4 * a + 2 * b + 3 * i + 1 with hr
  set n := 4 * a + 2 * b + 3 * c + 2 with hn
  have hrn : r < n := by omega
  have hb : ∀ u ∈ Icc (0 : ℝ) 1, pmap f (per n (r + u)) ∈ bd Y := by
    intro u hu
    rw [hs]
    refine ⟨spt (sW (ew a b c)) 0 r u, ⟨0, r, u, ?_, freeSide_hole hi, hu, rfl⟩, ?_⟩
    · rw [sW_zero, ew_length]
      exact hrn
    · rw [spt_ew]
      rfl
  let v : ℝ → A := fun u => g (per n (r + u)) - h (pmap f (per n (r + u)))
  have hδ : 0 < min ε ε' / 9 := by positivity
  have hc := const_of_near (v := v) hδ (fun s hs' t ht hst => by
    have hlip : ∀ x y : ℝ, |x - y| < min ε ε' / 9 → ‖per n (r + x) - per n (r + y)‖ < min ε ε' := by
      intro x y hxy
      have h3 := norm_per_sub (show 0 < n by omega) (r + x) (r + y)
      rw [show (r : ℝ) + x - (r + y) = x - y by ring] at h3
      have : 0 < min ε ε' := by positivity
      linarith
    have h3 := hlip t s (by rwa [abs_sub_comm])
    have e1 := h1 _ (mem_ball_per n (r + t)) _ (mem_ball_per n (r + s)) (lt_of_lt_of_le h3
      (min_le_left _ _))
    have e2 := hbd _ (hb t ht) _ (hb s hs') (h2 _ (mem_ball_per n (r + t)) _ (mem_ball_per n
      (r + s))
      (lt_of_lt_of_le h3 (min_le_right _ _)))
    rw [e1] at e2
    simp only [v]
    rw [sub_eq_iff_eq_add] at e2 ⊢
    rw [e2]
    abel)
  have h3 := hc 1 ⟨zero_le_one, le_rfl⟩
  simp only [v] at h3
  have e0 : per n (r + (0 : ℝ)) = cor a b c r := by simp [cor, hn]
  have e1 : per n (r + (1 : ℝ)) = cor a b c (r + 1) := by simp [cor, hn]
  rw [e0, e1] at h3
  have e2 : pmap f (cor a b c (r + 1)) = pmap f (cor a b c r) := hole_cor hf hi
  rw [e2] at h3
  have hst : st a b c r = r := by
    simp only [st, hr, sgn_t hi (by omega : 1 < 3)]
    rfl
  have hen : en a b c r = r + 1 := by
    simp only [en, hr, sgn_t hi (by omega : 1 < 3)]
    rfl
  rw [volt, hst, hen]
  exact sub_eq_zero.mpr (sub_left_inj.mp h3)

theorem loop_st_en (hf : Presents (sW (ew a b c)) f) {p : ℕ} (hp : p < 4 * a + 2 * b) :
    pmap f (cor a b c (en a b c p)) = pmap f (cor a b c (st a b c p)) := by
  unfold en st
  by_cases h : sgn a b c p
  · rw [ite_eq_left h, ite_eq_left h]
    exact loop_cor hf hp
  · rw [ite_eq_right h, ite_eq_right h]
    exact (loop_cor hf hp).symm

theorem rep_lt' {k : ℕ} (hk : k < 2 * a + b) : rep a b c k < 4 * a + 2 * b := by
  unfold rep
  split_ifs <;> omega

/-- Equivalent local cocycles have the same values on the labels of the handles and of the
cross-caps. -/
theorem lval_rel {φ φ' : Y → Y → A} {g g' : ℂ → A} (hf : Presents (sW (ew a b c)) f) (hg : IsPrim φ
  (pmap f) g)
    (hg' : IsPrim φ' (pmap f) g') (hr : CohRel φ φ') {k : ℕ} (hk : k < 2 * a + b) :
    lval a b c g k = lval a b c g' k := by
  obtain ⟨h, N, hN, hrel⟩ := hr
  have h2 := hg.of_rel (pmap_cont hf) hN hrel
  set x := cor a b c (st a b c (rep a b c k)) with hx
  set y := cor a b c (en a b c (rep a b c k)) with hy
  have h3 : g' y - g' x = (g y - h (pmap f y)) - (g x - h (pmap f x)) := by
    have h5 := hg'.sub_eq h2 (a := x) (b := y) (mem_ball_per _ _) (mem_ball_per _ _)
    simpa only [neg_add_eq_sub] using h5
  have h4 : pmap f y = pmap f x := loop_st_en hf (rep_lt' (c := c) hk)
  rw [lval, lval, volt, volt, ← hx, ← hy, h3, h4]
  abel

/-- Two local cocycles with the same values on the labels of the handles and of the cross-caps are
equivalent, if both
vanish on the boundary. -/
theorem cohRel_of_lval [T2Space Y] {φ φ' : Y → Y → A} {g g' : ℂ → A} (hf : Presents (sW
  (ew a b c)) f) (hφ : IsCoc φ)
    (hφ' : IsCoc φ') (hb : BdTriv φ) (hb' : BdTriv φ') (hg : IsPrim φ (pmap f) g) (hg' : IsPrim φ'
      (pmap f) g')
    (he : ∀ k < 2 * a + b, lval a b c g k = lval a b c g' k) : CohRel φ φ' := by
  set n := 4 * a + 2 * b + 3 * c + 2 with hn
  let V : ℕ → A := fun k => lval a b c g k - lval a b c g' k
  have hSm : ∀ j, Sm a b c V j = Sm a b c (lval a b c g) j - Sm a b c (lval a b c g') j := by
    intro j
    simp only [Sm, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [lv, V]
    split_ifs <;> abel
  let d : ℂ → A := fun z => g z - g' z
  have hdc : ∀ j ≤ n, d (cor a b c j) = d (cor a b c 0) + Sm a b c V j := by
    intro j hj
    simp only [d]
    rw [g_cor hf hg hj, g_cor hf hg' hj, hSm]
    abel
  have hV1 : ∀ k < 2 * a + b, V k = 0 := fun k hk => sub_eq_zero.mpr (he k hk)
  have hV2 : ∀ i < c, V (2 * a + b + 2 * i + 1) = 0 := by
    intro i hi
    have e : lab a b c (4 * a + 2 * b + 3 * i + 1) = 2 * a + b + 2 * i + 1 := lab_t hi (by omega)
    have hp : 4 * a + 2 * b + 3 * i + 1 < n := by omega
    simp only [V]
    rw [← e, ← volt_eq hf hg hp, ← volt_eq hf hg' hp, volt_free hf hb hg hi,
      volt_free hf hb' hg' hi, sub_zero]
  have hpair : ∀ p q, p < n → q < n → p ≠ q → lab a b c p = lab a b c q → ∀ u ∈ Icc (0 : ℝ) 1,
      d (per n (q + flp (sgn a b c p) (sgn a b c q) u)) = d (per n (p + u)) := by
    intro p q hp hq hne hl u hu
    obtain ⟨c₁, h1⟩ := side_const hf hg hp hq hne hl
    obtain ⟨c₂, h2⟩ := side_const hf hg' hp hq hne hl
    have ht1 : twin a b c p ≠ p := by
      intro ht
      rcases lab_two hp hq hl with h3 | h3
      · exact hne h3.symm
      · exact hne (ht.symm.trans h3.symm)
    have ht2 : twin a b c q ≠ q := by
      intro ht
      rcases lab_two hq hp hl.symm with h3 | h3
      · exact hne h3
      · exact hne (h3.trans ht)
    have h3 := hdc _ (st_lt hp)
    have h4 := hdc _ (st_lt hq)
    rw [Sm_st_zero V hV1 hV2 hp ht1, add_zero] at h3
    rw [Sm_st_zero V hV1 hV2 hq ht2, add_zero] at h4
    have h5 := h1 _ (ofs_mem' (e := sgn a b c p) (t := 0) (.inl rfl))
    have h6 := h2 _ (ofs_mem' (e := sgn a b c p) (t := 0) (.inl rfl))
    rw [flp_ofs, per_st, per_st] at h5 h6
    have h7 : c₁ - c₂ = 0 := by
      have h8 : d (cor a b c (st a b c q)) = d (cor a b c (st a b c p)) + (c₁ - c₂) := by
        simp only [d]
        rw [h5, h6]
        abel
      rw [h3, h4] at h8
      exact (add_eq_left.mp h8.symm)
    have h9 : c₁ = c₂ := sub_eq_zero.mp h7
    simp only [d]
    rw [h1 u hu, h2 u hu, h9]
    abel
  have hstp : ∀ x y, Stp (sW (ew a b c)) x y → d x.2 = d y.2 := by
    intro x y hs
    obtain ⟨i, j, p, q, k, e, e', u, h1, h2, h3, hu, rfl, rfl⟩ := stp_iff.mp hs
    obtain ⟨rfl, h4⟩ := sW_get h1
    obtain ⟨rfl, h5⟩ := sW_get h2
    obtain ⟨hp, hl, rfl⟩ := (ew_get_iff _ _ _ _ _ _).mp h4
    obtain ⟨hq, hl', rfl⟩ := (ew_get_iff _ _ _ _ _ _).mp h5
    have h6 := hpair p q hp hq (fun he => h3 (by rw [he])) (hl.trans hl'.symm) u hu
    rw [spt_ew, spt_ew]
    exact h6.symm
  have hprel : ∀ x y, PRel (sW (ew a b c)) x y → d x.2 = d y.2 := by
    intro x y hxy
    induction hxy with
    | rel x y hs => exact hstp x y hs
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ h1 h2 => exact h1.trans h2
  refine cohRel_of_descent hφ hφ' (pmap_cont hf) (pmap_image hf) hg hg' fun x hx y hy he => ?_
  have hm : ∀ z ∈ closedBall (0 : ℂ) 1, ((0 : ℕ), z) ∈ Dsk (sW (ew a b c)) := fun z hz =>
    ⟨(ew_mem_dsk a b c).1, by simpa using hz⟩
  exact hprel (0, x) (0, y) ((hf.2.2 _ (hm x hx) _ (hm y hy)).mp he)

end GraphMinor.Surface
