/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.WordGerm

/-!
# A presented space is a surface

Let `W` be a finite family of words with each label on at most two sides. Then a Hausdorff space
presented by `W` is a
surface and its boundary is the image of the free sides (`surface_of_presents`).

A point inside a disc has a small ball around it. At another point `y`, take the rectangles of all
germs at `y`. They
form a fan of squares by the lemmas of `WordGerm.lean`, so their union is a closed disc, which is a
neighbourhood of `y`.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Germ

universe u

variable {W : ℕ → List Letter} {Y : Type u} [TopologicalSpace Y] {f : ℕ × ℂ → Y}

/-- The germs at a point of a presented space. -/
def germsAt (W : ℕ → List Letter) (f : ℕ × ℂ → Y) (y : Y) : Set Germ := {g | Valid W g ∧ f (g.pt W)
  = y}

theorem finite_germsAt (hW : FinW W) (hP : IsPaired W) (hf : Presents W f) (y : Y) :
  (germsAt W f y).Finite := by
  classical
  by_cases hne : (germsAt W f y).Nonempty
  · obtain ⟨g₀, hg₀⟩ := hne
    have hF := finite_class hW hP hg₀.1.pt_mem
    refine Set.Finite.of_finite_image (f := fun g : Germ => (g.pt W, g.τ))
      ((hF.prod (finite_univ (α := Bool))).subset ?_) ?_
    · rintro _ ⟨g, hg, rfl⟩
      refine ⟨?_, mem_univ _⟩
      exact (hf.2.2 _ hg₀.1.pt_mem _ hg.1.pt_mem).mp (hg₀.2.trans hg.2.symm)
    · intro g hg g' hg' he
      obtain ⟨h1, h2⟩ := Prod.mk.inj he
      exact eq_of_pt hg.1 hg'.1 h2 h1
  · rw [not_nonempty_iff_eq_empty.mp hne]
    exact finite_empty

theorem exists_small_of_finite {A : Set ℝ} (hA : A.Finite) (hpos : ∀ t ∈ A, 0 < t) : ∃ h, 0 < h
  ∧ ∀ t ∈ A, h < t := by
  obtain ⟨t₀, ht₀, hmin⟩ := Set.exists_min_image (insert 1 A) id (hA.insert 1) (insert_nonempty _ _)
  have h0 : 0 < t₀ := by
    rcases ht₀ with rfl | h
    · exact one_pos
    · exact hpos _ h
  exact ⟨t₀ / 2, by linarith, fun t ht => by
    have := hmin t (.inr ht)
    simp only [id] at this
    linarith⟩

theorem exists_scale {G : Set Germ} (hG : G.Finite) (hv : ∀ g ∈ G, Valid W g) :
    ∃ h, 0 < h ∧ h < 1 ∧ (∀ g ∈ G, Small h g) ∧ Sep h G := by
  classical
  let c1 : Germ → ℝ := fun g => if g.τ = true then 1 - g.u else g.u
  let c2 : Germ × Germ → ℝ := fun x => if x.1.i = x.2.i ∧ x.1.p = x.2.p
    ∧ x.1.u ≠ x.2.u then |x.1.u - x.2.u| / 2 else 1
  have hA : (insert 1 (c1 '' G ∪ c2 '' (G ×ˢ G))).Finite := ((hG.image _).union
    ((hG.prod hG).image _)).insert 1
  obtain ⟨h, h0, hb⟩ := exists_small_of_finite hA (by
    rintro t (rfl | ⟨g, hg, rfl⟩ | ⟨x, -, rfl⟩)
    · exact one_pos
    · have h1 := hv g hg
      simp only [c1]
      split_ifs with h2
      · linarith [h1.2.2.1 h2]
      · exact h1.2.2.2 (by simpa using h2)
    · simp only [c2]
      split_ifs with h2
      · have : 0 < |x.1.u - x.2.u| := abs_pos.mpr (sub_ne_zero.mpr h2.2.2)
        linarith
      · exact one_pos)
  refine ⟨h, h0, hb 1 (.inl rfl), fun g hg => ⟨fun ht => ?_, fun ht => ?_⟩, ?_⟩
  · have h1 := hb (c1 g) (.inr (.inl ⟨g, hg, rfl⟩))
    simp only [c1, ht, ite_true] at h1
    linarith
  · have h1 := hb (c1 g) (.inr (.inl ⟨g, hg, rfl⟩))
    simp only [c1, ht] at h1
    simp only [Bool.false_eq_true, ite_false] at h1
    linarith
  · intro g hg g' hg' hi hp hu
    have h1 := hb (c2 (g, g')) (.inr (.inr ⟨(g, g'), ⟨hg, hg'⟩, rfl⟩))
    simp only [c2, hi, hp, hu, ne_eq, not_false_eq_true, and_self, ite_true] at h1
    linarith

/-- The germ in the direction into the side at a point of a side. -/
theorem exists_germ_of_side {i p : ℕ} (hp : p < (W i).length) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    ∃ g, Valid W g ∧ g.i = i ∧ g.p = p ∧ g.u = u := by
  by_cases h : u < 1
  · exact ⟨⟨i, p, u, true⟩, ⟨hp, hu, fun _ => h, by simp⟩, rfl, rfl, rfl⟩
  · have h1 : u = 1 := le_antisymm hu.2 (not_lt.mp h)
    exact ⟨⟨i, p, u, false⟩, ⟨hp, hu, by simp, fun _ => by linarith⟩, rfl, rfl, rfl⟩

theorem presents_eq_of_stp (hf : Presents W f) {a b : ℕ × ℂ} (h : Stp W a b) : f a = f b :=
  (hf.2.2 _ h.mem_Dsk.1 _ h.mem_Dsk.2).mpr (.rel _ _ h)

/-- The rectangles of the germs at a point form a fan of squares. -/
theorem exists_fan (hW : FinW W) (hP : IsPaired W) (hf : Presents W f) (y : Y) :
    ∃ (h : ℝ) (tw pt : germsAt W f y → germsAt W f y), 0 < h ∧ h < 1 ∧
      IsSquareFan y (fun g => f ∘ rect W h g.1) tw pt ∧ (∀ g, pt g = g ↔ FreeSide W g.1.i g.1.p)
        := by
  classical
  obtain ⟨h, h0, h1, hS, hsep⟩ := exists_scale (finite_germsAt hW hP hf y) fun g hg => hg.1
  have hG : ∀ g ∈ germsAt W f y, Valid W g := fun g hg => hg.1
  have htw : ∀ g : germsAt W f y, ∃ g' : germsAt W f y, g'.1.pt W = g.1.pt W ∧ g'.1.τ = !g.1.τ := by
    intro g
    obtain ⟨g', h2, h3, h4⟩ := exists_twin g.2.1
    exact ⟨⟨g', h2, by rw [h3]; exact g.2.2⟩, h3, h4⟩
  choose tw htw1 htw2 using htw
  have hpt : ∀ g : germsAt W f y, ∃ g' : germsAt W f y, (g' = g ∧ FreeSide W g.1.i g.1.p)
    ∨ Partner W g.1 g'.1 := by
    intro g
    by_cases hfree : FreeSide W g.1.i g.1.p
    · exact ⟨g, .inl ⟨rfl, hfree⟩⟩
    · obtain ⟨g', h2, h3⟩ := exists_partner g.2.1 hfree
      refine ⟨⟨g', h2, ?_⟩, .inr h3⟩
      obtain ⟨e, e', h4, h5, -⟩ := h3.stp g.2.1.2.1
      rw [← g.2.2]
      have h6 : spt W g'.i g'.p (flp e e' g.1.u) = g'.pt W := by rw [← h5]; rfl
      rw [h6] at h4
      exact (presents_eq_of_stp hf h4).symm
  choose pt hpt using hpt
  have hfree : ∀ g, pt g = g ↔ FreeSide W g.1.i g.1.p := by
    intro g
    rcases hpt g with h2 | h2
    · exact ⟨fun _ => h2.2, fun _ => h2.1⟩
    · exact ⟨fun h3 => absurd (congrArg Subtype.val h3) h2.ne, fun h3 => absurd h3 h2.not_free⟩
  have hmem : ∀ (g : germsAt W f y) {z : ℂ}, z ∈ unitSq → rect W h g.1 z ∈ Dsk W :=
    fun g _ hz => rect_mem h0 h1 g.2.1 hz
  have hsame : ∀ (g g' : germsAt W f y) {z z' : ℂ}, z ∈ unitSq → z' ∈ unitSq → rect W h g.1 z
    = rect W h g'.1 z' →
      (g = g' ∧ z = z') ∨ (z = 0 ∧ z' = 0) ∨ (z = z' ∧ z.re = 0 ∧ g' = tw g) ∨ (z = z' ∧ z.im = 0
        ∧ g' = pt g) := by
    intro g g' z z' hz hz' he
    obtain ⟨h2, h3⟩ := rect_same h0 h1 hG hS hsep g.2 g'.2 hz hz' he
    rcases h3 with h3 | ⟨h3, h4, h5⟩
    · exact .inl ⟨Subtype.ext h3, h2⟩
    · refine .inr (.inr (.inl ⟨h2, h3, Subtype.ext ?_⟩))
      exact eq_of_pt g'.2.1 (tw g).2.1 (by rw [h4, htw2]) (by rw [h5, htw1])
  have hstp : ∀ (g g' : germsAt W f y) {z z' : ℂ}, z ∈ unitSq → z' ∈ unitSq → z.im = 0 → z'.im = 0
    → 0 < z.re →
      Stp W (rect W h g.1 z) (rect W h g'.1 z') → z = z' ∧ g' = pt g := by
    intro g g' z z' hz hz' hi hi' hre he
    rcases hpt g with h2 | h2
    · exfalso
      have hm := th_mem h0 g.2.1 (hS g g.2) hz
      rw [rect_im g.1 hi] at he
      obtain ⟨k, e, hs⟩ := g.2.1.exists_label
      obtain ⟨j, q, e', h3, h4, -⟩ := stp_of_side hP hs (hm.2 hre) he
      exact h4 (h2.2 _ _ k e e' hs h3)
    · obtain ⟨h3, h4⟩ := rect_stp h0 hP hG hS hsep g.2 g'.2 (pt g).2 h2 hz hz' hi hi' hre he
      exact ⟨h3, Subtype.ext h4⟩
  refine ⟨h, tw, pt, h0, h1, ⟨fun g => ?_, fun g => ?_, fun g he => ?_, fun g s hs => ?_,
    fun g s hs => ?_, ?_, ?_⟩, hfree⟩
  · exact hf.1.comp (continuous_rect W h g.1).continuousOn fun z hz => hmem g hz
  · simp only [Function.comp, rect_zero]
    exact g.2.2
  · have h2 := htw2 g
    rw [he] at h2
    cases hτ : g.1.τ <;> simp [hτ] at h2
  · simp only [Function.comp, rect_left]
    have h2 := htw1 g
    have h3 : (tw g).1.i = g.1.i := congrArg Prod.fst h2
    rw [h2, h3]
  · rcases hpt g with h2 | h2
    · simp only [h2.1]
    · simp only [Function.comp]
      have hm := th_mem h0 g.2.1 (hS g g.2) (IsSquareFan.mem_low hs)
      obtain ⟨e, e', h4, h5, h6⟩ := h2.stp hm.1
      have h7 : flp e e' (th h g.1 s) = th h (pt g).1 s := by
        rw [th, flp_add, th, h5, h6]
      rw [h7] at h4
      rw [rect_im g.1 (by simp), rect_im (pt g).1 (by simp)]
      exact (presents_eq_of_stp hf h4).symm
  · intro g g' z z' hz hz' he
    have hr : PRel W (rect W h g.1 z) (rect W h g'.1 z') := (hf.2.2 _ (hmem g hz) _
      (hmem g' hz')).mp he
    by_cases hρ : z.im = 0
    · by_cases hρ' : z'.im = 0
      · by_cases hre : 0 < z.re
        · have hm := th_mem h0 g.2.1 (hS g g.2) hz
          obtain ⟨k, e, hs⟩ := g.2.1.exists_label
          have hr' := hr
          rw [rect_im g.1 hρ] at hr'
          rcases PRel.eq_or_stp hP hs (hm.2 hre) hr' with h2 | h2
          · rw [← rect_im g.1 hρ] at h2
            exact hsame g g' hz hz' h2.symm
          · rw [← rect_im g.1 hρ] at h2
            obtain ⟨h3, h4⟩ := hstp g g' hz hz' hρ hρ' hre h2
            exact .inr (.inr (.inr ⟨h3, hρ, h4⟩))
        · have hre0 : z.re = 0 := le_antisymm (not_lt.mp hre) hz.1.1
          by_cases hre' : 0 < z'.re
          · have hm := th_mem h0 g'.2.1 (hS g' g'.2) hz'
            obtain ⟨k, e, hs⟩ := g'.2.1.exists_label
            have hr' : PRel W (rect W h g'.1 z') (rect W h g.1 z) := .symm _ _ hr
            rw [rect_im g'.1 hρ'] at hr'
            rcases PRel.eq_or_stp hP hs (hm.2 hre') hr' with h2 | h2
            · rw [← rect_im g'.1 hρ'] at h2
              exact hsame g g' hz hz' h2
            · rw [← rect_im g'.1 hρ'] at h2
              obtain ⟨h3, -⟩ := hstp g' g hz' hz hρ' hρ hre' h2
              rw [h3, hre0] at hre'
              exact absurd hre' (lt_irrefl _)
          · have hre0' : z'.re = 0 := le_antisymm (not_lt.mp hre') hz'.1.1
            exact .inr (.inl ⟨Complex.ext hre0 hρ, Complex.ext hre0' hρ'⟩)
      · have hlt : ‖(rect W h g'.1 z').2‖ < 1 := by
          rw [norm_rect h0 h1 hz']
          have := mul_pos h0 (lt_of_le_of_ne hz'.2.1 (Ne.symm hρ'))
          linarith
        exact hsame g g' hz hz' (PRel.eq_of_lt (.symm _ _ hr) hlt)
    · have hlt : ‖(rect W h g.1 z).2‖ < 1 := by
        rw [norm_rect h0 h1 hz]
        have := mul_pos h0 (lt_of_le_of_ne hz.2.1 (Ne.symm hρ))
        linarith
      exact hsame g g' hz hz' (PRel.eq_of_lt hr hlt).symm
  · rintro A ⟨g₀, hg₀⟩ hcl
    let B : Set (ℕ × ℂ) := {x | ∃ g ∈ A, g.1.pt W = x}
    have htw' : ∀ (g g' : germsAt W f y), g'.1.pt W = g.1.pt W → g' = g ∨ g' = tw g := by
      intro g g' he
      by_cases hτ : g'.1.τ = g.1.τ
      · exact .inl (Subtype.ext (eq_of_pt g'.2.1 g.2.1 hτ he))
      · refine .inr (Subtype.ext (eq_of_pt g'.2.1 (tw g).2.1 ?_ (by rw [he, htw1])))
        rw [htw2]
        cases h7 : g.1.τ <;> cases h8 : g'.1.τ <;> simp_all
    have hstep : ∀ x x', Stp W x x' → x ∈ B → x' ∈ B := by
      intro x x' hs hx
      obtain ⟨g, hg, hgx⟩ := hx
      obtain ⟨i, j, p, q, k, e, e', u, h2, h3, h4, hu, rfl, rfl⟩ := stp_iff.mp hs
      obtain ⟨g₃, hv₃, hi₃, hp₃, hu₃⟩ := exists_germ_of_side (lt_length h2) hu
      subst hi₃ hp₃ hu₃
      have hg₃ : g₃ ∈ germsAt W f y := ⟨hv₃, by
        change f (spt W _ _ _) = y
        rw [← hgx]
        exact g.2.2⟩
      have hA₃ : (⟨g₃, hg₃⟩ : germsAt W f y) ∈ A := by
        rcases htw' g ⟨g₃, hg₃⟩ hgx.symm with h5 | h5
        · rw [h5]
          exact hg
        · rw [h5]
          exact (hcl g hg).1
      refine ⟨pt ⟨g₃, hg₃⟩, (hcl _ hA₃).2, ?_⟩
      rcases hpt ⟨g₃, hg₃⟩ with h5 | h5
      · exact absurd (h5.2 _ _ k e e' h2 h3) h4
      · obtain ⟨k₂, e₂, e₂', h6, h7, h8, h9, -⟩ := h5
        rw [h2] at h6
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h6)
        have h10 := (hP.third h2 h7 h3 h8).resolve_left h4.symm
        obtain ⟨h11, h12⟩ := Prod.mk.inj h10
        rw [h12, h11] at h3
        rw [h3] at h7
        obtain ⟨-, h13⟩ := Prod.mk.inj (Option.some.inj h7)
        change spt W _ _ _ = _
        rw [h9, ← h11, ← h12, ← h13]
    have hkey : ∀ x x', PRel W x x' → (x ∈ B ↔ x' ∈ B) := by
      intro x x' hxy
      induction hxy with
      | rel x y hs => exact ⟨hstep x y hs, hstep y x hs.symm⟩
      | refl _ => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ h1 h2 => exact h1.trans h2
    refine eq_univ_of_forall fun g => ?_
    have h2 : PRel W (g₀.1.pt W) (g.1.pt W) := (hf.2.2 _ g₀.2.1.pt_mem _ g.2.1.pt_mem).mp
      (g₀.2.2.trans g.2.2.symm)
    obtain ⟨g', hg', he⟩ := (hkey _ _ h2).mp ⟨g₀, hg₀, rfl⟩
    rcases htw' g' g he.symm with h3 | h3
    · rw [h3]
      exact hg'
    · rw [h3]
      exact (hcl g' hg').1

theorem per_add (n : ℕ) (x y : ℝ) : per n (x + y) = per n x * cis' (2 * Real.pi * y / n) := by
  simp only [per, cis']
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Near a point of the circle the unit disc is covered by the rectangles of the two germs at the
point. -/
theorem eventually_rect {g g' : Germ} (hv : Valid W g) (_hv' : Valid W g') (hτ : g.τ = true)
  (hτ' : g'.τ = false)
    (he : g'.pt W = g.pt W) {h : ℝ} (h0 : 0 < h) :
    ∀ᶠ w in 𝓝 (g.pt W).2, ‖w‖ ≤ 1 → ∃ c ∈ unitSq, rect W h g c = (g.i, w) ∨ rect W h g' c =
      (g.i, w) := by
  set z₀ := (g.pt W).2 with hz₀
  have hn1 : ‖z₀‖ = 1 := norm_per _ _
  have hz0 : z₀ ≠ 0 := fun h => by simp [h] at hn1
  set n := (W g.i).length with hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hv.len_pos
  have hc : ContinuousAt (fun w : ℂ => Complex.arg (w / z₀)) z₀ := by
    have h1 : ContinuousAt (fun w : ℂ => w / z₀) z₀ := by fun_prop
    have h2 : ContinuousAt Complex.arg (z₀ / z₀) := by
      rw [div_self hz0]
      exact Complex.continuousAt_arg (by simp)
    exact ContinuousAt.comp (f := fun w : ℂ => w / z₀) h2 h1
  have hε : 0 < 2 * Real.pi * h / n := by positivity
  have h1 : ∀ᶠ w in 𝓝 z₀, |Complex.arg (w / z₀)| < 2 * Real.pi * h / n := by
    have h2 : Filter.Tendsto (fun w : ℂ => Complex.arg (w / z₀)) (𝓝 z₀) (𝓝 0) := by
      have h3 := hc.tendsto
      simpa [div_self hz0] using h3
    have h3 := h2.eventually (Metric.ball_mem_nhds (0 : ℝ) hε)
    filter_upwards [h3] with w hw
    simpa using hw
  have h2 : ∀ᶠ w in 𝓝 z₀, 1 - h < ‖w‖ := by
    have h3 : Filter.Tendsto (fun w : ℂ => ‖w‖) (𝓝 z₀) (𝓝 ‖z₀‖) := continuous_norm.tendsto _
    rw [hn1] at h3
    exact h3.eventually (lt_mem_nhds (by linarith))
  filter_upwards [h1, h2] with w hw1 hw2 hle
  set A := Complex.arg (w / z₀) with hA
  set t := A * n / (2 * Real.pi) with ht
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hAt : 2 * Real.pi * t / n = A := by
    rw [ht]
    field_simp
  have htb : |t| < h := by
    rw [ht, abs_div, abs_mul, Nat.abs_cast, abs_of_pos hpi, div_lt_iff₀ hpi]
    have := (lt_div_iff₀ hnpos).mp hw1
    linarith
  have hw : w = ((‖w‖ : ℝ) : ℂ) * (z₀ * cis' A) := by
    have h3 := Complex.norm_mul_exp_arg_mul_I (w / z₀)
    rw [norm_div, hn1, div_one] at h3
    have h4 : w = z₀ * (w / z₀) := by field_simp
    conv_lhs => rw [h4, ← h3]
    simp only [cis']
    ring
  have him : (1 - ‖w‖) / h ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (by linarith) h0.le
    · rw [div_le_one h0]
      linarith
  have hsim : h * ((1 - ‖w‖) / h) = 1 - ‖w‖ := by field_simp
  have hgp : per n (g.p + g.u) = z₀ := rfl
  have hgp' : per (W g'.i).length (g'.p + g'.u) = z₀ := by
    have h3 : (g'.pt W).2 = (g.pt W).2 := congrArg Prod.snd he
    exact h3
  have hi' : g'.i = g.i := congrArg Prod.fst he
  have hgp'' : per n (g'.p + g'.u) = z₀ := by
    rw [hn, ← hi']
    exact hgp'
  have hre : ∀ v s : ℝ, ((v : ℂ) + (s : ℂ) * Complex.I).re = v := fun v s => by simp
  have him' : ∀ v s : ℝ, ((v : ℂ) + (s : ℂ) * Complex.I).im = s := fun v s => by simp
  have hmk : ∀ v ∈ Icc (0 : ℝ) 1, ((v : ℂ) + (((1 - ‖w‖) / h : ℝ) : ℂ) * Complex.I) ∈ unitSq
    := fun v hv => by
    constructor
    · change ((v : ℂ) + (((1 - ‖w‖) / h : ℝ) : ℂ) * Complex.I).re ∈ Icc (0 : ℝ) 1
      rw [hre]
      exact hv
    · change ((v : ℂ) + (((1 - ‖w‖) / h : ℝ) : ℂ) * Complex.I).im ∈ Icc (0 : ℝ) 1
      rw [him']
      exact him
  rcases le_total 0 t with hsign | hsign
  · rw [abs_of_nonneg hsign] at htb
    refine ⟨_, hmk (t / h) ⟨by positivity, by rw [div_le_one h0]; exact htb.le⟩, .inl ?_⟩
    simp only [rect, th, hτ, sg_true]
    rw [hre, him', hsim]
    have h6 : h * (t / h) = t := by field_simp
    rw [h6, one_mul, ← add_assoc, per_add, hgp, hAt]
    rw [Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    rw [show (1 - (1 - ‖w‖) : ℝ) = ‖w‖ by ring]
    exact hw.symm
  · rw [abs_of_nonpos hsign] at htb
    refine ⟨_, hmk (-t / h) ⟨div_nonneg (by linarith) h0.le, by rw [div_le_one h0]; exact htb.le⟩,
      .inr ?_⟩
    simp only [rect, th, hτ', sg_false]
    rw [hre, him', hsim]
    have h6 : -1 * (h * (-t / h)) = t := by field_simp
    rw [h6, ← add_assoc, hi', per_add, ← hn, hgp'', hAt]
    rw [Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    rw [show (1 - (1 - ‖w‖) : ℝ) = ‖w‖ by ring]
    exact hw.symm

theorem exists_germ_of_circle {a : ℕ × ℂ} (ha : a ∈ Dsk W) (hn : ‖a.2‖ = 1) : ∃ g, Valid W g ∧ g.τ
  = true ∧ g.pt W = a := by
  obtain ⟨p, k, e, u, hu, hs, he⟩ := exists_spt ha hn
  obtain ⟨g, hv, h1, h2, h3⟩ := exists_germ_of_side (lt_length hs) hu
  have hp : g.pt W = a := by
    rw [he, pt, h1, h2, h3]
  cases hτ : g.τ
  · obtain ⟨g', h1, h2, h3⟩ := exists_twin hv
    exact ⟨g', h1, by rw [h3, hτ]; rfl, h2.trans hp⟩
  · exact ⟨g, hv, hτ, hp⟩

/-- The rectangles at a point of a presented space give a neighbourhood of the point. -/
theorem rects_mem_nhds [T2Space Y] (hW : FinW W) (hf : Presents W f) {y : Y} (hne :
  (germsAt W f y).Nonempty)
    {h : ℝ} (h0 : 0 < h) : (⋃ g : germsAt W f y, (f ∘ rect W h g.1) '' unitSq) ∈ 𝓝 y := by
  obtain ⟨g₀, hg₀⟩ := hne
  have hnorm : ∀ a ∈ Dsk W, f a = y → ‖a.2‖ = 1 := by
    intro a ha hy
    by_contra hc
    have hlt : ‖a.2‖ < 1 := lt_of_le_of_ne ha.2 hc
    have h1 : PRel W a (g₀.pt W) := (hf.2.2 _ ha _ hg₀.1.pt_mem).mp (hy.trans hg₀.2.symm)
    have h2 := PRel.eq_of_lt h1 hlt
    rw [← h2] at hlt
    exact absurd hg₀.1.norm_pt hlt.ne
  let K : Set (ℕ × ℂ) := ⋃ g : germsAt W f y, rect W h g.1 '' unitSq
  let S : Set (ℕ × ℂ) := K ∪ (Dsk W)ᶜ
  have hS : ∀ a ∈ Dsk W, f a = y → S ∈ 𝓝 a := by
    intro a ha hy
    obtain ⟨g, hv, hτ, rfl⟩ := exists_germ_of_circle ha (hnorm a ha hy)
    obtain ⟨g', hv', h2, h3⟩ := exists_twin hv
    have hτ' : g'.τ = false := by rw [h3, hτ]; rfl
    have hgG : g ∈ germsAt W f y := ⟨hv, hy⟩
    have hgG' : g' ∈ germsAt W f y := ⟨hv', by rw [h2]; exact hy⟩
    have hev := eventually_rect hv hv' hτ hτ' h2 h0
    rw [show g.pt W = ((g.pt W).1, (g.pt W).2) from rfl, mem_nhds_prod_iff]
    refine ⟨{(g.pt W).1}, by simp, _, hev, ?_⟩
    rintro ⟨i, w⟩ ⟨hi, hw⟩
    have hi' : i = g.i := hi
    subst hi'
    by_cases hle : ‖w‖ ≤ 1
    · obtain ⟨c, hc, h4 | h4⟩ := hw hle
      · exact .inl (mem_iUnion.mpr ⟨⟨g, hgG⟩, c, hc, h4⟩)
      · exact .inl (mem_iUnion.mpr ⟨⟨g', hgG'⟩, c, hc, h4⟩)
    · exact .inr fun h5 => hle h5.2
  have hC : IsClosed (f '' (Dsk W \ interior S)) :=
    (((isCompact_Dsk hW).diff isOpen_interior).image_of_continuousOn (hf.1.mono
      sdiff_subset)).isClosed
  have hy : (f '' (Dsk W \ interior S))ᶜ ∈ 𝓝 y := by
    refine hC.isOpen_compl.mem_nhds ?_
    rintro ⟨a, ha, hay⟩
    exact ha.2 (mem_interior_iff_mem_nhds.mpr (hS a ha.1 hay))
  refine Filter.mem_of_superset hy fun w hw => ?_
  have h1 : w ∈ f '' Dsk W := by
    rw [hf.2.1]
    exact mem_univ w
  obtain ⟨a, ha, rfl⟩ := h1
  have h2 : a ∈ interior S := by
    by_contra hc
    exact hw ⟨a, ⟨ha, hc⟩, rfl⟩
  rcases interior_subset h2 with h3 | h3
  · obtain ⟨g, c, hc, rfl⟩ := mem_iUnion.mp h3
    exact mem_iUnion.mpr ⟨g, c, hc, rfl⟩
  · exact absurd ha h3

/-- A point inside a disc gives an interior point. -/
theorem isInteriorPoint_of_lt [T2Space Y] (hW : FinW W) (hf : Presents W f) {a : ℕ × ℂ}
  (ha : a ∈ Dsk W)
    (hn : ‖a.2‖ < 1) : IsInteriorPoint (f a) := by
  obtain ⟨i, z⟩ := a
  have hn' : ‖z‖ < 1 := hn
  have hr : 0 < (1 - ‖z‖) / 2 := by linarith
  set r := (1 - ‖z‖) / 2 with hrdef
  let Ψ : ℂ → Y := fun w => f (i, w)
  have hin : ∀ w ∈ closedBall z r, (i, w) ∈ Dsk W ∧ ‖w‖ < 1 := by
    intro w hw
    have h1 : ‖w‖ ≤ ‖z‖ + r := by
      have h2 := mem_closedBall_iff_norm.mp hw
      have h3 := norm_sub_norm_le w z
      linarith
    have h2 : ‖w‖ < 1 := by linarith
    exact ⟨⟨ha.1, h2.le⟩, h2⟩
  have hc : ContinuousOn Ψ (closedBall z r) :=
    hf.1.comp (by fun_prop) fun w hw => (hin w hw).1
  have hi : InjOn Ψ (closedBall z r) := fun w hw w' hw' he => by
    have h1 : PRel W (i, w) (i, w') := (hf.2.2 _ (hin w hw).1 _ (hin w' hw').1).mp he
    have h2 := PRel.eq_of_lt h1 (hin w hw).2
    exact (congrArg Prod.snd h2).symm
  let V' : Set (ℕ × ℂ) := {i} ×ˢ ball z r
  have hV' : IsOpen V' := (isOpen_discrete _).prod isOpen_ball
  have hcl : IsClosed (f '' (Dsk W \ V')) :=
    (((isCompact_Dsk hW).diff hV').image_of_continuousOn (hf.1.mono sdiff_subset)).isClosed
  have he : Ψ '' ball z r = (f '' (Dsk W \ V'))ᶜ := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩ ⟨b, hb, hbe⟩
      have hw' := ball_subset_closedBall hw
      have h1 : PRel W (i, w) b := (hf.2.2 _ (hin w hw').1 _ hb.1).mp hbe.symm
      have h2 := PRel.eq_of_lt h1 (hin w hw').2
      rw [h2] at hb
      exact hb.2 ⟨rfl, hw⟩
    · intro hx
      have h1 : x ∈ f '' Dsk W := by
        rw [hf.2.1]
        exact mem_univ x
      obtain ⟨⟨j, w⟩, hb, rfl⟩ := h1
      have h2 : (j, w) ∈ V' := by
        by_contra hc
        exact hx ⟨_, ⟨hb, hc⟩, rfl⟩
      obtain ⟨h3, h4⟩ := h2
      have h3' : j = i := h3
      subst h3'
      exact ⟨w, h4, rfl⟩
  exact isInteriorPoint_of_injOn (isCompact_closedBall _ _) hc hi ball_subset_closedBall isOpen_ball
    (he ▸ hcl.isOpen_compl) (mem_ball_self hr)

/-- The points of the free sides of a family of words. -/
def freePts (W : ℕ → List Letter) : Set (ℕ × ℂ) :=
  {x | ∃ i p u, p < (W i).length ∧ FreeSide W i p ∧ u ∈ Icc (0 : ℝ) 1 ∧ x = spt W i p u}

/-- A Hausdorff space presented by a finite family of words with each label on at most two sides is
a surface, and its
boundary is the image of the free sides. -/
theorem surface_of_presents [T2Space Y] (hW : FinW W) (hP : IsPaired W) (hf : Presents W f) :
    IsSurface Y ∧ bd Y = f '' freePts W := by
  classical
  have hsurj : ∀ y : Y, ∃ a ∈ Dsk W, f a = y := fun y => by
    have h1 : y ∈ f '' Dsk W := by
      rw [hf.2.1]
      exact mem_univ y
    exact h1
  have hfan : ∀ y : Y, (germsAt W f y).Nonempty → ∃ E : Set Y, IsClosedDisc E ∧ E ∈ 𝓝 y ∧
      ((∀ g ∈ germsAt W f y, ¬ FreeSide W g.i g.p) → y ∉ discBd E) ∧
      ((∃ g ∈ germsAt W f y, FreeSide W g.i g.p) → y ∈ discBd E) := by
    intro y hne
    obtain ⟨h, tw, pt, h0, -, hS, hfree⟩ := exists_fan hW hP hf y
    have : Finite (germsAt W f y) := (finite_germsAt hW hP hf y).to_subtype
    have : Nonempty (germsAt W f y) := hne.to_subtype
    obtain ⟨E, h1, h2, h3, h4⟩ := hS.exists_disc
    refine ⟨E, h1, ?_, fun hn => h3 fun g he => hn g.1 g.2 ((hfree g).mp he), ?_⟩
    · rw [h2]
      exact rects_mem_nhds hW hf hne h0
    · rintro ⟨g, hg, hg'⟩
      exact h4 ⟨⟨g, hg⟩, (hfree ⟨g, hg⟩).mpr hg'⟩
  have hgerm : ∀ a ∈ Dsk W, ‖a.2‖ = 1 → (germsAt W f (f a)).Nonempty := by
    intro a ha hn
    obtain ⟨g, hv, -, rfl⟩ := exists_germ_of_circle ha hn
    exact ⟨g, hv, rfl⟩
  have hman : ∀ y : Y, IsManifoldPoint y := by
    intro y
    obtain ⟨a, ha, rfl⟩ := hsurj y
    by_cases hn : ‖a.2‖ < 1
    · exact (isInteriorPoint_of_lt hW hf ha hn).isManifoldPoint
    · obtain ⟨E, h1, h2, -⟩ := hfan _ (hgerm a ha (le_antisymm ha.2 (not_lt.mp hn)))
      exact isManifoldPoint_of_disc h1 h2
  have hc : CompactSpace Y := ⟨by
    rw [← hf.2.1]
    exact (isCompact_Dsk hW).image_of_continuousOn hf.1⟩
  refine ⟨⟨hc, inferInstance, hman⟩, ?_⟩
  ext y
  constructor
  · intro hy
    obtain ⟨a, ha, rfl⟩ := hsurj y
    have hn : ‖a.2‖ = 1 := by
      by_contra hc
      exact hy (isInteriorPoint_of_lt hW hf ha (lt_of_le_of_ne ha.2 hc))
    obtain ⟨E, h1, h2, h3, -⟩ := hfan _ (hgerm a ha hn)
    by_contra hcon
    have hno : ∀ g ∈ germsAt W f (f a), ¬ FreeSide W g.i g.p := by
      intro g hg hfr
      exact hcon ⟨g.pt W, ⟨g.i, g.p, g.u, hg.1.1, hfr, hg.1.2.1, rfl⟩, hg.2⟩
    have h4 : f a ∈ discInt E := ⟨mem_of_mem_nhds h2, h3 hno⟩
    exact hy (isInteriorPoint_of_mem_discInt hman h1 h4)
  · rintro ⟨x, ⟨i, p, u, hp, hfr, hu, rfl⟩, rfl⟩
    obtain ⟨g, hv, rfl, rfl, rfl⟩ := exists_germ_of_side hp hu
    have hg : g ∈ germsAt W f (f (spt W g.i g.p g.u)) := ⟨hv, rfl⟩
    obtain ⟨E, h1, h2, -, h3⟩ := hfan _ ⟨g, hg⟩
    exact mem_bd_of_disc h2 (h3 ⟨g, hg, hfr⟩)

end GraphMinor.Surface
