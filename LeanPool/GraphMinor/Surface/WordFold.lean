/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.WordMoves

/-!
# Folding and renaming

Two adjacent sides `x x⁻¹` of a word can be folded together (`exists_isPolyMap_fold`): the map of
discs opens the
polygon onto the upper half disc and then squares. Renaming labels does not change the relation
between points.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Filter Function

universe u

theorem sv_sv (ε : Bool) (t : ℝ) : sv ε (sv ε t) = t := by
  cases ε <;> simp [sv]

theorem sv_not (ε : Bool) (t : ℝ) : sv (!ε) t = 1 - sv ε t := by
  cases ε <;> simp [sv]

theorem exists_sqrt_half {z : ℂ} (hz : ‖z‖ ≤ 1) : ∃ w ∈ halfD 1, w ^ 2 = z := by
  have hw : (z ^ ((2 : ℕ) : ℂ)⁻¹) ^ 2 = z := Complex.cpow_nat_inv_pow z two_ne_zero
  generalize z ^ ((2 : ℕ) : ℂ)⁻¹ = w at hw
  have hn : ‖w‖ ≤ 1 := by
    have : ‖w‖ ^ 2 ≤ 1 := by rw [← norm_pow, hw]; exact hz
    nlinarith [norm_nonneg w]
  rcases le_total 0 w.im with h | h
  · exact ⟨w, ⟨hn, by simpa using h⟩, hw⟩
  · exact ⟨-w, ⟨by simpa using hn, by simpa using h⟩, by rw [neg_sq, hw]⟩

theorem up_sq {n _p : ℕ} (_hn : 0 < n) (x : ℝ) : (cis' (Real.pi * x / n)) ^ 2 = per n x := by
  simp only [cis', per]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

section fold

variable {W : ℕ → List Letter} {i : ℕ} {u : List Letter} {y : ℕ} {e : Bool}

/-- Folding two adjacent sides. -/
theorem exists_isPolyMap_fold (hu : u ≠ []) (hy : FreshIn (update W i u) y) :
    ∃ θ, IsPolyMap (update W i u) (update W i ((y, e) :: (y, !e) :: u)) θ := by
  classical
  set n := u.length with hn
  have hn0 : 0 < n := List.length_pos_iff.mpr hu
  obtain ⟨Φ, Φ', m, hv⟩ := exists_up_map (a := 2) (l := n) two_pos hn0
  rw [Nat.add_comm 2 n] at hv
  set W0 := update W i u with hW0
  set W1 := update W i ((y, e) :: (y, !e) :: u) with hW1
  have e1 : W1 i = (y, e) :: (y, !e) :: u := by rw [hW1, update_self]
  have e2 : W0 i = u := by rw [hW0, update_self]
  have e3 : ∀ s, s ≠ i → W1 s = W0 s := fun s h => by rw [hW1, hW0, update_of_ne h, update_of_ne h]
  have hyu : ∀ l' ∈ u, l'.1 ≠ y := fun l' h => hy i l' (by rw [e2]; exact h)
  have hlen1 : (W1 i).length = n + 2 := by rw [e1]; simp [hn]
  have hlen0 : (W0 i).length = n := by rw [e2]
  have hball : ∀ {V : ℕ → List Letter} {s : ℕ} {z : ℂ}, (s, z) ∈ Dsk V → z ∈ closedBall (0 : ℂ) 1 :=
    fun h => mem_closedBall_zero_iff.mpr h.2
  have hHalf : ∀ {z}, z ∈ closedBall (0 : ℂ) 1 → Φ z ∈ halfD 1 := fun hz => m.1 hz
  have hinj : ∀ {z z'}, z ∈ closedBall (0 : ℂ) 1 → z' ∈ closedBall (0 : ℂ) 1 → Φ z = Φ z' → z = z'
    :=
    fun hz hz' he => by rw [← m.2.2.1 hz, ← m.2.2.1 hz', he]
  have hb : ∀ {t : ℝ}, ‖sdPt (n + 2) 0 e t‖ ≤ 1 ∧ ‖sdPt (n + 2) 1 (!e) t‖ ≤ 1 :=
    ⟨(norm_per _ _).le, (norm_per _ _).le⟩
  have hs0 : ∀ t ∈ Icc (0 : ℝ) 1, Φ (sdPt (n + 2) 0 e t) = ((-1 + sv e t : ℝ) : ℂ) := by
    intro t ht
    have hs := sv_mem e ht
    have h1 : sdPt (n + 2) 0 e t = per (n + 2) (sv e t) := by simp [sdPt, sv]
    have h3 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [h1, hv _ ⟨hs.1, by push_cast; linarith [hs.2]⟩, upLoop_le (by push_cast; linarith [hs.2])]
    push_cast
    ring
  have hs1 : ∀ t ∈ Icc (0 : ℝ) 1, Φ (sdPt (n + 2) 1 (!e) t) = ((1 - sv e t : ℝ) : ℂ) := by
    intro t ht
    have hs := sv_mem e ht
    have h1 : sdPt (n + 2) 1 (!e) t = per (n + 2) (1 + (1 - sv e t)) := by
      rw [← sv_not]
      simp [sdPt, sv]
    have h3 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [h1, hv _ ⟨by linarith [hs.2], by push_cast; linarith [hs.1]⟩,
      upLoop_le (by push_cast; linarith [hs.1])]
    push_cast
    ring
  have hs2 : ∀ p ε t, p < n → t ∈ Icc (0 : ℝ) 1 →
      (Φ (sdPt (n + 2) (p + 2) ε t)) ^ 2 = sdPt n p ε t := by
    intro p ε t hp ht
    have hs := sv_mem ε ht
    have h1 : sdPt (n + 2) (p + 2) ε t = per (n + 2) (((p + 2 : ℕ) : ℝ) + sv ε t) := rfl
    have h2 : ((p + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hp
    push_cast at h2
    have h3 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    rw [h1, hv _ ⟨by push_cast; linarith [hs.1], by push_cast; linarith [hs.2]⟩,
      upLoop_ge two_pos (by push_cast; linarith [hs.1])]
    have h4 := up_sq (n := n) (_p := 0) hn0 ((p : ℝ) + sv ε t)
    have h5 : (((p + 2 : ℕ) : ℝ) + sv ε t - (2 : ℕ)) = (p : ℝ) + sv ε t := by
      push_cast
      ring
    rw [h5, h4]
    rfl
  let θ : ℕ × ℂ → ℕ × ℂ := fun a => if a.1 = i then (i, (Φ a.2) ^ 2) else a
  have θi : ∀ z, θ (i, z) = (i, (Φ z) ^ 2) := fun z => by simp [θ]
  have θo : ∀ s z, s ≠ i → θ (s, z) = (s, z) := fun s z h1 => by simp [θ, h1]
  have hmix : ∀ z z', z ∈ closedBall (0 : ℂ) 1 → z' ∈ closedBall (0 : ℂ) 1 → Φ z = - Φ z' →
      0 ≤ (Φ z').re → PRel W1 (i, z) (i, z') := by
    intro z z' hz hz' he hr
    have h1 := hHalf hz
    have h2 := hHalf hz'
    have h3 : (Φ z').im = 0 := by
      have h4 := h1.2
      rw [he] at h4
      simp only [one_mul, Complex.neg_im] at h4
      have h5 := h2.2
      simp only [one_mul] at h5
      linarith
    have h6 : (Φ z').re ≤ 1 := (Complex.re_le_norm _).trans h2.1
    have hsm : (1 - (Φ z').re) ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    let t := sv e (1 - (Φ z').re)
    have ht : t ∈ Icc (0 : ℝ) 1 := sv_mem e hsm
    have hst : sv e t = 1 - (Φ z').re := sv_sv e _
    have h7 : Φ z' = (((Φ z').re : ℝ) : ℂ) := Complex.ext rfl (by simp [h3])
    have ha : z = sdPt (n + 2) 0 e t := by
      refine hinj hz (mem_closedBall_zero_iff.mpr (norm_per _ _).le) ?_
      rw [hs0 t ht, he, hst, h7]
      apply Complex.ext <;> simp
      ring
    have hb' : z' = sdPt (n + 2) 1 (!e) t := by
      refine hinj hz' (mem_closedBall_zero_iff.mpr (norm_per _ _).le) ?_
      rw [hs1 t ht, hst, h7]
      apply Complex.ext <;> simp
    refine .rel _ _ ⟨i, i, 0, 1, y, e, !e, t, by rw [e1]; rfl, by rw [e1]; rfl,
      by simp, ht, ?_, ?_⟩
    · rw [hlen1, ha]
    · rw [hlen1, hb']
  refine ⟨θ, IsPolyMap.of_sides (Y := {y}) ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · rw [continuousOn_prod_of_discrete_left]
    intro s
    by_cases h1 : s = i
    · subst h1
      have hs : (fun z => θ (s, z)) = fun z => (s, (Φ z) ^ 2) := funext θi
      rw [hs]
      exact continuousOn_const.prodMk ((m.2.2.2.2.1.mono fun z hz => hball hz).pow 2)
    · have hs : (fun z => θ (s, z)) = fun z => (s, z) := funext fun z => θo s z h1
      rw [hs]
      exact (Continuous.prodMk continuous_const continuous_id).continuousOn
  · rintro ⟨s, z⟩ hz
    by_cases h1 : s = i
    · subst h1
      rw [θi]
      refine ⟨by rw [e2]; exact hu, ?_⟩
      have := (hHalf (hball hz)).1
      simp only [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) this
    · rw [θo s z h1]
      refine ⟨?_, hz.2⟩
      have := hz.1
      rwa [e3 s h1] at this
  · rintro ⟨s, z⟩ hz
    by_cases h1 : s = i
    · subst h1
      obtain ⟨w, hw, rfl⟩ := exists_sqrt_half hz.2
      refine ⟨(s, Φ' w), ⟨by rw [e1]; simp, mem_closedBall_zero_iff.mp (m.2.1 hw)⟩, ?_⟩
      rw [θi, m.2.2.2.1 hw]
    · refine ⟨(s, z), ⟨?_, hz.2⟩, θo s z h1⟩
      have := hz.1
      rwa [← e3 s h1] at this
  · rintro ⟨s, z⟩ hz ⟨s', z'⟩ hz' he
    by_cases h1 : s = i <;> by_cases h3 : s' = i
    · subst h1 h3
      rw [θi, θi] at he
      have h4 := (Prod.mk.inj he).2
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp h4 with h5 | h5
      · rw [hinj (hball hz) (hball hz') h5]
        exact .refl _
      · rcases le_total 0 (Φ z').re with h6 | h6
        · exact hmix _ _ (hball hz) (hball hz') h5 h6
        · refine (hmix _ _ (hball hz') (hball hz) (by rw [h5, neg_neg]) ?_).symm
          rw [h5, Complex.neg_re]
          linarith
    · subst h1
      rw [θi, θo s' z' h3] at he
      exact absurd (Prod.mk.inj he).1.symm h3
    · subst h3
      rw [θo s z h1, θi] at he
      exact absurd (Prod.mk.inj he).1 h1
    · rw [θo s z h1, θo s' z' h3] at he
      rw [he]
      exact .refl _
  · intro s p c ε h hc
    by_cases h1 : s = i
    · subst h1
      rw [e1] at h
      match p, h with
      | 0, h =>
        have : (y, e) = (c, ε) := by simpa using h
        exact absurd (Prod.mk.inj this).1.symm hc
      | 1, h =>
        have : (y, !e) = (c, ε) := by simpa using h
        exact absurd (Prod.mk.inj this).1.symm hc
      | p + 2, h =>
        rw [List.getElem?_cons_succ, List.getElem?_cons_succ] at h
        have hp : p < n := (List.getElem?_eq_some_iff.mp h).1
        refine ⟨s, p, ε, by rw [e2]; exact h, fun t ht => ?_⟩
        rw [θi, hlen1, hlen0, hs2 p ε t hp ht]
    · refine ⟨s, p, ε, by rwa [← e3 s h1], fun t _ => ?_⟩
      rw [θo _ _ h1, e3 s h1]
  · intro s p c ε h
    by_cases h1 : s = i
    · subst h1
      rw [e2] at h
      have hp : p < n := (List.getElem?_eq_some_iff.mp h).1
      refine ⟨s, p + 2, ε, by rw [e1, List.getElem?_cons_succ, List.getElem?_cons_succ]; exact h,
        fun t ht => ?_⟩
      rw [θi, hlen1, hlen0, hs2 p ε t hp ht]
    · refine ⟨s, p, ε, by rwa [e3 s h1], fun t _ => ?_⟩
      rw [θo _ _ h1, e3 s h1]
  · have hside : ∀ s q ε, (W1 s)[q]? = some (y, ε) → ∀ t ∈ Icc (0 : ℝ) 1,
        θ (s, sdPt (W1 s).length q ε t) = (i, ((1 - sv e t : ℝ) : ℂ) ^ 2) := by
      intro s q ε h t ht
      by_cases h1 : s = i
      · subst h1
        rw [e1] at h
        match q, h with
        | 0, h =>
          have : ε = e := by simpa using h.symm
          subst this
          rw [θi, hlen1, hs0 t ht]
          congr 1
          push_cast
          ring
        | 1, h =>
          have : ε = !e := by simpa using h.symm
          subst this
          rw [θi, hlen1, hs1 t ht]
        | q + 2, h =>
          rw [List.getElem?_cons_succ, List.getElem?_cons_succ] at h
          exact absurd rfl (hyu _ (List.mem_of_getElem? h))
      · rw [e3 s h1] at h
        have h3 := hy s _ (List.mem_of_getElem? h)
        exact absurd rfl h3
    intro s s' q q' c ε ε' t hc h1 h2 ht
    obtain rfl : c = y := hc
    rw [hside s q ε h1 t ht, hside s' q' ε' h2 t ht]

end fold

/-- Renaming labels. -/
def relab (r : ℕ → ℕ) (W : ℕ → List Letter) : ℕ → List Letter :=
  fun i => (W i).map fun l => (r l.1, l.2)

theorem relab_getElem {r : ℕ → ℕ} {W : ℕ → List Letter} {i p : ℕ} {c : ℕ} {ε : Bool}
    (h : (W i)[p]? = some (c, ε)) : (relab r W i)[p]? = some (r c, ε) := by
  simp [relab, h]

theorem relab_getElem' {r : ℕ → ℕ} {W : ℕ → List Letter} {i p : ℕ} {c : ℕ} {ε : Bool}
    (h : (relab r W i)[p]? = some (c, ε)) : ∃ c', r c' = c ∧ (W i)[p]? = some (c', ε) := by
  simp only [relab, List.getElem?_map, Option.map_eq_some_iff, Prod.mk.injEq, Prod.exists] at h
  obtain ⟨a, b, h1, h2, h3⟩ := h
  exact ⟨a, h2, by rw [h1, h3]⟩

theorem relab_length {r : ℕ → ℕ} {W : ℕ → List Letter} {i : ℕ} : (relab r W i).length =
  (W i).length := by
  simp [relab]

theorem Dsk_relab {r : ℕ → ℕ} {W : ℕ → List Letter} : Dsk (relab r W) = Dsk W := by
  ext a
  simp [Dsk, relab]

/-- Renaming labels, without merging two labels that occur in the family, keeps a presentation. -/
theorem presents_relab {T : Type u} [TopologicalSpace T] {r : ℕ → ℕ} {W : ℕ → List Letter}
    (hr : ∀ i j, ∀ l ∈ W i, ∀ l' ∈ W j, r l.1 = r l'.1 → l.1 = l'.1) (f : ℕ × ℂ → T) :
    Presents W f ↔ Presents (relab r W) f := by
  have key : ∀ a b, Stp W a b ↔ Stp (relab r W) a b := by
    intro a b
    constructor
    · rintro ⟨i, j, p, q, k, ε, ε', t, h1, h2, h3, ht, rfl, rfl⟩
      exact ⟨i, j, p, q, r k, ε, ε', t, relab_getElem h1, relab_getElem h2, h3, ht,
        by rw [relab_length], by rw [relab_length]⟩
    · rintro ⟨i, j, p, q, k, ε, ε', t, h1, h2, h3, ht, rfl, rfl⟩
      obtain ⟨c, rfl, h4⟩ := relab_getElem' h1
      obtain ⟨c', he, h5⟩ := relab_getElem' h2
      have := hr i j _ (List.mem_of_getElem? h4) _ (List.mem_of_getElem? h5) he.symm
      obtain rfl : c = c' := this
      exact ⟨i, j, p, q, c, ε, ε', t, h4, h5, h3, ht, by rw [relab_length], by rw [relab_length]⟩
  have hS : Stp W = Stp (relab r W) := by
    ext a b
    exact key a b
  unfold Presents PRel
  rw [Dsk_relab, hS]

/-- Renaming labels, without merging two labels that occur in the family. -/
theorem peq_relab {r : ℕ → ℕ} {W : ℕ → List Letter}
    (hr : ∀ i j, ∀ l ∈ W i, ∀ l' ∈ W j, r l.1 = r l'.1 → l.1 = l'.1) : PEq.{u} W (relab r W) :=
  fun _T _ _ => exists_congr (presents_relab hr)

end GraphMinor.Surface
