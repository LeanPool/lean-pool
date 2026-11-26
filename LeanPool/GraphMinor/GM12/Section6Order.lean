/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.Surface.DiscGrow
public import LeanPool.GraphMinor.GM11.Forest

/-!
# Graph Minors XII, Section 6: the two arcs at a chord

In the setting of (6.1) the vertices of `F` are `v₁, …, v_{2k}` in order, and `P_i` joins `v_i` to
`v_{2k+1-i}`. So the ends of `P_i` cut `F` into two lines, and for `j ≠ i` both ends of `P_j` lie on
the same one of them.
-/

public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface

local notation "𝕀" => unitInterval

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- Two parameters at distance less than a full turn have different images on the circle. -/
theorem exp_inj_of_lt {x y : ℝ} (hxy : x < y) (hlt : y < x + 2 * Real.pi) :
    Circle.exp x ≠ Circle.exp y := by
  have hmem : x ∈ Ico x (x + 2 * Real.pi) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  exact fun h => hxy.ne
    (Circle.exp_injOn_Ico (a := x) (b := x + 2 * Real.pi) (by simp)
      hmem ⟨hxy.le, hlt⟩ h)

/-- The arc of the circle from `x` to `y`, pushed into `F`, is a line, when `y - x < 2π`. -/
theorem isLine_arc {F : Set X} (f : Circle ≃ₜ F) {x y : ℝ} (hxy : x < y)
    (hlt : y ≤ x + 2 * Real.pi) (hne : (f (Circle.exp x)).1 ≠ (f (Circle.exp y)).1) :
    IsLineWithEnds ((fun t => (f (Circle.exp t)).1) '' Icc x y) (f (Circle.exp x)).1
      (f (Circle.exp y)).1 := by
  let g : ℝ → X := fun t => (f (Circle.exp t)).1
  have hg : Continuous g := by
    have := f.continuous
    fun_prop
  let c : 𝕀 → ℝ := fun s => x + s.1 * (y - x)
  have hc : Continuous c := by fun_prop
  have hd : 0 < y - x := by linarith
  have hcm : ∀ s, c s ∈ Icc x y := fun s => by
    have h0 := s.2.1
    have h1 := s.2.2
    constructor
    · have := mul_nonneg h0 hd.le
      simp only [c]
      linarith
    · have := mul_le_mul_of_nonneg_right h1 hd.le
      simp only [c]
      linarith
  have hinj : Function.Injective (g ∘ c) := by
    intro s s' hss
    by_contra hne'
    have hval : s.1 ≠ s'.1 := fun h => hne' (Subtype.ext h)
    have hfe : Circle.exp (c s) = Circle.exp (c s') := by
      have : f (Circle.exp (c s)) = f (Circle.exp (c s')) := Subtype.ext hss
      exact f.injective this
    wlog hlts : s.1 < s'.1 generalizing s s'
    · exact this hss.symm (Ne.symm hne') hval.symm hfe.symm
        (lt_of_le_of_ne (not_lt.mp hlts) hval.symm)
    have hcc : c s < c s' := by
      simp only [c]
      nlinarith
    have hub : c s' < c s + 2 * Real.pi ∨ (c s = x ∧ c s' = y) := by
      by_cases h0 : c s = x ∧ c s' = y
      · exact .inr h0
      · left
        rw [not_and_or] at h0
        have h1 := hcm s
        have h2 := hcm s'
        rcases h0 with h0 | h0
        · have : x < c s := lt_of_le_of_ne h1.1 (Ne.symm h0)
          linarith [h2.2]
        · have : c s' < y := lt_of_le_of_ne h2.2 h0
          linarith [h1.1]
    rcases hub with hub | ⟨h0, h1⟩
    · exact exp_inj_of_lt hcc hub hfe
    · apply hne
      rw [← h0, ← h1, hfe]
  have harc : IsArcMap (g ∘ c) := ⟨hg.comp hc, hinj⟩
  have hl := harc.isLineWithEnds
  have hr : range (g ∘ c) = g '' Icc x y := by
    ext z
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨c s, hcm s, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      have hs : (w - x) / (y - x) ∈ unitInterval :=
        ⟨div_nonneg (by linarith [hw.1]) hd.le, (div_le_one hd).mpr (by linarith [hw.2])⟩
      refine ⟨⟨_, hs⟩, ?_⟩
      have : c ⟨_, hs⟩ = w := by
        simp only [c]
        field_simp
        ring
      simp only [Function.comp, this]
  rw [hr] at hl
  have h0 : (g ∘ c) 0 = (f (Circle.exp x)).1 := by simp [g, c]
  have h1 : (g ∘ c) 1 = (f (Circle.exp y)).1 := by simp [g, c]
  rwa [h0, h1] at hl

/-- Every point of the circle has a parameter in a given window of one full turn. -/
theorem exists_param (u : ℝ) (z : Circle) :
    ∃ t ∈ Ico u (u + 2 * Real.pi), Circle.exp t = z :=
  GraphMinor.Surface.exists_circleExp_mem_Ico u z

/-- Two parameters `u < v` less than a turn apart cut `F` into two lines. -/
theorem exists_two_lines {F : Set X} (f : Circle ≃ₜ F) {u v : ℝ} (huv : u < v)
    (hvu : v < u + 2 * Real.pi) :
    ∃ M N : Set X, IsLineWithEnds M (f (Circle.exp u)).1 (f (Circle.exp v)).1 ∧
      IsLineWithEnds N (f (Circle.exp u)).1 (f (Circle.exp v)).1 ∧ M ∪ N = F ∧
      M ∩ N = {(f (Circle.exp u)).1, (f (Circle.exp v)).1} ∧
      (∀ w ∈ Icc u v, (f (Circle.exp w)).1 ∈ M) ∧
      (∀ w ∈ Icc v (u + 2 * Real.pi), (f (Circle.exp w)).1 ∈ N) := by
  let g : ℝ → X := fun t => (f (Circle.exp t)).1
  have hne : g u ≠ g v := fun h => exp_inj_of_lt huv hvu (f.injective (Subtype.ext h))
  have hp : Circle.exp (u + 2 * Real.pi) = Circle.exp u := by simp
  have hgp : g (u + 2 * Real.pi) = g u := by simp only [g, hp]
  have l1 := isLine_arc f huv (by linarith) hne
  have l2 := isLine_arc f hvu (by linarith [Real.pi_pos]) (by
    change g v ≠ g (u + 2 * Real.pi)
    rw [hgp]
    exact hne.symm)
  change IsLineWithEnds (g '' Icc v (u + 2 * Real.pi)) (g v) (g (u + 2 * Real.pi)) at l2
  rw [hgp] at l2
  refine ⟨g '' Icc u v, g '' Icc v (u + 2 * Real.pi), l1, GraphMinor.GM11.IsLineWithEnds.symm l2,
    ?_, ?_,
    fun w hw => ⟨w, hw, rfl⟩, fun w hw => ⟨w, hw, rfl⟩⟩
  · ext z
    constructor
    · rintro (⟨w, -, rfl⟩ | ⟨w, -, rfl⟩) <;> exact (f _).2
    · intro hz
      obtain ⟨w, hw, he⟩ := exists_param u (f.symm ⟨z, hz⟩)
      have hgw : g w = z := by simp [g, he]
      by_cases hwv : w ≤ v
      · exact .inl ⟨w, ⟨hw.1, hwv⟩, hgw⟩
      · exact .inr ⟨w, ⟨(not_le.mp hwv).le, hw.2.le⟩, hgw⟩
  · ext z
    constructor
    · rintro ⟨⟨w, hw, rfl⟩, ⟨w', hw', he⟩⟩
      have hee : Circle.exp w' = Circle.exp w := f.injective (Subtype.ext he)
      by_cases hw1 : w = u
      · exact .inl (by rw [hw1])
      by_cases hw2 : w = v
      · exact .inr (by rw [hw2]; rfl)
      exfalso
      have h1 : u < w := lt_of_le_of_ne hw.1 (Ne.symm hw1)
      have h2 : w < v := lt_of_le_of_ne hw.2 hw2
      have h3 : w < w' := by linarith [hw'.1]
      have h4 : w' < w + 2 * Real.pi := by linarith [hw'.2]
      exact exp_inj_of_lt h3 h4 hee.symm
    · rintro (rfl | rfl)
      · exact ⟨⟨u, ⟨le_rfl, huv.le⟩, rfl⟩, ⟨u + 2 * Real.pi, ⟨by linarith, le_rfl⟩, hgp⟩⟩
      · exact ⟨⟨v, ⟨huv.le, le_rfl⟩, rfl⟩, ⟨v, ⟨le_rfl, by linarith⟩, rfl⟩⟩

/-- The order on `F` of (6.1). The ends of `P_i` cut `F` into two lines. Both ends of each later
path lie on the first line, and both ends of each earlier path lie on the second. -/
theorem exists_chord_arcs {F : Set X} {k : ℕ} {a b : Fin k → X}
    (hord : IsListedInOrderOn F (List.ofFn a ++ (List.ofFn b).reverse)) (i : Fin k) :
    ∃ M N : Set X, IsLineWithEnds M (a i) (b i) ∧ IsLineWithEnds N (a i) (b i) ∧ M ∪ N = F ∧
      M ∩ N = {a i, b i} ∧ (∀ j, i < j → a j ∈ M ∧ b j ∈ M) ∧
      (∀ j, j < i → a j ∈ N ∧ b j ∈ N) := by
  obtain ⟨f, t, hmono, hlt, hl⟩ := hord
  set l := List.ofFn a ++ (List.ofFn b).reverse with hldef
  have hlen : l.length = 2 * k := by simp [hldef]; omega
  have hA : ∀ j : Fin k, (f (Circle.exp (t j))).1 = a j := by
    intro j
    have hj : j.1 < l.length := by have := j.2; omega
    rw [hl j.1 hj]
    simp only [hldef]
    rw [List.getElem_append_left (by simp)]
    simp
  have hB : ∀ j : Fin k, (f (Circle.exp (t (2 * k - 1 - j.1)))).1 = b j := by
    intro j
    have hj' := j.2
    have hj : 2 * k - 1 - j.1 < l.length := by omega
    rw [hl _ hj]
    simp only [hldef]
    rw [List.getElem_append_right (by simp; omega)]
    simp only [List.length_ofFn, List.getElem_reverse, List.getElem_ofFn]
    congr 1
    apply Fin.ext
    simp only
    omega
  have hi := i.2
  have hlast : t (2 * k - 1 - i.1) < t 0 + 2 * Real.pi := hlt _ (by omega)
  have ht0 : t 0 ≤ t i.1 := hmono.monotone (Nat.zero_le _)
  have huv : t i.1 < t (2 * k - 1 - i.1) := hmono (by omega)
  obtain ⟨M, N, hM, hN, hu, hc, hin, hout⟩ := exists_two_lines f huv (by linarith)
  rw [hA i, hB i] at hM hN hc
  refine ⟨M, N, hM, hN, hu, hc, ?_, ?_⟩
  · intro j hj
    have hij : i.1 < j.1 := hj
    have hj' := j.2
    constructor
    · rw [← hA j]
      exact hin _ ⟨(hmono hij).le, (hmono (by omega)).le⟩
    · rw [← hB j]
      exact hin _ ⟨(hmono (by omega)).le, (hmono (by omega)).le⟩
  · intro j hj
    have hij : j.1 < i.1 := hj
    have hj' := j.2
    have hper : ∀ w : ℝ, (f (Circle.exp (w + 2 * Real.pi))).1 = (f (Circle.exp w)).1 := by
      intro w
      simp
    constructor
    · rw [← hA j, ← hper]
      refine hout _ ⟨?_, ?_⟩
      · have : t 0 ≤ t j.1 := hmono.monotone (Nat.zero_le _)
        linarith
      · have : t j.1 < t i.1 := hmono hij
        linarith
    · rw [← hB j]
      have h2 : 2 * k - 1 - j.1 < l.length := by omega
      refine hout _ ⟨(hmono (by omega)).le, ?_⟩
      have := hlt _ h2
      linarith

end GraphMinor.GM12
