/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.CuffOrder
public import LeanPool.GraphMinor.GM12.Section2Corners

/-!
# Order around a circle that is cut into lines

An `O`-arc is cut into connected pieces `F i`, where `F i` joins the point `nd i` to the next point
and has no other point `nd j`. If a set `I` of
indices is an interval of `0, 1, ...` then, for four points in order around the arc, if the first
and third have index in `I`, so does the second or
the fourth (`mem_of_inOrderOn`). This gives (P7) in XVII (13.1).

The proof uses any parametrization of the arc that shows the four points in order. The first and
third points cut it into two closed arcs. A piece
that avoids the two points lies in one of the two arcs. So all the points outside the interval
between the first and third are on the same arc.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface GM19

variable {T : Type*} [TopologicalSpace T] [T2Space T] {Θ : Set T} {k : ℕ} {nd : Fin k
  → T} {F : Fin k → Set T} {nx : Fin k → Fin k}
  {I : Set (Fin k)}

private theorem mem_of_inOrderOn_aux (hinj : Function.Injective nd) (hnx : ∀ i, (nx i).1 =
  (i.1 + 1) % k)
    (hF : ∀ i, IsPreconnected (F i) ∧ F i ⊆ Θ ∧ nd i ∈ F i ∧ nd (nx i) ∈ F i ∧ ∀ j, nd j ∈ F i → j
      = i ∨ j = nx i)
    (hI : ∀ a b c, a < b → b < c → a ∈ I → c ∈ I → b ∈ I) {a b c d : Fin k} (hac : a < c)
    (hba : b ≠ a) (hbc : b ≠ c) (hda : d ≠ a) (hdc : d ≠ c)
    (h : InOrderOn Θ (nd a) (nd b) (nd c) (nd d)) (ha : a ∈ I) (hc : c ∈ I) : b ∈ I ∨ d ∈ I := by
  obtain ⟨f, t₁, t₂, t₃, t₄, h12, h23, h34, h41, e1, e2, e3, e4⟩ := h
  by_contra hn
  push Not at hn
  obtain ⟨hbI, hdI⟩ := hn
  let Out : Fin k → Prop := fun j => j < a ∨ c < j
  have hb : Out b := by
    by_contra hb
    simp only [Out, not_or, not_lt] at hb
    exact hbI (hI a b c (lt_of_le_of_ne hb.1 hba.symm) (lt_of_le_of_ne hb.2 hbc) ha hc)
  have hd : Out d := by
    by_contra hb
    simp only [Out, not_or, not_lt] at hb
    exact hdI (hI a d c (lt_of_le_of_ne hb.1 hda.symm) (lt_of_le_of_ne hb.2 hdc) ha hc)
  let A₁ : Set T := cuffPoint f '' Icc t₁ t₃
  let A₂ : Set T := cuffPoint f '' Icc t₃ (t₁ + 2 * Real.pi)
  have hA₁ : IsClosed A₁ := (isCompact_Icc.image (cuffPoint_continuous f)).isClosed
  have hA₂ : IsClosed A₂ := (isCompact_Icc.image (cuffPoint_continuous f)).isClosed
  have hcov : Θ ⊆ A₁ ∪ A₂ := fun x hx => by
    obtain ⟨t, ht, rfl⟩ := exists_cuffPoint_mem_Ico f t₁ hx
    rcases le_total t t₃ with h | h
    · exact Or.inl ⟨t, ⟨ht.1, h⟩, rfl⟩
    · exact Or.inr ⟨t, ⟨h, ht.2.le⟩, rfl⟩
  have hint : ∀ x, x ∈ A₁ → x ∈ A₂ → x = nd a ∨ x = nd c := by
    rintro _ ⟨u, hu, rfl⟩ ⟨w, hw, he⟩
    obtain ⟨m, hm⟩ := (cuffPoint_eq_iff f).mp he
    have hpi := Real.pi_pos
    have h1 : (m : ℝ) * (2 * Real.pi) ≤ 2 * Real.pi := by linarith [hu.1, hw.2]
    have h2 : -(2 * Real.pi) ≤ (m : ℝ) * (2 * Real.pi) := by linarith [hu.2, hw.1, hu.1, hw.2]
    have h3 : (m : ℝ) ≤ 1 := by nlinarith
    have h4 : (-1 : ℝ) ≤ m := by nlinarith
    have h5 : m ≤ 1 := by exact_mod_cast h3
    have h6 : -1 ≤ m := by exact_mod_cast h4
    have hcases : m = -1 ∨ m = 0 ∨ m = 1 := by omega
    rcases hcases with rfl | rfl | rfl
    · exfalso
      push_cast at hm
      linarith [hu.2, hw.1]
    · right
      push_cast at hm
      have : u = t₃ := by linarith [hu.2, hw.1]
      rw [← e3, this]
    · left
      push_cast at hm
      have : u = t₁ := by linarith [hu.1, hw.2]
      rw [← e1, this]
  have hb₁ : nd b ∈ A₁ := ⟨t₂, ⟨h12, h23⟩, e2⟩
  have hd₂ : nd d ∈ A₂ := ⟨t₄, ⟨h34, h41⟩, e4⟩
  have hin : ∀ j, Out j → nd j ∉ A₁ ∨ nd j ∉ A₂ := fun j hj => by
    by_contra hn
    push Not at hn
    rcases hint _ hn.1 hn.2 with he | he
    · have := hinj he
      subst this
      rcases hj with h | h
      · exact lt_irrefl _ h
      · exact lt_irrefl _ (hac.trans h)
    · have := hinj he
      subst this
      rcases hj with h | h
      · exact lt_irrefl _ (hac.trans h)
      · exact lt_irrefl _ h
  have hstep : ∀ j, Out j → Out (nx j) → (nd j ∈ A₁ ↔ nd (nx j) ∈ A₁) := fun j hj hj' => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hF j
    let Q : Bool → Set T := fun x => if x then A₁ else A₂
    have hQ : ∀ x, IsClosed (Q x) := fun x => by
      cases x
      · exact hA₂
      · exact hA₁
    have hcover : F j ⊆ ⋃ x, Q x := fun y hy => by
      rcases hcov (h2 hy) with h | h
      · exact mem_iUnion.2 ⟨true, h⟩
      · exact mem_iUnion.2 ⟨false, h⟩
    have hmiss : ∀ i : Fin k, Out j → Out (nx j) → (i = a ∨ i = c) → nd i ∉ F j := fun i _ _ hi hm
      => by
      rcases h5 i hm with rfl | rfl
      · rcases hi with rfl | rfl
        · rcases hj with h | h
          · exact lt_irrefl _ h
          · exact lt_irrefl _ (hac.trans h)
        · rcases hj with h | h
          · exact lt_irrefl _ (hac.trans h)
          · exact lt_irrefl _ h
      · rcases hi with rfl | rfl
        · rcases hj' with h | h
          · exact lt_irrefl _ h
          · exact lt_irrefl _ (hac.trans h)
        · rcases hj' with h | h
          · exact lt_irrefl _ (hac.trans h)
          · exact lt_irrefl _ h
    have hdisj : ∀ x y : Bool, x ≠ y → Disjoint (F j) (Q x ∩ Q y) := fun x y hxy => by
      refine Set.disjoint_left.mpr fun z hz hzz => ?_
      have hz' : z ∈ A₁ ∧ z ∈ A₂ := by
        cases x <;> cases y
        · exact absurd rfl hxy
        · exact ⟨hzz.2, hzz.1⟩
        · exact hzz
        · exact absurd rfl hxy
      rcases hint z hz'.1 hz'.2 with rfl | rfl
      · exact hmiss a hj hj' (Or.inl rfl) hz
      · exact hmiss c hj hj' (Or.inr rfl) hz
    constructor
    · intro hm
      exact GM12.preconnected_subset_closed_piece h1 Q hQ hcover hdisj (i := true) ⟨_, h3, hm⟩ h4
    · intro hm
      exact GM12.preconnected_subset_closed_piece h1 Q hQ hcover hdisj (i := true) ⟨_, h4, hm⟩ h3
  have hk : 0 < k := Nat.zero_lt_of_lt a.2
  have hsucc : ∀ n (h : n + 1 < k), nx ⟨n, by omega⟩ = ⟨n + 1, h⟩ := fun n h => Fin.ext
    (by rw [hnx]; exact Nat.mod_eq_of_lt h)
  have hup : ∀ x y : ℕ, ∀ (hxy : x ≤ y) (hy : y < k), (c.1 < x ∨ y < a.1) →
      (nd ⟨x, by omega⟩ ∈ A₁ ↔ nd ⟨y, hy⟩ ∈ A₁) := fun x y hxy => by
    induction y, hxy using Nat.le_induction with
    | base => exact fun _ _ => Iff.rfl
    | succ y hxy ih =>
      intro hy hc'
      refine (ih (by omega) (by omega)).trans ?_
      have := hstep ⟨y, by omega⟩ (by
        rcases hc' with h | h
        · exact Or.inr (Fin.lt_def.mpr (by simp only; omega))
        · exact Or.inl (Fin.lt_def.mpr (by simp only; omega))) (by
        rw [hsucc y hy]
        rcases hc' with h | h
        · exact Or.inr (Fin.lt_def.mpr (by simp only; omega))
        · exact Or.inl (Fin.lt_def.mpr (by simp only; omega)))
      rwa [hsucc y hy] at this
  have hall : ∀ x y : Fin k, Out x → Out y → x ≤ y → (nd x ∈ A₁ ↔ nd y ∈ A₁) := fun x y hx hy hxy
    => by
    rcases hx with hx | hx
    · rcases hy with hy | hy
      · exact hup x.1 y.1 hxy y.2 (Or.inr hy)
      · have hlast : k - 1 < k := by omega
        have h0 := hup 0 x.1 (Nat.zero_le _) x.2 (Or.inr hx)
        have h1 := hup y.1 (k - 1) (by omega) hlast (Or.inl hy)
        have h3 : nx ⟨k - 1, hlast⟩ = ⟨0, hk⟩ := Fin.ext (by
          rw [hnx]
          simp only
          rw [show k - 1 + 1 = k by omega, Nat.mod_self])
        have hlastOut : Out ⟨k - 1, hlast⟩ := by
          right
          change c.1 < k - 1
          have hyk := y.2
          have hcy : c.1 < y.1 := hy
          omega
        have hfirstOut : Out (nx ⟨k - 1, hlast⟩) := by
          rw [h3]
          left
          change 0 < a.1
          have hxa : x.1 < a.1 := hx
          omega
        have h2 := hstep ⟨k - 1, hlast⟩ hlastOut hfirstOut
        rw [h3] at h2
        exact h0.symm.trans (h2.symm.trans h1.symm)
    · rcases hy with hy | hy
      · exact absurd (lt_of_le_of_lt hxy (hy.trans (hac.trans hx))) (lt_irrefl _)
      · exact hup x.1 y.1 hxy y.2 (Or.inl hx)
  have hbd : nd b ∈ A₁ ↔ nd d ∈ A₁ := by
    rcases le_total b d with h | h
    · exact hall b d hb hd h
    · exact (hall d b hd hb h).symm
  rcases hin d hd with h | h
  · exact h (hbd.mp hb₁)
  · exact h hd₂

/-- **Order around a cut circle.** If the first and third of four points in order have index in the
interval `I`, then so does the second or the fourth. -/
theorem mem_of_inOrderOn (hinj : Function.Injective nd) (hnx : ∀ i, (nx i).1 = (i.1 + 1) % k)
    (hF : ∀ i, IsPreconnected (F i) ∧ F i ⊆ Θ ∧ nd i ∈ F i ∧ nd (nx i) ∈ F i ∧ ∀ j, nd j ∈ F i → j
      = i ∨ j = nx i)
    (hI : ∀ a b c, a < b → b < c → a ∈ I → c ∈ I → b ∈ I) {a b c d : Fin k}
    (h : InOrderOn Θ (nd a) (nd b) (nd c) (nd d)) (ha : a ∈ I) (hc : c ∈ I) : b ∈ I ∨ d ∈ I := by
  by_cases hba : b = a
  · exact Or.inl (hba ▸ ha)
  by_cases hbc : b = c
  · exact Or.inl (hbc ▸ hc)
  by_cases hda : d = a
  · exact Or.inr (hda ▸ ha)
  by_cases hdc : d = c
  · exact Or.inr (hdc ▸ hc)
  rcases lt_trichotomy a c with hac | rfl | hac
  · exact mem_of_inOrderOn_aux hinj hnx hF hI hac hba hbc hda hdc h ha hc
  · exfalso
    obtain ⟨f, t₁, t₂, t₃, t₄, h12, h23, h34, h41, e1, e2, e3, e4⟩ := h
    obtain ⟨m, hm⟩ := (cuffPoint_eq_iff f).mp (e1.trans e3.symm)
    have hpi := Real.pi_pos
    have h3 : (m : ℝ) ≤ 0 := by
      by_contra hn
      push Not at hn
      nlinarith
    have h4 : (-1 : ℝ) ≤ m := by
      by_contra hn
      push Not at hn
      nlinarith
    have h5 : m ≤ 0 := by exact_mod_cast h3
    have h6 : -1 ≤ m := by exact_mod_cast h4
    have hcases : m = -1 ∨ m = 0 := by omega
    rcases hcases with rfl | rfl
    · push_cast at hm
      have : t₄ = t₃ := by linarith
      exact hdc (hinj (by rw [← e4, ← e3, this]))
    · push_cast at hm
      have : t₂ = t₁ := by linarith
      exact hba (hinj (by rw [← e2, ← e1, this]))
  · exact (mem_of_inOrderOn_aux hinj hnx hF hI hac hdc hda hbc hba (inOrderOn_cyclic2 h) hc ha).symm

end GraphMinor.GM17
