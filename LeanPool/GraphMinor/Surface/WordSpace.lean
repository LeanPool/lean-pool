/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.VertexLink
public import LeanPool.GraphMinor.Surface.WordSide

/-!
# The space of a family of words

`WordSpace W` is the quotient of the discs of a family of words by the pasting relation. For a
finite paired family the
relation is closed, since off a finite set of corners a class has at most two points. So the
quotient is
compact and Hausdorff (`t2Space_wordSpace`), and it is presented by `W` (`presents_wordMap`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

universe u

theorem exists_spt {W : ℕ → List Letter} {a : ℕ × ℂ} (ha : a ∈ Dsk W) (hn : ‖a.2‖ = 1) :
    ∃ p k e, ∃ u ∈ Icc (0 : ℝ) 1, (W a.1)[p]? = some (k, e) ∧ a = spt W a.1 p u := by
  obtain ⟨i, z⟩ := a
  have hpos : 0 < (W i).length := List.length_pos_iff.mpr ha.1
  have h1 : z ∈ sphere (0 : ℂ) 1 := by simpa using hn
  rw [← per_image hpos] at h1
  obtain ⟨x, hx, rfl⟩ := h1
  have hex : ∃ p < (W i).length, x ∈ Icc (p : ℝ) (p + 1) := by
    set n := (W i).length with hndef
    refine ⟨min ⌊x⌋₊ (n - 1), by omega, ?_⟩
    have hle : ⌊x⌋₊ ≤ x := Nat.floor_le hx.1
    have hlt : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
    by_cases h1 : ⌊x⌋₊ ≤ n - 1
    · rw [min_eq_left h1]
      exact ⟨hle, hlt.le⟩
    · have h2 : ⌊x⌋₊ = n := by
        have : ⌊x⌋₊ ≤ n := Nat.floor_le_of_le hx.2
        omega
      have h3 : ((n - 1 : ℕ) : ℝ) = n - 1 := by
        rw [Nat.cast_sub hpos]
        simp
      rw [min_eq_right (by omega), h3]
      rw [h2] at hle
      constructor <;> linarith [hx.2]
  obtain ⟨p, hp, hxp⟩ := hex
  refine ⟨p, ((W i)[p]'hp).1, ((W i)[p]'hp).2, x - p, ⟨by linarith [hxp.1], by linarith [hxp.2]⟩,
    ?_, ?_⟩
  · exact List.getElem?_eq_getElem hp
  · simp [spt]

/-- The pasting relation on the discs. -/
def wordSetoid (W : ℕ → List Letter) : Setoid (Dsk W) :=
  ⟨fun a b => PRel W a.1 b.1, ⟨fun _ => .refl _, fun h => .symm _ _ h, fun h h'
    => .trans _ _ _ h h'⟩⟩

/-- The quotient of the discs of `W` by the pasting relation. -/
abbrev WordSpace (W : ℕ → List Letter) : Type := Quotient (wordSetoid W)

/-- The map of the discs to the quotient. -/
noncomputable def wordMap {W : ℕ → List Letter} (h0 : (Dsk W).Nonempty) (a : ℕ × ℂ) : WordSpace W :=
  open Classical in if h : a ∈ Dsk W then Quotient.mk _ ⟨a, h⟩ else Quotient.mk _ ⟨h0.some,
    h0.some_mem⟩

theorem wordMap_of_mem {W : ℕ → List Letter} (h0 : (Dsk W).Nonempty) {a : ℕ × ℂ} (h : a ∈ Dsk W) :
    wordMap h0 a = Quotient.mk _ ⟨a, h⟩ := by
  simp [wordMap, h]

theorem presents_wordMap {W : ℕ → List Letter} (h0 : (Dsk W).Nonempty) : Presents W (wordMap h0)
  := by
  refine ⟨?_, ?_, fun a ha b hb => ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have e : (Dsk W).domRestrict (wordMap h0) = Quotient.mk (wordSetoid W) := by
      funext a
      exact wordMap_of_mem h0 a.2
    rw [e]
    exact continuous_quotient_mk'
  · refine eq_univ_of_forall fun x => ?_
    obtain ⟨a, rfl⟩ := Quotient.exists_rep x
    exact ⟨a.1, a.2, wordMap_of_mem h0 a.2⟩
  · rw [wordMap_of_mem h0 ha, wordMap_of_mem h0 hb]
    exact ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

variable {W : ℕ → List Letter}

theorem compactSpace_dsk (hW : FinW W) : CompactSpace (Dsk W) :=
  isCompact_iff_compactSpace.mp (isCompact_Dsk hW)

theorem compactSpace_wordSpace (hW : FinW W) : CompactSpace (WordSpace W) :=
  have := compactSpace_dsk hW
  Quotient.compactSpace

theorem finite_sides (hW : FinW W) : {x : ℕ × ℕ | ∃ l, (W x.1)[x.2]? = some l}.Finite := by
  refine (hW.biUnion fun i _ => ((finite_singleton i).prod (finite_lt_nat (W i).length))).subset ?_
  rintro ⟨i, p⟩ ⟨l, h⟩
  have h1 : (W i)[p]? = some l := h
  have hlt : p < (W i).length := (List.getElem?_eq_some_iff.mp h1).1
  refine mem_biUnion (x := i) (fun he => ?_) ⟨rfl, hlt⟩
  simp [he] at hlt

/-- The corners of a family of words. -/
noncomputable def crn (W : ℕ → List Letter) : Set (ℕ × ℂ) :=
  (fun x : ℕ × ℕ => spt W x.1 x.2 0) '' {x : ℕ × ℕ | ∃ l, (W x.1)[x.2]? = some l} ∪
    (fun x : ℕ × ℕ => spt W x.1 x.2 1) '' {x : ℕ × ℕ | ∃ l, (W x.1)[x.2]? = some l}

theorem finite_crn (hW : FinW W) : (crn W).Finite :=
  ((finite_sides hW).image _).union ((finite_sides hW).image _)

/-- A point of the discs that is not a corner is related to itself and to the points one step away.
-/
theorem prel_of_not_crn (hP : IsPaired W) {a b : ℕ × ℂ} (ha : a ∈ Dsk W) (hna : a ∉ crn W)
  (hr : PRel W a b) :
    b = a ∨ Stp W a b := by
  by_cases hn : ‖a.2‖ < 1
  · exact .inl (PRel.eq_of_lt hr hn)
  · have hn1 : ‖a.2‖ = 1 := le_antisymm ha.2 (not_lt.mp hn)
    obtain ⟨p, k, e, u, hu, hs, ha'⟩ := exists_spt ha hn1
    have hu' : u ∈ Ioo (0 : ℝ) 1 := by
      refine ⟨lt_of_le_of_ne hu.1 fun h0 => hna (.inl ⟨(a.1, p), ⟨_, hs⟩, ?_⟩),
        lt_of_le_of_ne hu.2 fun h1 => hna
        (.inr ⟨(a.1, p), ⟨_, hs⟩, ?_⟩)⟩
      · rw [ha', ← h0]
        simp [spt]
      · rw [ha', h1]
        simp [spt]
    rw [ha'] at hr ⊢
    exact PRel.eq_or_stp hP hs hu' hr

/-- A pasting class is finite. -/
theorem finite_class (hW : FinW W) (hP : IsPaired W) {a : ℕ × ℂ} (ha : a ∈ Dsk W) : {b | PRel W a
  b}.Finite := by
  classical
  by_cases hc : {b | PRel W a b} ⊆ crn W
  · exact (finite_crn hW).subset hc
  obtain ⟨b, hb, hbc⟩ := not_subset.mp hc
  have hbD : b ∈ Dsk W := (prel_mem_iff hb).mp ha
  have hfin : {x | Stp W b x}.Finite := by
    by_cases hn : ‖b.2‖ < 1
    · refine (finite_singleton b).subset fun x hx => ?_
      exact PRel.eq_of_lt (.rel _ _ hx) hn
    · have hn1 : ‖b.2‖ = 1 := le_antisymm hbD.2 (not_lt.mp hn)
      obtain ⟨p, k, e, u, hu, hs, hb'⟩ := exists_spt hbD hn1
      have hu' : u ∈ Ioo (0 : ℝ) 1 := by
        refine ⟨lt_of_le_of_ne hu.1 fun h0 => hbc (.inl ⟨(b.1, p), ⟨_, hs⟩, ?_⟩),
          lt_of_le_of_ne hu.2 fun h1 => hbc
          (.inr ⟨(b.1, p), ⟨_, hs⟩, ?_⟩)⟩
        · rw [hb', ← h0]
          simp [spt]
        · rw [hb', h1]
          simp [spt]
      refine (((finite_sides hW).prod (finite_univ (α := Bool))).image
        fun x => spt W x.1.1 x.1.2 (flp e x.2 u)).subset fun x hx => ?_
      have hx' : Stp W (spt W b.1 p u) x := hb' ▸ hx
      obtain ⟨j, q, e', h1, -, rfl⟩ := stp_of_side hP hs hu' hx'
      exact ⟨((j, q), e'), ⟨⟨_, h1⟩, mem_univ _⟩, rfl⟩
  refine ((finite_singleton b).union hfin).subset fun x hx => ?_
  rcases prel_of_not_crn hP hbD hbc (.trans _ _ _ (.symm _ _ hb) hx) with h | h
  · exact .inl h
  · exact .inr h

/-- The pasting relation is closed. -/
theorem isClosed_prel (hW : FinW W) (hP : IsPaired W) :
    IsClosed {p : Dsk W × Dsk W | PRel W p.1.1 p.2.1} := by
  classical
  let Cn := crn W
  have hCn : Cn.Finite := finite_crn hW
  have hsym : ∀ x y, Stp W x y → Stp W y x := by
    rintro _ _ ⟨i, j, p, q, k, e, e', t, h1, h2, h3, ht, rfl, rfl⟩
    exact ⟨j, i, q, p, k, e', e, t, h2, h1, h3.symm, ht, rfl, rfl⟩
  have hkey : ∀ a ∈ Dsk W, ∀ b, a ∉ Cn → PRel W a b → b = a ∨ Stp W a b :=
    fun a ha b hna hr => prel_of_not_crn hP ha hna hr
  let R1 : Set (Dsk W × Dsk W) := {p | p.1 = p.2}
  let R2 : Set (Dsk W × Dsk W) := {p | Stp W p.1.1 p.2.1}
  let R3 : Set (Dsk W × Dsk W) := {p | p.1.1 ∈ Cn ∧ p.2.1 ∈ Cn ∧ PRel W p.1.1 p.2.1}
  have hR2 : IsClosed R2 := by
    have hc : Continuous fun p : Dsk W × Dsk W => (p.1.1, p.2.1) := by fun_prop
    exact (isCompact_stp hW).isClosed.preimage hc
  have hR3 : R3.Finite := by
    have hinj : InjOn (fun p : Dsk W × Dsk W => (p.1.1, p.2.1)) R3 := fun p _ q _ he => by
      obtain ⟨h1, h2⟩ := Prod.mk.inj he
      exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
    exact Set.Finite.of_finite_image ((hCn.prod hCn).subset (by
      rintro _ ⟨p, hp, rfl⟩
      exact ⟨hp.1, hp.2.1⟩)) hinj
  have e : {p : Dsk W × Dsk W | PRel W p.1.1 p.2.1} = R1 ∪ R2 ∪ R3 := by
    ext ⟨a, b⟩
    constructor
    · intro hr
      have hr' : PRel W a.1 b.1 := hr
      by_cases ha : a.1 ∈ Cn
      · by_cases hb : b.1 ∈ Cn
        · exact .inr ⟨ha, hb, hr'⟩
        · rcases hkey b.1 b.2 a.1 hb (.symm _ _ hr') with h | h
          · exact .inl (.inl (Subtype.ext h))
          · exact .inl (.inr (hsym _ _ h))
      · rcases hkey a.1 a.2 b.1 ha hr' with h | h
        · exact .inl (.inl (Subtype.ext h.symm))
        · exact .inl (.inr h)
    · rintro ((h | h) | h)
      · have h' : a = b := h
        subst h'
        exact .refl _
      · exact .rel _ _ h
      · exact h.2.2
  rw [e]
  exact (isClosed_eq continuous_fst continuous_snd |>.union hR2).union hR3.isClosed

theorem t2Space_wordSpace (hW : FinW W) (hP : IsPaired W) : T2Space (WordSpace W) :=
  have := compactSpace_dsk hW
  t2Space_quotient_of_isClosed (wordSetoid W) (isClosed_prel hW hP)

end GraphMinor.Surface
