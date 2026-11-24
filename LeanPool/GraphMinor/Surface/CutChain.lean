/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CutGraph

/-!
# Arcs in a graph are chains of edges

An arc or an `O`-arc inside the union of the edges of a graph is a chain of edges (`exists_chain`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

universe u

local notation "𝕀" => unitInterval

variable {X : Type u} [TopologicalSpace X] [T2Space X] {V : Set X} {E : Set (Set X)}

/-- A path that is injective, or a loop, in the union of the edges of a graph runs through a chain
of edges. -/
theorem exists_chain (hg : IsGraph V E) (A : Set X → 𝕀 → X)
    (hA : ∀ e ∈ E, IsArcMap (A e) ∧ range (A e) = e ∧ e ∩ V = {A e 0, A e 1}) {ι : ℝ → X}
      (hιc : Continuous ι)
    (hinj : InjOn ι (Ico 0 1)) (hinj' : InjOn ι (Ioc 0 1)) (hG : ι '' Icc 0 1 ⊆ gr V E)
      (h0 : ι 0 ∈ V) (h1 : ι 1 ∈ V)
    (hne : ι 0 ≠ ι 1 ∨ ∃ x ∈ Ioo (0 : ℝ) 1, ι x ∈ V) :
    ∃ (m : ℕ) (t : ℕ → ℝ) (s : ℕ → Set X) (ε : ℕ → Bool), 0 < m ∧ t 0 = 0 ∧ t m = 1 ∧
      (∀ p < m, t p < t (p + 1)) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, ι x ∈ V → ∃ p ≤ m, x = t p) ∧
      (∀ p < m, s p ∈ E ∧ ι '' Icc (t p) (t (p + 1)) = s p ∧ ι (t p) = extI (A (s p))
        (if ε p then 0 else 1) ∧
        ι (t (p + 1)) = extI (A (s p)) (if ε p then 1 else 0)) ∧
      ∀ p < m, ∀ q < m, p ≠ q → s p ≠ s q := by
  classical
  have hcl : ∀ f ∈ E, IsClosed f := fun f hf => by
    obtain ⟨u, v, -, hl, -⟩ := hg.edge f hf
    exact hl.isCompact.isClosed
  have hline : ∀ e ∈ E, IsLineWithEnds e (A e 0) (A e 1) := fun e he => by
    have := (hA e he).1.isLineWithEnds
    rwa [(hA e he).2.1] at this
  let T : Set ℝ := Icc 0 1 ∩ ι ⁻¹' V
  have hTf : T.Finite := by
    have h1 : (Ico 0 1 ∩ ι ⁻¹' V : Set ℝ).Finite :=
      Set.Finite.of_finite_image (hg.fin.subset (by rintro _ ⟨x, hx, rfl⟩; exact hx.2))
        (hinj.mono inter_subset_left)
    refine (h1.union (finite_singleton (1 : ℝ))).subset ?_
    rintro x ⟨hx, hxV⟩
    rcases eq_or_lt_of_le hx.2 with rfl | h2
    · exact .inr rfl
    · exact .inl ⟨⟨hx.1, h2⟩, hxV⟩
  have h0T : (0 : ℝ) ∈ T := ⟨⟨le_rfl, zero_le_one⟩, h0⟩
  have h1T : (1 : ℝ) ∈ T := ⟨⟨zero_le_one, le_rfl⟩, h1⟩
  obtain ⟨m, t, hm, ht0, htm, hlt, hmem, hgap, hall⟩ := exists_sorted hTf inter_subset_left h0T h1T
  have key : ∀ p, ∃ (e : Set X) (b : Bool), p < m → e ∈ E ∧ ι '' Icc (t p) (t (p + 1)) = e ∧
      ι (t p) = extI (A e) (if b then 0 else 1) ∧ ι (t (p + 1)) = extI (A e) (if b then 1 else 0)
        := by
    intro p
    by_cases hp : p < m
    swap
    · exact ⟨∅, true, fun h => absurd h hp⟩
    have hab := hlt p hp
    have ha1 := hmem p hp.le
    have hb1 := hmem (p + 1) hp
    have hopen : ∀ x ∈ Ioo (t p) (t (p + 1)), ι x ∉ V := fun x hx hxV =>
      hgap p hp x ⟨⟨ha1.1.1.trans hx.1.le, hx.2.le.trans hb1.1.2⟩, hxV⟩ hx
    have hsubI : Ioo (t p) (t (p + 1)) ⊆ Icc 0 1 := fun x hx => ⟨ha1.1.1.trans hx.1.le,
      hx.2.le.trans hb1.1.2⟩
    have hJP : ι '' Ioo (t p) (t (p + 1)) ⊆ ι '' Icc 0 1 := image_mono hsubI
    have hconn : IsPreconnected (ι '' Ioo (t p) (t (p + 1))) := isPreconnected_Ioo.image _
      hιc.continuousOn
    have hdisj : Disjoint (ι '' Ioo (t p) (t (p + 1))) V := Set.disjoint_left.mpr fun z hz hzV => by
      obtain ⟨x, hx, rfl⟩ := hz
      exact hopen x hx hzV
    obtain ⟨x0, hx0⟩ : (Ioo (t p) (t (p + 1))).Nonempty := nonempty_Ioo.mpr hab
    have hJG : ι '' Ioo (t p) (t (p + 1)) ⊆ ⋃₀ E := fun z hz =>
      (hG (hJP hz)).resolve_left (Set.disjoint_left.mp hdisj hz)
    obtain ⟨e, he, hxe⟩ := hJG (mem_image_of_mem ι hx0)
    have hJe := hg.subset_edge hconn hJG hdisj he ⟨_, mem_image_of_mem ι hx0, hxe⟩
    have hIe : ι '' Icc (t p) (t (p + 1)) ⊆ e := by
      rw [← closure_Ioo hab.ne]
      exact (image_closure_subset_closure_image hιc).trans (closure_minimal hJe (hcl e he))
    have hea : ι (t p) ∈ e ∩ V := ⟨hIe ⟨_, ⟨le_rfl, hab.le⟩, rfl⟩, ha1.2⟩
    have heb : ι (t (p + 1)) ∈ e ∩ V := ⟨hIe ⟨_, ⟨hab.le, le_rfl⟩, rfl⟩, hb1.2⟩
    have hne' : ι (t p) ≠ ι (t (p + 1)) := by
      intro he'
      have ha0 : t p = 0 := by
        by_contra hc
        have h1 : t p ∈ Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_ne ha1.1.1 (Ne.symm hc), ha1.1.2⟩
        exact hab.ne (hinj' h1 ⟨ha1.1.1.trans_lt hab, hb1.1.2⟩ he')
      have hb2 : t (p + 1) = 1 := by
        by_contra hc
        have h1 : t (p + 1) ∈ Ico (0 : ℝ) 1 := ⟨hb1.1.1, lt_of_le_of_ne hb1.1.2 hc⟩
        exact hab.ne (hinj ⟨ha1.1.1, hab.trans h1.2⟩ h1 he')
      rw [ha0, hb2] at he' hopen
      rcases hne with h3 | ⟨x, hx, hxV⟩
      · exact h3 he'
      · exact hopen x hx hxV
    have hpair : e ∩ V = {A e 0, A e 1} := (hA e he).2.2
    rw [hpair] at hea heb
    have hval0 : extI (A e) 0 = A e 0 := extI_coe (A e) 0
    have hval1 : extI (A e) 1 = A e 1 := extI_coe (A e) 1
    have hconnI : IsPreconnected (ι '' Icc (t p) (t (p + 1))) := isPreconnected_Icc.image _
      hιc.continuousOn
    rcases hea with hea | hea <;> rcases heb with heb | heb
    · exact absurd (hea.trans heb.symm) hne'
    · have heb' : ι (t (p + 1)) = A e 1 := heb
      refine ⟨e, true, fun _ => ⟨he, ?_, by simp [hea, hval0], by simp [heb', hval1]⟩⟩
      exact (hline e he).eq_of_subset hconnI hIe ⟨_, ⟨le_rfl, hab.le⟩, hea⟩ ⟨_, ⟨hab.le, le_rfl⟩,
        heb⟩
    · have hea' : ι (t p) = A e 1 := hea
      refine ⟨e, false, fun _ => ⟨he, ?_, by simp [hea', hval1], by simp [heb, hval0]⟩⟩
      exact (hline e he).eq_of_subset hconnI hIe ⟨_, ⟨hab.le, le_rfl⟩, heb⟩ ⟨_, ⟨le_rfl, hab.le⟩,
        hea⟩
    · exact absurd (hea.trans heb.symm) hne'
  choose s ε hs using key
  refine ⟨m, t, s, ε, hm, ht0, htm, hlt, ?_, hs, ?_⟩
  · intro x hx hxV
    obtain ⟨p, hp, e⟩ := hall x ⟨hx, hxV⟩
    exact ⟨p, hp, e.symm⟩
  · have hmono : ∀ p q, p + 1 ≤ q → q ≤ m → t (p + 1) ≤ t q := by
      intro p q hpq hq
      induction q, hpq using Nat.le_induction with
      | base => exact le_rfl
      | succ q hq' ih => exact (ih (by omega)).trans (hlt q (by omega)).le
    have key2 : ∀ p < m, ∀ q < m, p < q → s p ≠ s q := by
      intro p hp q hq hpq he
      have hab := hlt p hp
      have ha1 := hmem p hp.le
      have hb1 := hmem (p + 1) hp
      obtain ⟨x, hx⟩ : (Ioo (t p) (t (p + 1))).Nonempty := nonempty_Ioo.mpr hab
      have h1 : ι x ∈ s q := by
        rw [← he, ← (hs p hp).2.1]
        exact mem_image_of_mem ι ⟨hx.1.le, hx.2.le⟩
      rw [← (hs q hq).2.1] at h1
      obtain ⟨y, hy, hxy⟩ := h1
      have hxy2 : x < y := hx.2.trans_le ((hmono p q hpq hq.le).trans hy.1)
      have hx0 : 0 < x := ha1.1.1.trans_lt hx.1
      have hy1 : y ≤ 1 := hy.2.trans (hmem _ hq).1.2
      exact hxy2.ne (hinj' ⟨hx0, hx.2.le.trans hb1.1.2⟩ ⟨hx0.trans hxy2, hy1⟩ hxy.symm)
    intro p hp q hq hpq
    rcases lt_or_gt_of_ne hpq with h | h
    · exact key2 p hp q hq h
    · exact (key2 q hq p hp h).symm

end GraphMinor.Surface
