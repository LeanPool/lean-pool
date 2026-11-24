/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CuffLift

/-!
# The order of the vertices on a top arc

Graph Minors VII, (5.9), page 235. The paths `N_i(C)` are disjoint, and each holds one end `t_i`. So
an arc of `N(C)` between two neighbouring ends `t_l` and `t_r` holds first a piece of `N_l(C)` and
then a piece of `N_r(C)`, and nothing else.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function Metric GraphMinor.Surface GraphMinor.GM11

universe u

theorem isLine_Icc {a b : ℝ} (h : a < b) : IsLineWithEnds (Icc a b) a b := by
  let e : unitInterval → ℝ := fun s => a + s.1 * (b - a)
  have hc : Continuous e := by fun_prop
  have hne : b - a ≠ 0 := (sub_pos.mpr h).ne'
  have hi : Injective e := fun s s' he => by
    have h1 : s.1 * (b - a) = s'.1 * (b - a) := by
      simp only [e] at he
      linarith
    exact Subtype.ext (mul_right_cancel₀ hne h1)
  have hr : range e = Icc a b := by
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      have h1 := s.2.1
      have h2 := s.2.2
      have h3 := sub_pos.mpr h
      simp only [e]
      constructor <;> nlinarith
    · intro hy
      have h3 := sub_pos.mpr h
      refine ⟨⟨(y - a) / (b - a), div_nonneg (by linarith [hy.1]) h3.le,
        (div_le_one h3).mpr (by linarith [hy.2])⟩, ?_⟩
      simp only [e]
      field_simp
      ring
  refine ⟨(hc.isClosedEmbedding hi).isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hr), ?_, ?_⟩
  · change e 0 = a
    simp [e]
  · change e 1 = b
    simp [e]

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- A line in an `O`-arc is one of the two arcs between its ends. -/
theorem exists_other_arc {F P : Set S} {u v : S} (hF : IsOArc F) (hP : IsLineWithEnds P u v)
  (hPF : P ⊆ F) (huv : u ≠ v) : ∃ P', IsLineWithEnds P' u v ∧ P ∪ P' = F ∧ P ∩ P' = {u, v} := by
  obtain ⟨A, B, hA, hB, hu, hi⟩ := hF.lines (hPF hP.left_mem) (hPF hP.right_mem) huv
  have key : ∀ {A B : Set S}, IsLineWithEnds A u v → IsLineWithEnds B u v → A ∪ B = F → A ∩ B
    = {u, v} → P \ {u, v} ⊆ A → P = A := fun {A B} hA hB hu hi hs => by
    have h1 : P ⊆ A := by
      have h2 : P ⊆ closure (P \ {u, v}) := fun z hz => hP.subset_closure_diff hz
      exact h2.trans (closure_minimal hs hA.isCompact.isClosed)
    refine subset_antisymm h1 ?_
    intro z hz
    by_contra hzP
    have hzu : z ≠ u := fun h => hzP (h ▸ hP.left_mem)
    have hzv : z ≠ v := fun h => hzP (h ▸ hP.right_mem)
    obtain ⟨L₁, L₂, h₁, h₂, hu', hi'⟩ := hA.split hz hzu hzv
    have hd : Disjoint P (L₁ ∩ L₂) := by
      rw [hi', disjoint_singleton_right]
      exact hzP
    rcases GM12.subset_side h₁.isCompact.isClosed h₂.isCompact.isClosed (GM12.line_conn hP)
      (by rw [hu']; exact h1) hd with h3 | h3
    · have h4 : v ∈ L₁ ∩ L₂ := ⟨h3 hP.right_mem, h₂.right_mem⟩
      rw [hi'] at h4
      exact hzv h4.symm
    · have h4 : u ∈ L₁ ∩ L₂ := ⟨h₁.left_mem, h3 hP.left_mem⟩
      rw [hi'] at h4
      exact hzu h4.symm
  have hd : Disjoint (P \ {u, v}) (A ∩ B) := by
    rw [hi]
    exact disjoint_left.mpr fun z hz h => hz.2 h
  rcases GM12.subset_side hA.isCompact.isClosed hB.isCompact.isClosed hP.isPreconnected_diff
    (by rw [hu]; exact fun z hz => hPF hz.1) hd with h1 | h1
  · rw [key hA hB hu hi h1]
    exact ⟨B, hB, hu, hi⟩
  · rw [key hB hA (by rw [union_comm]; exact hu) (by rw [inter_comm]; exact hi) h1]
    exact ⟨A, hA, by rw [union_comm]; exact hu, by rw [inter_comm]; exact hi⟩

/-- A connected set in an `O`-arc that misses the two ends of a line in the `O`-arc is inside the
line or misses it. -/
theorem subset_line_or_off {F P Y : Set S} {u v : S} (hF : IsOArc F) (hP : IsLineWithEnds P u v)
  (hPF : P ⊆ F) (huv : u ≠ v) (hY : IsPreconnected Y) (hYF : Y ⊆ F) (hu : u ∉ Y)
    (hv : v ∉ Y) {y : S} (hy : y ∈ Y) (hyP : y ∈ P) : Y ⊆ P := by
  obtain ⟨P', hl, h1, h2⟩ := exists_other_arc hF hP hPF huv
  have hd : Disjoint Y (P ∩ P') := by
    rw [h2, disjoint_left]
    rintro z hz (rfl | rfl)
    · exact hu hz
    · exact hv hz
  rcases GM12.subset_side hP.isCompact.isClosed hl.isCompact.isClosed hY
    (by rw [h1]; exact hYF) hd with h3 | h3
  · exact h3
  · have h4 : y ∈ P ∩ P' := ⟨hyP, h3 hy⟩
    exact (disjoint_left.mp hd hy h4).elim

theorem IsParam.isLine {P : Set S} {u v : S} {p : ℝ → S} (h : IsParam P u v p) : IsLineWithEnds P u
  v := by
  have h1 := isLineWithEnds_image (isLine_Icc (zero_lt_one' ℝ)) h.cont h.inj
  rwa [h.image, h.zero, h.one] at h1

variable {N : Drawing S} {ι : Type*} {R : ι → Drawing S} {t : ι → S}

/-- The set of a subdrawing of a path is connected, in the case of a path. -/
theorem isPreconnected_of_isPathBetween {P : Drawing S} {a b : S} (hP : P.IsPathBetween a b) :
  IsPreconnected P.U := by
  by_cases hab : a = b
  · subst hab
    obtain ⟨W, hW, hV, hE⟩ := hP
    have hnil : ∀ x ∈ P.U, x = a := fun x hx => by
      by_cases hxV : x ∈ P.V
      · rw [hV] at hxV
        cases W with
        | nil _ => simpa [GraphWalk.support] using hxV
        | cons _ r =>
          exact absurd (List.nodup_cons.mp hW).1 (by simpa using r.end_mem_support)
      · obtain ⟨e, he, -⟩ := P.exists_edge_of_mem hx hxV
        rw [hE] at he
        cases W with
        | nil _ => simp [GraphWalk.edges] at he
        | cons _ r =>
          exact absurd (List.nodup_cons.mp hW).1 (by simpa using r.end_mem_support)
    have hU : P.U ⊆ {a} := hnil
    rcases subset_singleton_iff_eq.mp hU with h | h
    · rw [h]
      exact isPreconnected_empty
    · rw [h]
      exact isPreconnected_singleton
  · exact GM12.line_conn (isLine_of_isPathBetween hP hab)

/-- **The order on a top arc.** Let `P` be a line in the circuit `N` from `t l` to `t r`, and let
the `R i` be connected pieces of `N` with `t i` in `R i`, where no other `t i` is on `P`. Then on
`P` first comes the part of `R l`, and last the part of `R r`, and no other piece meets `P`. -/
theorem exists_top_split (hN : IsOArc N.U) (hR : ∀ i, (R i).IsSubdrawing N)
  (hRp : ∀ i, IsPreconnected (R i).U) (hdis : ∀ i i', i ≠ i' → Disjoint (R i).U (R i').U)
    (ht : ∀ i, t i ∈ (R i).V) {l r : ι} (hlr : l ≠ r) {τ : ℝ → S} {P : Set S} (hτ : IsParam P (t l)
      (t r) τ) (hP : P ⊆ N.U) (hoff : ∀ i, i ≠ l → i ≠ r → t i ∉ P) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧ ∀ m ∈ Icc (0 : ℝ) 1, ∀ i, τ m ∈ (R i).U → (i = l ∧ m ≤ a) ∨
      (i = r ∧ b ≤ m) := by
  classical
  have hUU : ∀ {i i' : ι} {z}, i ≠ i' → z ∈ (R i).U → z ∉ (R i').U := fun {i i' z} h1 h2 h3
    => disjoint_left.mp (hdis i i' h1) h2 h3
  have htU : ∀ i, t i ∈ (R i).U := fun i => (R i).V_subset_U (ht i)
  have hne : t l ≠ t r := fun h => hUU hlr (htU l) (h ▸ htU r)
  have hmem01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 ∧ (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨⟨le_rfl, zero_le_one⟩,
    zero_le_one, le_rfl⟩
  have hsub : ∀ i, (R i).U ⊆ N.U := fun i => (hR i).U_subset
  have hthird : ∀ m ∈ Icc (0 : ℝ) 1, ∀ i, τ m ∈ (R i).U → i = l ∨ i = r := fun m hm i hi => by
    by_contra hc
    push Not at hc
    obtain ⟨h1, h2⟩ := hc
    have h3 : (R i).U ⊆ P := subset_line_or_off hN hτ.isLine hP hne (hRp i) (hsub i) (hUU h1.symm
      (htU l)) (hUU h2.symm (htU r)) hi (hτ.mem hm)
    exact hoff i h1 h2 (h3 (htU i))
  have hbad : ∀ m ∈ Icc (0 : ℝ) 1, ∀ m' ∈ Icc (0 : ℝ) 1, m < m' → τ m ∈ (R r).U → τ m' ∈ (R l).U
    → False := fun m hm m' hm' hlt h1 h2 => by
    have hm0 : m ≠ 0 := fun h => hUU hlr (htU l) (by rw [← hτ.zero, ← h]; exact h1)
    have hlt1 : m < 1 := lt_of_lt_of_le hlt hm'.2
    have hs : Icc m 1 ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc_left hm.1
    have hl₀ : IsLineWithEnds (τ '' Icc m 1) (τ m) (τ 1) := isLineWithEnds_image (isLine_Icc hlt1)
      (hτ.cont.mono hs) (hτ.inj.mono hs)
    rw [hτ.one] at hl₀
    have hPs : τ '' Icc m 1 ⊆ N.U := fun z hz => by
      obtain ⟨s, hs', rfl⟩ := hz
      exact hP (hτ.mem (hs hs'))
    have hne' : τ m ≠ t r := fun h => absurd (hτ.inj hm hmem01.2 (h.trans hτ.one.symm)) hlt1.ne
    have h3 : (R l).U ⊆ τ '' Icc m 1 := subset_line_or_off hN hl₀ hPs hne' (hRp l) (hsub l)
      (hUU hlr.symm h1) (hUU hlr.symm (htU r)) h2 ⟨m', ⟨hlt.le, hm'.2⟩, rfl⟩
    obtain ⟨s, hs', he⟩ := h3 (htU l)
    have h4 : s = 0 := hτ.inj (hs hs') hmem01.1 (he.trans hτ.zero.symm)
    have h5 : m ≤ 0 := h4 ▸ hs'.1
    exact hm0 (le_antisymm h5 hm.1)
  have hcomp : ∀ i, IsCompact {m | m ∈ Icc (0 : ℝ) 1 ∧ τ m ∈ (R i).U} := fun i => by
    have h1 := hτ.cont.preimage_isClosed_of_isClosed isClosed_Icc (R i).isClosed_U
    exact isCompact_Icc.of_isClosed_subset h1 (fun _ hm => hm.1)
  obtain ⟨a, ha, hamax⟩ := (hcomp l).exists_isMaxOn
    ⟨0, hmem01.1, by rw [hτ.zero]; exact htU l⟩ continuous_id.continuousOn
  obtain ⟨b, hb, hbmin⟩ := (hcomp r).exists_isMinOn
    ⟨1, hmem01.2, by rw [hτ.one]; exact htU r⟩ continuous_id.continuousOn
  have hab : a < b := by
    by_contra hc
    push Not at hc
    rcases hc.lt_or_eq with h1 | h1
    · exact hbad b hb.1 a ha.1 h1 hb.2 ha.2
    · exact hUU hlr ha.2 (h1 ▸ hb.2)
  refine ⟨a, b, ha.1.1, hab, hb.1.2, fun m hm i hi => ?_⟩
  rcases hthird m hm i hi with rfl | rfl
  · exact .inl ⟨rfl, hamax ⟨hm, hi⟩⟩
  · exact .inr ⟨rfl, hbmin ⟨hm, hi⟩⟩

end GraphMinor.GM07
