/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Draw7
public import LeanPool.GraphMinor.GM17.Defs
public import Mathlib.Data.Fin.Tuple.Sort

/-!
# Drawing a graph in a surface of large genus

Each edge of a finite graph has two half-edges. We list the half-edges in order of the vertices they
start from, and we run one curve for each half-edge across a row of handles or of cross-caps. The
curves come out on the right in the order of the edges. Short vertical segments then join the two
halves of each edge. This draws the graph in any model with many handles or with many cross-caps.
-/

@[expose] public section

namespace GraphMinor.GM20.Draw

open Set Topology GraphMinor.Surface GraphMinor.GM17

universe u v

variable {a b c : ℕ} {α' : Type u} {β' : Type v}

theorem exists_ends (H : Hypergraph α' β') (hH : H.IsGraph) {e : β'} (he : e ∈ H.edgeSet) :
    ∃ u v, H.ends e = {u, v} := by
  obtain ⟨h₁, h₂⟩ := hH e he
  have hfin : (H.ends e).Finite := H.vertexSet_finite.subset fun v hv ↦ H.vertex_mem_of_inc hv
  have h₃ : 0 < (H.ends e).ncard := (Set.ncard_pos hfin).mpr h₁
  have h₄ : (H.ends e).ncard = 1 ∨ (H.ends e).ncard = 2 := by omega
  rcases h₄ with h₄ | h₄
  · obtain ⟨u, hu⟩ := Set.ncard_eq_one.mp h₄
    exact ⟨u, u, by simpa using hu⟩
  · obtain ⟨u, v, _, huv⟩ := Set.ncard_eq_two.mp h₄
    exact ⟨u, v, huv⟩

private theorem cap_intersections {a b c m : ℕ} {R : ℝ}
    {A : Fin (2 * m) → Set (SurfaceModel a b c)} {Z : Fin m → Set (ℝ × ℝ)}
    (π : Equiv.Perm (Fin (2 * m))) (blk : Fin (2 * m) → Fin m)
    (hblk : ∀ d, (blk d : ℕ) = (d : ℕ) / 2)
    (hA₄ : ∀ p z, Ok a b c z → R ≤ z.1 → qq a b c z ∈ A p →
      qq a b c z = qq a b c (R, ((π p : ℕ) : ℝ)))
    (hclR : ∀ y, Clear a b c (R, y))
    (hcapClear : ∀ j z, z ∈ Z j → Clear a b c z)
    (hZ : ∀ j, ∀ z ∈ Z j, z.1 = R ∧ 2 * ((j : ℕ) : ℝ) ≤ z.2 ∧ z.2 ≤ 2 * (j : ℕ) + 1) :
    let q : Fin m → Set (SurfaceModel a b c) := fun j ↦ qq a b c '' Z j
    (∀ j p w, w ∈ q j → w ∈ A p → blk (π p) = j ∧
      w = qq a b c (R, ((π p : ℕ) : ℝ))) ∧
    (∀ j j' w, j ≠ j' → w ∈ q j → w ∈ q j' → False) := by
  intro q
  have hcapA : ∀ j p w, w ∈ q j → w ∈ A p → blk (π p) = j ∧
      w = qq a b c (R, ((π p : ℕ) : ℝ)) := by
    rintro j p _ ⟨z, hz, rfl⟩ hw
    have zc : Clear a b c z := hcapClear j z hz
    obtain ⟨hz₁, hz₂, hz₃⟩ := hZ j z hz
    have h₁ := hA₄ p z zc.ok hz₁.ge hw
    have h₂ := eq_of_qq_eq zc (hclR _).ok h₁
    refine ⟨?_, h₁⟩
    rw [h₂] at hz₂ hz₃
    simp only at hz₂ hz₃
    have h₃ : 2 * (j : ℕ) ≤ ((π p : Fin (2 * m)) : ℕ) := by exact_mod_cast hz₂
    have h₄ : ((π p : Fin (2 * m)) : ℕ) ≤ 2 * (j : ℕ) + 1 := by exact_mod_cast hz₃
    exact Fin.ext (by simp only [hblk]; omega)
  have hcapcap : ∀ j j' w, j ≠ j' → w ∈ q j → w ∈ q j' → False := by
    rintro j j' _ hjj ⟨z, hz, rfl⟩ ⟨z', hz', heq⟩
    have h₁ := eq_of_qq_eq (hcapClear j' z' hz') (hcapClear j z hz).ok heq
    subst h₁
    obtain ⟨_, h₂, h₃⟩ := hZ j z' hz
    obtain ⟨_, h₄, h₅⟩ := hZ j' z' hz'
    rcases lt_or_gt_of_ne hjj with h | h
    · have h₆ : (((j : ℕ) + 1 : ℕ) : ℝ) ≤ ((j' : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at h₆
      linarith
    · have h₆ : (((j' : ℕ) + 1 : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at h₆
      linarith
  exact ⟨hcapA, hcapcap⟩

private theorem isLine_or_isOArc_of_joined_pieces
    {T : Type*} [TopologicalSpace T] [T2Space T] {ι : Type*} {s t : ι}
    (ν : ι → T) {left cap right : Set T} {p : T}
    (hleft : IsLineWithEnds (left ∪ cap) (ν s) p)
    (hright : IsLineWithEnds right (ν t) p)
    (hmeet : ∀ w, w ∈ left → w ∈ right → w = ν s ∧ s = t)
    (htop : ∀ w, w ∈ cap → w ∈ right → w = p) :
    (s ≠ t → IsLineWithEnds ((left ∪ cap) ∪ right) (ν s) (ν t)) ∧
    (s = t → IsOArc ((left ∪ cap) ∪ right)) := by
  constructor
  · intro hst
    refine GM11.IsLineWithEnds.union (GM11.IsLineWithEnds.symm hleft)
      (GM11.IsLineWithEnds.symm hright) ?_
    ext w
    constructor
    · rintro ⟨hw | hw, hw'⟩
      · exact absurd (hmeet w hw hw').2 hst
      · exact htop w hw hw'
    · rintro rfl
      exact ⟨(mem_of_line hleft).2, (mem_of_line hright).2⟩
  · intro hst
    have h := hright
    rw [← hst] at h
    refine isOArc_of_lines hleft h ?_
    rintro w ⟨hw | hw, hw'⟩
    · exact Or.inl (hmeet w hw hw').1
    · exact Or.inr (htop w hw hw')

/-- A finite graph has a list of half-edges such that any set of curves that reorders the list as
needed gives a drawing of the graph. -/
theorem exists_perm (H : Hypergraph α' β') (hH : H.IsGraph) :
    ∃ (n : ℕ) (_ : Even n) (π : Equiv.Perm (Fin n)), ∀ (a b c : ℕ)
      [T2Space (SurfaceModel a b c)] (m₀ m₁ : ℤ), m₀ < m₁ →
      Slab a b c n (3 * (m₀ : ℝ) + 3 / 2) (3 * (m₁ : ℝ) + 3 / 2) π →
      CanBeDrawn (SurfaceModel a b c) H := by
  classical
  have hEf : Finite H.edgeSet := H.edgeSet_finite.to_subtype
  obtain ⟨m, ⟨Eq⟩⟩ := Finite.exists_equiv_fin H.edgeSet
  let e : Fin m → β' := fun j ↦ (Eq.symm j).1
  have hem : ∀ j, e j ∈ H.edgeSet := fun j ↦ (Eq.symm j).2
  choose s t hst using fun j ↦ exists_ends H hH (hem j)
  have hsm : ∀ j, s j ∈ H.ends (e j) := fun j ↦ by rw [hst]; exact Or.inl rfl
  have htm : ∀ j, t j ∈ H.ends (e j) := fun j ↦ by rw [hst]; exact Or.inr rfl
  have hsV : ∀ j, s j ∈ H.vertexSet := fun j ↦ H.vertex_mem_of_inc (hsm j)
  have htV : ∀ j, t j ∈ H.vertexSet := fun j ↦ H.vertex_mem_of_inc (htm j)
  obtain ⟨idx, hidx⟩ := Set.countable_iff_exists_injOn.mp H.vertexSet_finite.countable
  have hdiv : ∀ d : Fin (2 * m), (d : ℕ) / 2 < m := fun d ↦ by omega
  let blk : Fin (2 * m) → Fin m := fun d ↦ ⟨d / 2, hdiv d⟩
  let hv : Fin (2 * m) → α' := fun d ↦ if (d : ℕ) % 2 = 0 then s (blk d) else t (blk d)
  have hvm : ∀ d, hv d ∈ H.ends (e (blk d)) := fun d ↦ by
    simp only [hv]
    split_ifs
    · exact hsm _
    · exact htm _
  let f : Fin (2 * m) → ℕ := fun d ↦ idx (hv d)
  let π : Equiv.Perm (Fin (2 * m)) := Tuple.sort f
  have hmono : Monotone fun p ↦ ((f (π p) : ℕ) : ℝ) := fun p p' hpp ↦
    Nat.cast_le.mpr (Tuple.monotone_sort f hpp)
  refine ⟨2 * m, even_two_mul m, π, fun a b c _ m₀ m₁ hm hS ↦ ?_⟩
  have hm' : (m₀ : ℝ) + 1 ≤ m₁ := by exact_mod_cast hm
  set X : ℝ := 3 * (m₀ : ℝ) + 5 / 4 with hX
  set R : ℝ := 3 * (m₁ : ℝ) + 3 / 2 with hR
  have hXR : X + 1 < R := by simp only [hX, hR]; linarith
  obtain ⟨A, hA₁, hA₂, hA₃, hA₄⟩ := exists_fans (by simp only [hR]; linarith) hS hmono
  let d₀ : Fin m → Fin (2 * m) := fun j ↦ ⟨2 * j, by omega⟩
  let d₁ : Fin m → Fin (2 * m) := fun j ↦ ⟨2 * j + 1, by omega⟩
  have hb₀ : ∀ j, blk (d₀ j) = j := fun j ↦ Fin.ext (by simp only [blk, d₀]; omega)
  have hb₁ : ∀ j, blk (d₁ j) = j := fun j ↦ Fin.ext (by simp only [blk, d₁]; omega)
  have hv₀ : ∀ j, hv (d₀ j) = s j := fun j ↦ by
    simp only [hv, hb₀]
    rw [ite_eq_left (by simp only [d₀]; omega)]
  have hv₁ : ∀ j, hv (d₁ j) = t j := fun j ↦ by
    simp only [hv, hb₁]
    rw [ite_eq_right (by simp only [d₁]; omega)]
  let ν : α' → SurfaceModel a b c := fun v ↦ qq a b c (X, ((idx v : ℕ) : ℝ))
  have hclX : ∀ y, Clear a b c (X, y) := fun y ↦
    clear_of_gap m₀ (by simp only [hX]; linarith) (by simp only [hX]; linarith)
  have hclR : ∀ y, Clear a b c (R, y) := fun y ↦
    clear_of_gap m₁ (by simp only [hR]; linarith) (by simp only [hR]; linarith)
  let Z : Fin m → Set (ℝ × ℝ) := fun j ↦ sg (R, (2 * (j : ℕ) : ℝ)) (R, (2 * (j : ℕ) + 1 : ℝ))
  have hcap := fun j : Fin m ↦ isLine_sg (a := a) (b := b) (c := c) m₁
    (z := (R, (2 * (j : ℕ) : ℝ))) (z' := (R, (2 * (j : ℕ) + 1 : ℝ)))
    (by simp only [hR]; linarith) (by simp only [hR]; linarith)
    (by simp only [hR]; linarith) (by simp only [hR]; linarith)
    (fun he ↦ by
      have := congrArg Prod.snd he
      simp only at this
      linarith)
  have hZ : ∀ j, ∀ z ∈ Z j, z.1 = R ∧ 2 * ((j : ℕ) : ℝ) ≤ z.2 ∧ z.2 ≤ 2 * (j : ℕ) + 1 := by
    rintro j _ ⟨u, hu, rfl⟩
    simp only
    have h₁ := hu.1
    have h₂ := hu.2
    refine ⟨by ring, ?_, ?_⟩ <;> nlinarith
  let q : Fin m → Set (SurfaceModel a b c) := fun j ↦ qq a b c '' Z j
  let p₀ : Fin m → Fin (2 * m) := fun j ↦ π.symm (d₀ j)
  let p₁ : Fin m → Fin (2 * m) := fun j ↦ π.symm (d₁ j)
  have hπ₀ : ∀ j, π (p₀ j) = d₀ j := fun j ↦ π.apply_symm_apply _
  have hπ₁ : ∀ j, π (p₁ j) = d₁ j := fun j ↦ π.apply_symm_apply _
  have hne : ∀ j, p₀ j ≠ p₁ j := fun j he ↦ by
    have h₁ : d₀ j = d₁ j := by rw [← hπ₀, ← hπ₁, he]
    have h₂ := congrArg Fin.val h₁
    simp only [d₀, d₁] at h₂
    omega
  have hL₀ : ∀ j, IsLineWithEnds (A (p₀ j)) (ν (s j)) (qq a b c (R, (2 * (j : ℕ) : ℝ))) := by
    intro j
    have h₁ := hA₁ (p₀ j)
    have h₂ : f (π (p₀ j)) = idx (s j) := by
      rw [hπ₀]
      simp only [f, hv₀]
    have h₃ : (((π (p₀ j) : Fin (2 * m)) : ℕ) : ℝ) = 2 * (j : ℕ) := by
      rw [hπ₀]
      simp only [d₀]
      push_cast
      rfl
    simp only [h₂, h₃] at h₁
    exact h₁
  have hL₁ : ∀ j, IsLineWithEnds (A (p₁ j)) (ν (t j)) (qq a b c (R, (2 * (j : ℕ) + 1 : ℝ))) := by
    intro j
    have h₁ := hA₁ (p₁ j)
    have h₂ : f (π (p₁ j)) = idx (t j) := by
      rw [hπ₁]
      simp only [f, hv₁]
    have h₃ : (((π (p₁ j) : Fin (2 * m)) : ℕ) : ℝ) = 2 * (j : ℕ) + 1 := by
      rw [hπ₁]
      simp only [d₁]
      push_cast
      rfl
    simp only [h₂, h₃] at h₁
    exact h₁
  obtain ⟨hcapA, hcapcap⟩ :=
    cap_intersections π blk (fun _ ↦ rfl) hA₄ hclR (fun j ↦ (hcap j).2) hZ
  have hT : ∀ j, IsLineWithEnds (A (p₀ j) ∪ q j) (ν (s j))
      (qq a b c (R, (2 * (j : ℕ) + 1 : ℝ))) := by
    intro j
    refine GM11.IsLineWithEnds.union (GM11.IsLineWithEnds.symm (hL₀ j)) (hcap j).1 ?_
    ext w
    constructor
    · rintro ⟨hw, hw'⟩
      have h₁ := (hcapA j (p₀ j) w hw' hw).2
      rw [hπ₀] at h₁
      rw [mem_singleton_iff, h₁]
      simp only [d₀]
      push_cast
      rfl
    · rintro rfl
      exact ⟨(mem_of_line (hL₀ j)).2, (mem_of_line (hcap j).1).1⟩
  have htop : ∀ j w, w ∈ q j → w ∈ A (p₁ j) → w = qq a b c (R, (2 * (j : ℕ) + 1 : ℝ)) := by
    intro j w hw hw'
    have h₁ := (hcapA j (p₁ j) w hw hw').2
    rw [hπ₁] at h₁
    rw [h₁]
    simp only [d₁]
    push_cast
    rfl
  have hvert₀ : ∀ j, qq a b c (X, ((f (π (p₀ j)) : ℕ) : ℝ)) = ν (s j) := fun j ↦ by
    simp only [hπ₀, f, hv₀, ν]
  have hmeet : ∀ j w, w ∈ A (p₀ j) → w ∈ A (p₁ j) → w = ν (s j) ∧ s j = t j := by
    intro j w hw hw'
    obtain ⟨h₁, h₂⟩ := hA₂ _ _ (hne j) w hw hw'
    rw [hvert₀] at h₁
    refine ⟨h₁, hidx (hsV j) (htV j) ?_⟩
    have h₃ : idx (s j) = idx (t j) := by
      have h₄ : f (π (p₀ j)) = f (π (p₁ j)) := by exact_mod_cast h₂
      rw [hπ₀, hπ₁] at h₄
      simpa only [f, hv₀, hv₁] using h₄
    exact h₃
  let B : Fin m → Set (SurfaceModel a b c) := fun j ↦ (A (p₀ j) ∪ q j) ∪ A (p₁ j)
  have hjoined := fun j => isLine_or_isOArc_of_joined_pieces ν (hT j) (hL₁ j) (hmeet j) (htop j)
  have hBline := fun j => (hjoined j).1
  have hBloop := fun j => (hjoined j).2
  have hBcases : ∀ j w, w ∈ B j → (∃ p, blk (π p) = j ∧ w ∈ A p) ∨ w ∈ q j := by
    rintro j w ((hw | hw) | hw)
    · exact Or.inl ⟨p₀ j, by rw [hπ₀, hb₀], hw⟩
    · exact Or.inr hw
    · exact Or.inl ⟨p₁ j, by rw [hπ₁, hb₁], hw⟩
  have hE : ∀ b (hb : b ∈ H.edgeSet), e (Eq ⟨b, hb⟩) = b := fun b hb ↦ by simp [e]
  refine ⟨ν, fun b ↦ if hb : b ∈ H.edgeSet then B (Eq ⟨b, hb⟩) else ∅, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu v hv' heq
    have h₁ := eq_of_qq_eq (hclX _) (hclX _).ok heq
    have h₂ := congrArg Prod.snd h₁
    simp only at h₂
    exact hidx hu hv' (by exact_mod_cast h₂)
  · intro b hb u v hu hv' huv
    simp only [dite_eq_left hb]
    have h₁ := hst (Eq ⟨b, hb⟩)
    rw [hE] at h₁
    have hu' : u ∈ H.ends b := hu
    have hv'' : v ∈ H.ends b := hv'
    rw [h₁] at hu' hv''
    rcases hu' with rfl | rfl
    · rcases hv'' with rfl | rfl
      · exact absurd rfl huv
      · exact hBline _ huv
    · rcases hv'' with rfl | rfl
      · have h₂ := hBline _ huv.symm
        exact GM11.IsLineWithEnds.symm h₂
      · exact absurd rfl huv
  · intro b hb v hv'
    simp only [dite_eq_left hb]
    have h₁ := hsm (Eq ⟨b, hb⟩)
    have h₂ := htm (Eq ⟨b, hb⟩)
    rw [hE, hv'] at h₁ h₂
    have h₃ : s (Eq ⟨b, hb⟩) = v := h₁
    have h₄ : t (Eq ⟨b, hb⟩) = v := h₂
    refine ⟨hBloop _ (h₃.trans h₄.symm), ?_⟩
    rw [← h₃]
    exact Or.inl (Or.inl (mem_of_line (hL₀ _)).1)
  · intro b hb b' hb' hne' w hw
    simp only [dite_eq_left hb, dite_eq_left hb'] at hw
    have hjj : Eq ⟨b, hb⟩ ≠ Eq ⟨b', hb'⟩ := fun h ↦ hne' (congrArg Subtype.val (Eq.injective h))
    rcases hBcases _ _ hw.1 with ⟨p, hp, hwp⟩ | hwq
    · rcases hBcases _ _ hw.2 with ⟨p', hp', hwp'⟩ | hwq'
      · have hpp : p ≠ p' := fun h ↦ hjj (by rw [← hp, ← hp', h])
        have h₁ := (hA₂ p p' hpp w hwp hwp').1
        exact ⟨hv (π p), H.vertex_mem_of_inc (hvm (π p)), h₁.symm⟩
      · exact absurd ((hcapA _ p w hwq' hwp).1.symm.trans hp) hjj.symm
    · rcases hBcases _ _ hw.2 with ⟨p', hp', hwp'⟩ | hwq'
      · exact absurd ((hcapA _ p' w hwq hwp').1.symm.trans hp') hjj
      · exact (hcapcap _ _ w hjj hwq hwq').elim
  · intro b hb v hvV hw
    simp only [dite_eq_left hb] at hw
    rcases hBcases _ _ hw with ⟨p, hp, hwp⟩ | ⟨z, hz, heq⟩
    · have h₁ := hA₃ p _ hwp
      have h₂ : idx v = idx (hv (π p)) := by exact_mod_cast h₁
      have h₃ := hidx hvV (H.vertex_mem_of_inc (hvm (π p))) h₂
      have h₄ := hvm (π p)
      rw [hp, hE, ← h₃] at h₄
      exact h₄
    · have h₁ := eq_of_qq_eq ((hcap _).2 z hz) (hclX _).ok heq
      have h₂ := (hZ _ z hz).1
      rw [h₁] at h₂
      simp only at h₂
      linarith

/-- **A surface of large genus has a drawing of a finite graph.** Given a graph `H`, some `L` is
such
that `H` can be drawn in every model surface with at least `L` handles or at least `L` cross-caps.
-/
theorem exists_canBeDrawn (H : Hypergraph α' β') (hH : H.IsGraph) :
    ∃ L, ∀ (a b c : ℕ) [T2Space (SurfaceModel a b c)], L ≤ a ∨ L ≤ b →
      CanBeDrawn (SurfaceModel a b c) H := by
  obtain ⟨n, hn, π, h⟩ := exists_perm H hH
  obtain ⟨L₁, hL₁, h₁⟩ := wiring_handles hn π
  obtain ⟨L₂, hL₂, h₂⟩ := wiring_crosscaps hn π
  refine ⟨max L₁ L₂, fun a b c _ hab ↦ ?_⟩
  rcases hab with hab | hab
  · exact h a b c (-1) ((2 * L₁ : ℕ) - 1) (by push_cast; omega)
      (h₁ a b c ((le_max_left _ _).trans hab))
  · exact h a b c ((2 * a : ℕ) - 1) ((2 * a + L₂ : ℕ) - 1) (by push_cast; omega)
      (h₂ a b c ((le_max_right _ _).trans hab))

end GraphMinor.GM20.Draw
