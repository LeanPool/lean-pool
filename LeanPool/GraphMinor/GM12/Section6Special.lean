/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section6Regions
public import LeanPool.GraphMinor.GM12.Section3DiscStarLines
public import LeanPool.GraphMinor.GM11.RadialPrescribed

/-!
# Graph Minors XII, Section 6: the special radial drawing of (6.1)

The proof of (6.1) (page 258) says: "Since $\Gamma_1$ is 2-cell it follows that $r_0, r_1, \dots,
r_{\theta/2}$ are all distinct. Hence we may choose a radial drawing $K$ of $\Gamma$ such that for
$0 \le i \le \theta/2$, $D_i$ contains a vertex $v_i$ say of $K$, and $D_i$ includes edges of $K$
from $v_i$ to every vertex of $P_i$ (if $i \ge 1$) and to every vertex of $P_{i+1}$ (if
$i < \theta/2$)."

We do this here (`exists_special_radial`). In the closed disc `DBar_m` we draw lines from one inner
point `c m` to the vertices of the two paths on its boundary (`exists_star_lines_in_disc`). The
discs `DBar_m` overlap only on the paths (`discInt_disjoint`), so lines in different discs meet only
at
common ends. Then `exists_radial_with_spokes` gives a radial drawing with these lines as edges. The
regions `r_m` are distinct, so each has one point `c m`.
-/

@[expose] public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]
  {Γ : Drawing S} {F Δ : Set S} {k : ℕ} {a b : Fin k → S} {P : Fin k → Drawing S}
  {X Y A B : Fin k → Set S} {E r : Fin (k + 1) → Set S}

/-- The vertices on the boundary of the disc `DBar_m`: those of the paths next to it. -/
def sideVerts (P : Fin k → Drawing S) (m : Fin (k + 1)) : Set S :=
  {x | ∃ i : Fin k, (i.castSucc = m ∨ i.succ = m) ∧ x ∈ (P i).V}

/-- `DBar_m` lies on the far side of the chords before `m`, and on the near side of the others. -/
theorem Pieces61.sub_X (hp : Pieces61 Γ F Δ a b P X Y A B E r) {m : Fin (k + 1)} {i : Fin k}
    (hi : m.1 ≤ i.1) : E m ⊆ X i :=
  ((hp.disc m).subset_closure_discInt).trans
    (closure_minimal (hp.int_X m i hi) (hp.side i).discX.isClosed)

theorem Pieces61.sub_Y (hp : Pieces61 Γ F Δ a b P X Y A B E r) {m : Fin (k + 1)} {i : Fin k}
    (hi : i.1 < m.1) : E m ⊆ Y i :=
  ((hp.disc m).subset_closure_discInt).trans
    (closure_minimal (hp.int_Y m i hi) (hp.side i).discY.isClosed)

/-- **Two discs `DBar_m` overlap only on the paths.** The inside of one misses the other. -/
theorem Pieces61.discInt_disjoint (hp : Pieces61 Γ F Δ a b P X Y A B E r) {m m' : Fin (k + 1)}
    (hne : m ≠ m') : Disjoint (discInt (E m)) (E m') := by
  have hval : m.1 ≠ m'.1 := fun e => hne (Fin.ext e)
  rcases Nat.lt_or_gt_of_ne hval with hlt | hlt
  · let i : Fin k := ⟨m.1, by have := m'.2; omega⟩
    refine disjoint_left.mpr fun y hy hy' => ?_
    have h1 : y ∈ X i ∩ Y i := ⟨hp.int_X m i le_rfl hy, hp.sub_Y (i := i) hlt hy'⟩
    rw [(hp.side i).inter] at h1
    exact disjoint_left.mp (hp.int_P m i) hy h1
  · let i : Fin k := ⟨m'.1, by have := m.2; omega⟩
    refine disjoint_left.mpr fun y hy hy' => ?_
    have h1 : y ∈ X i ∩ Y i := ⟨hp.sub_X (i := i) le_rfl hy', hp.int_Y m i hlt hy⟩
    rw [(hp.side i).inter] at h1
    exact disjoint_left.mp (hp.int_P m i) hy h1

omit [T2Space S] in
theorem Pieces61.sideVerts_sub (hp : Pieces61 Γ F Δ a b P X Y A B E r) (m : Fin (k + 1)) :
    sideVerts P m ⊆ discBd (E m) := by
  rintro x ⟨i, hi, hx⟩
  have hxU := (P i).V_subset_U hx
  rcases hi with rfl | rfl
  · exact (hp.bd i).1 hxU
  · exact (hp.bd i).2 hxU

/-- **The special radial drawing of (6.1).** There is a radial drawing `K` of `Γ` with a vertex `c
m`
in each `D_m`, and for each vertex `x` of a path next to `D_m` an edge of `K` from `c m` to `x`
whose
closure is a line `L m x` in `DBar_m` that meets the boundary of `DBar_m` only at `x`. -/
theorem exists_special_radial (h : Setup61 Γ F Δ k a b P) (hS : IsClosedSurface S)
    (hT : (PaintingOrDrawing.drawing Γ).IsTwoCell) (hp : Pieces61 Γ F Δ a b P X Y A B E r) :
    ∃ (K : Drawing S) (c : Fin (k + 1) → S) (L : Fin (k + 1) → S → Set S),
      (PaintingOrDrawing.drawing Γ).IsRadialDrawing K ∧
      (∀ m, c m ∈ discInt (E m) ∧ c m ∈ K.V) ∧
      ∀ m, ∀ x ∈ sideVerts P m, IsLineWithEnds (L m x) (c m) x ∧ L m x ⊆ E m ∧
        L m x ∩ discBd (E m) = {x} ∧ (∀ y ∈ sideVerts P m, x ≠ y → L m x ∩ L m y = {c m}) ∧
        L m x \ {c m, x} ∈ K.E := by
  classical
  have hst := fun m => exists_star_lines_in_disc (hp.disc m) (hp.sideVerts_sub m)
  choose c hc L hL hLL using hst
  -- the point of each region
  have : Nonempty S := ⟨c 0⟩
  let hub : Set S → S := fun s =>
    if hs : ∃ m, r m = s then c hs.choose else Classical.epsilon (· ∈ s)
  have hub_r : ∀ m, hub (r m) = c m := by
    intro m
    have hs : ∃ m', r m' = r m := ⟨m, rfl⟩
    simp only [hub, dite_eq_left hs]
    rw [hp.inj hs.choose_spec]
  have hhub : ∀ s ∈ Γ.R, hub s ∈ s := by
    intro s hs
    by_cases hm : ∃ m, r m = s
    · obtain ⟨m, rfl⟩ := hm
      rw [hub_r]
      exact hp.int_r m (hc m)
    · simp only [hub, dite_eq_right hm]
      exact Classical.epsilon_spec (region_nonempty hs)
  have hZV : ∀ m, sideVerts P m ⊆ Γ.V := by
    rintro m x ⟨i, -, hx⟩
    exact (h.isSub i).1 hx
  have hfin : {p : Fin (k + 1) × S | p.2 ∈ sideVerts P p.1}.Finite :=
    (finite_univ.prod Γ.finite_V).subset fun p hp' => ⟨mem_univ _, hZV p.1 hp'⟩
  let s : Finset (Fin (k + 1) × S) := hfin.toFinset
  have hs : ∀ p, p ∈ s ↔ p.2 ∈ sideVerts P p.1 := fun p => by simp [s]
  have hLr : ∀ m, ∀ x ∈ sideVerts P m, L m x \ {x} ⊆ r m := by
    intro m x hx y ⟨hyL, hyx⟩
    refine hp.int_r m ⟨(hL m x hx).2.1 hyL, fun hyb => hyx ?_⟩
    have : y ∈ L m x ∩ discBd (E m) := ⟨hyL, hyb⟩
    rwa [(hL m x hx).2.2] at this
  obtain ⟨K, hK, hKV, hKE⟩ := exists_radial_with_spokes hS hT hub hhub (fun p => r p.1)
    (fun p => p.2) (fun p => L p.1 p.2) s (fun p _ => hp.reg p.1)
    (fun p hp' => hZV p.1 ((hs p).mp hp'))
    (fun p hp' => by rw [hub_r]; exact (hL p.1 p.2 ((hs p).mp hp')).1)
    (fun p hp' => hLr p.1 p.2 ((hs p).mp hp'))
    (by
      rintro ⟨m, x⟩ hp₁ ⟨m', x'⟩ hp₂ hne y ⟨hy, hy'⟩
      have hx := (hs _).mp hp₁
      have hx' := (hs _).mp hp₂
      simp only at hx hx' hy hy' ⊢
      rw [hub_r]
      by_cases hmm : m = m'
      · subst hmm
        have hxx : x ≠ x' := fun e => hne (by rw [e])
        have := hLL m x hx x' hx' hxx
        have hyc : y ∈ L m x ∩ L m x' := ⟨hy, hy'⟩
        rw [this] at hyc
        exact Or.inl hyc
      · by_cases hyx : y = x
        · exact Or.inr hyx
        · exfalso
          have hyi : y ∈ discInt (E m) := ⟨(hL m x hx).2.1 hy, fun hyb => hyx (by
            have : y ∈ L m x ∩ discBd (E m) := ⟨hy, hyb⟩
            rwa [(hL m x hx).2.2] at this)⟩
          exact disjoint_left.mp (hp.discInt_disjoint hmm) hyi ((hL m' x' hx').2.1 hy'))
    (by
      rintro ⟨m, x⟩ - ⟨m', x'⟩ - hρ hxx
      simp only at hρ hxx
      rw [hp.inj hρ, hxx])
  refine ⟨K, c, L, hK, fun m => ⟨hc m, hub_r m ▸ hKV (r m) (hp.reg m)⟩, ?_⟩
  intro m x hx
  refine ⟨(hL m x hx).1, (hL m x hx).2.1, (hL m x hx).2.2, hLL m x hx, ?_⟩
  have := hKE (m, x) ((hs _).mpr hx)
  simp only [hub_r] at this
  exact this

end GraphMinor.GM12
