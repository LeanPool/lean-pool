/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.MeshLine

/-!
# Cutting a Jordan domain into small pieces

`cutTree_small`: for every `O`-arc `F` and `ε > 0` there is a finite tree of cuts from `F` whose
leaves have diameter below `ε`. The cuts are segments of a grid. By `no_cross`, cutting along the
long segments of one line leaves pieces that stay on one side of the line, up to a small margin
(`line_tree`). Doing this for each line of the grid gives pieces inside small squares.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Complex

local notation "𝕀" => unitInterval

/-- Disjoint segments of a line that lie inside `G` or outside it can be cut one after the other. -/
theorem tree_segments {ι : ℝ → ℂ} (hι : Isometry ι) (L : List (ℝ × ℝ)) :
    ∀ G : Set ℂ, Nonempty (Circle ≃ₜ G) → (∀ x ∈ L, x.1 < x.2) →
      L.Pairwise (fun x y => Disjoint (Ioo x.1 x.2) (Ioo y.1 y.2)) →
      (∀ x ∈ L, ι x.1 ∉ inner G ∧ ι x.2 ∉ inner G) →
      (∀ x ∈ L, ι '' Ioo x.1 x.2 ⊆ inner G ∨ Disjoint (ι '' Ioo x.1 x.2) (inner G)) →
      CutTree (fun U => ∀ x ∈ L, Disjoint (ι '' Ioo x.1 x.2) U) G := by
  induction L with
  | nil =>
    intro G _ _ _ _ _
    exact .leaf (by simp)
  | cons x L ih =>
    intro G hG hlt hpair hend hside
    obtain ⟨φ⟩ := id hG
    have J := isJordanParts φ
    have hanti : ∀ {U V : Set ℂ}, U ⊆ V → Disjoint (ι '' Ioo x.1 x.2) V →
        Disjoint (ι '' Ioo x.1 x.2) U := fun h hd => hd.mono_right h
    have hmap : ∀ {H : Set ℂ}, Nonempty (Circle ≃ₜ H) →
        CutTree (fun U => Disjoint (ι '' Ioo x.1 x.2) U ∧ ∀ y ∈ L, Disjoint (ι '' Ioo y.1 y.2) U) H
          →
        CutTree (fun U => ∀ y ∈ x :: L, Disjoint (ι '' Ioo y.1 y.2) U) H := fun hH t =>
      t.map hH fun H' _ hp y hy => by
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hp.1
        · exact hp.2 y hy
    have hxlt := hlt x (List.mem_cons_self)
    have hrest : ∀ y ∈ L, y ∈ x :: L := fun y hy => List.mem_cons_of_mem _ hy
    obtain ⟨hpx, hpL⟩ := List.pairwise_cons.mp hpair
    rcases hside x List.mem_cons_self with hin | hout
    · -- Cut along the segment.
      let e : 𝕀 → ℂ := fun s => ι (x.1 + (x.2 - x.1) * s)
      have hgap : 0 < x.2 - x.1 := by linarith [hxlt]
      have hec : Continuous e := hι.continuous.comp (by fun_prop)
      have hei : Function.Injective e := fun s s' h => by
        have h1 := hι.injective h
        exact Subtype.ext (mul_left_cancel₀ hgap.ne' (add_left_cancel h1))
      have he0 : e 0 = ι x.1 := by simp [e]
      have he1 : e 1 = ι x.2 := by simp [e]
      have hmemIcc : ∀ s : 𝕀, x.1 + (x.2 - x.1) * s ∈ Icc x.1 x.2 := fun s => by
        have h0 : 0 ≤ (s : ℝ) := s.2.1
        have h1 : (s : ℝ) ≤ 1 := s.2.2
        constructor <;> nlinarith
      have hrange : range e = ι '' Icc x.1 x.2 := by
        ext z
        constructor
        · rintro ⟨s, rfl⟩
          exact ⟨_, hmemIcc s, rfl⟩
        · rintro ⟨r, hr, rfl⟩
          refine ⟨⟨(r - x.1) / (x.2 - x.1), div_nonneg (by linarith [hr.1]) hgap.le,
            (div_le_one hgap).mpr (by linarith [hr.2])⟩, ?_⟩
          simp only [e]
          rw [mul_div_cancel₀ _ hgap.ne']
          congr 1
          ring
      have hend' : ∀ r ∈ Icc x.1 x.2, ι r ∉ inner G → ι r ∈ G := by
        intro r hr hrn
        have h3 : ι r ∈ closure (ι '' Ioo x.1 x.2) := by
          have h4 : r ∈ closure (Ioo x.1 x.2) := by rw [closure_Ioo hxlt.ne]; exact hr
          exact image_closure_subset_closure_image hι.continuous ⟨r, h4, rfl⟩
        have h6 := closure_mono hin h3
        rw [J.closure_inner] at h6
        exact h6.resolve_left hrn
      have hx12 := hend x List.mem_cons_self
      have h0G : e 0 ∈ G := he0 ▸ hend' _ ⟨le_rfl, hxlt.le⟩ hx12.1
      have h1G : e 1 ∈ G := he1 ▸ hend' _ ⟨hxlt.le, le_rfl⟩ hx12.2
      have hne : e 0 ≠ e 1 := fun h => by
        have := hei h
        exact absurd (congrArg Subtype.val this) (by simp)
      have hinside : ∀ s, s ≠ 0 → s ≠ 1 → e s ∈ inner G := by
        intro s h0 h1
        have h0' : (0 : ℝ) < s := lt_of_le_of_ne s.2.1 fun h => h0 (Subtype.ext h.symm)
        have h1' : (s : ℝ) < 1 := lt_of_le_of_ne s.2.2 fun h => h1 (Subtype.ext h)
        refine hin ⟨_, ⟨?_, ?_⟩, rfl⟩ <;> nlinarith
      obtain ⟨a, b, hc⟩ := exists_isCut φ ⟨hec, hei⟩ hne h0G h1G hinside
      have hT := hc.isTheta J
      have hsplit : ∀ y ∈ L, ι '' Ioo y.1 y.2 ⊆ inner G →
          ι '' Ioo y.1 y.2 ⊆ inner (side a e) ∨ ι '' Ioo y.1 y.2 ⊆ inner (side b e) := by
        intro y hy hyin
        have hdisj : Disjoint (ι '' Ioo y.1 y.2) (range e) := by
          rw [hrange]
          refine Set.disjoint_left.mpr ?_
          rintro _ ⟨r, hr, rfl⟩ ⟨r', hr', he⟩
          have hrr : r' = r := hι.injective he
          subst hrr
          rcases eq_or_lt_of_le hr'.1 with h | h
          · exact hx12.1 (h ▸ hyin ⟨_, hr, rfl⟩)
          · rcases eq_or_lt_of_le hr'.2 with h' | h'
            · exact hx12.2 (h' ▸ hyin ⟨_, hr, rfl⟩)
            · exact Set.disjoint_left.mp (hpx y hy) ⟨h, h'⟩ hr
        have hsub : ι '' Ioo y.1 y.2 ⊆ inner (side a e) ∪ inner (side b e) := by
          rw [← hT.inner_sdiff]
          exact fun z hz => ⟨hyin hz, Set.disjoint_left.mp hdisj hz⟩
        have hpre : IsPreconnected (ι '' Ioo y.1 y.2) :=
          isPreconnected_Ioo.image _ hι.continuous.continuousOn
        have hJa := hT.parts₁
        have hJb := hT.parts₂
        by_cases hemp : (ι '' Ioo y.1 y.2 ∩ inner (side a e)).Nonempty
        · exact Or.inl (hpre.subset_left_of_subset_union hJa.isOpen_inner hJb.isOpen_inner
            hT.disjoint_inner hsub hemp)
        · right
          intro z hz
          exact (hsub hz).resolve_left fun hz' => hemp ⟨z, hz, hz'⟩
      have hchild : ∀ {c : 𝕀 → ℂ} {d : 𝕀 → ℂ}, IsCut G c d e →
          (∀ y ∈ L, ι '' Ioo y.1 y.2 ⊆ inner G → ι '' Ioo y.1 y.2 ⊆ inner (side c e) ∨
            ι '' Ioo y.1 y.2 ⊆ inner (side d e)) →
          (Disjoint (inner (side c e)) (inner (side d e))) →
          CutTree (fun U => ∀ y ∈ x :: L, Disjoint (ι '' Ioo y.1 y.2) U) (side c e) := by
        intro c d hcd hsp hdj
        have hsub' := (hcd.inner_side_subset J).1
        have hoa := hcd.oArc_side
        have ht := ih (side c e) hoa (fun y hy => hlt y (hrest y hy)) hpL
          (fun y hy => ⟨fun h => (hend y (hrest y hy)).1 (hsub' h),
            fun h => (hend y (hrest y hy)).2 (hsub' h)⟩)
          (fun y hy => by
            rcases hside y (hrest y hy) with h | h
            · rcases hsp y hy h with h' | h'
              · exact Or.inl h'
              · right
                exact (Set.disjoint_of_subset_left h' hdj.symm)
            · exact Or.inr (h.mono_right hsub'))
        refine hmap hoa (ht.strengthen hanti hoa ?_)
        refine Set.disjoint_left.mpr fun z hz hzin => ?_
        have hzr : z ∈ range e := by
          rw [hrange]
          obtain ⟨r, hr, rfl⟩ := hz
          exact ⟨r, ⟨hr.1.le, hr.2.le⟩, rfl⟩
        exact hzin.1 (Or.inr hzr)
      refine .node hc (hchild hc hsplit hT.disjoint_inner)
        (hchild hc.symm (fun y hy h => (hsplit y hy h).symm) hT.disjoint_inner.symm)
    · have ht := ih G hG (fun y hy => hlt y (hrest y hy)) hpL (fun y hy => hend y (hrest y hy))
        (fun y hy => hside y (hrest y hy))
      exact hmap hG (ht.strengthen hanti hG hout)

/-- Cutting along the long segments of a line leaves pieces on one side of it, up to a margin. -/
theorem line_tree {F : Set ℂ} (φ : Circle ≃ₜ F) {ρ : ℝ} (hρ : 0 < ρ) {ι : ℝ → ℂ} (hι : Isometry ι)
    {ℓ : ℂ → ℝ} (hℓ : Continuous ℓ) {t : ℝ} (hline : ∀ z, ℓ z = t → z ∈ range ι)
    (hℓι : ∀ r, ℓ (ι r) = t) (hlip : ∀ z r, |ℓ z - t| ≤ dist z (ι r)) :
    CutTree (fun U => ∀ y₁ ∈ U, ∀ y₂ ∈ U, ℓ y₁ < t - ρ → ℓ y₂ ≤ t + ρ) F := by
  classical
  have J := isJordanParts φ
  obtain ⟨δ₀, hδ₀, hsmall⟩ := exists_small_arc φ hρ
  set δ := min δ₀ ρ with hδ
  have hδpos : 0 < δ := lt_min hδ₀ hρ
  set V := ι ⁻¹' inner F with hV
  have hVb : Bornology.IsBounded V := by
    obtain ⟨R, hR⟩ := J.isBounded_inner.subset_ball 0
    refine (Metric.isBounded_closedBall (x := (0 : ℝ)) (r := R + ‖ι 0‖)).subset fun r hr => ?_
    have h3 : ‖ι r‖ < R := mem_ball_zero_iff.mp (hR hr)
    have h4 := norm_sub_le (ι r) (ι 0)
    rw [← dist_eq_norm, hι.dist_eq, Real.dist_eq, sub_zero] at h4
    rw [mem_closedBall, Real.dist_eq, sub_zero]
    linarith
  obtain ⟨N, hN⟩ := hVb.subset_closedBall 0
  let C : Set (ℝ × ℝ) := {x | Ioo x.1 x.2 ⊆ V ∧ x.1 ∉ V ∧ x.2 ∉ V ∧ δ ≤ x.2 - x.1}
  let κ : ℝ × ℝ → ℤ := fun x => ⌊2 * x.1 / δ⌋ + 1
  have hpoint : ∀ x ∈ C, (κ x : ℝ) * δ / 2 ∈ Ioo x.1 x.2 := by
    intro x hx
    have h1 := Int.floor_le (2 * x.1 / δ)
    have h2 := Int.lt_floor_add_one (2 * x.1 / δ)
    have h3 : (⌊2 * x.1 / δ⌋ : ℝ) * δ ≤ 2 * x.1 := by
      rwa [le_div_iff₀ hδpos] at h1
    have h4 : 2 * x.1 < ((⌊2 * x.1 / δ⌋ : ℝ) + 1) * δ := by
      rwa [div_lt_iff₀ hδpos] at h2
    have h5 := hx.2.2.2
    simp only [κ]
    push_cast
    constructor <;> nlinarith
  have hfin : C.Finite := by
    set K : ℤ := ⌈2 * N / δ⌉ + 1 with hK
    refine Set.Finite.of_injOn (f := κ) (t := Icc (-K) K) ?_ ?_ (Set.finite_Icc _ _)
    · intro x hx
      have h1 : (κ x : ℝ) * δ / 2 ∈ V := hx.1 (hpoint x hx)
      have h2 := hN h1
      rw [mem_closedBall, Real.dist_eq, sub_zero] at h2
      have h3 := abs_le.mp h2
      have h4 := Int.le_ceil (2 * N / δ)
      have h5 : 2 * N ≤ (⌈2 * N / δ⌉ : ℝ) * δ := by rwa [div_le_iff₀ hδpos] at h4
      have h6 : (κ x : ℝ) ≤ K := by
        have : (κ x : ℝ) * δ ≤ (K : ℝ) * δ := by
          rw [hK]
          push_cast
          nlinarith [h3.2]
        exact le_of_mul_le_mul_right this hδpos
      have h7 : (-K : ℝ) ≤ κ x := by
        have : (-(K : ℝ)) * δ ≤ (κ x : ℝ) * δ := by
          rw [hK]
          push_cast
          nlinarith [h3.1]
        exact le_of_mul_le_mul_right this hδpos
      exact ⟨by exact_mod_cast h7, by exact_mod_cast h6⟩
    · intro x hx y hy hxy
      have hp := hpoint x hx
      have hp' := hpoint y hy
      rw [show (κ x : ℝ) = κ y by rw [hxy]] at hp
      obtain ⟨h1, h2⟩ := interval_unique hx.1 hy.1 hx.2.1 hx.2.2.1 hy.2.1 hy.2.2.1 hp hp'
      exact Prod.ext h1 h2
  let L : List (ℝ × ℝ) := hfin.toFinset.toList
  have hL : ∀ x, x ∈ L ↔ x ∈ C := fun x => by simp [L]
  have hlt : ∀ x ∈ L, x.1 < x.2 := fun x hx => by
    have := ((hL x).mp hx).2.2.2
    linarith
  have hpair : L.Pairwise (fun x y => Disjoint (Ioo x.1 x.2) (Ioo y.1 y.2)) := by
    refine (hfin.toFinset.nodup_toList).imp_of_mem ?_
    intro x y hx hy hne
    have hx' := (hL x).mp hx
    have hy' := (hL y).mp hy
    refine Set.disjoint_left.mpr fun r h1 h2 => hne ?_
    obtain ⟨h3, h4⟩ := interval_unique hx'.1 hy'.1 hx'.2.1 hx'.2.2.1 hy'.2.1 hy'.2.2.1 h1 h2
    exact Prod.ext h3 h4
  have ht := tree_segments hι L F ⟨φ⟩ hlt hpair
    (fun x hx => ⟨((hL x).mp hx).2.1, ((hL x).mp hx).2.2.1⟩)
    (fun x hx => Or.inl (image_subset_iff.mpr ((hL x).mp hx).1))
  have hanti : ∀ {U W : Set ℂ}, U ⊆ W → W ⊆ inner F → U ⊆ inner F := fun h h' => h.trans h'
  refine (ht.strengthen hanti ⟨φ⟩ Subset.rfl).map ⟨φ⟩ fun G hG hp y₁ hy₁ y₂ hy₂ h1 => ?_
  obtain ⟨ψ⟩ := hG
  by_contra hc
  rw [not_le] at hc
  refine no_cross φ hρ (min_le_right _ _) (fun u hu v hv huv => hsmall u hu v hv
    (lt_of_lt_of_le huv (min_le_left _ _))) hι hℓ hline hℓι hlip
    (isJordanParts ψ).isConnected_inner.isPreconnected hp.1 ?_ hy₁ hy₂ h1 hc
  intro a b hsub ha hb hl r hr hrG
  have hx : (a, b) ∈ L := (hL _).mpr ⟨hsub, ha, hb, hl⟩
  exact Set.disjoint_left.mp (hp.2 _ hx) ⟨r, hr, rfl⟩ hrG

/-- The two kinds of lines of the grid. -/
private def lineMap (b : Bool) (t r : ℝ) : ℂ := if b then ⟨t, r⟩ else ⟨r, t⟩

private def lineCoord (b : Bool) (z : ℂ) : ℝ := if b then z.re else z.im

private theorem isometry_lineMap (b : Bool) (t : ℝ) : Isometry (lineMap b t) := by
  refine Isometry.of_dist_eq fun r s => ?_
  cases b
  · simp only [lineMap, Bool.false_eq_true, ite_false]
    exact Complex.dist_of_im_eq (z := ⟨r, t⟩) (w := ⟨s, t⟩) rfl
  · simp only [lineMap, ite_true]
    exact Complex.dist_of_re_eq (z := ⟨t, r⟩) (w := ⟨t, s⟩) rfl

private theorem lineCoord_lip (b : Bool) (t : ℝ) (z : ℂ) (r : ℝ) :
    |lineCoord b z - t| ≤ dist z (lineMap b t r) := by
  rw [dist_eq_norm]
  cases b
  · simpa [lineCoord, lineMap] using Complex.abs_im_le_norm (z - ⟨r, t⟩)
  · simpa [lineCoord, lineMap] using Complex.abs_re_le_norm (z - ⟨t, r⟩)

private theorem tree_lines (ρ : ℝ) (hρ : 0 < ρ) (Ls : List (Bool × ℝ)) :
    ∀ G : Set ℂ, Nonempty (Circle ≃ₜ G) → CutTree (fun U => ∀ p ∈ Ls, ∀ y₁ ∈ U, ∀ y₂ ∈ U,
      lineCoord p.1 y₁ < p.2 - ρ → lineCoord p.1 y₂ ≤ p.2 + ρ) G := by
  induction Ls with
  | nil =>
    intro G _
    exact .leaf (by simp)
  | cons p Ls ih =>
    intro G hG
    obtain ⟨φ⟩ := id hG
    have hc : Continuous (lineCoord p.1) := by
      cases hb : p.1
      · exact Complex.continuous_im
      · exact Complex.continuous_re
    have ht := line_tree (t := p.2) φ hρ (isometry_lineMap p.1 p.2) hc
      (fun z hz => by
        cases hb : p.1
        · simp only [hb, lineCoord, Bool.false_eq_true, ite_false] at hz
          refine ⟨z.re, ?_⟩
          simp only [lineMap, Bool.false_eq_true, ite_false]
          exact Complex.ext rfl hz.symm
        · simp only [hb, lineCoord, ite_true] at hz
          refine ⟨z.im, ?_⟩
          simp only [lineMap, ite_true]
          exact Complex.ext hz.symm rfl)
      (fun r => by
        cases hb : p.1 <;> simp [lineCoord, lineMap])
      (lineCoord_lip p.1 p.2)
    have hbound := ht.bind (P := fun U => ∀ p ∈ Ls, ∀ y₁ ∈ U, ∀ y₂ ∈ U,
      lineCoord p.1 y₁ < p.2 - ρ → lineCoord p.1 y₂ ≤ p.2 + ρ)
      (fun h hq y₁ h1 y₂ h2 => hq y₁ (h h1) y₂ (h h2)) hG ih
    refine hbound.map hG fun H _ hp q hq => ?_
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hp.1
    · exact hp.2 q hq

/-- **Small pieces.** Every Jordan domain can be cut into pieces of diameter below `ε` by a finite
tree of cuts. -/
theorem cutTree_small {F : Set ℂ} (hF : Nonempty (Circle ≃ₜ F)) {ε : ℝ} (hε : 0 < ε) :
    CutTree (fun U => ∀ x ∈ U, ∀ y ∈ U, dist x y < ε) F := by
  classical
  obtain ⟨φ⟩ := id hF
  have J := isJordanParts φ
  obtain ⟨R, hR⟩ := J.isBounded_inner.subset_ball 0
  set η := ε / 8 with hη
  have hηpos : 0 < η := by positivity
  set K : ℤ := ⌈R / η⌉ + 3 with hK
  let Ls : List (Bool × ℝ) := (Finset.Icc (-K) K).toList.flatMap fun k =>
    [(true, (k : ℝ) * η), (false, (k : ℝ) * η)]
  have hLs : ∀ (b : Bool) (k : ℤ), k ∈ Icc (-K) K → (b, (k : ℝ) * η) ∈ Ls := by
    intro b k hk
    refine List.mem_flatMap.mpr ⟨k, by simpa using hk, ?_⟩
    cases b <;> simp
  have ht := tree_lines η hηpos Ls F hF
  refine ((ht.strengthen (Q := fun U => U ⊆ inner F) (fun h h' => h.trans h') hF
    Subset.rfl)).map hF fun G _ hp x hx y hy => ?_
  -- In each direction the two points are close.
  have hclose : ∀ (b : Bool) (x y : ℂ), x ∈ inner G → y ∈ inner G →
      lineCoord b y - lineCoord b x ≤ 3 * η := by
    intro b x y hx hy
    by_contra hc
    rw [not_le] at hc
    set A := lineCoord b x with hA
    have hxn : ‖x‖ < R := mem_ball_zero_iff.mp (hR (hp.1 hx))
    have hAabs : |A| < R := by
      refine lt_of_le_of_lt ?_ hxn
      cases b
      · exact Complex.abs_im_le_norm x
      · exact Complex.abs_re_le_norm x
    set k : ℤ := ⌊(A + η) / η⌋ + 1 with hkdef
    have h1 := Int.floor_le ((A + η) / η)
    have h2 := Int.lt_floor_add_one ((A + η) / η)
    have h3 : (⌊(A + η) / η⌋ : ℝ) * η ≤ A + η := by rwa [le_div_iff₀ hηpos] at h1
    have h4 : A + η < ((⌊(A + η) / η⌋ : ℝ) + 1) * η := by rwa [div_lt_iff₀ hηpos] at h2
    have hkc : (k : ℝ) = (⌊(A + η) / η⌋ : ℝ) + 1 := by rw [hkdef]; push_cast; ring
    have h5 : A + η < (k : ℝ) * η := by rw [hkc]; exact h4
    have h6 : (k : ℝ) * η ≤ A + 2 * η := by rw [hkc]; nlinarith
    have hRK := Int.le_ceil (R / η)
    have hRK' : R ≤ (⌈R / η⌉ : ℝ) * η := by rwa [div_le_iff₀ hηpos] at hRK
    have hKη : (K : ℝ) * η = (⌈R / η⌉ : ℝ) * η + 3 * η := by rw [hK]; push_cast; ring
    have hAb := abs_lt.mp hAabs
    have hkU : k ≤ K := by
      have : (k : ℝ) * η ≤ (K : ℝ) * η := by rw [hKη]; linarith [hAb.2]
      exact_mod_cast le_of_mul_le_mul_right this hηpos
    have hkL : -K ≤ k := by
      have : (-(K : ℝ)) * η ≤ (k : ℝ) * η := by
        have : (-(K : ℝ)) * η = -((K : ℝ) * η) := by ring
        rw [this, hKη]
        linarith [hAb.1]
      exact_mod_cast le_of_mul_le_mul_right this hηpos
    have hkey := hp.2 (b, (k : ℝ) * η) (hLs b k ⟨hkL, hkU⟩) x hx y hy (by simp only; linarith)
    simp only at hkey
    linarith
  have hre : |x.re - y.re| ≤ 3 * η := abs_le.mpr ⟨by
    have := hclose true x y hx hy
    simp only [lineCoord, ite_true] at this
    linarith, by
    have := hclose true y x hy hx
    simp only [lineCoord, ite_true] at this
    linarith⟩
  have him : |x.im - y.im| ≤ 3 * η := abs_le.mpr ⟨by
    have := hclose false x y hx hy
    simp only [lineCoord, Bool.false_eq_true, ite_false] at this
    linarith, by
    have := hclose false y x hy hx
    simp only [lineCoord, Bool.false_eq_true, ite_false] at this
    linarith⟩
  rw [dist_eq_norm]
  have hn := Complex.norm_le_abs_re_add_abs_im (x - y)
  simp only [Complex.sub_re, Complex.sub_im] at hn
  rw [hη] at hre him
  linarith

end GraphMinor.Surface
