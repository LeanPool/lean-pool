/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.NetSwapBoundary
public import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.Surface.CutLift
import LeanPool.GraphMinor.Surface.Fan
import LeanPool.GraphMinor.Surface.PlaneDisc
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# A disc beside a cap

Page 228 of VII (4.6). A circle `A` bounds a disc `R` that contains a cap `E`, and `B` is an arc of
`A` that meets `E` only in its ends. Then `B` and one arc of `bd(E)` bound a disc that misses the
inside of `E`. To see this, we cut `R` and `E` along one chord of `E` between the ends of `B`.
-/

public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface

universe u

variable {T : Type u} [TopologicalSpace T]

/-- Two points of the boundary of a closed disc are joined by a chord. We pull the chord back from
the unit disc, since `Surface.exists_chord` is stated for spaces in the lowest universe. -/
theorem exists_disc_chord [T2Space T] {E : Set T} (hE : IsClosedDisc E) {a b : T}
    (ha : a ∈ discBd E) (hb : b ∈ discBd E) (hab : a ≠ b) :
    ∃ c, IsLineWithEnds c a b ∧ c ⊆ E ∧ c ∩ discBd E = {a, b} := by
  obtain ⟨eE⟩ := hE
  let B : Set ℂ := Metric.closedBall (0 : ℂ) 1
  obtain ⟨e₀⟩ := (isClosedDisc_closedBall.1 : IsClosedDisc B)
  let e : B ≃ₜ E := e₀.symm.trans eE
  have hb₀ : ∀ z : B, (e z).1 ∈ discBd E ↔ z.1 ∈ discBd B := by
    intro z
    have h := image_bd_homeomorph e
    constructor
    · rintro ⟨w, hw, hwz⟩
      have hw' : w ∈ e '' bd B := h ▸ hw
      obtain ⟨y, hy, rfl⟩ := hw'
      exact ⟨y, hy, by rw [e.injective (Subtype.ext hwz)]⟩
    · rintro ⟨w, hw, hwz⟩
      have hzw : z = w := Subtype.ext hwz.symm
      exact ⟨e z, h ▸ mem_image_of_mem e (hzw ▸ hw), rfl⟩
  have hbE : ∀ {p : T}, p ∈ discBd E → ∃ z : B, z.1 ∈ discBd B ∧ (e z).1 = p := by
    intro p hp
    obtain ⟨q, _, rfl⟩ := hp
    have hq : ∃ q' : E, q'.1 = q.1 := ⟨q, rfl⟩
    refine ⟨e.symm q, ?_, by simp⟩
    rw [← hb₀, e.apply_symm_apply]
    exact ⟨q, by assumption, rfl⟩
  obtain ⟨za, hza, hea⟩ := hbE ha
  obtain ⟨zb, hzb, heb⟩ := hbE hb
  have hne : za.1 ≠ zb.1 := fun h => hab (by rw [← hea, ← heb, Subtype.ext h])
  obtain ⟨F₀, hF₀, hsub, hcap⟩ := Surface.exists_chord (Δ := B) isClosedDisc_closedBall.1 hza hzb
    hne
  obtain ⟨k, hk, hkr, hk0, hk1⟩ := hF₀.exists_arc
  have hkB : ∀ t, k t ∈ B := fun t => hsub (hkr ▸ mem_range_self t)
  let k' : unitInterval → T := fun t => (e ⟨k t, hkB t⟩).1
  have hk' : IsArcMap k' := ⟨continuous_subtype_val.comp (e.continuous.comp
    (hk.1.subtype_mk hkB)), fun x y h => hk.2 (congrArg Subtype.val (e.injective (Subtype.ext h)))⟩
  have h0 : k' 0 = a := by
    change (e ⟨k 0, _⟩).1 = a
    rw [show (⟨k 0, hkB 0⟩ : B) = za from Subtype.ext hk0, hea]
  have h1 : k' 1 = b := by
    change (e ⟨k 1, _⟩).1 = b
    rw [show (⟨k 1, hkB 1⟩ : B) = zb from Subtype.ext hk1, heb]
  refine ⟨range k', by simpa only [h0, h1] using hk'.isLineWithEnds, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact (e ⟨k t, hkB t⟩).2
  ext x
  constructor
  · rintro ⟨⟨t, rfl⟩, hx⟩
    have hb' : k t ∈ F₀ ∩ discBd B := ⟨hkr ▸ mem_range_self t, (hb₀ ⟨k t, hkB t⟩).mp hx⟩
    rw [hcap] at hb'
    rcases hb' with h | h
    · refine Or.inl ?_
      change (e ⟨k t, hkB t⟩).1 = a
      rw [show (⟨k t, hkB t⟩ : B) = za from Subtype.ext h, hea]
    · refine Or.inr ?_
      change (e ⟨k t, hkB t⟩).1 = b
      rw [show (⟨k t, hkB t⟩ : B) = zb from Subtype.ext h, heb]
  · rintro (rfl | hx)
    · exact ⟨h0 ▸ mem_range_self 0, ha⟩
    · rw [mem_singleton_iff.mp hx]
      exact ⟨h1 ▸ mem_range_self 1, hb⟩

/-- A line has a point other than its two ends. -/
theorem exists_mem_line_ne {a b : T} {c : Set T} (hc : IsLineWithEnds c a b) (_hab : a ≠ b) :
    ∃ p ∈ c, p ≠ a ∧ p ≠ b := by
  obtain ⟨f, f0, f1⟩ := hc
  let m : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  refine ⟨(f m).1, (f m).2, ?_, ?_⟩
  · intro h
    have : f m = f 0 := Subtype.ext (h.trans f0.symm)
    have h2 := congrArg Subtype.val (f.injective this)
    norm_num [m] at h2
  · intro h
    have : f m = f 1 := Subtype.ext (h.trans f1.symm)
    have h2 := congrArg Subtype.val (f.injective this)
    norm_num [m] at h2

private theorem beside_cap_aux [T2Space T] (hman : ∀ x : T, IsManifoldPoint x)
    {R E B c Δ₁ Q D₁ D₂ L L' : Set T} {a b : T} (hab : a ≠ b)
    (hB : IsLineWithEnds B a b) (hBE : B ∩ E ⊆ {a, b})
    (hc : IsLineWithEnds c a b) (hcE : c ⊆ E) (hcbd : c ∩ discBd E = {a, b})
    (hΔ₁ : IsClosedDisc Δ₁) (hbΔ₁ : discBd Δ₁ = B ∪ c)
    (hQΔ : Q ∩ Δ₁ ⊆ c) (hbdR : discBd R = B ∪ Q)
    (hD₂ : IsClosedDisc D₂) (hDu : D₁ ∪ D₂ = E)
    (hb₁ : discBd D₁ = L' ∪ c) (hb₂ : discBd D₂ = L ∪ c)
    (hL : IsLineWithEnds L a b) (hLE : L ⊆ discBd E) (hL'E : L' ⊆ discBd E)
    (hint₂ : discInt D₂ ⊆ discInt E)
    (hin : discInt D₂ ⊆ discInt Δ₁) (hout : Disjoint (discInt D₁) Δ₁) :
    ∃ Z, IsClosedDisc Z ∧ discBd Z = L ∪ B ∧ Disjoint Z (discInt E) ∧
      Disjoint (L \ {a, b}) (discBd R) := by
  obtain ⟨k, hk, hkr, hk0, hk1⟩ := hB.exists_arc
  subst hkr
  subst hk0 hk1
  have hcl : IsClosed Δ₁ := hΔ₁.isClosed
  have hD₂Δ : D₂ ⊆ Δ₁ := hD₂.subset_closure_discInt.trans
    (closure_minimal (hin.trans (discInt_subset _)) hcl)
  have hLD₂ : L ⊆ D₂ := fun x hx => discBd_subset _ (hb₂ ▸ .inl hx)
  have hLΔ : L ⊆ Δ₁ := hLD₂.trans hD₂Δ
  have hends : ({k 0, k 1} : Set T) ⊆ L ∧ ({k 0, k 1} : Set T) ⊆ discBd Δ₁ := by
    constructor
    · rintro x (rfl | hx)
      · exact hL.left_mem
      · exact (mem_singleton_iff.mp hx) ▸ hL.right_mem
    · rintro x (rfl | hx)
      · exact hbΔ₁ ▸ .inr hc.left_mem
      · exact hbΔ₁ ▸ .inr ((mem_singleton_iff.mp hx) ▸ hc.right_mem)
  have hLbd : L ∩ discBd Δ₁ = {k 0, k 1} := by
    apply Subset.antisymm
    · rintro x ⟨hxL, hxb⟩
      rw [hbΔ₁] at hxb
      rcases hxb with h | h
      · exact hBE ⟨h, discBd_subset _ (hLE hxL)⟩
      · exact hcbd ▸ ⟨h, hLE hxL⟩
    · exact fun x hx => ⟨hends.1 hx, hends.2 hx⟩
  obtain ⟨C', Z, Y, hC', hcov, hZ, hY, hZY, hZYi, hbZ, hbY, hrest⟩ :=
    exists_disc_cut_with_boundary_arc hΔ₁ k hk (hbΔ₁ ▸ subset_union_left) hL hLΔ hLbd
  have hinner : ∀ x ∈ c, x ≠ k 0 → x ≠ k 1 → x ∉ discBd E := fun x hx h0 h1 hxb => by
    have : x ∈ c ∩ discBd E := ⟨hx, hxb⟩
    rw [hcbd] at this
    rcases this with h | h
    · exact h0 h
    · exact h1 h
  have hcZ : ∀ x ∈ c, x ≠ k 0 → x ≠ k 1 → x ∉ Z := by
    intro x hx h0 h1 hxZ
    have hxY : x ∈ Y := by
      apply hrest
      refine ⟨hbΔ₁ ▸ .inr hx, ?_⟩
      intro hxr
      rcases hBE ⟨hxr, hcE hx⟩ with h | h
      · exact h0 h
      · exact h1 h
    have hxL : x ∈ L := hZYi ▸ ⟨hxZ, hxY⟩
    exact hinner x hx h0 h1 (hLE hxL)
  have hBint : ∀ x ∈ discInt E, x ∉ range k := by
    intro x hx hxB
    rcases hBE ⟨hxB, hx.1⟩ with h | h
    · exact hx.2 (hcbd.symm.subset (.inl h)).2
    · exact hx.2 (hcbd.symm.subset (.inr h)).2
  have hZD₂ : Disjoint (discInt D₂) Z := by
    have hdis : Disjoint (discInt D₂) (discBd Z) := by
      rw [disjoint_left, hbZ]
      rintro x hx (h | h)
      · exact hBint x (hint₂ hx) h
      · exact hx.2 (hb₂ ▸ .inl h)
    rcases hZ.side hman hD₂.isPreconnected_discInt hdis with hsub | h
    · exfalso
      obtain ⟨p, hp, hp0, hp1⟩ := exists_mem_line_ne hc hab
      have hpD : p ∈ D₂ := discBd_subset _ (hb₂ ▸ .inr hp)
      have : D₂ ⊆ Z := hD₂.subset_closure_discInt.trans
        (closure_minimal (hsub.trans (discInt_subset _)) hZ.isClosed)
      exact hcZ p hp hp0 hp1 (this hpD)
    · exact h
  have hZΔ : Z ⊆ Δ₁ := hZY ▸ subset_union_left
  refine ⟨Z, hZ, ?_, ?_, ?_⟩
  · rw [hbZ, union_comm]
  · rw [disjoint_right]
    intro x hx hxZ
    have hxE : x ∈ D₁ ∪ D₂ := hDu ▸ hx.1
    have hnc : x ∈ c → False := fun hxc => by
      refine hcZ x hxc ?_ ?_ hxZ
      · rintro rfl
        exact hx.2 (hcbd.symm.subset (.inl rfl)).2
      · rintro rfl
        exact hx.2 (hcbd.symm.subset (.inr rfl)).2
    rcases hxE with h | h
    · by_cases hb : x ∈ discBd D₁
      · rcases hb₁ ▸ hb with h' | h'
        · exact hx.2 (hL'E h')
        · exact hnc h'
      · exact disjoint_left.mp hout ⟨h, hb⟩ (hZΔ hxZ)
    · by_cases hb : x ∈ discBd D₂
      · rcases hb₂ ▸ hb with h' | h'
        · exact hx.2 (hLE h')
        · exact hnc h'
      · exact disjoint_left.mp hZD₂ ⟨h, hb⟩ hxZ
  · rw [disjoint_left]
    rintro x ⟨hxL, hxe⟩ hxb
    rw [hbdR] at hxb
    rcases hxb with h | h
    · exact hxe (hBE ⟨h, discBd_subset _ (hLE hxL)⟩)
    · have hxc : x ∈ c := hQΔ ⟨h, hLΔ hxL⟩
      exact hxe (hcbd ▸ ⟨hxc, hLE hxL⟩)

/-- The disc beside a cap, on page 228 of VII (4.6). The disc `R` contains the disc `E`, and `B` is
an arc of `bd(R)` that meets `E` only in its ends. Then one arc `C` of `bd(E)` with the same ends
as `B` bounds, with `B`, a disc that misses the inside of `E`, and the inside of `C` misses
`bd(R)`. -/
theorem exists_disc_beside_cap [T2Space T] (hman : ∀ x : T, IsManifoldPoint x)
    {R E B : Set T} {a b : T} (hab : a ≠ b) (hR : IsClosedDisc R) (hE : IsClosedDisc E)
    (hER : E ⊆ R) (hEB : Disjoint (discInt E) (discBd R)) (hB : IsLineWithEnds B a b)
    (hBR : B ⊆ discBd R) (hBE : B ∩ E ⊆ {a, b}) (ha : a ∈ discBd E) (hb : b ∈ discBd E) :
    ∃ Z C, IsLineWithEnds C a b ∧ C ⊆ discBd E ∧ IsClosedDisc Z ∧ discBd Z = C ∪ B ∧
      Disjoint Z (discInt E) ∧ Disjoint (C \ {a, b}) (discBd R) := by
  obtain ⟨c, hc, hcE, hcbd⟩ := exists_disc_chord hE ha hb hab
  have hbdc : ∀ x ∈ c, x ≠ a → x ≠ b → x ∈ discInt E := fun x hx h0 h1 =>
    ⟨hcE hx, fun hxb => by
      have : x ∈ c ∩ discBd E := ⟨hx, hxb⟩
      rw [hcbd] at this
      rcases this with h | h
      · exact h0 h
      · exact h1 h⟩
  have hBa : a ∈ discBd R := hBR hB.left_mem
  have hBb : b ∈ discBd R := hBR hB.right_mem
  have hcR : c ∩ discBd R = {a, b} := by
    apply Subset.antisymm
    · rintro x ⟨hxc, hxb⟩
      by_contra hn
      have h0 : x ≠ a := fun h => hn (.inl h)
      have h1 : x ≠ b := fun h => hn (.inr h)
      exact disjoint_left.mp hEB (hbdc x hxc h0 h1) hxb
    · rintro x (rfl | hx)
      · exact ⟨hc.left_mem, hBa⟩
      · rw [mem_singleton_iff.mp hx]
        exact ⟨hc.right_mem, hBb⟩
  obtain ⟨k, hk, hkr, hk0, hk1⟩ := hB.exists_arc
  obtain ⟨Q, Δ₁, Δ₂, hQ, hcov, hd₁, hd₂, hu, hi, hb₁, hb₂, hrest⟩ :=
    exists_disc_cut_with_boundary_arc hR k hk (hkr ▸ hBR) (hk0 ▸ hk1 ▸ hc)
      (hcE.trans hER) (hk0 ▸ hk1 ▸ hcR)
  rw [hkr] at hcov hb₁
  rw [hk0, hk1] at hQ
  obtain ⟨P, P', hP, hP', hPu, hPi⟩ := IsOArc.lines hE.isOArc_discBd ha hb hab
  obtain ⟨k', hk', hkr', hk0', hk1'⟩ := hP.exists_arc
  obtain ⟨P₂, D₁, D₂, hP₂, hcovE, hD₁, hD₂, huE, hiE, hbD₁, hbD₂, -⟩ :=
    exists_disc_cut_with_boundary_arc hE k' hk' (hkr' ▸ hPu ▸ subset_union_left)
      (hk0' ▸ hk1' ▸ hc) hcE (hk0' ▸ hk1' ▸ hcbd)
  rw [hkr'] at hcovE hbD₁
  rw [hk0', hk1'] at hP₂
  have hP₁E : P ⊆ discBd E := hcovE ▸ subset_union_left
  have hP₂E : P₂ ⊆ discBd E := hcovE ▸ subset_union_right
  have hint₁ : discInt D₁ ⊆ discInt E := by
    intro x hx
    refine ⟨huE ▸ .inl hx.1, ?_⟩
    intro hxb
    rcases hcovE ▸ hxb with h | h
    · exact hx.2 (hbD₁ ▸ .inl h)
    · have hx2 : x ∈ D₂ := discBd_subset _ (hbD₂ ▸ .inl h)
      exact hx.2 (hbD₁ ▸ .inr (hiE ▸ ⟨hx.1, hx2⟩))
  have hint₂ : discInt D₂ ⊆ discInt E := by
    intro x hx
    refine ⟨huE ▸ .inr hx.1, ?_⟩
    intro hxb
    rcases hcovE ▸ hxb with h | h
    · have hx1 : x ∈ D₁ := discBd_subset _ (hbD₁ ▸ .inl h)
      exact hx.2 (hbD₂ ▸ .inr (hiE ▸ ⟨hx1, hx.1⟩))
    · exact hx.2 (hbD₂ ▸ .inl h)
  have hBint : ∀ x ∈ discInt E, x ∉ B := by
    intro x hx hxB
    rcases hBE ⟨hxB, hx.1⟩ with h | h
    · exact hx.2 (h ▸ ha)
    · exact hx.2 ((mem_singleton_iff.mp h) ▸ hb)
  have hside : ∀ {X L₀ : Set T}, IsClosedDisc X → discInt X ⊆ discInt E →
      discBd X = L₀ ∪ c → discInt X ⊆ discInt Δ₁ ∨ Disjoint (discInt X) Δ₁ := by
    intro X L₀ hX hXi hXb
    refine hd₁.side hman hX.isPreconnected_discInt ?_
    rw [disjoint_left, hb₁]
    rintro x hx (h | h)
    · exact hBint x (hXi hx) h
    · exact hx.2 (hXb ▸ .inr h)
  obtain ⟨p, hp, hp0, hp1⟩ := exists_mem_line_ne hc hab
  have hpE : p ∈ discInt E := hbdc p hp hp0 hp1
  have hopen : IsOpen (discInt E) := hE.isOpen_discInt hman
  have hpick : ∀ {W : Set T} (hW : IsClosedDisc W), p ∈ W →
      ∃ y ∈ discInt W, y ∈ discInt E := by
    intro W hW hpW
    have := hW.subset_closure_discInt hpW
    obtain ⟨y, hy, hyW⟩ := mem_closure_iff.mp this _ hopen hpE
    exact ⟨y, hyW, hy⟩
  have hsplit : ∀ {W L₀ : Set T}, IsClosedDisc W → c ⊆ discBd W → ∀ y ∈ discInt W,
      y ∈ discInt E → y ∈ discInt D₁ ∨ y ∈ discInt D₂ := by
    intro W L₀ hW hcW y hyW hyE
    have hyc : y ∉ c := fun h => hyW.2 (hcW h)
    rcases (huE ▸ hyE.1 : y ∈ D₁ ∪ D₂) with h | h
    · refine .inl ⟨h, fun hb' => ?_⟩
      rcases hbD₁ ▸ hb' with h' | h'
      · exact hyE.2 (hP₁E h')
      · exact hyc h'
    · refine .inr ⟨h, fun hb' => ?_⟩
      rcases hbD₂ ▸ hb' with h' | h'
      · exact hyE.2 (hP₂E h')
      · exact hyc h'
  have hc₁ : c ⊆ discBd Δ₁ := hb₁ ▸ subset_union_right
  have hc₂ : c ⊆ discBd Δ₂ := hb₂ ▸ subset_union_right
  obtain ⟨y₁, hy₁, hy₁E⟩ := hpick hd₁ (discBd_subset _ (hc₁ hp))
  obtain ⟨y₂, hy₂, hy₂E⟩ := hpick hd₂ (discBd_subset _ (hc₂ hp))
  have hoff : ∀ y ∈ discInt Δ₂, y ∉ Δ₁ := fun y hy hy' => hy.2 (hc₂ (hi ▸ ⟨hy', hy.1⟩))
  have hy₁s := hsplit (L₀ := B) hd₁ hc₁ y₁ hy₁ hy₁E
  have hy₂s := hsplit (L₀ := B) hd₂ hc₂ y₂ hy₂ hy₂E
  have hQΔ : Q ∩ Δ₁ ⊆ c := fun x hx => hi ▸ ⟨hx.2, discBd_subset _ (hb₂ ▸ .inl hx.1)⟩
  have hbdR : discBd R = B ∪ Q := hcov.symm
  have hs₁ := hside hD₁ hint₁ hbD₁
  have hs₂ := hside hD₂ hint₂ hbD₂
  have hcase : (discInt D₂ ⊆ discInt Δ₁ ∧ Disjoint (discInt D₁) Δ₁) ∨
      (discInt D₁ ⊆ discInt Δ₁ ∧ Disjoint (discInt D₂) Δ₁) := by
    rcases hs₁ with h₁ | h₁ <;> rcases hs₂ with h₂ | h₂
    · exfalso
      rcases hy₂s with h | h
      · exact hoff y₂ hy₂ (discInt_subset _ (h₁ h))
      · exact hoff y₂ hy₂ (discInt_subset _ (h₂ h))
    · exact .inr ⟨h₁, h₂⟩
    · exact .inl ⟨h₂, h₁⟩
    · exfalso
      rcases hy₁s with h | h
      · exact disjoint_left.mp h₁ h hy₁.1
      · exact disjoint_left.mp h₂ h hy₁.1
  rcases hcase with ⟨hin, hout⟩ | ⟨hin, hout⟩
  · obtain ⟨Z, hZ, hbZ, hZE, hoffR⟩ := beside_cap_aux hman hab hB hBE hc hcE hcbd hd₁ hb₁
      hQΔ hbdR hD₂ huE hbD₁ hbD₂ hP₂ hP₂E hP₁E hint₂ hin hout
    exact ⟨Z, P₂, hP₂, hP₂E, hZ, hbZ, hZE, hoffR⟩
  · obtain ⟨Z, hZ, hbZ, hZE, hoffR⟩ := beside_cap_aux hman hab hB hBE hc hcE hcbd hd₁ hb₁
      hQΔ hbdR hD₁ (by rwa [union_comm]) hbD₂ hbD₁ hP hP₁E hP₂E hint₁ hin hout
    exact ⟨Z, P, hP, hP₁E, hZ, hbZ, hZE, hoffR⟩

end GraphMinor.GM07
