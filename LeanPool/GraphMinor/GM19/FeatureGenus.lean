/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FeatureCover

/-!
# The pieces of a cut surface are no more complicated than the surface

Let `ψ` map `Y` onto `S`, and suppose that `ψ` is one to one off the boundary of `Y`. A clopen part
`W` of `Y` is a model surface
`Σ(a, b, c)`. Each choice of values in `ℤ/2` on the `2a + b` loops of `W` gives a class on `S`: the
function of the word of `W`
vanishes near the free sides, so it extends over the fibres of `ψ`, and `exists_cocycle_quot`
applies. Different choices give
different classes, because pulling back to `W` recovers the values. So `2a + b` is at most the same
number for `S`
(`genus_le`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Function Metric GraphMinor.Surface

universe u

section words

variable {a b c : ℕ}

/-- The points of the free sides of the word `ew a b c`. -/
def freeSet (a b c : ℕ) : Set ℂ :=
  {z | ∃ i < c, ∃ u ∈ Icc (0 : ℝ) 1, z = per (4 * a + 2 * b + 3 * c + 2)
    ((4 * a + 2 * b + 3 * i + 1 : ℕ) + u)}

/-- A pasting step does not leave the free sides. -/
theorem stp_free {x y : ℕ × ℂ} (h : Stp (sW (ew a b c)) x y) (hx : x.2 ∈ freeSet a b c) : y.2 ∈
  freeSet a b c := by
  obtain ⟨i, j, p, q, k, e, e', u, h1, h2, h3, hu, rfl, rfl⟩ := stp_iff.mp h
  obtain ⟨rfl, h4⟩ := sW_get h1
  obtain ⟨rfl, h5⟩ := sW_get h2
  obtain ⟨hp, hl, rfl⟩ := (ew_get_iff _ _ _ _ _ _).mp h4
  obtain ⟨hq, hl', rfl⟩ := (ew_get_iff _ _ _ _ _ _).mp h5
  have hne : p ≠ q := fun he ↦ h3 (by rw [he])
  have htw : q = twin a b c p := (lab_two hp hq (hl.trans hl'.symm)).resolve_left hne.symm
  obtain ⟨l, hlc, v, hv, hxv⟩ := hx
  rw [spt_ew] at hxv
  simp only at hxv
  set n := 4 * a + 2 * b + 3 * c + 2 with hn
  set r := 4 * a + 2 * b + 3 * l + 1 with hr
  have hrn : r + 1 < n := by omega
  have hnr : p ≠ r := fun he ↦ by
    have : twin a b c p = p := (twin_eq_iff hp).mpr ⟨l, hlc, he⟩
    exact hne (htw.trans this).symm
  have hu01 : u ∉ Ioo (0 : ℝ) 1 := fun hi ↦ hnr (side_unique hp (by omega) hi hv hxv).1
  have hv01 : v ∉ Ioo (0 : ℝ) 1 := fun hi ↦ hnr (side_unique (by omega) hp hi hu hxv.symm).1.symm
  have hend : ∀ w ∈ Icc (0 : ℝ) 1, w ∉ Ioo (0 : ℝ) 1 → w = 0 ∨ w = 1 := fun w hw hw' ↦ by
    by_contra hc
    push Not at hc
    exact hw' ⟨lt_of_le_of_ne hw.1 (Ne.symm hc.1), lt_of_le_of_ne hw.2 hc.2⟩
  have hkey : ∀ w w' : ℕ, w ≤ n → 1 ≤ w' → w' < n → per n w = per n w' → w = w' := by
    intro w w' h₁ h₂ h₃ he
    obtain ⟨m, hm⟩ := per_eq (show 0 < n by omega) he
    have hm' : (w : ℤ) = w' + m * n := by exact_mod_cast hm
    have hn0 : (0 : ℤ) < n := by exact_mod_cast (show 0 < n by omega)
    have h₄ : m = 0 := by
      have h₅ : m < 1 := by
        by_contra hc
        have : (n : ℤ) ≤ m * n := by nlinarith
        omega
      have h₆ : -1 < m := by
        by_contra hc
        have : m * (n : ℤ) ≤ -1 * n := by nlinarith
        omega
      omega
    subst h₄
    omega
  have hcase : ∀ {w w' : ℕ}, (p : ℝ) + u = w → (r : ℝ) + v = w' → w ≤ n → 1 ≤ w' → w' < n → w = w'
    := fun {w w'} h₁ h₂ h₃ h₄ h₅ ↦ by
    rw [h₁, h₂] at hxv
    exact hkey w w' h₃ h₄ h₅ hxv
  rw [spt_ew]
  simp only
  rcases hend u hu hu01 with rfl | rfl <;> rcases hend v hv hv01 with rfl | rfl
  · exact absurd (hcase (w := p) (w' := r) (by simp) (by simp) (by omega) (by omega) (by omega)) hnr
  · have h₁ : p = r + 1 :=
      hcase (w := p) (w' := r + 1) (by simp) (by simp) (by omega) (by omega) (by omega)
    have hpe : p = 4 * a + 2 * b + 3 * l + 2 := by omega
    have htp : twin a b c p = 4 * a + 2 * b + 3 * l := by
      subst hpe
      unfold twin
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_right
        (by omega), ite_eq_left (by omega)]
      omega
    have hs₁ : sgn a b c p = false := by
      rw [hpe, sgn_t hlc (δ := 2) (by norm_num)]
      rfl
    have hs₂ : sgn a b c q = true := by
      rw [htw, htp]
      exact (sgn_t hlc (δ := 0) (by norm_num)).trans rfl
    refine ⟨l, hlc, 0, by simp, ?_⟩
    rw [hs₁, hs₂, htw, htp]
    congr 1
    norm_num [flp]
  · have h₁ : p + 1 = r :=
      hcase (w := p + 1) (w' := r) (by simp) (by simp) (by omega) (by omega) (by omega)
    have hpe : p = 4 * a + 2 * b + 3 * l := by omega
    have htp : twin a b c p = 4 * a + 2 * b + 3 * l + 2 := by
      subst hpe
      unfold twin
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left
        (by omega)]
    have hs₁ : sgn a b c p = true := by
      rw [hpe]
      exact (sgn_t hlc (δ := 0) (by norm_num)).trans rfl
    have hs₂ : sgn a b c q = false := by
      rw [htw, htp, sgn_t hlc (δ := 2) (by norm_num)]
      rfl
    refine ⟨l, hlc, 1, by simp, ?_⟩
    rw [hs₁, hs₂, htw, htp]
    congr 1
    norm_num [flp]
    ring
  · have h₁ : p + 1 = r + 1 :=
      hcase (w := p + 1) (w' := r + 1) (by simp) (by simp) (by omega) (by omega) (by omega)
    exact absurd (by omega) hnr

/-- Points of the discs pasted to a point of a free side are on the free sides. -/
theorem prel_free {x y : ℕ × ℂ} (h : PRel (sW (ew a b c)) x y) : x.2 ∈ freeSet a b c ↔ y.2 ∈
  freeSet a b c := by
  induction h with
  | rel x y hs => exact ⟨stp_free hs, stp_free hs.symm⟩
  | refl _ => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ h₁ h₂ => exact h₁.trans h₂

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] {f : ℕ × ℂ → Y}

theorem mem_free_of_bd (hf : Presents (sW (ew a b c)) f) {x : ℕ × ℂ} (hx : x ∈ Dsk (sW (ew a b c)))
  (hb : f x ∈ bd Y) : x.2 ∈ freeSet a b c := by
  have hbd := (surface_of_presents (finW_sW _) (isPaired_ew a b c) hf).2
  rw [hbd] at hb
  obtain ⟨_, ⟨i, p, u, hp, hfr, hu, rfl⟩, he⟩ := hb
  have hi : i = 0 := by
    by_contra hi
    simp [sW, hi, nW] at hp
  subst hi
  rw [sW_zero, ew_length] at hp
  obtain ⟨l, hl, rfl⟩ := (twin_eq_iff hp).mp (twin_of_free hp hfr)
  have hm : spt (sW (ew a b c)) 0 (4 * a + 2 * b + 3 * l + 1) u ∈ Dsk (sW (ew a b c)) :=
    spt_mem (by rw [sW_zero, ew_length]; exact hp) u
  have hr := (hf.2.2 _ hm _ hx).mp he
  refine (prel_free hr).mp ⟨l, hl, u, hu, ?_⟩
  rw [spt_ew]

/-- Values on the loops only. -/
noncomputable def loopV (a b : ℕ) (v : Fin (2 * a + b) → ZMod 2) (k : ℕ) : ZMod 2
  := if h : k < 2 * a + b then v ⟨k, h⟩ else 0

theorem two_smul_zmod (x : ZMod 2) : (2 : ℕ) • x = 0 := by
  revert x
  decide

theorem loopV_zero {v : Fin (2 * a + b) → ZMod 2} {k : ℕ} (h : 2 * a + b ≤ k) : loopV a b v k = 0
  := by
  simp [loopV, not_lt.mpr h]

theorem total_zero (v : Fin (2 * a + b) → ZMod 2) : Sm a b c (loopV a b v)
  (4 * a + 2 * b + 3 * c + 2) = 0 := by
  rw [Sm_total, two_smul_zmod, Finset.sum_eq_zero fun i _ ↦ loopV_zero (by omega), add_zero]

/-- The function of the word vanishes on the free sides. -/
theorem gz_free (v : Fin (2 * a + b) → ZMod 2) {z : ℂ} (hz : z ∈ freeSet a b c) : gz a b c
  (loopV a b v) z = 0 := by
  obtain ⟨i, hi, u, hu, rfl⟩ := hz
  rw [gz_per _ (total_zero v) (by omega) hu, gx]
  have h₁ : st a b c (4 * a + 2 * b + 3 * i + 1) = 4 * a + 2 * b + 3 * i + 1 := by
    have h₂ : sgn a b c (4 * a + 2 * b + 3 * i + 1) = true := (sgn_t hi (δ := 1)
      (by norm_num)).trans rfl
    simp [st, h₂]
  have h₅ : lv a b c (loopV a b v) (4 * a + 2 * b + 3 * i) = 0 := by
    have h₆ := lv_t (a := a) (b := b) (loopV a b v) hi (δ := 0) (by norm_num)
    rw [add_zero] at h₆
    rw [h₆, ite_eq_left (by norm_num)]
    exact loopV_zero (by omega)
  rw [h₁, Sm_succ, Sm_holes _ hi.le, lab_t hi (δ := 1) (by norm_num), h₅]
  rw [two_smul_zmod, Finset.sum_eq_zero fun i _ ↦ loopV_zero (by omega)]
  have h₃ : loopV a b v (2 * a + b + 2 * i + 1 % 2) = 0 := loopV_zero (by omega)
  simp [h₃]

theorem lval_gz (v : Fin (2 * a + b) → ZMod 2) {k : ℕ} (hk : k ≤ 2 * a + b + 2 * c) : lval a b c
  (gz a b c (loopV a b v)) k = loopV a b v k := by
  have hr := rep_lt hk (a := a) (b := b) (c := c)
  have hV := total_zero (c := c) v
  have h₆ : ∀ t : ℝ, t = 0 ∨ t = 1 → gz a b c (loopV a b v) (per (4 * a + 2 * b + 3 * c + 2)
    (rep a b c k + ofs (sgn a b c (rep a b c k)) t)) =
      gx a b c (loopV a b v) (rep a b c k) (ofs (sgn a b c (rep a b c k)) t)
        := fun t ht ↦ gz_per _ hV hr (ofs_mem' ht)
  have h₇ := h₆ 0 (.inl rfl)
  have h₈ := h₆ 1 (.inr rfl)
  rw [per_st] at h₇
  rw [per_en] at h₈
  rw [lval, volt, h₇, h₈, gx, gx, lab_rep hk]
  cases sgn a b c (rep a b c k) <;> norm_num [ofs]

end words

section main

variable {S Y : Type u} [TopologicalSpace S] [T2Space S] [TopologicalSpace Y] [T2Space Y]
  [CompactSpace Y]

/-- **The bound on the pieces of a cut surface.** -/
theorem genus_le {ψ : Y → S} (hψ : Continuous ψ) (hsurj : Surjective ψ) (hfib : ∀ y y', ψ y = ψ y'
  → y = y' ∨ (y ∈ bd Y ∧ y' ∈ bd Y))
    (hbd : ∀ y, ψ y ∈ bd S → y ∈ bd Y) {W : Set Y} (hW : IsClopen W) {a b c a₀ b₀ c₀ : ℕ}
      (e : W ≃ₜ SurfaceModel a b c) (e₀ : S ≃ₜ SurfaceModel a₀ b₀ c₀) :
    2 * a + b ≤ 2 * a₀ + b₀ := by
  classical
  obtain ⟨-, f₀, hf₀⟩ := presents_ew a b c
  have hf : Presents (sW (ew a b c)) (e.symm ∘ f₀) := presents_comp hf₀ e.symm
  set f := e.symm ∘ f₀ with hfd
  obtain ⟨-, f₁, hf₁⟩ := presents_ew a₀ b₀ c₀
  have hfS : Presents (sW (ew a₀ b₀ c₀)) (e₀.symm ∘ f₁) := presents_comp hf₁ e₀.symm
  let D₁ := Dsk (sW (ew a b c))
  let R : Set Y := Wᶜ
  have : CompactSpace D₁ := compactSpace_dsk (finW_sW _)
  have : CompactSpace R := isCompact_iff_compactSpace.mp hW.isOpen.isClosed_compl.isCompact
  let D := D₁ ⊕ R
  have hne : Nonempty D := ⟨.inl ⟨_, ew_mem_dsk a b c⟩⟩
  let Q : D → Y := Sum.elim (fun x ↦ (f x.1).1) fun y ↦ y.1
  have hfc : Continuous fun x : D₁ ↦ f x.1 := hf.1.comp_continuous continuous_subtype_val fun x ↦
    x.2
  have hQ : Continuous Q := (continuous_subtype_val.comp hfc).sumElim continuous_subtype_val
  have hF : Continuous (ψ ∘ Q) := hψ.comp hQ
  have hQs : Surjective Q := fun y ↦ by
    by_cases hy : y ∈ W
    · have h₁ : (⟨y, hy⟩ : W) ∈ f '' Dsk (sW (ew a b c)) := hf.2.1 ▸ mem_univ _
      obtain ⟨x, hx, he⟩ := h₁
      exact ⟨.inl ⟨x, hx⟩, congrArg Subtype.val he⟩
    · exact ⟨.inr ⟨y, hy⟩, rfl⟩
  have hFs : Surjective (ψ ∘ Q) := hsurj.comp hQs
  let gD : (Fin (2 * a + b) → ZMod 2) → D → ZMod 2 := fun v ↦ Sum.elim (fun x ↦ gz a b c
    (loopV a b v) x.1.2) fun _ ↦ 0
  have hg0 : ∀ v x, Q x ∈ bd Y → gD v x = 0 := fun v x hx ↦ by
    rcases x with x | x
    · have h₁ : f x.1 ∈ bd W := (mem_bd_sub hW.isOpen).mpr hx
      exact gz_free v (mem_free_of_bd hf x.2 h₁)
    · rfl
  have hcl : ∀ v (c' : ZMod 2), IsClosed {p : D × D | (ψ ∘ Q) p.1 = (ψ ∘ Q) p.2
    ∧ gD v p.2 - gD v p.1 = c'} := by
    intro v c'
    let _ : TopologicalSpace (ZMod 2) := ⊥
    have : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    have hrel := isClosed_covRel (A := ZMod 2) (g := fun x ↦ gz a b c (loopV a b v) x.2)
      (finW_sW _) (isPaired_ew a b c) (sideConst_gz (loopV a b v) (total_zero v))
    let B : Set D := Q ⁻¹' bd Y
    have hB : IsClosed B := (isClosed_bd Y).preimage hQ
    let E₁ : Set (D × D) := {p | p.1 ∈ B ∧ p.2 ∈ B ∧ (ψ ∘ Q) p.1 = (ψ ∘ Q) p.2 ∧ c' = 0}
    have hE₁ : IsClosed E₁ := by
      by_cases hc : c' = 0
      · have e₁ : E₁ = (B ×ˢ B) ∩ {p | (ψ ∘ Q) p.1 = (ψ ∘ Q) p.2} := by
          ext p
          simp only [E₁, hc, and_true, mem_inter_iff, mem_prod, mem_ofPred_eq, and_assoc]
        rw [e₁]
        exact (hB.prod hB).inter (isClosed_eq (hF.comp continuous_fst) (hF.comp continuous_snd))
      · have e₁ : E₁ = ∅ := by
          ext p
          simp only [E₁, hc, and_false, mem_ofPred_eq, mem_empty_iff_false]
        rw [e₁]
        exact isClosed_empty
    let T : Set (D₁ × D₁) := {p | PRel (sW (ew a b c)) p.1.1 p.2.1 ∧ gz a b c
      (loopV a b v) p.2.1.2 - gz a b c (loopV a b v) p.1.1.2 = c'}
    have hT : IsClosed T := by
      have e₁ : T = (fun p : D₁ × D₁ ↦ (((p.1, 0), (p.2, c')) : (Dsk (sW (ew a b c)) × ZMod 2) ×
        (Dsk (sW (ew a b c)) × ZMod 2))) ⁻¹'
          {p | covRel (sW (ew a b c)) (fun x ↦ gz a b c (loopV a b v) x.2) p.1 p.2} := by
        ext p
        simp only [T, covRel, mem_ofPred_eq, mem_preimage, add_zero]
        refine and_congr_right fun _ ↦ ?_
        constructor
        · intro h
          rw [← h]
          ring
        · intro h
          have : -gz a b c (loopV a b v) p.1.1.2 = -gz a b c (loopV a b v) p.2.1.2 + c' := h
          linear_combination this
      rw [e₁]
      exact hrel.preimage (by fun_prop)
    let E₂ : Set (D × D) := (fun p : D₁ × D₁ ↦ ((Sum.inl p.1, Sum.inl p.2) : D × D)) '' T
    have hE₂ : IsClosed E₂ := (IsClosedEmbedding.inl.prodMap IsClosedEmbedding.inl).isClosedMap _ hT
    let E₃ : Set (D × D) := {p | p.1 = p.2 ∧ p.1 ∈ range (Sum.inr : R → D) ∧ c' = 0}
    have hE₃ : IsClosed E₃ := by
      by_cases hc : c' = 0
      · have e₁ : E₃ = {p | p.1 = p.2} ∩ (range (Sum.inr : R → D) ×ˢ univ) := by
          ext p
          simp only [E₃, hc, and_true, mem_inter_iff, mem_prod, mem_univ]
          exact Iff.rfl
        rw [e₁]
        exact (isClosed_eq continuous_fst continuous_snd).inter
          (IsClosedEmbedding.inr.isClosed_range.prod isClosed_univ)
      · have e₁ : E₃ = ∅ := by
          ext p
          simp only [E₃, hc, and_false, mem_ofPred_eq, mem_empty_iff_false]
        rw [e₁]
        exact isClosed_empty
    have heq : {p : D × D | (ψ ∘ Q) p.1 = (ψ ∘ Q) p.2 ∧ gD v p.2 - gD v p.1 = c'} = E₁ ∪ E₂ ∪ E₃
      := by
      ext ⟨x, y⟩
      constructor
      · rintro ⟨h₁, h₂⟩
        simp only at h₁ h₂
        rcases hfib _ _ h₁ with h₃ | ⟨h₃, h₄⟩
        · rcases x with x | x <;> rcases y with y | y
          · have h₄ : f x.1 = f y.1 := Subtype.ext h₃
            exact .inl (.inr ⟨(x, y), ⟨(hf.2.2 _ x.2 _ y.2).mp h₄, h₂⟩, rfl⟩)
          · have h₄ : (f x.1).1 = y.1 := h₃
            exact absurd (h₄ ▸ (f x.1).2) y.2
          · have h₄ : x.1 = (f y.1).1 := h₃
            exact absurd (h₄.symm ▸ (f y.1).2) x.2
          · have h₄ : x = y := Subtype.ext h₃
            subst h₄
            exact .inr ⟨rfl, ⟨x, rfl⟩, by simpa using h₂.symm⟩
        · refine .inl (.inl ⟨h₃, h₄, h₁, ?_⟩)
          rw [← h₂, hg0 v x h₃, hg0 v y h₄, sub_zero]
      · rintro ((⟨h₁, h₂, h₃, h₄⟩ | ⟨⟨x', y'⟩, ⟨h₁, h₂⟩, h₃⟩) | ⟨h₁, ⟨z, h₂⟩, h₃⟩)
        · refine ⟨h₃, ?_⟩
          simp only at h₁ h₂
          simp only
          rw [hg0 v x h₁, hg0 v y h₂, h₄, sub_zero]
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₃
          refine ⟨?_, h₂⟩
          have h₄ : f x'.1 = f y'.1 := (hf.2.2 _ x'.2 _ y'.2).mpr h₁
          exact congrArg (fun z : W ↦ ψ z.1) h₄
        · simp only at h₁ h₂ h₃
          subst h₁
          exact ⟨rfl, by simpa using h₃.symm⟩
    rw [heq]
    exact (hE₁.union hE₂).union hE₃
  have hex := fun v ↦ exists_cocycle_quot hF hFs (gD v) (hcl v)
  choose φ hφ hN hB using hex
  have hBd : ∀ v, BdTriv (φ v) := fun v ↦ hB v fun x hx ↦ hg0 v x (hbd _ hx)
  let cl : (Fin (2 * a + b) → ZMod 2) → KCl S (ZMod 2) := fun v ↦ Quotient.mk (kSetoid S
    (ZMod 2)) ⟨φ v, hφ v, hBd v⟩
  have hprim : ∀ v, IsPrim (fun x y : W ↦ φ v (ψ x.1) (ψ y.1)) (pmap f) (gz a b c (loopV a b v))
    := fun v ↦ by
    obtain ⟨N, hN₁, hN₂⟩ := hN v
    have hba : ∀ z ∈ closedBall (0 : ℂ) 1, ((0 : ℕ), z) ∈ Dsk (sW (ew a b c))
      := fun z hz ↦ ⟨(ew_mem_dsk a b c).1, by simpa using hz⟩
    let P : ℂ → D := fun z ↦ if h : z ∈ closedBall (0 : ℂ) 1 then .inl ⟨(0, z), hba z h⟩ else .inl
      ⟨(0, 0), hba 0 (by simp)⟩
    have hP : ∀ z (h : z ∈ closedBall (0 : ℂ) 1), P z = .inl ⟨(0, z), hba z h⟩
      := fun z h ↦ by simp only [P, h, dite_eq_left]
    have hPc : ContinuousOn P (closedBall 0 1) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have e₁ : (closedBall (0 : ℂ) 1).domRestrict P = Sum.inl ∘ fun z : closedBall (0 : ℂ) 1 ↦
        (⟨(0, z.1), hba z.1 z.2⟩ : D₁) := by
        funext z
        exact hP z.1 z.2
      rw [e₁]
      refine continuous_inl.comp (Continuous.subtype_mk ?_ _)
      fun_prop
    obtain ⟨ε, hε, h₁⟩ := exists_eps (isCompact_closedBall 0 1) hPc hN₁
    refine ⟨ε, hε, fun x hx y hy hxy ↦ ?_⟩
    have h₂ := hN₂ _ _ (h₁ x hx y hy hxy)
    rw [hP x hx, hP y hy] at h₂
    exact h₂
  have hinj : Injective cl := fun v v' he ↦ by
    obtain ⟨h, N, hN₁, hN₂⟩ : CohRel (φ v) (φ v') := Quotient.exact he
    have hr : CohRel (fun x y : W ↦ φ v (ψ x.1) (ψ y.1)) (fun x y : W ↦ φ v' (ψ x.1) (ψ y.1)) := by
      have hc : Continuous fun x : W ↦ ψ x.1 := hψ.comp continuous_subtype_val
      refine ⟨fun x ↦ h (ψ x.1), (fun p : W × W ↦ (ψ p.1.1, ψ p.2.1)) ⁻¹' N, fun x ↦ ?_,
        fun x y hxy ↦ hN₂ _ _ hxy⟩
      have hc' : Continuous fun p : W × W ↦ (ψ p.1.1, ψ p.2.1) := (hc.comp continuous_fst).prodMk
        (hc.comp continuous_snd)
      exact hc'.continuousAt.preimage_mem_nhds (hN₁ _)
    funext k
    have h₁ := lval_rel hf (hprim v) (hprim v') hr k.2
    rw [lval_gz v (by have := k.2; omega), lval_gz v' (by have := k.2; omega)] at h₁
    simpa [loopV, k.2] using h₁
  have hcard : Nat.card (KCl S (ZMod 2)) = 2 ^ (2 * a₀ + b₀) := by
    rw [card_kCl hfS, card_lam_two]
  have : Finite (KCl S (ZMod 2)) := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have h₁ := Nat.card_le_card_of_injective _ hinj
  rw [hcard, card_fin_fun] at h₁
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h₁

end main

end GraphMinor.GM19
