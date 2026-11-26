/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73StripCollapse
public import LeanPool.GraphMinor.GM12.Section73CollapseComposition
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Contracting a long interval inside a thin strip

For the radial-edge contractions in XII (7.3), page 261, the strip
may extend only a short way beyond the arc ends. Divide its axis
interval into short pieces and collapse them from right to left.
Each piece has support in the prescribed strip. The composition
collapses exactly the whole interval and fixes the outside.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface Complex

/-- An arbitrarily thin rectangular strip suffices to contract its
axis interval, identifying no other points. This removes the support
restriction from the local contractions used in XII (7.3). -/
theorem exists_thin_strip_interval_collapse
    {T : Type} [TopologicalSpace T] [T2Space T] {O : Set ℂ} {K : ℂ → T}
    (hK : StripChart O K) {l r δ : ℝ} (hlr : l < r) (hδ : 0 < δ)
    (hRO : Icc (l - δ) (r + δ) ×ℂ Icc (-δ) δ ⊆ O) :
    ∃ f : C(T, T), Function.Surjective f ∧
      (∀ x ∉ K '' (Icc (l - δ) (r + δ) ×ℂ Icc (-δ) δ), f x = x) ∧
      (∀ x ∈ K '' (Complex.ofReal '' Icc l r), f x = K (l : ℂ)) ∧
      (∀ t : ℝ, (t : ℂ) ∈ O → t ≤ l → f (K (t : ℂ)) = K (t : ℂ)) ∧
      (∀ x y, f x = f y ↔ x = y ∨
        (x ∈ K '' (Complex.ofReal '' Icc l r) ∧ y ∈ K '' (Complex.ofReal '' Icc l r))) := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt ((r - l) / δ)
  have hNpos : (0 : ℝ) < N := (div_pos (sub_pos.mpr hlr) hδ).trans hN
  let h : ℝ := (r - l) / N
  have hh : 0 < h := div_pos (sub_pos.mpr hlr) hNpos
  have hhδ : h < δ := by
    apply (div_lt_iff₀ hNpos).mpr
    have hmul := (div_lt_iff₀ hδ).mp hN
    simpa only [mul_comm] using hmul
  have hNh : h * (N : ℝ) = r - l := div_mul_cancel₀ _ hNpos.ne'
  let c : ℕ → ℝ := fun k => r - k * h
  let R : Set ℂ := Icc (l - δ) (r + δ) ×ℂ Icc (-δ) δ
  let A : ℕ → Set T := fun k => K '' (Complex.ofReal '' Icc (c k) r)
  have hcN : c N = l := by dsimp only [c]; rw [mul_comm _ h, hNh]; ring
  have hcbounds : ∀ k ≤ N, l ≤ c k ∧ c k ≤ r := by
    intro k hk
    have hkn : (k : ℝ) ≤ N := by exact_mod_cast hk
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hle := mul_le_mul_of_nonneg_right hkn hh.le
    have hnon := mul_nonneg hk0 hh.le
    dsimp only [c]
    constructor <;> nlinarith [hNh]
  have hcstep : ∀ k, c (k + 1) = c k - h := by
    intro k
    dsimp only [c]
    rw [Nat.cast_add, Nat.cast_one]
    ring
  have haxis : ∀ k ≤ N, ∀ t ∈ Icc (c k) r, (t : ℂ) ∈ O := by
    intro k hk t ht
    apply hRO
    refine ⟨?_, ?_⟩
    · change l - δ ≤ t ∧ t ≤ r + δ
      constructor <;> linarith [(hcbounds k hk).1, ht.1, ht.2]
    · change -δ ≤ (t : ℂ).im ∧ (t : ℂ).im ≤ δ
      simp only [ofReal_im]
      exact ⟨neg_nonpos.mpr hδ.le, hδ.le⟩
  have build : ∀ k ≤ N, ∃ f : C(T, T), Function.Surjective f ∧
      (∀ x ∉ K '' R, f x = x) ∧ (∀ x ∈ A k, f x = K (c k : ℂ)) ∧
      (∀ t : ℝ, (t : ℂ) ∈ O → t ≤ c k → f (K (t : ℂ)) = K (t : ℂ)) ∧
      (∀ x y, f x = f y ↔ x = y ∨ (x ∈ A k ∧ y ∈ A k)) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have hA0 : A 0 = {K (r : ℂ)} := by simp [A, c]
      refine ⟨⟨id, continuous_id⟩, Function.surjective_id, fun _ _ => rfl, ?_,
        fun _ _ _ => rfl, ?_⟩
      · intro x hx
        change x = K (c 0 : ℂ)
        simpa only [c, Nat.cast_zero, zero_mul, sub_zero] using mem_singleton_iff.mp (hA0.subset hx)
      · intro x y
        change x = y ↔ x = y ∨ (x ∈ A 0 ∧ y ∈ A 0)
        constructor
        · exact Or.inl
        · rintro (hxy | ⟨hx, hy⟩)
          · exact hxy
          · exact (hA0.subset hx).trans (hA0.subset hy).symm
    | succ k ih =>
      intro hk
      have hkN : k ≤ N := (Nat.le_succ k).trans hk
      obtain ⟨f, hfs, hfix, hconst, hleft, hfibre⟩ := ih hkN
      have hstep : c (k + 1) < c k := by rw [hcstep]; exact sub_lt_self _ hh
      have hpiece : collapseRectangle (c (k + 1)) (c k) δ ⊆ R := by
        intro z hz
        refine ⟨?_, hz.2⟩
        change l - δ ≤ z.re ∧ z.re ≤ r + δ
        have hlow := (hcbounds (k + 1) hk).1
        have hupp := (hcbounds k hkN).2
        have hstep' := hcstep k
        constructor <;> linarith [hz.1.1, hz.1.2]
      obtain ⟨g, hgs, hgfix, hgconst, hgleft, hgfibre⟩ :=
        exists_strip_interval_collapse hK hstep hδ (hpiece.trans hRO)
      let B : Set T := K '' (Complex.ofReal '' Icc (c (k + 1)) (c k))
      have hBfix : ∀ x ∈ B, f x = x := by
        rintro x ⟨z, ⟨t, ht, rfl⟩, rfl⟩
        exact hleft t (haxis (k + 1) hk t ⟨ht.1, ht.2.trans (hcbounds k hkN).2⟩) ht.2
      have haB : K (c k : ℂ) ∈ B := ⟨(c k : ℂ), ⟨c k, ⟨hstep.le, le_rfl⟩, rfl⟩, rfl⟩
      obtain ⟨hcomconst, hcomfib⟩ := collapse_composition_fibres hfibre hgfibre hconst hBfix haB
      have hUnion : A k ∪ B = A (k + 1) := by
        change (K '' (Complex.ofReal '' Icc (c k) r)) ∪
          (K '' (Complex.ofReal '' Icc (c (k + 1)) (c k))) = _
        rw [← image_union, ← image_union, union_comm,
          Icc_union_Icc_eq_Icc hstep.le (hcbounds k hkN).2]
      have hpoint : g (K (c k : ℂ)) = K (c (k + 1) : ℂ) := hgconst _ haB
      refine ⟨g.comp f, hgs.comp hfs, ?_, ?_, ?_, ?_⟩
      · intro x hx
        change g (f x) = x
        rw [hfix x hx]
        exact hgfix x (fun hp => hx (image_mono hpiece hp))
      · intro x hx
        change g (f x) = _
        rw [← hUnion] at hx
        exact (hcomconst x hx).trans hpoint
      · intro t ht htc
        change g (f (K (t : ℂ))) = _
        rw [hleft t ht (htc.trans hstep.le), hgleft t ht htc]
      · intro x y
        change g (f x) = g (f y) ↔ _
        have hfibxy : g (f x) = g (f y) ↔ x = y ∨ (x ∈ A k ∪ B ∧ y ∈ A k ∪ B) := hcomfib x y
        rwa [hUnion] at hfibxy
  obtain ⟨f, hfs, hfix, hconst, hleft, hfibre⟩ := build N le_rfl
  refine ⟨f, hfs, hfix, ?_, ?_, ?_⟩
  · simpa only [A, hcN] using hconst
  · simpa only [hcN] using hleft
  · simpa only [A, hcN] using hfibre

end GraphMinor.GM12
