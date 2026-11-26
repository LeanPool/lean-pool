/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM07.NetSeparate
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# Paired sides for the general separating exchange

For the type-(ii) exchange in VII (2.6), page 218, remove the
selected paired sides after pasting them. Replace that pair by
the two lifts of the cutting line. Every other refined side
lies wholly in one cut piece and keeps its old parameter.
The resulting family has the same number of pairs.
-/

public section
namespace GraphMinor.GM07
open Set Surface

/-- Construct all paired boundary arcs for the general type-(ii)
exchange of VII (2.6), page 218. The selected pair is replaced by
the two cutting-line lifts, and every other side is retained. -/
theorem Net.exists_separating_side_family
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    (N : Net S) (i : Fin N.r) {F A B : Set N.D} {s t : N.D}
    (hF : IsLineWithEnds F s t) (hFbd : F ∩ bd N.D = {s, t})
    (hs : ∀ j r, r ∈ Ioo (0 : unitInterval) 1 → N.f j r ≠ s ∧ N.g j r ≠ s)
    (ht : ∀ j r, r ∈ Ioo (0 : unitInterval) 1 → N.f j r ≠ t ∧ N.g j r ≠ t)
    (hA : IsClosedDisc A) (hB : IsClosedDisc B) (hAB : A ∪ B = univ) (hI : A ∩ B = F)
    (hAd : discBd A = (A ∩ bd N.D) ∪ F) (hBd : discBd B = (B ∩ bd N.D) ∪ F)
    (α : A → T) (β : B → T) (hcα : Continuous α) (hcβ : Continuous β)
    (hiα : Function.Injective α) (hiβ : Function.Injective β)
    (hcross : ∀ (x : A) (y : B), α x = β y ↔ ∃ r, x.val = N.f i r ∧ y.val = N.g i r)
    (hαbd : ∀ x : A, α x ∈ bd T ↔ x.val ∈ discBd A ∧
      x.val ∉ N.f i '' Ioo (0 : unitInterval) 1)
    (hβbd : ∀ y : B, β y ∈ bd T ↔ y.val ∈ discBd B ∧
      y.val ∉ N.g i '' Ioo (0 : unitInterval) 1)
    (φ : T → S) (hφA : ∀ x : A, φ (α x) = N.φ x.val)
    (hφB : ∀ y : B, φ (β y) = N.φ y.val) :
    ∃ (k : Curve N.D) (f g : Fin N.r → Curve T),
      Function.Injective k ∧ range k = F ∧ k 0 = s ∧ k 1 = t ∧
      (∀ j, Function.Injective (f j)) ∧ (∀ j, Function.Injective (g j)) ∧
      (∀ j, range (f j) ⊆ bd T) ∧ (∀ j, range (g j) ⊆ bd T) ∧
      (∀ j l, j ≠ l → ∀ r ∈ Ioo (0 : unitInterval) 1, f j r ∉ range (f l)) ∧
      (∀ j l, j ≠ l → ∀ r ∈ Ioo (0 : unitInterval) 1, g j r ∉ range (g l)) ∧
      (∀ j l, ∀ r ∈ Ioo (0 : unitInterval) 1, f j r ∉ range (g l)) ∧
      (∀ j l, ∀ r ∈ Ioo (0 : unitInterval) 1, g j r ∉ range (f l)) ∧
      (∀ j r, φ (f j r) = φ (g j r)) ∧
      (∀ r (x : A), x.val = k r → f i r = α x) ∧
      (∀ r (y : B), y.val = k r → g i r = β y) ∧
      (∀ j, j ≠ i →
        (∃ h : ∀ r, N.f j r ∈ A, ∀ r, f j r = α ⟨N.f j r, h r⟩) ∨
        (∃ h : ∀ r, N.f j r ∈ B, ∀ r, f j r = β ⟨N.f j r, h r⟩)) ∧
      (∀ j, j ≠ i →
        (∃ h : ∀ r, N.g j r ∈ A, ∀ r, g j r = α ⟨N.g j r, h r⟩) ∨
        (∃ h : ∀ r, N.g j r ∈ B, ∀ r, g j r = β ⟨N.g j r, h r⟩)) := by
  classical
  obtain ⟨k, hki, hkF, hk0, hk1, hkInt, hkf, hkg⟩ :=
    N.exists_separating_cut_curve hF hFbd hs ht
  have hkA : ∀ r, k r ∈ A := fun r => (hI.symm ▸ (hkF ▸ mem_range_self r)).1
  have hkB : ∀ r, k r ∈ B := fun r => (hI.symm ▸ (hkF ▸ mem_range_self r)).2
  let p : Curve T := ⟨fun r => α ⟨k r, hkA r⟩, hcα.comp (k.continuous.subtype_mk hkA)⟩
  let q : Curve T := ⟨fun r => β ⟨k r, hkB r⟩, hcβ.comp (k.continuous.subtype_mk hkB)⟩
  have hpRep : (∃ h : ∀ r, k r ∈ A, ∀ r, p r = α ⟨k r, h r⟩) ∨
      (∃ h : ∀ r, k r ∈ B, ∀ r, p r = β ⟨k r, h r⟩) := Or.inl ⟨hkA, fun _ => rfl⟩
  have hqRep : (∃ h : ∀ r, k r ∈ A, ∀ r, q r = α ⟨k r, h r⟩) ∨
      (∃ h : ∀ r, k r ∈ B, ∀ r, q r = β ⟨k r, h r⟩) := Or.inr ⟨hkB, fun _ => rfl⟩
  obtain ⟨hfSide, hgSide⟩ := N.sides_subset_one_cut_piece hA hB hAB hI hFbd hs ht
  choose Lf hLf using fun j => exists_curve_lift α β hcα hcβ (N.f j) (hfSide j)
  choose Lg hLg using fun j => exists_curve_lift α β hcα hcβ (N.g j) (hgSide j)
  let f : Fin N.r → Curve T := fun j => if j = i then p else Lf j
  let g : Fin N.r → Curve T := fun j => if j = i then q else Lg j
  have hfi : f i = p := ite_eq_left rfl
  have hgi : g i = q := ite_eq_left rfl
  have hfj : ∀ j, j ≠ i → f j = Lf j := fun j hj => ite_eq_right hj
  have hgj : ∀ j, j ≠ i → g j = Lg j := fun j hj => ite_eq_right hj
  have hpi := curve_lift_injective α β hiα hiβ k p hki hpRep
  have hqi := curve_lift_injective α β hiα hiβ k q hki hqRep
  have hpbd : range p ⊆ bd T := by
    rintro z ⟨r, rfl⟩
    apply (hαbd ⟨k r, hkA r⟩).mpr
    refine ⟨hAd ▸ Or.inr (hkF ▸ mem_range_self r), ?_⟩
    rintro ⟨v, hv, hvr⟩
    exact (hkf i).2 v hv ⟨r, hvr.symm⟩
  have hqbd : range q ⊆ bd T := by
    rintro z ⟨r, rfl⟩
    apply (hβbd ⟨k r, hkB r⟩).mpr
    refine ⟨hBd ▸ Or.inr (hkF ▸ mem_range_self r), ?_⟩
    rintro ⟨v, hv, hvr⟩
    exact (hkg i).2 v hv ⟨r, hvr.symm⟩
  have hOldBd : ∀ (a : Curve N.D) (c : Curve T),
      range a ⊆ bd N.D →
      (∀ r ∈ Ioo (0 : unitInterval) 1, N.f i r ∉ range a) →
      (∀ r ∈ Ioo (0 : unitInterval) 1, N.g i r ∉ range a) →
      ((∃ h : ∀ r, a r ∈ A, ∀ r, c r = α ⟨a r, h r⟩) ∨
       (∃ h : ∀ r, a r ∈ B, ∀ r, c r = β ⟨a r, h r⟩)) → range c ⊆ bd T := by
    intro a c ha haf hag hc z hz
    obtain ⟨r, rfl⟩ := hz
    rcases hc with ⟨haA, hcA⟩ | ⟨haB, hcB⟩
    · rw [hcA r]
      apply (hαbd _).mpr
      refine ⟨hAd ▸ Or.inl ⟨haA r, ha (mem_range_self r)⟩, ?_⟩
      rintro ⟨v, hv, hvr⟩
      exact haf v hv ⟨r, hvr.symm⟩
    · rw [hcB r]
      apply (hβbd _).mpr
      refine ⟨hBd ▸ Or.inl ⟨haB r, ha (mem_range_self r)⟩, ?_⟩
      rintro ⟨v, hv, hvr⟩
      exact hag v hv ⟨r, hvr.symm⟩
  have hLFbd : ∀ j, j ≠ i → range (Lf j) ⊆ bd T := by
    intro j hj
    exact hOldBd (N.f j) (Lf j) (N.range_f_subset_bd j)
      (N.internally_disjoint_ff i j hj.symm) (N.internally_disjoint_gf i j) (hLf j)
  have hLGbd : ∀ j, j ≠ i → range (Lg j) ⊆ bd T := by
    intro j hj
    exact hOldBd (N.g j) (Lg j) (N.range_g_subset_bd j)
      (N.internally_disjoint_fg i j) (N.internally_disjoint_gg i j hj.symm) (hLg j)
  have hDisj := lifted_curves_internally_disjoint α β hiα hiβ (N.f i) (N.g i) hcross
  have hpq : ∀ r ∈ Ioo (0 : unitInterval) 1, p r ∉ range q := by
    intro r hr
    rintro ⟨v, hvr⟩
    obtain ⟨u, hru, _⟩ := (hcross ⟨k r, hkA r⟩ ⟨k v, hkB v⟩).mp hvr.symm
    exact hkInt r hr (N.range_f_subset_bd i ⟨u, hru.symm⟩)
  have hqp : ∀ r ∈ Ioo (0 : unitInterval) 1, q r ∉ range p := by
    intro r hr
    rintro ⟨v, hvr⟩
    obtain ⟨u, _, hru⟩ := (hcross ⟨k v, hkA v⟩ ⟨k r, hkB r⟩).mp hvr
    exact hkInt r hr (N.range_g_subset_bd i ⟨u, hru.symm⟩)
  have hPF : ∀ j, j ≠ i →
      (∀ r ∈ Ioo (0 : unitInterval) 1, p r ∉ range (Lf j)) ∧
      (∀ r ∈ Ioo (0 : unitInterval) 1, Lf j r ∉ range p) := by
    intro j hj
    exact ⟨hDisj k (N.f j) p (Lf j) hpRep (hLf j) (hkf j).1 (hkf i).1 (hkg i).1,
      hDisj (N.f j) k (Lf j) p (hLf j) hpRep (hkf j).2
        (N.internally_disjoint_ff j i hj) (N.internally_disjoint_fg j i)⟩
  have hPG : ∀ j, j ≠ i →
      (∀ r ∈ Ioo (0 : unitInterval) 1, p r ∉ range (Lg j)) ∧
      (∀ r ∈ Ioo (0 : unitInterval) 1, Lg j r ∉ range p) := by
    intro j hj
    exact ⟨hDisj k (N.g j) p (Lg j) hpRep (hLg j) (hkg j).1 (hkf i).1 (hkg i).1,
      hDisj (N.g j) k (Lg j) p (hLg j) hpRep (hkg j).2
        (N.internally_disjoint_gf j i) (N.internally_disjoint_gg j i hj)⟩
  have hQF : ∀ j, j ≠ i →
      (∀ r ∈ Ioo (0 : unitInterval) 1, q r ∉ range (Lf j)) ∧
      (∀ r ∈ Ioo (0 : unitInterval) 1, Lf j r ∉ range q) := by
    intro j hj
    exact ⟨hDisj k (N.f j) q (Lf j) hqRep (hLf j) (hkf j).1 (hkf i).1 (hkg i).1,
      hDisj (N.f j) k (Lf j) q (hLf j) hqRep (hkf j).2
        (N.internally_disjoint_ff j i hj) (N.internally_disjoint_fg j i)⟩
  have hQG : ∀ j, j ≠ i →
      (∀ r ∈ Ioo (0 : unitInterval) 1, q r ∉ range (Lg j)) ∧
      (∀ r ∈ Ioo (0 : unitInterval) 1, Lg j r ∉ range q) := by
    intro j hj
    exact ⟨hDisj k (N.g j) q (Lg j) hqRep (hLg j) (hkg j).1 (hkf i).1 (hkg i).1,
      hDisj (N.g j) k (Lg j) q (hLg j) hqRep (hkg j).2
        (N.internally_disjoint_gf j i) (N.internally_disjoint_gg j i hj)⟩
  refine ⟨k, f, g, hki, hkF, hk0, hk1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j = i
    · subst j; rw [hfi]; exact hpi
    · rw [hfj j hj]; exact curve_lift_injective α β hiα hiβ (N.f j) (Lf j) (N.injective_f j) (hLf j)
  · intro j
    by_cases hj : j = i
    · subst j; rw [hgi]; exact hqi
    · rw [hgj j hj]; exact curve_lift_injective α β hiα hiβ (N.g j) (Lg j) (N.injective_g j) (hLg j)
  · intro j
    by_cases hj : j = i
    · subst j; rw [hfi]; exact hpbd
    · rw [hfj j hj]; exact hLFbd j hj
  · intro j
    by_cases hj : j = i
    · subst j; rw [hgi]; exact hqbd
    · rw [hgj j hj]; exact hLGbd j hj
  · intro j l hjl
    by_cases hj : j = i
    · subst j
      rw [hfi, hfj l hjl.symm]
      exact (hPF l hjl.symm).1
    · by_cases hl : l = i
      · subst l; rw [hfj j hj, hfi]; exact (hPF j hj).2
      · rw [hfj j hj, hfj l hl]
        exact hDisj (N.f j) (N.f l) (Lf j) (Lf l) (hLf j) (hLf l)
          (N.internally_disjoint_ff j l hjl) (N.internally_disjoint_ff j i hj)
            (N.internally_disjoint_fg j i)
  · intro j l hjl
    by_cases hj : j = i
    · subst j
      rw [hgi, hgj l hjl.symm]
      exact (hQG l hjl.symm).1
    · by_cases hl : l = i
      · subst l; rw [hgj j hj, hgi]; exact (hQG j hj).2
      · rw [hgj j hj, hgj l hl]
        exact hDisj (N.g j) (N.g l) (Lg j) (Lg l) (hLg j) (hLg l)
          (N.internally_disjoint_gg j l hjl) (N.internally_disjoint_gf j i)
            (N.internally_disjoint_gg j i hj)
  · intro j l
    by_cases hj : j = i
    · subst j
      by_cases hl : l = i
      · subst l; rw [hfi, hgi]; exact hpq
      · rw [hfi, hgj l hl]; exact (hPG l hl).1
    · by_cases hl : l = i
      · subst l; rw [hfj j hj, hgi]; exact (hQF j hj).2
      · rw [hfj j hj, hgj l hl]
        exact hDisj (N.f j) (N.g l) (Lf j) (Lg l) (hLf j) (hLg l)
          (N.internally_disjoint_fg j l) (N.internally_disjoint_ff j i hj)
            (N.internally_disjoint_fg j i)
  · intro j l
    by_cases hj : j = i
    · subst j
      by_cases hl : l = i
      · subst l; rw [hgi, hfi]; exact hqp
      · rw [hgi, hfj l hl]; exact (hQF l hl).1
    · by_cases hl : l = i
      · subst l; rw [hgj j hj, hfi]; exact (hPG j hj).2
      · rw [hgj j hj, hfj l hl]
        exact hDisj (N.g j) (N.f l) (Lg j) (Lf l) (hLg j) (hLf l)
          (N.internally_disjoint_gf j l) (N.internally_disjoint_gf j i)
            (N.internally_disjoint_gg j i hj)
  · intro j r
    by_cases hj : j = i
    · subst j; rw [hfi, hgi]
      exact (hφA ⟨k r, hkA r⟩).trans (hφB ⟨k r, hkB r⟩).symm
    · rw [hfj j hj, hgj j hj]
      exact (curve_lift_map α β φ N.φ hφA hφB (N.f j) (Lf j) (hLf j) r).trans
        ((N.pasting_eq j r).trans (curve_lift_map α β φ N.φ hφA hφB (N.g j) (Lg j) (hLg j) r).symm)
  · intro r x hx
    rw [hfi]
    exact congrArg α (Subtype.ext hx.symm)
  · intro r y hy
    rw [hgi]
    exact congrArg β (Subtype.ext hy.symm)
  · intro j hj
    rw [hfj j hj]
    exact hLf j
  · intro j hj
    rw [hgj j hj]
    exact hLg j

end GraphMinor.GM07
