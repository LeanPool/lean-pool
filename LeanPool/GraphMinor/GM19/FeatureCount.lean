/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FeatureLines
public import LeanPool.GraphMinor.GM19.Conditional2
public import LeanPool.GraphMinor.GM11.PaintingCells

/-!
# Graph Minors XIX, (5.2): there are finitely many features of bounded size

Each feature gives a family of lines with a bounded number of lines (`exists_feature_lines`). Cut
the surface along the lines. There
are finitely many codes of the result (`finite_codes`), and two families with one code differ by a
homeomorphism of the surface
(`homeo_of_code`). We add to the code a tag for each line, which says what the line does in the
frame and in the feature. Two features
with one code and the same tags differ by a homeomorphism that keeps the frame
(`frame_homeo_of_lines`). This homeomorphism may reverse the
orientation, but then it reverses all orientations (`homeo_orientation`), and two reversing maps in
a row keep them. So each code and
list of tags needs at most two features (`finite_reps_of_labels`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Function Metric GraphMinor.Surface

local notation "𝕀" => unitInterval

/-- At most two representatives for each label, when two objects with one label are equal or
opposite, and two opposites make
an equal. -/
theorem finite_reps_of_labels {D L : Type*} [Finite L] (Q : L → D → Prop) (Eqv Rev : D → D → Prop)
    (hsame : ∀ l K K', Q l K → Q l K' → Eqv K K' ∨ Rev K K') (hrr : ∀ K K' K'', Rev K K'
      → Rev K' K'' → Eqv K K'') :
    ∃ 𝓕 : Set D, 𝓕.Finite ∧ ∀ K, (∃ l, Q l K) → ∃ K₀ ∈ 𝓕, Eqv K₀ K := by
  classical
  have h1 : ∀ l, ∃ s : Set D, s.Finite ∧ ∀ K, Q l K → ∃ K₀ ∈ s, Eqv K₀ K := by
    intro l
    by_cases hne : ∃ K, Q l K
    · obtain ⟨K₀, h0⟩ := hne
      by_cases hrev : ∃ K₁, Q l K₁ ∧ Rev K₀ K₁
      · obtain ⟨K₁, h2, h3⟩ := hrev
        refine ⟨{K₀, K₁}, by simp, fun K hK ↦ ?_⟩
        rcases hsame l K₀ K h0 hK with h | h
        · exact ⟨K₀, .inl rfl, h⟩
        · rcases hsame l K₁ K h2 hK with h' | h'
          · exact ⟨K₁, .inr rfl, h'⟩
          · exact ⟨K₀, .inl rfl, hrr _ _ _ h3 h'⟩
      · refine ⟨{K₀}, by simp, fun K hK ↦ ?_⟩
        rcases hsame l K₀ K h0 hK with h | h
        · exact ⟨K₀, rfl, h⟩
        · exact absurd ⟨K, hK, h⟩ hrev
    · exact ⟨∅, finite_empty, fun K hK ↦ absurd ⟨K, hK⟩ hne⟩
  choose s hs hs' using h1
  refine ⟨⋃ l, s l, finite_iUnion hs, ?_⟩
  rintro K ⟨l, hl⟩
  obtain ⟨K₀, h0, h2⟩ := hs' l K hl
  exact ⟨K₀, mem_iUnion.mpr ⟨l, h0⟩, h2⟩

variable {S : Type} [TopologicalSpace S] [T2Space S]

/-- What a line of a family does: the side of the frame that holds it, the frame vertices at its two
ends, and whether its two ends are
vertices of the feature. -/
abbrev LineTag (Φ : Frame S) : Type := Option Φ.sides × Option Φ.V × Option Φ.V × Prop × Prop

/-- The tag `t` is right for the line `b i`. -/
def IsLineTag (Φ : Frame S) (K : Drawing S) {m : ℕ} (b : Fin m → 𝕀 → S) (inner : Fin m → Prop)
  (i : Fin m) (t : LineTag Φ) : Prop :=
  (¬ inner i → ∃ s : Φ.sides, t.1 = some s ∧ range (b i) \ Φ.V ⊆ s.1) ∧ (∀ v : Φ.V, b i 0
    = v.1 ↔ t.2.1 = some v) ∧
    (∀ v : Φ.V, b i 1 = v.1 ↔ t.2.2.1 = some v) ∧ (t.2.2.2.1 ↔ b i 0 ∈ K.V) ∧
      (t.2.2.2.2 ↔ b i 1 ∈ K.V)

omit [T2Space S] in
/-- Each line of a family made from a feature has a tag. -/
theorem exists_line_tag {Φ : Frame S} {K : Drawing S} {m : ℕ} {b : Fin m → 𝕀 → S} {inner : Fin m
  → Prop}
    (D : FeatureLines Φ K b inner) (i : Fin m) : ∃ t, IsLineTag Φ K b inner i t := by
  classical
  have hend : ∀ x : S, ∃ o : Option Φ.V, ∀ v : Φ.V, x = v.1 ↔ o = some v := fun x ↦ by
    by_cases hx : x ∈ Φ.V
    · refine ⟨some ⟨x, hx⟩, fun v ↦ ?_⟩
      simp only [Option.some.injEq]
      exact ⟨fun h ↦ Subtype.ext h, fun h ↦ by rw [← h]⟩
    · refine ⟨none, fun v ↦ ?_⟩
      simp only [reduceCtorEq, iff_false]
      exact fun h ↦ hx (h ▸ v.2)
  obtain ⟨o₀, h₀⟩ := hend (b i 0)
  obtain ⟨o₁, h₁⟩ := hend (b i 1)
  by_cases hi : inner i
  · exact ⟨(none, o₀, o₁, _, _), fun h ↦ absurd hi h, h₀, h₁, Iff.rfl, Iff.rfl⟩
  · obtain ⟨s, hs, hsub⟩ := D.side i hi
    exact ⟨(some ⟨s, hs⟩, o₀, o₁, _, _), fun _ ↦ ⟨⟨s, hs⟩, rfl, hsub⟩, h₀, h₁, Iff.rfl, Iff.rfl⟩

omit [T2Space S] in
/-- Two features with families of the same shape and the same tags differ by a homeomorphism that
keeps the frame, if the
homeomorphism carries lines to lines. -/
theorem frame_homeo_of_lines {Φ : Frame S} {K K' : Drawing S} {m : ℕ} {b b' : Fin m → 𝕀
  → S} {inner : Fin m → Prop}
    (D : FeatureLines Φ K b inner) (D' : FeatureLines Φ K' b' inner) {tag : Fin m → LineTag Φ}
    (ht : ∀ i, IsLineTag Φ K b inner i (tag i)) (ht' : ∀ i, IsLineTag Φ K' b' inner i (tag i))
      (e : S ≃ₜ S)
    (he : ∀ i, ∀ t : 𝕀, e (b i t) = b' i t) :
    (∀ v ∈ Φ.V, e v = v) ∧ (∀ s ∈ Φ.sides, e '' s = s) ∧ e '' K.U = K'.U ∧ e '' K.V = K'.V := by
  have hfix : ∀ v ∈ Φ.V, e v = v := by
    intro v hv
    obtain ⟨i, h | h⟩ := D.vertΦ v hv
    · have h1 := ((ht i).2.1 ⟨v, hv⟩).1 h
      have h2 := ((ht' i).2.1 ⟨v, hv⟩).2 h1
      rw [← h, he, h2, h]
    · have h1 := ((ht i).2.2.1 ⟨v, hv⟩).1 h
      have h2 := ((ht' i).2.2.1 ⟨v, hv⟩).2 h1
      rw [← h, he, h2, h]
  have hnotV : ∀ x, x ∉ Φ.V → e x ∉ Φ.V := fun x hx h ↦ by
    have := hfix _ h
    exact hx (e.injective this ▸ h)
  have hnotV' : ∀ x, e x ∉ Φ.V → x ∉ Φ.V := fun x hx h ↦ hx ((hfix x h).symm ▸ h)
  refine ⟨hfix, ?_, ?_, ?_⟩
  · intro s hs
    have hsbd : s ⊆ bd S \ Φ.V := hs.2.1
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨i, hi, t, rfl⟩ := D.border x (hsbd hx).1
      obtain ⟨s₁, hs₁, h1⟩ := (ht i).1 hi
      obtain ⟨s₂, hs₂, h2⟩ := (ht' i).1 hi
      have e1 : s₁ = s₂ := Option.some.inj (hs₁.symm.trans hs₂)
      subst e1
      have h3 : s₁.1 = s := GM11.arcComponent_eq s₁.2 hs (h1 ⟨⟨t, rfl⟩, (hsbd hx).2⟩) hx
      rw [he, ← h3]
      apply h2 ⟨⟨t, rfl⟩, ?_⟩
      rw [← he]
      exact hnotV _ (hsbd hx).2
    · intro y hy
      obtain ⟨i, hi, t, rfl⟩ := D'.border y (hsbd hy).1
      obtain ⟨s₁, hs₁, h1⟩ := (ht i).1 hi
      obtain ⟨s₂, hs₂, h2⟩ := (ht' i).1 hi
      have e1 : s₁ = s₂ := Option.some.inj (hs₁.symm.trans hs₂)
      subst e1
      have h3 : s₁.1 = s := GM11.arcComponent_eq s₁.2 hs (h2 ⟨⟨t, rfl⟩, (hsbd hy).2⟩) hy
      have hoff : b i t ∉ Φ.V := hnotV' _ (by rw [he]; exact (hsbd hy).2)
      exact ⟨b i t, h3 ▸ h1 ⟨⟨t, rfl⟩, hoff⟩, he i t⟩
  · rw [D.eqU, D'.eqU]
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨i, hi, t, rfl⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion₂.mpr ⟨i, hi, t, (he i t).symm⟩
    · intro y hy
      obtain ⟨i, hi, t, rfl⟩ := mem_iUnion₂.mp hy
      exact ⟨b i t, mem_iUnion₂.mpr ⟨i, hi, t, rfl⟩, he i t⟩
  · apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨i, -, h | h⟩ := D.vertK x hx
      · rw [← h, he]
        exact (ht' i).2.2.2.1.1 ((ht i).2.2.2.1.2 (h ▸ hx))
      · rw [← h, he]
        exact (ht' i).2.2.2.2.1 ((ht i).2.2.2.2.2 (h ▸ hx))
    · intro y hy
      obtain ⟨i, -, h | h⟩ := D'.vertK y hy
      · exact ⟨b i 0, (ht i).2.2.2.1.1 ((ht' i).2.2.2.1.2 (h ▸ hy)), by rw [he, h]⟩
      · exact ⟨b i 1, (ht i).2.2.2.2.1 ((ht' i).2.2.2.2.2 (h ▸ hy)), by rw [he, h]⟩

/-- The four conditions of a homeomorphism that keeps a frame and carries `K` to `K'`, and that
reverses all orientations. -/
def FeatureRev (Φ : Frame S) (K K' : Drawing S) : Prop :=
  ∃ f : S ≃ₜ S, (∀ v ∈ Φ.V, f v = v) ∧ (∀ s ∈ Φ.sides, f '' s = s) ∧ f '' K.U = K'.U ∧ f '' K.V
    = K'.V ∧
    ∀ ω : SurfaceOrientation S, IsReversedBy ω f

/-- **Graph Minors XIX, (5.2).** -/
theorem theorem_5_2_proof : Theorem52Statement := by
  classical
  intro S _ _ hS hconn Φ n
  obtain ⟨B, hB⟩ := exists_feature_lines hS Φ
  let M : ℕ := B + Φ.V.ncard + 3 * n
  have hex : ∀ (m : ℕ) (inner : Fin m → Prop), ∃ 𝒦 : Set (Set (PieceCode inner)), 𝒦.Finite ∧
    (Nonempty (Fin m) →
      ∀ b : Fin m → 𝕀 → S, IsLineFamily b inner → ∀ (V : Set S) (E 𝓕 : Set
        (Set S)), IsDissection V E 𝓕 →
        (∀ i, b i 0 ∈ V ∧ b i 1 ∈ V) → (∀ i, range (b i) ⊆ gr V E) → ∃ κ ∈ 𝒦, HasCode b inner κ)
          := by
    intro m inner
    by_cases hm : Nonempty (Fin m)
    · obtain ⟨𝒦, h1, h2⟩ := finite_codes hS inner
      exact ⟨𝒦, h1, fun _ ↦ h2⟩
    · exact ⟨∅, finite_empty, fun h ↦ absurd h hm⟩
  choose 𝒦 h𝒦 h𝒦c using hex
  have : Finite Φ.sides := Φ.finite_sides.to_subtype
  have : Finite Φ.V := Φ.finite_V.to_subtype
  have : ∀ m inner, Finite (𝒦 m inner) := fun m inner ↦ (h𝒦 m inner).to_subtype
  let L : Type := Σ m : Fin (M + 1), Σ inner : Fin m.1 → Prop, (Fin m.1 → LineTag Φ) × Option
    (𝒦 m.1 inner)
  let Q : L → Drawing S → Prop := fun l K ↦ ∃ b : Fin l.1.1 → 𝕀 → S, FeatureLines Φ K b l.2.1 ∧
    (∀ i, IsLineTag Φ K b l.2.1 i (l.2.2.1 i)) ∧ ((IsEmpty (Fin l.1.1) ∧ l.2.2.2 = none)
      ∨ ∃ κ, l.2.2.2 = some κ ∧ HasCode b l.2.1 κ.1)
  have hsame : ∀ l K K', Q l K → Q l K' → FeatureEquiv Φ K K' ∨ FeatureRev Φ K K' := by
    rintro ⟨m, inner, tag, κo⟩ K K' ⟨b, D, ht, hc⟩ ⟨b', D', ht', hc'⟩
    obtain ⟨e, he⟩ : ∃ e : S ≃ₜ S, ∀ i, ∀ t : 𝕀, e (b i t) = b' i t := by
      rcases hc with ⟨hemp, -⟩ | ⟨κ, h1, h2⟩
      · exact ⟨Homeomorph.refl S, fun i ↦ (hemp.false i).elim⟩
      · rcases hc' with ⟨-, h3⟩ | ⟨κ', h3, h4⟩
        · simp only at h1 h3
          rw [h1] at h3
          exact absurd h3 (by simp)
        · have hκ : κ = κ' := Option.some.inj (h1.symm.trans h3)
          subst hκ
          obtain ⟨e, he⟩ := homeo_of_code D.family D'.family h2 h4
          refine ⟨e, fun i t ↦ ?_⟩
          have := he i t t.2
          rwa [extI_coe, extI_coe] at this
    obtain ⟨h1, h2, h3, h4⟩ := frame_homeo_of_lines D D' ht ht' e he
    rcases homeo_orientation hS e with h5 | h5
    · exact .inl ⟨e, ⟨h1, h2, h5⟩, h3, h4⟩
    · exact .inr ⟨e, h1, h2, h3, h4, h5⟩
  have hrr : ∀ K K' K'', FeatureRev Φ K K' → FeatureRev Φ K' K'' → FeatureEquiv Φ K K'' := by
    rintro K K' K'' ⟨f, h1, h2, h3, h4, h5⟩ ⟨g, h1', h2', h3', h4', h5'⟩
    refine ⟨f.trans g, ⟨fun v hv ↦ ?_, fun s hs ↦ ?_, fun ω ↦ preserved_of_reversed (h5 ω)
      (h5' ω)⟩, ?_, ?_⟩
    · change g (f v) = v
      rw [h1 v hv, h1' v hv]
    · have : (f.trans g) '' s = g '' (f '' s) := by
        rw [image_image]
        rfl
      rw [this, h2 s hs, h2' s hs]
    · have : (f.trans g) '' K.U = g '' (f '' K.U) := by
        rw [image_image]
        rfl
      rw [this, h3, h3']
    · have : (f.trans g) '' K.V = g '' (f '' K.V) := by
        rw [image_image]
        rfl
      rw [this, h4, h4']
  obtain ⟨𝓕, hf, h𝓕⟩ := finite_reps_of_labels Q (FeatureEquiv Φ) (FeatureRev Φ) hsame hrr
  refine ⟨𝓕, hf, fun K hK hn ↦ h𝓕 K ?_⟩
  obtain ⟨m, b, inner, hm, D⟩ := hB K hK
  have hmM : m < M + 1 := by
    have : K.E.ncard ≤ n := by omega
    have : K.V.ncard ≤ n := by omega
    simp only [M]
    omega
  have htag := fun i ↦ exists_line_tag D i
  choose tag htag using htag
  by_cases hne : Nonempty (Fin m)
  · obtain ⟨V, E, 𝓕', hd, h0, h1⟩ := D.cuts
    obtain ⟨κ, hκ, hc⟩ := h𝒦c m inner hne b D.family V E 𝓕' hd h0 h1
    exact ⟨⟨⟨m, hmM⟩, inner, tag, some ⟨κ, hκ⟩⟩, b, D, htag, .inr ⟨⟨κ, hκ⟩, rfl, hc⟩⟩
  · exact ⟨⟨⟨m, hmM⟩, inner, tag, none⟩, b, D, htag, .inl ⟨not_nonempty_iff.mp hne, rfl⟩⟩

end GraphMinor.GM19
