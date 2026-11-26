/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section6a
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Graph Minors XX, Section 6, (6.1), the second and third axioms

The third axiom is immediate from the order on triples. The second axiom has three cases, according
to which sides contain `f`, as in the paper.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set GraphMinor.GM18 GraphMinor.GM10 Hypergraph GraphMinor.GM04

universe u v

variable {α : Type u} {β : Type v} {G A B C D : Hypergraph α β} {v : α ⊕ β → ℝ} {f : β}

theorem lex_thd_lt {a a' b b' c c' : ℝ} (h : toLex (a, toLex (b, c)) < toLex (a', toLex (b', c')))
    (ha : a = a') (hb : b = b') : c < c' := by
  subst ha
  subst hb
  rcases Prod.Lex.toLex_lt_toLex.mp h with h₁ | ⟨-, h₁⟩
  · exact absurd h₁ (lt_irrefl _)
  · rcases Prod.Lex.toLex_lt_toLex.mp h₁ with h₂ | ⟨-, h₂⟩
    · exact absurd h₂ (lt_irrefl _)
    · exact h₂

/-- The first term of `λ(A, B)` is the order of `(A, B)`. -/
theorem edgeBasedLam_eq (A B : Hypergraph α β) : ∃ b c : ℝ, edgeBasedLam G f v (A, B) =
    toLex ((separationOrder A B : ℝ), toLex (b, c)) := by
  by_cases hf : f ∈ A.edgeSet
  · rw [edgeBasedLam_of_mem hf]
    exact ⟨_, _, rfl⟩
  · rw [edgeBasedLam_of_notMem hf, separationOrder_comm A B]
    exact ⟨_, _, rfl⟩

/-- The third axiom. -/
theorem edgeBased_axiom3 : TieBreakerAxiom3 G (edgeBasedLam G f v) := by
  intro A B C D _ _ hlt
  obtain ⟨b, c, h₁⟩ := edgeBasedLam_eq (G := G) (f := f) (v := v) A B
  obtain ⟨b', c', h₂⟩ := edgeBasedLam_eq (G := G) (f := f) (v := v) C D
  rw [h₁, h₂]
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (Nat.cast_lt.mpr hlt))

theorem triple_congr {X Y X' Y' : Hypergraph α β} (ho : separationOrder X Y = separationOrder X' Y')
    (hz : zSet X = zSet X') (hV : (X ∩ Y).vertexSet = (X' ∩ Y').vertexSet) :
    edgeBasedTriple G v X Y = edgeBasedTriple G v X' Y' := by
  rw [edgeBasedTriple, edgeBasedTriple, ho, hz, hV]

theorem vertexSet_of_zSet_eq {X X' : Hypergraph α β} (h : zSet X = zSet X') :
    X.vertexSet = X'.vertexSet := by
  have key : ∀ {X X' : Hypergraph α β}, zSet X = zSet X' → X.vertexSet ⊆ X'.vertexSet := by
    intro X X' h x hx
    have : Sum.inl x ∈ zSet X' := h ▸ Or.inl ⟨x, hx, rfl⟩
    rcases this with ⟨y, hy, hxy⟩ | ⟨y, _, hxy⟩
    · exact Sum.inl_injective hxy ▸ hy
    · exact absurd hxy (by simp)
  exact (key h).antisymm (key h.symm)

/-- The step shared by the first two cases: if `X ⊆ X'`, `Y' ⊆ Y` with the same order and the triple
of `(X, Y)` is at most the triple of `(X', Y')`, then they are equal. -/
theorem tie_step (hv : IsIndependentWeight G v) {X Y X' Y' : Hypergraph α β} (hX' : X' ≤ G)
    (hz : zSet X ⊆ zSet X') (hY : Y' ≤ Y) (ho : separationOrder X Y = separationOrder X' Y')
    (h : edgeBasedTriple G v X Y ≤ edgeBasedTriple G v X' Y') :
    edgeBasedTriple G v X Y = edgeBasedTriple G v X' Y' := by
  have hs := lex_snd_le h (by exact_mod_cast ho)
  have hz' := hz.antisymm (zSet_subset_of_le_weight hv.1 hX' hz hs)
  refine triple_congr ho hz' ?_
  refine (Set.eq_of_subset_of_ncard_le (s := (X' ∩ Y').vertexSet) (t := (X ∩ Y).vertexSet) ?_ ho.le
    (X ∩ Y).vertexSet_finite).symm
  intro x hx
  exact ⟨by rw [vertexSet_of_zSet_eq hz']; exact hx.1, hY.vertexSet_subset hx.2⟩

/-- The second axiom. -/
theorem edgeBased_axiom2 (hf : f ∈ G.edgeSet) (hv : IsIndependentWeight G v) :
    TieBreakerAxiom2 G (edgeBasedLam G f v) := by
  intro A B C D h₁ h₂
  by_contra hcon
  rw [not_or, not_le, not_lt] at hcon
  obtain ⟨hl₁, hl₂⟩ := hcon
  have h₃ : G.IsSeparation (A ∪ C) (B ∩ D) := h₁.union_inter h₂
  have h₄ : G.IsSeparation (A ∩ C) (B ∪ D) := (h₁.symm.union_inter h₂.symm).symm
  have hax3 := edgeBased_axiom3 (G := G) (f := f) (v := v)
  have ho₁ : separationOrder A B ≤ separationOrder (A ∪ C) (B ∩ D) := by
    by_contra hn
    exact absurd hl₁ (not_lt.mpr (hax3 h₃ h₁ (not_le.mp hn)).le)
  have ho₂ : separationOrder C D ≤ separationOrder (A ∩ C) (B ∪ D) := by
    by_contra hn
    exact absurd hl₂ (not_le.mpr (hax3 h₄ h₂ (not_le.mp hn)))
  have hsum := order_add_order h₁ h₂
  have ho₃ : separationOrder A B = separationOrder (A ∪ C) (B ∩ D) := by omega
  have ho₄ : separationOrder C D = separationOrder (A ∩ C) (B ∪ D) := by omega
  have hzA : zSet A ⊆ zSet (A ∪ C) := zSet_mono (le_union_left h₁.left_le h₂.left_le)
  have hzC : zSet C ⊆ zSet (A ∪ C) := zSet_mono (le_union_right h₁.left_le h₂.left_le)
  have hzB : zSet B ⊆ zSet (B ∪ D) := zSet_mono (le_union_left h₁.right_le h₂.right_le)
  have hzD : zSet D ⊆ zSet (B ∪ D) := zSet_mono (le_union_right h₁.right_le h₂.right_le)
  have hleA : A ≤ A ∪ C := le_union_left h₁.left_le h₂.left_le
  have hleCU : C ≤ A ∪ C := le_union_right h₁.left_le h₂.left_le
  have hleB : B ≤ B ∪ D := le_union_left h₁.right_le h₂.right_le
  have hleDU : D ≤ B ∪ D := le_union_right h₁.right_le h₂.right_le
  have hBD : B ∩ D ≤ B := inter_le_left h₁.right_le h₂.right_le
  have hAC : A ∩ C ≤ C := inter_le_right h₁.left_le h₂.left_le
  have hnot : ∀ {X Y}, G.IsSeparation X Y → f ∈ X.edgeSet → f ∉ Y.edgeSet := fun h hX ↦
    IsSeparation.not_mem_of_mem h hX
  by_cases ha : f ∈ A.edgeSet
  · -- First case: `f ∈ E(A)`.
    have hu : f ∈ (A ∪ C).edgeSet := Or.inl ha
    rw [edgeBasedLam_of_mem ha, edgeBasedLam_of_mem hu] at hl₁
    exact absurd (tie_step hv h₃.left_le hzA hBD ho₃ hl₁.le) hl₁.ne
  have hb : f ∈ B.edgeSet := (mem_or_mem h₁ hf).resolve_left ha
  have hnac : f ∉ (A ∩ C).edgeSet := fun h ↦ ha h.1
  by_cases hd : f ∈ D.edgeSet
  · -- Second case: `f ∈ E(B) ∩ E(D)`.
    have hc : f ∉ C.edgeSet := hnot h₂.symm hd
    rw [edgeBasedLam_of_notMem hc, edgeBasedLam_of_notMem hnac] at hl₂
    have hBDC := inter_comm A C
    have heq := tie_step hv h₄.right_le hzD (Y' := A ∩ C) hAC
      (by rw [separationOrder_comm D C, separationOrder_comm (B ∪ D) _]; exact ho₄) hl₂
    obtain ⟨h₅, h₆⟩ := eq_of_triple_eq hv h₂.symm h₄.symm heq
    have hCA : C ≤ A := by rw [h₆]; exact inter_le_left h₁.left_le h₂.left_le
    have hBleD : B ≤ D := by rw [h₅]; exact hleB
    have e₁ : A ∪ C = A := le_antisymm (union_le le_rfl hCA) hleA
    have e₂ : B ∩ D = B := le_antisymm hBD
      ((le_iff_of_le h₁.right_le (inter_le h₁.right_le h₂.right_le)).mpr
        ⟨fun _ hx ↦ ⟨hx, hBleD.vertexSet_subset hx⟩, fun _ hx ↦ ⟨hx, hBleD.edgeSet_subset hx⟩⟩)
    rw [e₁, e₂] at hl₁
    exact lt_irrefl _ hl₁
  · -- Third case: `f ∈ E(B ∩ C)`.
    have hc : f ∈ C.edgeSet := (mem_or_mem h₂ hf).resolve_right hd
    have hu : f ∈ (A ∪ C).edgeSet := Or.inr hc
    rw [edgeBasedLam_of_notMem ha, edgeBasedLam_of_mem hu] at hl₁
    rw [edgeBasedLam_of_mem hc, edgeBasedLam_of_notMem hnac] at hl₂
    have ho₅ : (separationOrder B A : ℝ) = separationOrder (A ∪ C) (B ∩ D) := by
      rw [separationOrder_comm B A]
      exact_mod_cast ho₃
    have ho₆ : (separationOrder C D : ℝ) = separationOrder (B ∪ D) (A ∩ C) := by
      rw [separationOrder_comm (B ∪ D) (A ∩ C)]
      exact_mod_cast ho₄
    have s₁ := lex_snd_le hl₁.le ho₅
    have s₂ := lex_snd_le hl₂ ho₆
    have m₁ : weight G v (zSet G \ zSet (A ∪ C)) ≤ weight G v (zSet G \ zSet C) :=
      weight_le hv.1 (zSet_sdiff_antitone hzC)
    have m₂ : weight G v (zSet G \ zSet (B ∪ D)) ≤ weight G v (zSet G \ zSet B) :=
      weight_le hv.1 (zSet_sdiff_antitone hzB)
    have hzAC : zSet (A ∪ C) ⊆ zSet C := zSet_subset_of_le_weight hv.1 h₃.left_le hzC (by linarith)
    have hzBD : zSet (B ∪ D) ⊆ zSet B :=
      zSet_subset_of_le_weight hv.1 h₄.right_le hzB (by linarith)
    have huBC : weight G v (zSet G \ zSet B) = weight G v (zSet G \ zSet C) := by linarith
    have hBC : B = C := by
      have hZ := eq_of_weight_eq hv sdiff_subset sdiff_subset huBC
      have hBZ : zSet B ⊆ zSet C := fun z hz ↦ by
        by_contra hn
        have : z ∈ zSet G \ zSet C := ⟨zSet_mono h₁.right_le hz, hn⟩
        rw [← hZ] at this
        exact this.2 hz
      have hCZ : zSet C ⊆ zSet B := fun z hz ↦ by
        by_contra hn
        have : z ∈ zSet G \ zSet B := ⟨zSet_mono h₂.left_le hz, hn⟩
        rw [hZ] at this
        exact this.2 hz
      exact le_antisymm (le_of_zSet_subset h₁.right_le h₂.left_le hBZ)
        (le_of_zSet_subset h₂.left_le h₁.right_le hCZ)
    have hAleC : A ≤ C := hleA.trans (le_of_zSet_subset h₃.left_le h₂.left_le hzAC)
    have hDleB : D ≤ B := hleDU.trans (le_of_zSet_subset h₄.right_le h₁.right_le hzBD)
    have t₁ := lex_thd_lt hl₁ ho₅ (by linarith)
    have t₂ := lex_thd_le hl₂ ho₆ (by linarith)
    have e₁ : ((B ∪ D) ∩ (A ∩ C)).vertexSet = (B ∩ A).vertexSet := by
      ext x
      constructor
      · rintro ⟨h₅ | h₅, h₆, h₇⟩
        · exact ⟨h₅, h₆⟩
        · exact ⟨hDleB.vertexSet_subset h₅, h₆⟩
      · rintro ⟨h₅, h₆⟩
        exact ⟨Or.inl h₅, h₆, hAleC.vertexSet_subset h₆⟩
    have e₂ : ((A ∪ C) ∩ (B ∩ D)).vertexSet = (C ∩ D).vertexSet := by
      ext x
      constructor
      · rintro ⟨-, h₅, h₆⟩
        exact ⟨hBC ▸ h₅, h₆⟩
      · rintro ⟨h₅, h₆⟩
        exact ⟨Or.inr h₅, hDleB.vertexSet_subset h₆, h₆⟩
    rw [e₁] at t₂
    rw [e₂] at t₁
    exact absurd t₁ (not_lt.mpr t₂)

/-- Graph Minors XX, (6.1) (page 342): "`λ` is a tie-breaker." -/
theorem theorem_6_1_proof (hf : f ∈ G.edgeSet) (hv : IsIndependentWeight G v) :
    IsTieBreaker G (edgeBasedLam G f v) :=
  ⟨edgeBased_axiom1 hf hv, edgeBased_axiom2 hf hv, edgeBased_axiom3⟩

/-- There is a weight as in (6.1), since `ℝ` has infinite dimension over `ℚ`. -/
theorem exists_isIndependentWeight (G : Hypergraph α β) : ∃ v, IsIndependentWeight G v := by
  classical
  let b := Module.Basis.ofVectorSpace ℚ ℝ
  let ι := Module.Basis.ofVectorSpaceIndex ℚ ℝ
  have hinf : Infinite ι := by
    rw [← not_finite_iff_infinite]
    intro hfin
    have h₁ : Module.rank ℚ ℝ = Cardinal.mk ι := b.mk_eq_rank''.symm
    have h₂ : Cardinal.mk ι < Cardinal.aleph0 := Cardinal.lt_aleph0_iff_finite.mpr hfin
    rw [← h₁, Real.rank_rat_real] at h₂
    exact absurd h₂ (not_lt.mpr Cardinal.aleph0_le_continuum)
  obtain ⟨g, hg⟩ := exists_injOn_of_finite (δ := ι) (finite_zSet G)
  let v : α ⊕ β → ℝ := fun x ↦ |b (g x)|
  have hpos : ∀ x, 0 < v x := fun x ↦ abs_pos.mpr (b.ne_zero _)
  refine ⟨v, fun x _ ↦ hpos x, ?_⟩
  have hli : LinearIndependent ℚ (fun x : zSet G ↦ b (g x.1)) :=
    b.linearIndependent.comp _ fun x y h ↦ Subtype.ext (hg x.2 y.2 h)
  let s : zSet G → ℚˣ := fun x ↦ if 0 ≤ b (g x.1) then 1 else -1
  have := hli.units_smul s
  convert this using 1
  ext x
  simp only [Pi.smul_apply', s, v]
  split_ifs with h
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (not_le.mp h)]

end GraphMinor.GM20
