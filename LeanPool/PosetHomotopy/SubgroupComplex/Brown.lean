/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.PosetHomotopy.SubgroupComplex.Basic
public import LeanPool.PosetHomotopy.OrderComplex.FixedPoints
public import Mathlib.GroupTheory.Sylow

/-!
# Brown's homological Sylow theorem (roadmap 4.7)

For a finite group `G` and a prime `p`, the Euler characteristic of `S_p(G)` is congruent to `1`
modulo the `p`-part of `|G|` (`eulerChar_pSubgroupPoset_modEq`; K. S. Brown, « Euler
characteristics of groups: the p-fractional part », Invent. Math. 29 (1975), 1–5, Corollary 2 to
Theorem 2). The route is roadmap 3.5 for a Sylow `p`-subgroup `P` acting by conjugation: for a
nontrivial `Q ≤ P`, the fixed subposet `S_p(G)^Q` is the set of nontrivial `p`-subgroups
normalized by `Q`, on which `R ↦ RQ` is a closure operator whose closed elements lie above `Q`
(Brown 1975, the lemma to Theorem 2), so its Euler characteristic is `1`
(`chainSum_eq_one_of_closure`).
-/

@[expose] public section

open Finset Pointwise

namespace LeanPool.PosetHomotopy

universe u

variable {G : Type u} [Group G] {p : ℕ}

/-- Conjugation by `g` fixes a subgroup exactly when `g` normalizes it. -/
theorem toConjAct_smul_eq_iff (g : G) (H : Subgroup G) :
    ConjAct.toConjAct g • H = H ↔ g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    rw [← Subgroup.smul_mem_pointwise_smul_iff (a := ConjAct.toConjAct g), h, ConjAct.smul_def,
      ConjAct.ofConjAct_toConjAct]
  · intro h
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def, map_inv,
      ConjAct.ofConjAct_toConjAct, inv_inv]
    have := h (g⁻¹ * x * g)
    simp only [mul_assoc, mul_inv_cancel, mul_one, ← mul_assoc g, mul_inv_cancel, one_mul]
      at this
    rw [mul_assoc]
    exact this

/-- The action of a subgroup `P` of `G` on `S_p(G)` by conjugation. -/
@[reducible]
def subgroupConjAction (P : Subgroup G) : MulAction P (PSubgroupPoset G p) :=
  MulAction.compHom _ ((MulEquiv.toMonoidHom ConjAct.toConjAct).comp P.subtype)

/-- **Roadmap 4.7.** For a nontrivial subgroup `Q` of a `p`-subgroup `P` of `G`, the subposet of
`S_p(G)` fixed by `Q` under conjugation has Euler characteristic `1`. -/
theorem chainEulerChar_fixed_eq_one [Finite G] {P : Subgroup G} (hP : IsPGroup p P)
    (Q : Subgroup P) (hQ : Q ≠ ⊥) :
    letI := subgroupConjAction (p := p) P
    chainEulerChar {x : PSubgroupPoset G p // ∀ g ∈ Q, g • x = x} = 1 := by
  classical
  let := subgroupConjAction (p := p) P
  let := Fintype.ofFinite (PSubgroupPoset G p)
  set Q' : Subgroup G := Q.map P.subtype with hQ'
  have hQ'p : IsPGroup p Q' := hP.to_le (Subgroup.map_subtype_le Q) |>.to_le le_rfl
  have hQ'ne : Q' ≠ ⊥ := by
    rw [hQ', Ne, Subgroup.map_eq_bot_iff_of_injective _ P.subtype_injective]
    exact hQ
  have hfix : ∀ R : PSubgroupPoset G p,
      (∀ g ∈ Q, g • R = R) ↔ Q' ≤ Subgroup.normalizer ((R : Subgroup G) : Set G) := by
    intro R
    constructor
    · rintro h _ ⟨g, hg, rfl⟩
      exact (toConjAct_smul_eq_iff _ _).1 (congrArg Subtype.val (h g hg))
    · intro h g hg
      exact Subtype.ext ((toConjAct_smul_eq_iff _ _).2 (h ⟨g, hg, rfl⟩))
  let φ : PSubgroupPoset G p → PSubgroupPoset G p := fun R =>
    if h : Q' ≤ Subgroup.normalizer ((R : Subgroup G) : Set G) then
      ⟨R.1 ⊔ Q', fun h' => R.2.1 (eq_bot_iff.2 (le_sup_left.trans h'.le)),
        sup_comm Q' R.1 ▸ hQ'p.to_sup_of_normal_right' R.2.2 h⟩
    else R
  have hφ : ∀ R : PSubgroupPoset G p, Q' ≤ Subgroup.normalizer ((R : Subgroup G) : Set G) →
      (φ R : Subgroup G) = R.1 ⊔ Q' := fun R h => by simp only [φ, h, ↓reduceDIte]
  have hQ'norm : Q' ≤ Subgroup.normalizer (Q' : Set G) := Subgroup.le_normalizer
  rw [chainEulerChar_subtype]
  set S := univ.filter fun x : PSubgroupPoset G p => ∀ g ∈ Q, g • x = x
  have hmemS : ∀ R, R ∈ S ↔ Q' ≤ Subgroup.normalizer ((R : Subgroup G) : Set G) := fun R => by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hfix R
  -- `R ⊔ Q'` is normalized by `Q'`
  have hsupnorm : ∀ R : PSubgroupPoset G p,
      Q' ≤ Subgroup.normalizer ((R : Subgroup G) : Set G) →
      Q' ≤ Subgroup.normalizer ((R.1 ⊔ Q' : Subgroup G) : Set G) := by
    intro R h g hg
    rw [← toConjAct_smul_eq_iff, Subgroup.smul_sup, (toConjAct_smul_eq_iff _ _).2 (h hg),
      (toConjAct_smul_eq_iff _ _).2 (hQ'norm hg)]
  refine chainSum_eq_one_of_closure S φ (fun z hz => ?_) (fun a ha b hb hab => ?_)
    (fun z hz => ?_) (fun z hz => ?_) (q := ⟨Q', hQ'ne, hQ'p⟩) ?_ ?_ (fun z hz => ?_)
  · have hz' := (hmemS z).1 hz
    rw [hmemS, hφ z hz']
    exact hsupnorm z hz'
  · rw [hmemS] at ha hb
    change (φ a : Subgroup G) ≤ φ b
    rw [hφ a ha, hφ b hb]
    exact sup_le_sup_right hab Q'
  · rw [hmemS] at hz
    change (z : Subgroup G) ≤ φ z
    rw [hφ z hz]
    exact le_sup_left
  · have hz' := (hmemS z).1 hz
    have hz'' :
        Q' ≤ Subgroup.normalizer (((φ z : PSubgroupPoset G p) : Subgroup G) : Set G) := by
      rw [hφ z hz']; exact hsupnorm z hz'
    apply Subtype.ext
    rw [hφ _ hz'', hφ z hz', sup_assoc, sup_idem]
  · rw [hmemS]; exact hQ'norm
  · apply Subtype.ext
    rw [hφ _ hQ'norm]
    exact sup_idem _
  · rw [hmemS] at hz
    change Q' ≤ (φ z : Subgroup G)
    rw [hφ z hz]
    exact le_sup_right

/-- **Roadmap 4.7.** Brown's homological Sylow theorem: the Euler characteristic of `S_p(G)`, the
alternating count of the nonempty chains, is congruent to `1` modulo the `p`-part of `|G|`. -/
theorem eulerChar_pSubgroupPoset_modEq [Finite G] [Fact p.Prime] :
    chainEulerChar (PSubgroupPoset G p) ≡ 1
      [ZMOD ((p ^ (Nat.card G).factorization p : ℕ) : ℤ)] := by
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p G))
  let := subgroupConjAction (p := p) (S : Subgroup G)
  have hmono : ∀ (g : (S : Subgroup G)) (x y : PSubgroupPoset G p), x ≤ y → g • x ≤ g • y :=
    fun g x y h => smul_mono_subgroup (G := G) h (ConjAct.toConjAct (g : G))
  have := chainEulerChar_modEq_of_fixedPoints hmono
    (fun Q hQ => chainEulerChar_fixed_eq_one S.isPGroup Q hQ)
  rwa [← Sylow.card_eq_multiplicity S]

end LeanPool.PosetHomotopy
