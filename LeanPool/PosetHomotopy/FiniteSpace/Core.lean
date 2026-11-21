/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.PosetHomotopy.FiniteSpace.BeatPoint
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Data.Set.Card

/-!
# Stong's classification and invariant cores (roadmap 1.4, 1.5)

A self-map of a finite `T₀` space without beat points that is comparable with the identity is
the identity, by well-founded induction on the specialization order; with the fences of 1.2,
a self-map homotopic to the identity is the identity, and a homotopy equivalence between finite
`T₀` spaces without beat points is a homeomorphism (`exists_homeomorph_of_homotopyEquiv`;
J. A. Barmak, *Algebraic Topology of Finite Topological Spaces and Applications*, Lecture Notes
in Math. 2032, Springer, 2011, Corollary 1.3.7; R. E. Stong, « Finite topological spaces »,
Trans. Amer. Math. Soc. 123 (1966), 325–340).

If a group acts on a finite `T₀` space by homeomorphisms, the orbit of a beat point is an
antichain of beat points of the same kind, removed at once; iterating gives an invariant
subspace without beat points onto which the space strongly deformation retracts.
`exists_invariant_core` is the consequence of Barmak 2011, Lemma 8.1.2, obtained by
forgetting equivariance of the retraction and homotopy. When the space is contractible,
the invariant core gives a fixed point (`exists_fixedPoint_of_contractibleSpace`,
Barmak 2011, Proposition 8.1.3).
-/

@[expose] public section

open Topology
open scoped ContinuousMap

namespace LeanPool.PosetHomotopy

section Order

variable {P : Type*} [PartialOrder P]

/-- A monotone self-map below the identity of a finite partial order without beat points is the
identity. -/
theorem eq_of_le_of_forall_not_isBeatPoint [Finite P] (hP : ∀ x : P, ¬ IsBeatPoint x)
    (g : P →o P) (hg : ∀ x, g x ≤ x) (x : P) : g x = x := by
  induction x using WellFoundedLT.induction with
  | ind x ih =>
    by_contra hne
    exact hP x (Or.inl ⟨g x, lt_of_le_of_ne (hg x) hne, fun z hz =>
      (ih z hz).symm.le.trans (g.monotone hz.le)⟩)

/-- A monotone self-map above the identity of a finite partial order without beat points is the
identity. -/
theorem eq_of_ge_of_forall_not_isBeatPoint [Finite P] (hP : ∀ x : P, ¬ IsBeatPoint x)
    (g : P →o P) (hg : ∀ x, x ≤ g x) (x : P) : g x = x := by
  induction x using WellFoundedGT.induction with
  | ind x ih =>
    by_contra hne
    exact hP x (Or.inr ⟨g x, lt_of_le_of_ne (hg x) (Ne.symm hne), fun z hz =>
      (g.monotone hz.le).trans (ih z hz).le⟩)

/-- Removing an antichain `O ⊆ Y` of down beat points of `Y`, each `o` sent to the largest element
`t o` of `Y` below it, is monotone on `Y`, lands in `Y \ O`, fixes `Y \ O` and lies below the
identity. -/
theorem exists_retraction_antichain {Y O : Set P} (t : P → P)
    (ht : ∀ o ∈ O, t o ∈ Y ∧ t o < o ∧ ∀ z ∈ Y, z < o → z ≤ t o)
    (hO : ∀ a ∈ O, ∀ b ∈ O, a ≤ b → a = b) :
    ∃ ρ : P → P, (∀ z ∈ Y, ρ z ∈ Y \ O) ∧ (∀ z ∈ Y \ O, ρ z = z) ∧
      (∀ a ∈ Y, ∀ b ∈ Y, a ≤ b → ρ a ≤ ρ b) ∧ ∀ z ∈ Y, ρ z ≤ z := by
  classical
  refine ⟨fun z => if z ∈ O then t z else z, fun z hz => ?_, fun z hz => ?_,
    fun a ha b hb hab => ?_, fun z _ => ?_⟩ <;> dsimp only
  · by_cases h : z ∈ O
    · simp only [h, ↓reduceIte]
      refine ⟨(ht z h).1, fun h' => ?_⟩
      exact (ht z h).2.1.ne (hO _ h' _ h (ht z h).2.1.le)
    · simp only [h, ↓reduceIte]; exact ⟨hz, h⟩
  · simp only [hz.2, ↓reduceIte]
  · by_cases ha' : a ∈ O <;> by_cases hb' : b ∈ O
    · rw [hO a ha' b hb' hab]
    · simp only [ha', hb', ↓reduceIte]; exact (ht a ha').2.1.le.trans hab
    · simp only [ha', hb', ↓reduceIte]
      exact (ht b hb').2.2 a ha (lt_of_le_of_ne hab fun h => ha' (h ▸ hb'))
    · simp only [ha', hb', ↓reduceIte]; exact hab
  · split_ifs with h
    · exact (ht z h).2.1.le
    · exact le_rfl

end Order

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

instance [Finite X] : Finite (Specialization X) := inferInstanceAs (Finite X)

section Stong

variable [Finite X] [T0Space X]

/-- A self-map of a finite `T₀` space without beat points comparable with the identity is the
identity. -/
theorem eq_id_of_specializes (hX : ∀ x : Specialization X, ¬ IsBeatPoint x) (f : C(X, X))
    (h : (∀ x, x ⤳ f x) ∨ ∀ x, f x ⤳ x) : f = ContinuousMap.id X := by
  ext x
  rcases h with h | h
  · exact eq_of_le_of_forall_not_isBeatPoint hX (Specialization.map f) h
      (Specialization.toEquiv x)
  · exact eq_of_ge_of_forall_not_isBeatPoint hX (Specialization.map f) h
      (Specialization.toEquiv x)

/-- **Roadmap 1.4.** A self-map of a finite `T₀` space without beat points homotopic to the
identity is the identity. -/
theorem eq_id_of_homotopic (hX : ∀ x : Specialization X, ¬ IsBeatPoint x) {f : C(X, X)}
    (h : f.Homotopic (ContinuousMap.id X)) : f = ContinuousMap.id X := by
  have key : ∀ a b : C(X, X),
      Relation.EqvGen (fun f₁ f₂ : C(X, X) => ∀ x, f₁ x ⤳ f₂ x) a b →
        (a = ContinuousMap.id X ↔ b = ContinuousMap.id X) := by
    intro a b hab
    induction hab with
    | rel a b hab =>
      constructor
      · rintro rfl; exact eq_id_of_specializes hX b (Or.inl hab)
      · rintro rfl; exact eq_id_of_specializes hX a (Or.inr hab)
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact (key _ _ (eqvGen_of_homotopic h)).2 rfl

/-- **Roadmap 1.4.** Stong's classification: a homotopy equivalence between finite `T₀` spaces
without beat points is a homeomorphism. -/
theorem exists_homeomorph_of_homotopyEquiv [Finite Y] [T0Space Y]
    (hX : ∀ x : Specialization X, ¬ IsBeatPoint x) (hY : ∀ y : Specialization Y, ¬ IsBeatPoint y)
    (e : X ≃ₕ Y) : ∃ h : X ≃ₜ Y, ⇑h = ⇑e.toFun := by
  have h₁ := eq_id_of_homotopic hX e.left_inv
  have h₂ := eq_id_of_homotopic hY e.right_inv
  exact ⟨⟨⟨e.toFun, e.invFun, fun x => DFunLike.congr_fun h₁ x, fun y => DFunLike.congr_fun h₂ y⟩,
    e.toFun.continuous, e.invFun.continuous⟩, rfl⟩

end Stong

section Action

variable {G Z : Type*} [Group G] [MulAction G Z]

/-- An element of a group acting on a finite type has a positive power acting trivially. -/
theorem exists_pow_smul_eq [Finite Z] (g : G) : ∃ k, 0 < k ∧ ∀ x : Z, g ^ k • x = x := by
  obtain ⟨k, hk, hk'⟩ := (isOfFinOrder_of_finite (MulAction.toPermHom G Z g)).exists_pow_eq_one
  refine ⟨k, hk, fun x => ?_⟩
  have := DFunLike.congr_fun hk' x
  rwa [← map_pow, MulAction.toPermHom_apply, MulAction.toPerm_apply] at this

theorem smul_mem_iff_of_invariant {S : Set Z} (hS : ∀ g : G, ∀ z ∈ S, g • z ∈ S) (g : G) (z : Z) :
    g • z ∈ S ↔ z ∈ S :=
  ⟨fun h => by simpa using hS g⁻¹ _ h, hS g z⟩

end Action

section Core

variable {G : Type*} [Group G] [MulAction G X] [ContinuousConstSMul G X]

/-- Specialization in `X` is preserved by the action. -/
theorem smul_le_smul_iff_toEquiv (g : G) {a b : X} :
    Specialization.toEquiv (g • a) ≤ Specialization.toEquiv (g • b) ↔
      Specialization.toEquiv a ≤ Specialization.toEquiv b := by
  simp only [Specialization.toEquiv_le_toEquiv]
  refine ⟨fun h => ?_, fun h => h.map (continuous_const_smul g)⟩
  simpa using h.map (continuous_const_smul g⁻¹)

/-- The orbit of a point of a finite `T₀` space under an action by homeomorphisms is an
antichain of the specialization order. -/
theorem eq_of_smul_le [Finite X] [T0Space X] (g : G) (x : X)
    (h : Specialization.toEquiv (g • x) ≤ Specialization.toEquiv x) : g • x = x := by
  by_contra hne
  have hlt : Specialization.toEquiv (g • x) < Specialization.toEquiv x :=
    lt_of_le_of_ne h fun h' => hne (Specialization.toEquiv.injective h')
  have : ∀ n : ℕ, Specialization.toEquiv (g ^ (n + 1) • x) < Specialization.toEquiv x := by
    intro n
    induction n with
    | zero => simpa using hlt
    | succ n ih =>
      rw [pow_succ', mul_smul]
      exact lt_of_le_of_lt ((smul_le_smul_iff_toEquiv g).2 ih.le) hlt
  obtain ⟨k, hk, hk'⟩ := exists_pow_smul_eq (Z := X) g
  have h' := this (k - 1)
  rw [Nat.sub_add_cancel hk, hk'] at h'
  exact lt_irrefl _ h'

/-- Orders of a subspace and of the ambient space agree. -/
theorem toEquiv_le_subtype_iff {Z : Set X} (a b : Z) :
    Specialization.toEquiv a ≤ Specialization.toEquiv b ↔
      Specialization.toEquiv (a : X) ≤ Specialization.toEquiv (b : X) :=
  subtype_specializes_iff b a

theorem toEquiv_lt_subtype_iff {Z : Set X} (a b : Z) :
    Specialization.toEquiv a < Specialization.toEquiv b ↔
      Specialization.toEquiv (a : X) < Specialization.toEquiv (b : X) := by
  simp only [lt_iff_le_not_ge, toEquiv_le_subtype_iff]

theorem smul_lt_smul_iff_toEquiv (g : G) {a b : X} :
    Specialization.toEquiv (g • a) < Specialization.toEquiv (g • b) ↔
      Specialization.toEquiv a < Specialization.toEquiv b := by
  simp only [lt_iff_le_not_ge, smul_le_smul_iff_toEquiv]

omit [MulAction G X] [ContinuousConstSMul G X] in
/-- A beat point of a subspace, read in the ambient order. -/
theorem isBeatPoint_subtype {Z : Set X} (y : Z) (hy : IsBeatPoint (Specialization.toEquiv y)) :
    (∃ y₀ ∈ Z, Specialization.toEquiv y₀ < Specialization.toEquiv (y : X) ∧
      ∀ z ∈ Z, Specialization.toEquiv z < Specialization.toEquiv (y : X) →
        Specialization.toEquiv z ≤ Specialization.toEquiv y₀) ∨
    (∃ y₀ ∈ Z, Specialization.toEquiv (y : X) < Specialization.toEquiv y₀ ∧
      ∀ z ∈ Z, Specialization.toEquiv (y : X) < Specialization.toEquiv z →
        Specialization.toEquiv y₀ ≤ Specialization.toEquiv z) := by
  rcases hy with ⟨y₀, hy₀, hmax⟩ | ⟨y₀, hy₀, hmin⟩
  · refine Or.inl ⟨(Specialization.ofEquiv y₀ : Z), (Specialization.ofEquiv y₀).2,
      (toEquiv_lt_subtype_iff (Specialization.ofEquiv y₀) y).1 hy₀, fun z hz hzy => ?_⟩
    exact (toEquiv_le_subtype_iff ⟨z, hz⟩ (Specialization.ofEquiv y₀)).1
      (hmax _ ((toEquiv_lt_subtype_iff ⟨z, hz⟩ y).2 hzy))
  · refine Or.inr ⟨(Specialization.ofEquiv y₀ : Z), (Specialization.ofEquiv y₀).2,
      (toEquiv_lt_subtype_iff y (Specialization.ofEquiv y₀)).1 hy₀, fun z hz hzy => ?_⟩
    exact (toEquiv_le_subtype_iff (Specialization.ofEquiv y₀) ⟨z, hz⟩).1
      (hmin _ ((toEquiv_lt_subtype_iff y ⟨z, hz⟩).2 hzy))

/-- The target map of an orbit: `g • y ↦ g • y₀`, for a chosen `g`. -/
noncomputable def orbitTarget (y y₀ : X) (z : X) : X :=
  open Classical in
  if h : ∃ g : G, g • y = z then Classical.choose h • y₀ else z

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
theorem orbitTarget_spec (y y₀ : X) (g : G) :
    ∃ g' : G, g' • y = g • y ∧ orbitTarget (G := G) y y₀ (g • y) = g' • y₀ := by
  have hex : ∃ g' : G, g' • y = g • y := ⟨g, rfl⟩
  refine ⟨Classical.choose hex, Classical.choose_spec hex, ?_⟩
  simp only [orbitTarget, hex, ↓reduceDIte]

/-- Removing the orbit of a beat point from an invariant strong deformation retract of a finite
`T₀` space leaves an invariant strong deformation retract. -/
theorem exists_smaller_of_isBeatPoint [Finite X] [T0Space X] {Z : Set X}
    (hZ : ∀ g : G, ∀ z ∈ Z, g • z ∈ Z) (hZr : IsStrongDeformationRetract Z) (y : Z)
    (hy : IsBeatPoint (Specialization.toEquiv y)) :
    ∃ Z' ⊂ Z, (∀ g : G, ∀ z ∈ Z', g • z ∈ Z') ∧ IsStrongDeformationRetract Z' := by
  set O : Set X := Set.range fun g : G => g • (y : X) with hOdef
  have hOZ : O ⊆ Z := by rintro _ ⟨g, rfl⟩; exact hZ g _ y.2
  have hOanti : ∀ a ∈ O, ∀ b ∈ O,
      Specialization.toEquiv a ≤ Specialization.toEquiv b → a = b := by
    rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩ hab
    have : (h⁻¹ * g) • (y : X) = y := eq_of_smul_le _ _ (by
      rw [mul_smul, ← smul_le_smul_iff_toEquiv h]; simpa using hab)
    rw [mul_smul, inv_smul_eq_iff] at this
    exact this
  have hOinv : ∀ g : G, ∀ z ∈ Z \ O, g • z ∈ Z \ O := by
    rintro g z ⟨hz, hzO⟩
    refine ⟨hZ g z hz, fun ⟨h, hh⟩ => hzO ⟨g⁻¹ * h, ?_⟩⟩
    change (g⁻¹ * h) • (y : X) = z
    change h • (y : X) = g • z at hh
    rw [mul_smul, hh, inv_smul_smul]
  have hsub : Z \ O ⊂ Z :=
    (Set.ssubset_iff_of_subset Set.sdiff_subset).2 ⟨y, y.2, fun h => h.2 ⟨1, one_smul _ _⟩⟩
  refine ⟨Z \ O, hsub, hOinv, ?_⟩
  rcases isBeatPoint_subtype y hy with ⟨y₀, hy₀Z, hy₀, hmax⟩ | ⟨y₀, hy₀Z, hy₀, hmin⟩
  · have ht : ∀ o ∈ O, orbitTarget (G := G) (y : X) y₀ o ∈ Z ∧
        Specialization.toEquiv (orbitTarget (G := G) (y : X) y₀ o) < Specialization.toEquiv o ∧
        ∀ z ∈ Z, Specialization.toEquiv z < Specialization.toEquiv o →
          Specialization.toEquiv z ≤
            Specialization.toEquiv (orbitTarget (G := G) (y : X) y₀ o) := by
      rintro _ ⟨g₀, rfl⟩
      obtain ⟨g, hg, hto⟩ := orbitTarget_spec (G := G) (y : X) y₀ g₀
      dsimp only at hg ⊢
      rw [show orbitTarget (G := G) (y : X) y₀ (g₀ • (y : X)) = g • y₀ from hto, ← hg]
      refine ⟨hZ g _ hy₀Z, (smul_lt_smul_iff_toEquiv g).2 hy₀, fun z hz hzo => ?_⟩
      have hlt : Specialization.toEquiv (g⁻¹ • z) < Specialization.toEquiv (y : X) := by
        rw [← smul_lt_smul_iff_toEquiv g, smul_inv_smul]; exact hzo
      have := hmax _ (hZ g⁻¹ z hz) hlt
      rwa [← smul_le_smul_iff_toEquiv g, smul_inv_smul] at this
    obtain ⟨ρ, hρZ, hρfix, hρmono, hρle⟩ := exists_retraction_antichain (P := Specialization X)
      (orbitTarget (X := X) (G := G) (y : X) y₀) ht hOanti
    exact hZr.diff ρ hρZ hρfix (fun a ha b hb hab => hρmono b hb a ha hab)
      (Or.inl fun z hz => hρle z hz)
  · have ht : ∀ o ∈ O, orbitTarget (G := G) (y : X) y₀ o ∈ Z ∧
        Specialization.toEquiv o < Specialization.toEquiv (orbitTarget (G := G) (y : X) y₀ o) ∧
        ∀ z ∈ Z, Specialization.toEquiv o < Specialization.toEquiv z →
          Specialization.toEquiv (orbitTarget (G := G) (y : X) y₀ o) ≤
            Specialization.toEquiv z := by
      rintro _ ⟨g₀, rfl⟩
      obtain ⟨g, hg, hto⟩ := orbitTarget_spec (G := G) (y : X) y₀ g₀
      dsimp only at hg ⊢
      rw [show orbitTarget (G := G) (y : X) y₀ (g₀ • (y : X)) = g • y₀ from hto, ← hg]
      refine ⟨hZ g _ hy₀Z, (smul_lt_smul_iff_toEquiv g).2 hy₀, fun z hz hzo => ?_⟩
      have hlt : Specialization.toEquiv (y : X) < Specialization.toEquiv (g⁻¹ • z) := by
        rw [← smul_lt_smul_iff_toEquiv g, smul_inv_smul]; exact hzo
      have := hmin _ (hZ g⁻¹ z hz) hlt
      rwa [← smul_le_smul_iff_toEquiv g, smul_inv_smul] at this
    obtain ⟨ρ, hρZ, hρfix, hρmono, hρle⟩ :=
      exists_retraction_antichain (P := (Specialization X)ᵒᵈ)
        (orbitTarget (X := X) (G := G) (y : X) y₀) ht
        (fun a ha b hb hab => (hOanti b hb a ha hab).symm)
    exact hZr.diff ρ hρZ hρfix (fun a ha b hb hab => hρmono a ha b hb hab)
      (Or.inr fun z hz => hρle z hz)

/-- Every invariant strong deformation retract of a finite `T₀` space contains an invariant
strong deformation retract without beat points. -/
theorem exists_core_subset [Finite X] [T0Space X] (Z : Set X)
    (hZ : ∀ g : G, ∀ z ∈ Z, g • z ∈ Z) (hZr : IsStrongDeformationRetract Z) :
    ∃ C ⊆ Z, (∀ g : G, ∀ c ∈ C, g • c ∈ C) ∧ (∀ c : Specialization C, ¬ IsBeatPoint c) ∧
      IsStrongDeformationRetract C := by
  induction h : Z.ncard using Nat.strong_induction_on generalizing Z with
  | _ n ih =>
    by_cases hb : ∀ c : Specialization Z, ¬ IsBeatPoint c
    · exact ⟨Z, le_rfl, hZ, hb, hZr⟩
    · push Not at hb
      obtain ⟨c, hc⟩ := hb
      obtain ⟨Z', hZ'Z, hZ', hZ'r⟩ :=
        exists_smaller_of_isBeatPoint hZ hZr (Specialization.ofEquiv c) hc
      obtain ⟨C, hCZ', hC⟩ := ih _ (h ▸ Set.ncard_lt_ncard hZ'Z) Z' hZ' hZ'r rfl
      exact ⟨C, hCZ'.trans hZ'Z.subset, hC⟩

/-- **Roadmap 1.5.** A finite `T₀` space on which a group acts by homeomorphisms has an invariant
core: an invariant subspace without beat points onto which it strongly deformation retracts. -/
theorem exists_invariant_core [Finite X] [T0Space X] :
    ∃ Y : Set X, (∀ g : G, ∀ y ∈ Y, g • y ∈ Y) ∧ (∀ y : Specialization Y, ¬ IsBeatPoint y) ∧
      ∃ r : C(X, Y), (∀ y : Y, r y = y) ∧
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(Y, X)).comp r).HomotopicRel
          (ContinuousMap.id X) Y := by
  obtain ⟨C, -, hC, hCb, hCr⟩ := exists_core_subset (G := G) (Set.univ : Set X)
    (fun _ _ _ => trivial) isStrongDeformationRetract_univ
  exact ⟨C, hC, hCb, hCr.exists_retraction⟩

/-- **Roadmap 1.5.** A group acting by homeomorphisms on a contractible finite `T₀` space has a
fixed point. -/
theorem exists_fixedPoint_of_contractibleSpace [Finite X] [T0Space X] [ContractibleSpace X] :
    ∃ x : X, ∀ g : G, g • x = x := by
  obtain ⟨C, hC, hCb, r, hr, hrh⟩ := exists_invariant_core (G := G) (X := X)
  let e : C ≃ₕ X :=
    { toFun := ⟨Subtype.val, continuous_subtype_val⟩
      invFun := r
      left_inv := by
        convert ContinuousMap.Homotopic.refl (ContinuousMap.id C)
        ext y
        exact congrArg Subtype.val (hr y)
      right_inv := hrh.homotopic }
  obtain ⟨u⟩ := ContractibleSpace.hequiv_unit' (X := X)
  obtain ⟨h, -⟩ := exists_homeomorph_of_homotopyEquiv hCb
    (fun y hy => by
      rcases hy with ⟨z, hz, -⟩ | ⟨z, hz, -⟩ <;> exact hz.ne (Subsingleton.elim (α := Unit) _ _))
    (e.trans u)
  refine ⟨h.symm (), fun g => ?_⟩
  have hmem : g • (h.symm () : X) ∈ C := hC g _ (h.symm ()).2
  have : (⟨_, hmem⟩ : C) = h.symm () := h.injective (Subsingleton.elim _ _)
  exact congrArg Subtype.val this

end Core

end LeanPool.PosetHomotopy
