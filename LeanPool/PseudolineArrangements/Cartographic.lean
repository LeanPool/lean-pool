/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.PseudolineArrangements.FlagSystem
public import Mathlib.GroupTheory.Coxeter.Basic

/-!
# The cartographic group

The string Coxeter matrix `stringCoxeterMatrix n p hp` on `Fin (n + 1)` has entry `p i` between
the generators `i` and `i + 1` (`0` meaning `∞`) and `2` between non-adjacent generators. With
all adjacent entries `∞` its Coxeter group is the cartographic group `cartographicGroup n` of
Grothendieck: the involutions of a flag system of rank `n` are exactly an action of it.

We construct the monodromy homomorphism of a flag system (`GMap.monodromyHom`) and the flag system
of a homomorphism (`GMap.ofMonodromyHom`), which are inverse; we characterise when the monodromy
homomorphism factors through a string Coxeter group of given type
(`GMap.exists_monoidHom_stringCoxeterMatrix_iff`); and we study morphisms and automorphisms:
a morphism to a connected flag system is surjective (`GMap.surjective_of_map_adj`), the
automorphism group of a connected flag system acts freely (`GMap.eq_of_mem_aut_of_apply_eq`), and
so has at most as many elements as there are flags (`GMap.natCard_aut_le`).

## References

* A. Grothendieck, *Esquisse d'un programme* (1984), §3, p. 14, and §4, pp. 21–22.
* S. Wilson, *Maniplexes: Part 1: maps, polytopes, symmetry and operators*, Symmetry 4 (2012),
  265–275, §5 and §7.
-/

@[expose] public section

namespace LeanPool.PseudolineArrangements

open Equiv

/-- Two involutions whose product has square one commute. -/
theorem commute_of_mul_self_eq_one {W : Type*} [Group W] {a b : W} (ha : a * a = 1)
    (hb : b * b = 1) (hab : (a * b) ^ 2 = 1) : Commute a b := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have : a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right (by rwa [sq] at hab)).symm
  rw [mul_inv_rev, ha', hb'] at this
  exact this

/-- Two simple reflections of a Coxeter system whose matrix entry is `2` commute. -/
theorem commute_simple_of_eq_two {B W : Type*} [Group W] {M : CoxeterMatrix B}
    (cs : CoxeterSystem M W) {i j : B} (h : M i j = 2) : Commute (cs.simple i) (cs.simple j) :=
  commute_of_mul_self_eq_one (cs.simple_mul_simple_self i) (cs.simple_mul_simple_self j)
    (h ▸ cs.simple_mul_simple_pow i j)

/-- The string Coxeter matrix with `M i (i + 1) = p i` (`0` meaning `∞`) and `2` between
non-adjacent generators. -/
def stringCoxeterMatrix (n : ℕ) (p : Fin n → ℕ) (hp : ∀ i, p i ≠ 1) :
    CoxeterMatrix (Fin (n + 1)) where
  M := Matrix.of fun i j =>
    if i = j then 1
    else if h : (i : ℕ) + 1 = j then p ⟨i, by have := j.isLt; omega⟩
    else if h' : (j : ℕ) + 1 = i then p ⟨j, by have := i.isLt; omega⟩
    else 2
  isSymm := by
    refine Matrix.IsSymm.ext fun i j => ?_
    simp only [Matrix.of_apply]
    split_ifs <;> omega
  diagonal i := by simp
  off_diagonal i j hij := by
    simp only [Matrix.of_apply]
    split_ifs
    · contradiction
    · exact hp _
    · exact hp _
    · omega

/-- Non-adjacent entries of a string Coxeter matrix are `2`. -/
theorem stringCoxeterMatrix_of_far {n : ℕ} {p : Fin n → ℕ} {hp : ∀ i, p i ≠ 1}
    {i j : Fin (n + 1)} (h : (i : ℕ) + 2 ≤ j) : stringCoxeterMatrix n p hp i j = 2 := by
  change Matrix.of _ i j = 2
  simp only [Matrix.of_apply]
  split_ifs with h1 h2 h3
  · subst h1; omega
  · omega
  · omega
  · rfl

/-- The entry of a string Coxeter matrix between `i` and `i + 1` is `p i`. -/
theorem stringCoxeterMatrix_castSucc_succ {n : ℕ} {p : Fin n → ℕ} {hp : ∀ i, p i ≠ 1}
    (i : Fin n) : stringCoxeterMatrix n p hp i.castSucc i.succ = p i := by
  change Matrix.of _ _ _ = _
  simp [Matrix.of_apply, Fin.ext_iff]

/-- The entry of a string Coxeter matrix between `i + 1` and `i` is `p i`. -/
theorem stringCoxeterMatrix_succ_castSucc {n : ℕ} {p : Fin n → ℕ} {hp : ∀ i, p i ≠ 1}
    (i : Fin n) : stringCoxeterMatrix n p hp i.succ i.castSucc = p i := by
  rw [(stringCoxeterMatrix n p hp).symmetric, stringCoxeterMatrix_castSucc_succ]

/-- The Coxeter matrix of the cartographic group: all adjacent entries are `∞`. -/
abbrev cartographicMatrix (n : ℕ) : CoxeterMatrix (Fin (n + 1)) :=
  stringCoxeterMatrix n 0 (fun _ => by simp)

/-- The cartographic group: the universal string Coxeter group with all adjacent entries `∞`. -/
abbrev cartographicGroup (n : ℕ) : Type :=
  (cartographicMatrix n).Group

namespace GMap

variable {n : ℕ} {D D' : Type*} (G : GMap n D)

/-- The involutions of a flag system satisfy the relations of the cartographic group. -/
theorem isLiftable_adj : (cartographicMatrix n).IsLiftable G.adj := by
  intro i j
  change (G.adj i * G.adj j) ^ (Matrix.of _ i j) = 1
  simp only [Matrix.of_apply]
  split_ifs with h1 h2 h3
  · subst h1; rw [pow_one, G.adj_mul_self]
  · rfl
  · rfl
  · have hne := Fin.val_ne_of_ne h1
    rcases (show (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i by omega) with hf | hf
    · rw [(G.commute_of_far i j hf).mul_pow, sq, sq, G.adj_mul_self, G.adj_mul_self, one_mul]
    · rw [(G.commute_of_far j i hf).symm.mul_pow, sq, sq, G.adj_mul_self, G.adj_mul_self,
        one_mul]

/-- The monodromy homomorphism `cartographicGroup n →* Perm D`. -/
noncomputable def monodromyHom : cartographicGroup n →* Perm D :=
  (cartographicMatrix n).toCoxeterSystem.lift ⟨G.adj, G.isLiftable_adj⟩

@[simp]
theorem monodromyHom_simple (i : Fin (n + 1)) :
    G.monodromyHom ((cartographicMatrix n).simple i) = G.adj i :=
  (cartographicMatrix n).toCoxeterSystem.lift_apply_simple G.isLiftable_adj i

/-- The flag system of a homomorphism `cartographicGroup n →* Perm D`. -/
def ofMonodromyHom (φ : cartographicGroup n →* Perm D) : GMap n D where
  adj i := φ ((cartographicMatrix n).simple i)
  involutive i d := by
    have h := (cartographicMatrix n).toCoxeterSystem.simple_mul_simple_self i
    rw [CoxeterMatrix.toCoxeterSystem_simple] at h
    rw [← Perm.mul_apply, ← map_mul, h, map_one, Perm.one_apply]
  commute_of_far i j h :=
    (commute_simple_of_eq_two (cartographicMatrix n).toCoxeterSystem
      (stringCoxeterMatrix_of_far h)).map φ

@[simp]
theorem ofMonodromyHom_adj (φ : cartographicGroup n →* Perm D) (i : Fin (n + 1)) :
    (ofMonodromyHom φ).adj i = φ ((cartographicMatrix n).simple i) := rfl

omit G in
theorem ext {G G' : GMap n D} (h : G.adj = G'.adj) : G = G' := by
  cases G; cases G'; cases h; rfl

theorem ofMonodromyHom_monodromyHom : ofMonodromyHom G.monodromyHom = G :=
  ext (funext fun i => G.monodromyHom_simple i)

theorem monodromyHom_ofMonodromyHom (φ : cartographicGroup n →* Perm D) :
    (ofMonodromyHom φ).monodromyHom = φ :=
  (cartographicMatrix n).toCoxeterSystem.ext_simple fun i => by
    rw [CoxeterMatrix.toCoxeterSystem_simple, monodromyHom_simple, ofMonodromyHom_adj]

/-- Flag systems of rank `n` on `D` are the same as homomorphisms
`cartographicGroup n →* Perm D`. -/
@[simps]
noncomputable def equivMonodromyHom : GMap n D ≃ (cartographicGroup n →* Perm D) where
  toFun G := G.monodromyHom
  invFun φ := ofMonodromyHom φ
  left_inv G := G.ofMonodromyHom_monodromyHom
  right_inv φ := monodromyHom_ofMonodromyHom φ

/-- The monodromy homomorphism factors through `(stringCoxeterMatrix n p hp).Group` iff
`(adj i * adj (i + 1)) ^ p i = 1` for every `i`. -/
theorem exists_monoidHom_stringCoxeterMatrix_iff (p : Fin n → ℕ) (hp : ∀ i, p i ≠ 1) :
    (∃ ψ : (stringCoxeterMatrix n p hp).Group →* Perm D,
        ∀ i, ψ ((stringCoxeterMatrix n p hp).simple i) = G.adj i) ↔
      ∀ i : Fin n, (G.adj i.castSucc * G.adj i.succ) ^ p i = 1 := by
  set M := stringCoxeterMatrix n p hp
  constructor
  · rintro ⟨ψ, hψ⟩ i
    rw [← hψ, ← hψ, ← map_mul, ← map_pow, ← stringCoxeterMatrix_castSucc_succ (hp := hp),
      ← CoxeterMatrix.toCoxeterSystem_simple, M.toCoxeterSystem.simple_mul_simple_pow, map_one]
  · intro h
    have hinv : ∀ a b : Perm D, a * a = 1 → b * b = 1 → ∀ m : ℕ, (a * b) ^ m = 1 →
        (b * a) ^ m = 1 := by
      intro a b ha hb m hm
      have : b * a = (a * b)⁻¹ := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb]
      rw [this, inv_pow, hm, inv_one]
    have hlift : M.IsLiftable G.adj := by
      intro i j
      change (G.adj i * G.adj j) ^ (Matrix.of _ i j) = 1
      simp only [Matrix.of_apply]
      split_ifs with h1 h2 h3
      · subst h1; rw [pow_one, G.adj_mul_self]
      · have := h ⟨i, by have := j.isLt; omega⟩
        have hi : (⟨i, by have := j.isLt; omega⟩ : Fin n).castSucc = i := Fin.ext rfl
        have hj : (⟨i, by have := j.isLt; omega⟩ : Fin n).succ = j := Fin.ext (by simp [← h2])
        rwa [hi, hj] at this
      · have := h ⟨j, by have := i.isLt; omega⟩
        have hj : (⟨j, by have := i.isLt; omega⟩ : Fin n).castSucc = j := Fin.ext rfl
        have hi : (⟨j, by have := i.isLt; omega⟩ : Fin n).succ = i := Fin.ext (by simp [← h3])
        rw [hj, hi] at this
        exact hinv _ _ (G.adj_mul_self j) (G.adj_mul_self i) _ this
      · have hne := Fin.val_ne_of_ne h1
        rcases (show (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i by omega) with hf | hf
        · rw [(G.commute_of_far i j hf).mul_pow, sq, sq, G.adj_mul_self, G.adj_mul_self,
            one_mul]
        · rw [(G.commute_of_far j i hf).symm.mul_pow, sq, sq, G.adj_mul_self, G.adj_mul_self,
            one_mul]
    exact ⟨M.toCoxeterSystem.lift ⟨G.adj, hlift⟩, M.toCoxeterSystem.lift_apply_simple hlift⟩

/-- The monodromy group is the range of the monodromy homomorphism. -/
theorem range_monodromyHom : G.monodromyHom.range = G.monodromy := by
  rw [MonoidHom.range_eq_map, ← (cartographicMatrix n).subgroupClosure_range_simple,
    MonoidHom.map_closure, ← Set.range_comp, monodromy]
  congr 2
  funext i
  exact G.monodromyHom_simple i

theorem monodromyHom_mem_monodromy (w : cartographicGroup n) : G.monodromyHom w ∈ G.monodromy :=
  G.range_monodromyHom ▸ ⟨w, rfl⟩

/-- A flag system is connected iff the cartographic group acts transitively through the
monodromy homomorphism. -/
theorem isConnected_iff_exists_monodromyHom :
    G.IsConnected ↔ ∀ d e : D, ∃ w, G.monodromyHom w d = e := by
  rw [isConnected_iff_forall_exists, ← range_monodromyHom]
  constructor
  · intro h d e
    obtain ⟨_, ⟨w, rfl⟩, h⟩ := h d e
    exact ⟨w, h⟩
  · intro h d e
    obtain ⟨w, hw⟩ := h d e
    exact ⟨_, ⟨w, rfl⟩, hw⟩

/-- A map of darts commuting with every `adj i` commutes with the whole monodromy action. -/
theorem map_monodromyHom {G' : GMap n D'} {f : D → D'}
    (hf : ∀ i d, f (G.adj i d) = G'.adj i (f d)) (w : cartographicGroup n) (d : D) :
    f (G.monodromyHom w d) = G'.monodromyHom w (f d) := by
  induction w using (cartographicMatrix n).toCoxeterSystem.simple_induction_left
    generalizing d with
  | one => simp
  | mul_simple_left w i ih =>
    rw [map_mul, map_mul, Perm.mul_apply, Perm.mul_apply, CoxeterMatrix.toCoxeterSystem_simple,
      monodromyHom_simple, monodromyHom_simple, hf, ih]

/-- A map of darts commuting with every `adj i`, from a nonempty flag system to a connected one,
is surjective. -/
theorem surjective_of_map_adj [Nonempty D] {G' : GMap n D'} (hG' : G'.IsConnected) (f : D → D')
    (hf : ∀ i d, f (G.adj i d) = G'.adj i (f d)) : Function.Surjective f := by
  obtain ⟨d₀⟩ := ‹Nonempty D›
  intro e
  obtain ⟨w, hw⟩ := (G'.isConnected_iff_exists_monodromyHom).1 hG' (f d₀) e
  exact ⟨G.monodromyHom w d₀, by rw [G.map_monodromyHom hf, hw]⟩

/-- The automorphism group: the centralizer of the `adj i`. -/
def aut : Subgroup (Perm D) := Subgroup.centralizer (Set.range G.adj)

theorem mem_aut_iff {σ : Perm D} : σ ∈ G.aut ↔ ∀ i d, σ (G.adj i d) = G.adj i (σ d) := by
  rw [aut, Subgroup.mem_centralizer_iff]
  constructor
  · intro h i d
    exact (congrArg (fun τ : Perm D => τ d) (h _ ⟨i, rfl⟩)).symm
  · rintro h _ ⟨i, rfl⟩
    exact Equiv.ext fun d => (h i d).symm

/-- The automorphism group of a connected flag system acts freely. -/
theorem eq_of_mem_aut_of_apply_eq (hG : G.IsConnected) {σ τ : Perm D} (hσ : σ ∈ G.aut)
    (hτ : τ ∈ G.aut) (d : D) (h : σ d = τ d) : σ = τ := by
  refine Equiv.ext fun e => ?_
  obtain ⟨w, rfl⟩ := (G.isConnected_iff_exists_monodromyHom).1 hG d e
  rw [G.map_monodromyHom ((G.mem_aut_iff).1 hσ), G.map_monodromyHom ((G.mem_aut_iff).1 hτ), h]

/-- A finite nonempty connected flag system has at most `Nat.card D` automorphisms. -/
theorem natCard_aut_le [Finite D] [Nonempty D] (hG : G.IsConnected) :
    Nat.card G.aut ≤ Nat.card D := by
  obtain ⟨d₀⟩ := ‹Nonempty D›
  refine Nat.card_le_card_of_injective (fun σ : G.aut => (σ : Perm D) d₀) fun σ τ h => ?_
  exact Subtype.ext (G.eq_of_mem_aut_of_apply_eq hG σ.2 τ.2 d₀ h)

end GMap

end LeanPool.PseudolineArrangements
