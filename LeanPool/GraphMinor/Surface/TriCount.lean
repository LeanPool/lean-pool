/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.CharP.Two
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Counting in a triangulation

This file is pure counting. A triangulated surface is recorded by `TriCx V E F`: vertices, edges and
faces, where each edge has two ends, each face has three vertices, each edge lies in two faces, and
three connectivity conditions hold. Over the field with two elements, the incidence matrices `M`
(faces against edges) and `N` (edges against vertices) satisfy `M * N = 0`. We compute their ranks
(`finrank_range_N`, `finrank_ker_M`).

Then we bound a subgraph. If `Y` is a set of edges, let `R` be the number of classes of faces under
sharing an edge outside `Y`. Then `|V| - |E| + |F| ≤ |V(Y)| - |Y| + R` (`euler_le`). This is the
Euler formula for a graph in a surface in the form that is needed for Graph Minors XIX, (6.5) (page
341). Regions need not be discs. For a drawing with at least three edges and no parallel edges, each
class meets three edges, and this gives `3 R ≤ 2 |E|` (`three_classes_le`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Matrix

/-- The combinatorics of a triangulation of a connected closed surface. -/
structure TriCx (V E F : Type) where
  /-- The two endpoints of each edge. -/
  ends : E → Set V
  /-- The three vertices of each face. -/
  verts : F → Set V
  ends_two : ∀ e, (ends e).ncard = 2
  ends_inj : Function.Injective ends
  verts_three : ∀ Φ, (verts Φ).ncard = 3
  pair : ∀ Φ, ∀ a ∈ verts Φ, ∀ b ∈ verts Φ, a ≠ b → ∃ e, ends e = {a, b}
  two : ∀ e, {Φ | ends e ⊆ verts Φ}.ncard = 2
  conn : ∀ S : Set V, (∀ e, ∀ a ∈ ends e, ∀ b ∈ ends e, a ∈ S → b ∈ S) → S.Nonempty → S = univ
  dual : ∀ S : Set F, (∀ e, ∀ Φ ∈ S, ∀ Φ', ends e ⊆ verts Φ → ends e ⊆ verts Φ' → Φ' ∈ S)
    → S.Nonempty → S = univ
  link : ∀ w, ∀ S : Set F, (∀ Φ ∈ S, w ∈ verts Φ) →
    (∀ e, w ∈ ends e → ∀ Φ ∈ S, ∀ Φ', ends e ⊆ verts Φ → ends e ⊆ verts Φ' → Φ' ∈ S) → S.Nonempty →
    ∀ Φ', w ∈ verts Φ' → Φ' ∈ S

namespace TriCx

variable {V E F : Type} [Fintype V] [Fintype E] [Fintype F] (T : TriCx V E F)

/-- An edge lies in a face. -/
def I (e : E) (Φ : F) : Prop := T.ends e ⊆ T.verts Φ

local notation "K" => ZMod 2

open Classical in
/-- Faces against edges. -/
noncomputable def M : Matrix F E K := fun Φ e => if T.I e Φ then 1 else 0

open Classical in
/-- Edges against vertices. -/
noncomputable def N : Matrix E V K := fun e v => if v ∈ T.ends e then 1 else 0

omit [Fintype V] [Fintype E] [Fintype F] in
theorem exists_ends (e : E) : ∃ a b, a ≠ b ∧ T.ends e = {a, b} := by
  obtain ⟨a, b, h, h'⟩ := ncard_eq_two.mp (T.ends_two e)
  exact ⟨a, b, h, h'⟩

omit [Fintype V] [Fintype E] [Fintype F] in
theorem exists_faces (e : E) : ∃ Φ Φ', Φ ≠ Φ' ∧ {Φ | T.I e Φ} = {Φ, Φ'} := by
  obtain ⟨a, b, h, h'⟩ := ncard_eq_two.mp (T.two e)
  exact ⟨a, b, h, h'⟩

omit [Fintype E] [Fintype F] in
theorem sum_ends (e : E) {a b : V} (hab : a ≠ b) (he : T.ends e = {a, b}) (w : V → K) :
    T.N.mulVec w e = w a + w b := by
  classical
  have h1 : ∀ v, T.N e v * w v = (if v = a then w v else 0) + (if v = b then w v else 0) := fun v
    => by
    simp only [N, he, mem_insert_iff, mem_singleton_iff]
    by_cases h2 : v = a
    · have h3 : v ≠ b := h2 ▸ hab
      simp [h2, hab]
    · by_cases h3 : v = b
      · simp [h3, hab.symm]
      · simp [h2, h3]
  simp only [mulVec, dotProduct, h1, Finset.sum_add_distrib]
  simp

omit [Fintype V] [Fintype E] in
theorem sum_faces (e : E) {Φ Φ' : F} (h : Φ ≠ Φ') (he : {Φ | T.I e Φ} = {Φ, Φ'}) (f : F → K) :
    T.Mᵀ.mulVec f e = f Φ + f Φ' := by
  classical
  have hm : ∀ Ψ, T.I e Ψ ↔ Ψ = Φ ∨ Ψ = Φ' := fun Ψ => by
    have : Ψ ∈ {Φ | T.I e Φ} ↔ Ψ ∈ ({Φ, Φ'} : Set F) := by rw [he]
    simpa using this
  have h1 : ∀ v, T.M v e * f v = (if v = Φ then f v else 0) + (if v = Φ' then f v else 0) := fun v
    => by
    simp only [M, hm]
    by_cases h2 : v = Φ
    · have h3 : v ≠ Φ' := h2 ▸ h
      simp [h2, h]
    · by_cases h3 : v = Φ'
      · simp [h3, h.symm]
      · simp [h2, h3]
  simp only [mulVec, dotProduct, transpose_apply, h1, Finset.sum_add_distrib]
  simp

theorem zmod_add_self (x : K) : x + x = 0 := CharTwo.add_self_eq_zero x

omit [Fintype V] [Fintype F] in
/-- Each vertex of a face lies on two edges of the face. -/
theorem card_at [Finite V] [Finite F] (Φ : F) {v : V} (hv : v ∈ T.verts Φ) [DecidablePred fun e
  => T.I e Φ ∧ v ∈ T.ends e] :
    (Finset.univ.filter fun e => T.I e Φ ∧ v ∈ T.ends e).card = 2 := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite F
  · have hc : (T.verts Φ \ {v}).ncard = 2 := by
      rw [ncard_sdiff (singleton_subset_iff.mpr hv) (Set.toFinite _), T.verts_three Φ,
        ncard_singleton]
    obtain ⟨b, c, hbc, hE⟩ := ncard_eq_two.mp hc
    have hb : b ∈ T.verts Φ \ {v} := hE ▸ .inl rfl
    have hc' : c ∈ T.verts Φ \ {v} := hE ▸ .inr rfl
    obtain ⟨e₁, h1⟩ := T.pair Φ v hv b hb.1 (Ne.symm hb.2)
    obtain ⟨e₂, h2⟩ := T.pair Φ v hv c hc'.1 (Ne.symm hc'.2)
    have hne : e₁ ≠ e₂ := fun h => by
      rw [h, h2] at h1
      have h3 : c ∈ ({v, b} : Set V) := h1 ▸ Or.inr rfl
      rcases h3 with h3 | h3
      · exact hc'.2 h3
      · exact hbc h3.symm
    have hset : (Finset.univ.filter fun e => T.I e Φ ∧ v ∈ T.ends e) = {e₁, e₂} := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨h3, h4⟩
        obtain ⟨p, q, hpq, he⟩ := T.exists_ends e
        have hother : ∃ o, o ≠ v ∧ T.ends e = {v, o} := by
          rw [he] at h4 ⊢
          rcases h4 with rfl | rfl
          · exact ⟨q, Ne.symm hpq, rfl⟩
          · exact ⟨p, hpq, pair_comm _ _⟩
        obtain ⟨o, hov, heo⟩ := hother
        have ho : o ∈ T.verts Φ \ {v} := ⟨h3 (heo ▸ Or.inr rfl), hov⟩
        rw [hE] at ho
        rcases ho with rfl | rfl
        · exact .inl (T.ends_inj (heo.trans h1.symm))
        · exact .inr (T.ends_inj (heo.trans h2.symm))
      · rintro (rfl | rfl)
        · refine ⟨fun y hy => ?_, h1 ▸ Or.inl rfl⟩
          rw [h1] at hy
          rcases hy with rfl | rfl
          · exact hv
          · exact hb.1
        · refine ⟨fun y hy => ?_, h2 ▸ Or.inl rfl⟩
          rw [h2] at hy
          rcases hy with rfl | rfl
          · exact hv
          · exact hc'.1
    rw [hset, Finset.card_pair hne]

omit [Fintype V] [Fintype F] in
/-- Each vertex lies on an even number of edges of a face. -/
theorem even_card [Finite V] [Finite F] (Φ : F) (v : V) [DecidablePred fun e => T.I e Φ
  ∧ v ∈ T.ends e] :
    Even (Finset.univ.filter fun e => T.I e Φ ∧ v ∈ T.ends e).card := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite F
  by_cases hv : v ∈ T.verts Φ
  · rw [T.card_at Φ hv]
    exact even_two
  · have : (Finset.univ.filter fun e => T.I e Φ ∧ v ∈ T.ends e) = ∅ := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
        not_and]
      exact fun h1 h2 => hv (h1 h2)
    rw [this]
    simp

omit [Fintype V] [Fintype F] in
theorem M_mul_N [Finite V] [Finite F] : T.M * T.N = 0 := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite F
  ext Φ v
  simp only [Matrix.zero_apply]
  have h1 : (∑ e, if T.I e Φ then (if v ∈ T.ends e then (1 : K) else 0) else 0) =
      ((Finset.univ.filter fun e => T.I e Φ ∧ v ∈ T.ends e).card : K) := by
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h2 : T.I e Φ <;> by_cases h3 : v ∈ T.ends e <;> simp [h2, h3]
  have h2 : (∑ e, (if T.I e Φ then (if v ∈ T.ends e then (1 : K) else 0) else 0)) = 0 := by
    rw [h1]
    obtain ⟨r, hr⟩ := T.even_card Φ v
    rw [hr, Nat.cast_add]
    exact zmod_add_self _
  calc _ = ∑ e, (if T.I e Φ then (if v ∈ T.ends e then (1 : K) else 0) else 0) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        by_cases h3 : T.I e Φ <;> by_cases h4 : v ∈ T.ends e <;> simp [M, N, h3, h4]
    _ = 0 := h2

/-- The boundary of a set of faces: the edges with exactly one face in the set. -/
noncomputable def bdry (f : F → K) : E → K := T.Mᵀ.mulVec f

open Classical in
omit [Fintype V] in
/-- The boundary of a set of faces has even degree at each vertex. -/
theorem bdry_even [Finite V] (f : F → K) (w : V) : ∑ e, (if w ∈ T.ends e then T.bdry f e else 0)
  = 0 := by
  let := Fintype.ofFinite V
  have h1 : ∑ e, (if w ∈ T.ends e then T.bdry f e else 0) = dotProduct (T.bdry f) (T.N.mulVec
    (Pi.single w 1)) := by
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h2 : T.N.mulVec (Pi.single w 1) e = T.N e w := by
      simp
    rw [h2]
    by_cases h3 : w ∈ T.ends e <;> simp [N, h3]
  rw [h1, bdry, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, M_mul_N,
    Matrix.zero_mulVec,
    dotProduct_zero]

omit [Fintype E] [Fintype F] in
/-- The constant functions are the only ones with zero image under `N`. -/
theorem ker_N_const [Finite E] [Finite F] {w : V → K} (hw : T.N.mulVec w = 0) (a b : V) : w a = w b
  := by
  classical
  let := Fintype.ofFinite E
  let := Fintype.ofFinite F
  have hstep : ∀ e, ∀ p ∈ T.ends e, ∀ q ∈ T.ends e, w p = w q := fun e p hp q hq => by
    obtain ⟨c, d, hcd, he⟩ := T.exists_ends e
    have h1 := T.sum_ends e hcd he w
    rw [hw] at h1
    have h2 : w c = w d := by
      have h3 : w c + w d = 0 := h1.symm
      exact CharTwo.add_eq_zero.mp h3
    rw [he] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> simp [h2]
  have := T.conn {v | w v = w a} (fun e p hp q hq h => (hstep e p hp q hq).symm.trans h) ⟨a, rfl⟩
  have hb : b ∈ {v | w v = w a} := this ▸ mem_univ b
  exact hb.symm

omit [Fintype V] [Fintype E] in
theorem ker_M_const [Finite V] [Finite E] {f : F → K} (hf : T.Mᵀ.mulVec f = 0) (a b : F) : f a
  = f b := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite E
  have hstep : ∀ e, ∀ p, T.I e p → ∀ q, T.I e q → f p = f q := fun e p hp q hq => by
    obtain ⟨c, d, hcd, he⟩ := T.exists_faces e
    have h1 := T.sum_faces e hcd he f
    rw [hf] at h1
    have h2 : f c = f d := CharTwo.add_eq_zero.mp h1.symm
    have hp' : p ∈ ({c, d} : Set F) := he ▸ hp
    have hq' : q ∈ ({c, d} : Set F) := he ▸ hq
    rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl <;> simp [h2]
  have := T.dual {v | f v = f a} (fun e p hp q h1 h2 => (hstep e p h1 q h2).symm.trans hp) ⟨a, rfl⟩
  have hb : b ∈ {v | f v = f a} := this ▸ mem_univ b
  exact hb.symm

theorem finrank_span_one {ι : Type} [Nonempty ι] {W : Submodule K (ι → K)} (h1 : (fun _ => 1) ∈ W)
    (h2 : ∀ w ∈ W, ∀ a b, w a = w b) : Module.finrank K W = 1 := by
  have h3 : W = Submodule.span K {(fun _ => 1 : ι → K)} := by
    refine le_antisymm (fun w hw => ?_) ((Submodule.span_singleton_le_iff_mem _ _).mpr h1)
    obtain ⟨a⟩ := ‹Nonempty ι›
    refine Submodule.mem_span_singleton.mpr ⟨w a, ?_⟩
    funext b
    simp [h2 w hw b a]
  rw [h3]
  refine finrank_span_singleton fun h => ?_
  obtain ⟨a⟩ := ‹Nonempty ι›
  have := congrFun h a
  simp at this

omit [Fintype E] [Fintype F] in
/-- The rank of `N`. -/
theorem finrank_range_N [Finite E] [Finite F] [Nonempty V] : Module.finrank K
  (LinearMap.range T.N.mulVecLin) + 1 = Fintype.card V := by
  let := Fintype.ofFinite E
  let := Fintype.ofFinite F
  have h1 := LinearMap.finrank_range_add_finrank_ker T.N.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h1
  rw [← h1]
  congr 1
  refine (finrank_span_one ?_ fun w hw a b => T.ker_N_const hw a b).symm
  rw [LinearMap.mem_ker]
  funext e
  obtain ⟨c, d, hcd, he⟩ := T.exists_ends e
  exact (T.sum_ends e hcd he _).trans (zmod_add_self _)

omit [Fintype V] in
theorem rank_M_add_one [Finite V] [Nonempty F] : T.M.rank + 1 = Fintype.card F := by
  let := Fintype.ofFinite V
  have h1 := LinearMap.finrank_range_add_finrank_ker T.Mᵀ.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h1
  rw [← Matrix.rank_transpose, ← h1, Matrix.rank]
  congr 1
  refine (finrank_span_one ?_ fun w hw a b => T.ker_M_const hw a b).symm
  rw [LinearMap.mem_ker]
  funext e
  obtain ⟨c, d, hcd, he⟩ := T.exists_faces e
  exact (T.sum_faces e hcd he _).trans (zmod_add_self _)

omit [Fintype V] in
/-- The size of the kernel of `M`. -/
theorem finrank_ker_M [Finite V] [Nonempty F] : Module.finrank K (LinearMap.ker T.M.mulVecLin) +
  Fintype.card F = Fintype.card E + 1 := by
  let := Fintype.ofFinite V
  have h1 := LinearMap.finrank_range_add_finrank_ker T.M.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h1
  have h2 := T.rank_M_add_one
  rw [Matrix.rank] at h2
  omega

/-- Faces related by an edge of `C`. -/
def rel (C : Set E) (Φ Φ' : F) : Prop := ∃ e ∈ C, T.I e Φ ∧ T.I e Φ'

/-- The matrix of the edges of `C`. -/
noncomputable def Msub (C : Set E) : Matrix F C K := T.M.submatrix id Subtype.val

omit [Fintype V] [Fintype E] in
theorem rel_eq [Finite V] [Finite E] {C : Set E} [Finite C] {f : F → K} (hf : (T.Msub C)ᵀ.mulVec f
  = 0) {Φ Φ' : F} (h : T.rel C Φ Φ') : f Φ = f Φ' := by
  let := Fintype.ofFinite V
  let := Fintype.ofFinite E
  let := Fintype.ofFinite C
  obtain ⟨e, he, hp, hq⟩ := h
  obtain ⟨c, d, hcd, hE⟩ := T.exists_faces e
  have h1 := T.sum_faces e hcd hE f
  have h3 : T.Mᵀ.mulVec f e = 0 := congrFun hf ⟨e, he⟩
  rw [h3] at h1
  have h2 : f c = f d := CharTwo.add_eq_zero.mp h1.symm
  have hp' : Φ ∈ ({c, d} : Set F) := hE ▸ hp
  have hq' : Φ' ∈ ({c, d} : Set F) := hE ▸ hq
  rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl <;> simp [h2]

omit [Fintype V] [Fintype E] in
theorem card_le_rank_add [Finite V] [Finite E] (C : Set E) [Fintype C] [Finite (Quot (T.rel C))] :
    Fintype.card F ≤ (T.Msub C).rank + Nat.card (Quot (T.rel C)) := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite E
  have : Fintype (Quot (T.rel C)) := Fintype.ofFinite _
  have h1 := LinearMap.finrank_range_add_finrank_ker (T.Msub C)ᵀ.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h1
  have hker : ∀ f : LinearMap.ker (T.Msub C)ᵀ.mulVecLin, ∀ a b, T.rel C a b → f.1 a = f.1 b
    := fun f a b h =>
    T.rel_eq (LinearMap.mem_ker.mp f.2) h
  let L : LinearMap.ker (T.Msub C)ᵀ.mulVecLin →ₗ[K] (Quot (T.rel C) → K) :=
    { toFun := fun f => Quot.lift f.1 (hker f)
      map_add' := fun f g => by
        funext q
        induction q using Quot.ind
        rfl
      map_smul' := fun c f => by
        funext q
        induction q using Quot.ind
        rfl }
  have hL : Function.Injective L := by
    intro f g hfg
    apply Subtype.ext
    funext a
    exact congrFun hfg (Quot.mk _ a)
  have h2 := LinearMap.finrank_le_finrank_of_injective hL
  rw [Module.finrank_fintype_fun_eq_card] at h2
  rw [← Matrix.rank_transpose, Matrix.rank, Nat.card_eq_fintype_card]
  omega

/-- **Euler's inequality for a subgraph.** -/
theorem euler_le (Y : Set E) (VY : Set V) (hY : ∀ e ∈ Y, T.ends e ⊆ VY)
  (hne : VY.Nonempty) :
    (Fintype.card V : ℤ) - Fintype.card E + Fintype.card F ≤ VY.ncard - Y.ncard + Nat.card (Quot
      (T.rel Yᶜ)) := by
  classical
  let S : Set V := VYᶜ
  let C : Set E := Yᶜ
  let ext : (S → K) →ₗ[K] (V → K) :=
    { toFun := fun z v => if h : v ∈ S then z ⟨v, h⟩ else 0
      map_add' := fun z z' => by
        funext v
        by_cases h : v ∈ S <;> simp [h]
      map_smul' := fun c z => by
        funext v
        by_cases h : v ∈ S <;> simp [h] }
  have hext : ∀ z, ∀ v ∈ VY, ext z v = 0 := fun z v hv => by
    have : v ∉ S := fun h => h hv
    simp [ext, this]
  let res : (E → K) →ₗ[K] (C → K) := LinearMap.funLeft K K Subtype.val
  let L₀ : (S → K) →ₗ[K] (C → K) := res ∘ₗ T.N.mulVecLin ∘ₗ ext
  have hzero : ∀ z, ∀ e ∈ Y, T.N.mulVec (ext z) e = 0 := fun z e he => by
    obtain ⟨c, d, hcd, hE⟩ := T.exists_ends e
    rw [T.sum_ends e hcd hE, hext z c (hY e he (hE ▸ Or.inl rfl)), hext z d (hY e he
      (hE ▸ Or.inr rfl)), add_zero]
  have hmem : ∀ z, L₀ z ∈ LinearMap.ker (T.Msub C).mulVecLin := fun z => by
    rw [LinearMap.mem_ker]
    funext Φ
    have h1 : (T.M * T.N).mulVec (ext z) Φ = 0 := by
      rw [T.M_mul_N, Matrix.zero_mulVec]
      rfl
    rw [← Matrix.mulVec_mulVec] at h1
    have h2 : (T.Msub C).mulVecLin (L₀ z) Φ = ∑ e : C, T.M Φ e.1 * T.N.mulVec (ext z) e.1 := rfl
    have h6 : (T.M.mulVec (T.N.mulVec (ext z))) Φ = ∑ e, T.M Φ e * T.N.mulVec (ext z) e := rfl
    rw [h6] at h1
    change _ = (0 : K)
    have h7 := Finset.sum_subtype (Finset.univ.filter (· ∈ C)) (p := (· ∈ C)) (F := inferInstanceAs
      (Fintype C)) (by simp)
      (fun e => T.M Φ e * T.N.mulVec (ext z) e)
    have h8 : (∑ e : C, T.M Φ e.1 * T.N.mulVec (ext z) e.1) = ∑ e : {e // e ∈ C}, T.M Φ e.1 *
      T.N.mulVec (ext z) e.1 := rfl
    rw [h2, ← h1, h8, ← h7]
    refine Finset.sum_subset (Finset.filter_subset _ _) fun e _ h3 => ?_
    have h4 : e ∈ Y := by
      by_contra h5
      exact h3 (by simpa [C] using h5)
    rw [hzero z e h4, mul_zero]
  let L : (S → K) →ₗ[K] LinearMap.ker (T.Msub C).mulVecLin := L₀.codRestrict _ hmem
  have hL : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).mpr fun z hz => ?_
    have h1 : L₀ z = 0 := congrArg Subtype.val hz
    have h2 : T.N.mulVec (ext z) = 0 := by
      funext e
      by_cases he : e ∈ Y
      · exact hzero z e he
      · exact congrFun h1 ⟨e, he⟩
    obtain ⟨v₀, hv₀⟩ := hne
    funext v
    have h3 := T.ker_N_const h2 v.1 v₀
    rw [hext z v₀ hv₀] at h3
    have h4 : ext z v.1 = z v := by simp [ext, v.2]
    rw [← h4, h3]
    rfl
  have h3 := LinearMap.finrank_le_finrank_of_injective hL
  rw [Module.finrank_fintype_fun_eq_card] at h3
  have h4 := LinearMap.finrank_range_add_finrank_ker (T.Msub C).mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h4
  have h5 := T.card_le_rank_add C
  rw [Matrix.rank] at h5
  have hc1 : Fintype.card S + VY.ncard = Fintype.card V := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_coe_set_eq, add_comm]
    have := ncard_add_ncard_compl VY
    rw [Nat.card_eq_fintype_card] at this
    exact this
  have hc2 : Fintype.card C + Y.ncard = Fintype.card E := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_coe_set_eq, add_comm]
    have := ncard_add_ncard_compl Y
    rw [Nat.card_eq_fintype_card] at this
    exact this
  have h6 : Nat.card (Quot (T.rel C)) = Nat.card (Quot (T.rel Yᶜ)) := rfl
  omega

/-- A subdivided graph in the triangulation: the edges of the graph are the paths `Y i`, whose inner
vertices are `Int i` and whose ends are `D i`. -/
structure Subdiv {I : Type} (T : TriCx V E F) (Y : I → Set E) (Int D : I → Set V) : Prop where
  disj : ∀ i j, i ≠ j → Disjoint (Y i) (Y j)
  ne : ∀ i, (Y i).Nonempty
  path : ∀ i, ∀ S ⊆ Y i, S.Nonempty → S ≠ Y i → ∃ w ∈ Int i, ∃ x ∈ S, ∃ x' ∈ Y i \ S, w ∈ T.ends x
    ∧ w ∈ T.ends x'
  deg : ∀ i, ∀ w ∈ Int i, {x | (∃ j, x ∈ Y j) ∧ w ∈ T.ends x}.ncard ≤ 2
  end_one : ∀ i, ∀ u ∈ D i, {x ∈ Y i | u ∈ T.ends x}.ncard = 1
  end_zero : ∀ i j, ∀ u ∈ D i, u ∉ D j → ∀ x ∈ Y j, u ∉ T.ends x
  two : ∀ i, (D i).ncard = 2
  inj : Function.Injective D

section Flags

variable {I : Type} [Fintype I] {T} {Y : I → Set E} {Int D : I → Set V}

/-- The indicator of a class of faces. -/
noncomputable def clsInd (C : Set E) (ρ : Quot (T.rel C)) : F → K := by
  classical
  exact fun Φ => if Quot.mk _ Φ = ρ then 1 else 0

omit [Fintype V] [Fintype E] in
theorem bdry_clsInd [Finite V] [Finite E] (C : Set E) (ρ : Quot (T.rel C)) {e : E}
  (he : e ∈ C) : T.bdry (clsInd C ρ) e = 0 := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite E
  obtain ⟨c, d, hcd, hE⟩ := T.exists_faces e
  rw [bdry, T.sum_faces e hcd hE]
  have hc : T.I e c := (hE ▸ Or.inl rfl : c ∈ {Φ | T.I e Φ})
  have hd : T.I e d := (hE ▸ Or.inr rfl : d ∈ {Φ | T.I e Φ})
  have h1 : Quot.mk (T.rel C) c = Quot.mk _ d := Quot.sound ⟨e, he, hc, hd⟩
  simp only [clsInd, h1]
  exact zmod_add_self _

omit [Fintype V] [Fintype E] in
/-- If the boundary vanishes at an edge and one face of the edge is in the set, so is the other. -/
theorem mem_of_bdry_zero [Finite V] [Finite E] (f : F → K) {e : E} (h : T.bdry f e = 0) {Φ Φ' : F}
  (hΦ : T.I e Φ) (hΦ' : T.I e Φ') : f Φ = f Φ' := by
  let := Fintype.ofFinite V
  let := Fintype.ofFinite E
  obtain ⟨c, d, hcd, hE⟩ := T.exists_faces e
  rw [bdry, T.sum_faces e hcd hE] at h
  have h2 : f c = f d := CharTwo.add_eq_zero.mp h
  have hp' : Φ ∈ ({c, d} : Set F) := hE ▸ hΦ
  have hq' : Φ' ∈ ({c, d} : Set F) := hE ▸ hΦ'
  rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl <;> simp [h2]

omit [Fintype V] [Fintype E] in
/-- If the boundary does not vanish at an edge, then a face of the edge has `f = 1`. -/
theorem exists_one_of_bdry [Finite V] [Finite E] (f : F → K) {e : E} (h : T.bdry f e ≠ 0) : ∃ Φ,
  T.I e Φ ∧ f Φ ≠ 0 := by
  let := Fintype.ofFinite V
  let := Fintype.ofFinite E
  obtain ⟨c, d, hcd, hE⟩ := T.exists_faces e
  rw [bdry, T.sum_faces e hcd hE] at h
  have hc : T.I e c := (hE ▸ Or.inl rfl : c ∈ {Φ | T.I e Φ})
  have hd : T.I e d := (hE ▸ Or.inr rfl : d ∈ {Φ | T.I e Φ})
  by_cases h1 : f c = 0
  · refine ⟨d, hd, fun h2 => h ?_⟩
    rw [h1, h2, add_zero]
  · exact ⟨c, hc, h1⟩

theorem zmod_ne_zero {x : K} (h : x ≠ 0) : x = 1 := by
  revert x
  decide

open Classical in
omit [Fintype V] in
/-- The sum of the boundary over the edges of the graph at a vertex vanishes. -/
theorem sum_graph [Finite V] (ρ : Quot (T.rel (⋃ i, Y i)ᶜ)) (w : V) :
    ∑ e ∈ Finset.univ.filter (fun e => (∃ j, e ∈ Y j) ∧ w ∈ T.ends e), T.bdry (clsInd _ ρ) e = 0
      := by
  let := Fintype.ofFinite V
  have h1 := T.bdry_even (clsInd _ ρ) w
  rw [← h1, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h2 : ∃ j, e ∈ Y j
  · by_cases h3 : w ∈ T.ends e <;> simp [h2, h3]
  · have h4 : e ∈ (⋃ i, Y i)ᶜ := by simpa using h2
    simp [h2, bdry_clsInd _ ρ h4]

omit [Fintype V] [Fintype E] [Fintype I] in
/-- Two edges of the graph at a vertex of degree two have the same boundary value. -/
theorem bdry_eq_of_deg [Finite V] [Finite E] [Finite I] (hS : T.Subdiv Y Int D) (ρ : Quot (T.rel
  (⋃ i, Y i)ᶜ)) {i : I} {w : V} (hw : w ∈ Int i) {x x' : E}
    (hx : ∃ j, x ∈ Y j) (hx' : ∃ j, x' ∈ Y j) (hwx : w ∈ T.ends x) (hwx' : w ∈ T.ends x')
      (hne : x ≠ x') :
    T.bdry (clsInd _ ρ) x = T.bdry (clsInd _ ρ) x' := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite E
  let := Fintype.ofFinite I
  have h1 := sum_graph ρ w
  have hset : Finset.univ.filter (fun e => (∃ j, e ∈ Y j) ∧ w ∈ T.ends e) = {x, x'} := by
    have hs : ({x, x'} : Finset E) ⊆ Finset.univ.filter (fun e => (∃ j, e ∈ Y j) ∧ w ∈ T.ends e)
      := by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · simpa using ⟨hx, hwx⟩
      · simpa using ⟨hx', hwx'⟩
    refine (Finset.eq_of_subset_of_card_le hs ?_).symm
    have h2 := hS.deg i w hw
    rw [Finset.card_pair hne]
    have h3 : ({x | (∃ j, x ∈ Y j) ∧ w ∈ T.ends x} : Set E) = ↑(Finset.univ.filter (fun e =>
      (∃ j, e ∈ Y j) ∧ w ∈ T.ends e)) := by
      ext e
      simp
    rwa [h3, ncard_coe_finset] at h2
  rw [hset, Finset.sum_pair hne] at h1
  exact CharTwo.add_eq_zero.mp h1

/-- A class is touched by an edge if one of its faces has this edge. -/
def Tch (C : Set E) (ρ : Quot (T.rel C)) (x : E) : Prop := ∃ Φ, T.I x Φ ∧ Quot.mk _ Φ = ρ

omit [Fintype V] [Fintype E] [Fintype F] in
theorem clsInd_ne {C : Set E} {ρ : Quot (T.rel C)} {Φ : F} : clsInd C ρ Φ ≠ 0 ↔ Quot.mk _ Φ = ρ
  := by
  classical
  simp only [clsInd]
  by_cases h : Quot.mk (T.rel C) Φ = ρ <;> simp [h]

omit [Fintype V] [Fintype E] [Fintype F] in
theorem exists_face [Finite V] [Finite E] [Finite F] (e : E) : ∃ Φ, T.I e Φ := by
  let := Fintype.ofFinite V
  let := Fintype.ofFinite E
  let := Fintype.ofFinite F
  obtain ⟨c, d, hcd, hE⟩ := T.exists_faces e
  exact ⟨c, (hE ▸ Or.inl rfl : c ∈ {Φ | T.I e Φ})⟩

omit [Fintype V] [Fintype E] [Fintype F] [Fintype I] in
/-- Touching passes along a vertex of degree two, by the link condition. -/
theorem tch_step [Finite V] [Finite E] [Finite F] [Finite I] (hS : T.Subdiv Y Int D) (ρ : Quot
  (T.rel (⋃ i, Y i)ᶜ)) {i : I} {w : V} (hw : w ∈ Int i) {x x' : E}
    (hx : ∃ j, x ∈ Y j) (hx' : ∃ j, x' ∈ Y j) (hwx : w ∈ T.ends x) (hwx' : w ∈ T.ends x')
      (hne : x ≠ x') (ht : Tch _ ρ x) :
    Tch _ ρ x' := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite E
  let := Fintype.ofFinite F
  let := Fintype.ofFinite I
  have heq := bdry_eq_of_deg hS ρ hw hx hx' hwx hwx' hne
  by_cases h0 : T.bdry (clsInd _ ρ) x' = 0
  · have h0x := heq.trans h0
    have hall : ∀ e, w ∈ T.ends e → T.bdry (clsInd _ ρ) e = 0 := fun e hwe => by
      by_cases h1 : e = x
      · rw [h1, h0x]
      by_cases h2 : e = x'
      · rw [h2, h0]
      by_cases h3 : ∃ j, e ∈ Y j
      · exfalso
        have hsub : ({x, x', e} : Set E) ⊆ {x | (∃ j, x ∈ Y j) ∧ w ∈ T.ends x} := by
          rintro y (rfl | rfl | rfl)
          · exact ⟨hx, hwx⟩
          · exact ⟨hx', hwx'⟩
          · exact ⟨h3, hwe⟩
        have h4 := ncard_le_ncard hsub (Set.toFinite _)
        rw [ncard_eq_three.mpr ⟨x, x', e, hne, Ne.symm h1, Ne.symm h2, rfl⟩] at h4
        have := hS.deg i w hw
        omega
      · exact bdry_clsInd _ ρ (by simpa using h3)
    obtain ⟨Φ, hΦ, hρ⟩ := ht
    obtain ⟨Φ', hΦ'⟩ := exists_face (T := T) x'
    refine ⟨Φ', hΦ', ?_⟩
    have hmem : Φ' ∈ {Ψ | w ∈ T.verts Ψ ∧ Quot.mk (T.rel (⋃ i, Y i)ᶜ) Ψ = ρ} := by
      refine T.link w {Ψ | w ∈ T.verts Ψ ∧ Quot.mk (T.rel (⋃ i, Y i)ᶜ) Ψ = ρ} (fun Ψ h => h.1)
        (fun e hwe Ψ hΨ Ψ' h1 h2 => ⟨h2 hwe, ?_⟩) ⟨Φ, hΦ hwx, hρ⟩ Φ' (hΦ' hwx')
      have h3 := mem_of_bdry_zero (clsInd _ ρ) (hall e hwe) h1 h2
      exact clsInd_ne.mp (by rw [← h3]; exact clsInd_ne.mpr hΨ.2)
    exact hmem.2
  · obtain ⟨Φ, hΦ, h1⟩ := exists_one_of_bdry _ h0
    exact ⟨Φ, hΦ, clsInd_ne.mp h1⟩

omit [Fintype V] [Fintype E] [Fintype F] [Fintype I] in
theorem subset_all (hS : T.Subdiv Y Int D) {i : I} {P : E → Prop}
    (hstep : ∀ w ∈ Int i, ∀ x ∈ Y i, ∀ x' ∈ Y i, w ∈ T.ends x → w ∈ T.ends x' → x ≠ x' → P x → P x')
    {x : E} (hx : x ∈ Y i) (hP : P x) {x' : E} (hx' : x' ∈ Y i) : P x' := by
  by_contra hn
  have hne : {y ∈ Y i | P y} ≠ Y i := fun h => by
    have h1 : x' ∈ {y ∈ Y i | P y} := by
      rw [h]
      exact hx'
    exact hn h1.2
  obtain ⟨w, hw, y, hy, y', hy', h1, h2⟩ := hS.path i {y ∈ Y i | P y} (fun y hy
    => hy.1) ⟨x, hx, hP⟩ hne
  have hyne : y ≠ y' := fun h => hy'.2 (h ▸ hy)
  exact hy'.2 ⟨hy'.1, hstep w hw y hy.1 y' hy'.1 h1 h2 hyne hy.2⟩

theorem bdry_cases (x : K) : x = 0 ∨ x = 1 := by
  revert x
  decide

omit [Fintype V] [Fintype E] [Fintype F] in
/-- Each class of faces is touched by at least three edges of the graph. -/
theorem three_le_touch [Finite V] [Finite E] [Finite F] (hS : T.Subdiv Y Int D) (hI : 3
  ≤ Fintype.card I) (ρ : Quot (T.rel (⋃ i, Y i)ᶜ)) :
    3 ≤ {i | ∃ x ∈ Y i, Tch _ ρ x}.ncard := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite E
  let := Fintype.ofFinite F
  by_contra hlt
  push Not at hlt
  have hY : ∀ {i x}, x ∈ Y i → ∃ j, x ∈ Y j := fun {i x} h => ⟨i, h⟩
  let g := T.bdry (clsInd _ ρ)
  have hgall : ∀ i, ∀ x ∈ Y i, g x ≠ 0 → ∀ x' ∈ Y i, g x' ≠ 0 := fun i x hx h x' hx' =>
    subset_all hS (P := fun y => g y ≠ 0) (fun w hw y hy y' hy' h1 h2 hne h3 h4 =>
      h3 ((bdry_eq_of_deg hS ρ hw (hY hy) (hY hy') h1 h2 hne).trans h4)) hx h hx'
  have htouch : ∀ i, ∀ x ∈ Y i, g x ≠ 0 → i ∈ {i | ∃ x ∈ Y i, Tch _ ρ x} := fun i x hx h => by
    obtain ⟨Φ, hΦ, h1⟩ := exists_one_of_bdry _ h
    exact ⟨x, hx, Φ, hΦ, clsInd_ne.mp h1⟩
  let J : Set I := {i | ∃ x ∈ Y i, g x ≠ 0}
  have hJs : J ⊆ {i | ∃ x ∈ Y i, Tch _ ρ x} := fun i ⟨x, hx, h⟩ => htouch i x hx h
  have hJ2 : J.ncard ≤ 2 := by
    have := ncard_le_ncard hJs (Set.toFinite _)
    omega
  have hother : ∀ i ∈ J, ∀ u ∈ D i, ∃ j ∈ J, j ≠ i ∧ u ∈ D j := fun i ⟨x₀, hx₀, hg₀⟩ u hu => by
    by_contra hn
    push Not at hn
    obtain ⟨x, hxs⟩ := ncard_eq_one.mp (hS.end_one i u hu)
    have hxm : x ∈ {x ∈ Y i | u ∈ T.ends x} := hxs ▸ rfl
    have hgx : g x ≠ 0 := hgall i x₀ hx₀ hg₀ x hxm.1
    have h1 := sum_graph ρ u
    rw [Finset.sum_eq_single_of_mem x (by simpa using ⟨hY hxm.1, hxm.2⟩)] at h1
    · exact hgx h1
    · intro e he hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
      obtain ⟨⟨j, hj⟩, hue⟩ := he
      by_contra hge
      have hjJ : j ∈ J := ⟨e, hj, hge⟩
      by_cases hij : j = i
      · subst hij
        have : e ∈ {x ∈ Y j | u ∈ T.ends x} := ⟨hj, hue⟩
        rw [hxs] at this
        exact hne this
      · by_cases huj : u ∈ D j
        · exact hn j hjJ hij huj
        · exact hS.end_zero i j u hu huj e hj hue
  have hJe : J = ∅ := by
    by_contra hc
    obtain ⟨i, hi⟩ := nonempty_iff_ne_empty.mpr hc
    obtain ⟨u, v, huv, hE⟩ := ncard_eq_two.mp (hS.two i)
    obtain ⟨j, hj, hji, hju⟩ := hother i hi u (hE ▸ Or.inl rfl)
    obtain ⟨j', hj', hji', hjv⟩ := hother i hi v (hE ▸ Or.inr rfl)
    have hjj : j = j' := by
      by_contra hne
      have h1 : ({i, j, j'} : Set I) ⊆ J := by
        rintro y (rfl | rfl | rfl)
        · exact hi
        · exact hj
        · exact hj'
      have h2 := ncard_le_ncard h1 (Set.toFinite _)
      rw [ncard_eq_three.mpr ⟨i, j, j', Ne.symm hji, Ne.symm hji', hne, rfl⟩] at h2
      omega
    subst hjj
    have hsub : D i ⊆ D j := by
      rw [hE]
      rintro y (rfl | rfl)
      · exact hju
      · exact hjv
    have h3 : D i = D j := eq_of_subset_of_ncard_le hsub (by rw [hS.two, hS.two]) (Set.toFinite _)
    exact hji (hS.inj h3).symm
  have hg0 : ∀ e, g e = 0 := fun e => by
    by_contra hne
    by_cases h1 : ∃ j, e ∈ Y j
    · obtain ⟨j, hj⟩ := h1
      have : j ∈ J := ⟨e, hj, hne⟩
      rw [hJe] at this
      exact this
    · exact hne (bdry_clsInd _ ρ (by simpa using h1))
  have hall : {Φ | Quot.mk (T.rel (⋃ i, Y i)ᶜ) Φ = ρ} = univ := by
    refine T.dual _ (fun e Φ hΦ Φ' h1 h2 => ?_) ?_
    · have h3 := mem_of_bdry_zero (clsInd _ ρ) (hg0 e) h1 h2
      exact clsInd_ne.mp (by rw [← h3]; exact clsInd_ne.mpr hΦ)
    · induction ρ using Quot.ind with
      | mk a => exact ⟨a, rfl⟩
  have huniv : {i | ∃ x ∈ Y i, Tch _ ρ x} = univ := by
    rw [eq_univ_iff_forall]
    intro i
    obtain ⟨x, hx⟩ := hS.ne i
    obtain ⟨Φ, hΦ⟩ := exists_face (T := T) x
    have : Φ ∈ {Φ | Quot.mk (T.rel (⋃ i, Y i)ᶜ) Φ = ρ} := hall ▸ mem_univ Φ
    exact ⟨x, hx, Φ, hΦ, this⟩
  rw [huniv, ncard_univ, Nat.card_eq_fintype_card] at hlt
  omega

omit [Fintype V] [Fintype E] [Fintype F] in
/-- **Three times the classes is at most twice the edges.** -/
theorem three_classes_le [Finite V] [Finite E] [Finite F] (hS : T.Subdiv Y Int D) (hI : 3
  ≤ Fintype.card I) [Finite (Quot (T.rel (⋃ i, Y i)ᶜ))] :
    3 * Nat.card (Quot (T.rel (⋃ i, Y i)ᶜ)) ≤ 2 * Fintype.card I := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite E
  let := Fintype.ofFinite F
  have : Fintype (Quot (T.rel (⋃ i, Y i)ᶜ)) := Fintype.ofFinite _
  set Q := Quot (T.rel (⋃ i, Y i)ᶜ) with hQ
  have hch : ∀ i, ∃ x, x ∈ Y i := fun i => hS.ne i
  choose x hx using hch
  have hf : ∀ i, ∃ a b, ∀ ρ : Q, (∃ y ∈ Y i, Tch _ ρ y) → ρ = a ∨ ρ = b := fun i => by
    obtain ⟨c, d, hcd, hE⟩ := T.exists_faces (x i)
    refine ⟨Quot.mk _ c, Quot.mk _ d, fun ρ ⟨y, hy, ht⟩ => ?_⟩
    have h1 : Tch _ ρ (x i) := subset_all hS (P := fun y => Tch _ ρ y)
      (fun w hw y hy y' hy' h1 h2 hne h3 =>
      tch_step hS ρ hw ⟨i, hy⟩ ⟨i, hy'⟩ h1 h2 hne h3) hy ht (hx i)
    obtain ⟨Φ, hΦ, rfl⟩ := h1
    have h2 : Φ ∈ ({c, d} : Set F) := hE ▸ hΦ
    rcases h2 with rfl | rfl
    · exact .inl rfl
    · exact .inr rfl
  choose a b hab using hf
  let P : Q → I → Prop := fun ρ i => ∃ y ∈ Y i, Tch _ ρ y
  have h1 : ∀ ρ : Q, 3 ≤ (Finset.univ.filter (P ρ)).card := fun ρ => by
    have h2 := three_le_touch hS hI ρ
    have h3 : ({i | ∃ x ∈ Y i, Tch _ ρ x} : Set I) = ↑(Finset.univ.filter (P ρ)) := by
      ext i
      simp [P]
    rwa [h3, ncard_coe_finset] at h2
  have h2 : ∀ i : I, (Finset.univ.filter fun ρ => P ρ i).card ≤ 2 := fun i => by
    refine (Finset.card_le_card (t := {a i, b i}) fun ρ hρ => ?_).trans Finset.card_le_two
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ
    simpa using hab i ρ hρ
  have h3 : ∑ ρ : Q, (Finset.univ.filter (P ρ)).card = ∑ i : I, (Finset.univ.filter fun ρ
    => P ρ i).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have h4 : Fintype.card Q * 3 ≤ ∑ ρ : Q, (Finset.univ.filter (P ρ)).card := by
    have := Finset.card_nsmul_le_sum Finset.univ _ 3 fun ρ _ => h1 ρ
    simpa using this
  have h5 : ∑ i : I, (Finset.univ.filter fun ρ => P ρ i).card ≤ Fintype.card I * 2 := by
    have := Finset.sum_le_card_nsmul Finset.univ _ 2 fun i _ => h2 i
    simpa using this
  rw [Nat.card_eq_fintype_card]
  omega

end Flags

theorem ncard_biUnion_sum {ι α : Type*} (s : Finset ι) (f : ι → Set α) [Finite α]
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (f i) (f j)) :
    (⋃ i ∈ s, f i).ncard = ∑ i ∈ s, (f i).ncard := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h2 : Disjoint (f a) (⋃ i ∈ s, f i) := by
      refine disjoint_iUnion₂_right.mpr fun i hi => hd a (Finset.mem_insert_self _ _) i
        (Finset.mem_insert_of_mem hi) ?_
      rintro rfl
      exact ha hi
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert, ncard_union_eq h2 (Set.toFinite _)
      (Set.toFinite _),
      ih (fun i hi j hj => hd i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))]

theorem ncard_biUnion_le_sum {ι α : Type*} (s : Finset ι) (f : ι → Set α) :
    (⋃ i ∈ s, f i).ncard ≤ ∑ i ∈ s, (f i).ncard := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert]
    exact (ncard_union_le _ _).trans (by omega)

/-- **The edge bound.** A simple graph with at least three edges in a triangulated surface has at
most `3 |V| - 3 χ` edges. -/
theorem edges_le {I : Type} [Fintype I] {Y : I → Set E} {Int D : I → Set V} (hS : T.Subdiv Y Int D)
  (hI : 3 ≤ Fintype.card I)
    {VD : Set V} (hVD : VD.Nonempty) (hVY : ∀ i, ∀ x ∈ Y i, T.ends x ⊆ VD ∪ ⋃ i, Int i)
    (hc : ∀ i, (Int i).ncard + 1 ≤ (Y i).ncard) :
    (Fintype.card I : ℤ) ≤ 3 * VD.ncard - 3 * ((Fintype.card V : ℤ) - Fintype.card E + Fintype.card
      F) := by
  classical
  have h1 := T.euler_le (⋃ i, Y i) (VD ∪ ⋃ i, Int i) (fun e he => by
    obtain ⟨i, hi⟩ := mem_iUnion.mp he
    exact hVY i e hi) (hVD.mono subset_union_left)
  have h2 := three_classes_le hS hI
  have h3 : (⋃ i, Y i).ncard = ∑ i, (Y i).ncard := by
    have := ncard_biUnion_sum Finset.univ Y fun i _ j _ hne => hS.disj i j hne
    simpa using this
  have h4 : (⋃ i, Int i).ncard ≤ ∑ i, (Int i).ncard := by
    have := ncard_biUnion_le_sum Finset.univ Int
    simpa using this
  have h5 : (VD ∪ ⋃ i, Int i).ncard ≤ VD.ncard + ∑ i, (Int i).ncard :=
    (ncard_union_le _ _).trans (by omega)
  have h6 : ∑ i, ((Int i).ncard + 1) ≤ ∑ i, (Y i).ncard := Finset.sum_le_sum fun i _ => hc i
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h6
  omega

omit [Fintype V] [Fintype F] in
theorem card_edges [Finite V] [Finite F] (Φ : F) [DecidablePred fun e => T.I e Φ] :
  (Finset.univ.filter fun e => T.I e Φ).card = 3 := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite F
  have hends : ∀ e, (Finset.univ.filter fun v => v ∈ T.ends e).card = 2 := fun e => by
    have h1 := T.ends_two e
    have h2 : T.ends e = ↑(Finset.univ.filter fun v => v ∈ T.ends e) := by
      ext v
      simp
    rwa [h2, ncard_coe_finset] at h1
  have hthree : ∀ Φ, (Finset.univ.filter fun v => v ∈ T.verts Φ).card = 3 := fun Φ => by
    have h1 := T.verts_three Φ
    have h2 : T.verts Φ = ↑(Finset.univ.filter fun v => v ∈ T.verts Φ) := by
      ext v
      simp
    rwa [h2, ncard_coe_finset] at h1
  have h1 : ∑ v, (Finset.univ.filter fun e => T.I e Φ ∧ v ∈ T.ends e).card =
      ∑ e, (Finset.univ.filter fun v => T.I e Φ ∧ v ∈ T.ends e).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have h2 : ∀ v, (Finset.univ.filter fun e => T.I e Φ ∧ v ∈ T.ends e).card
    = if v ∈ T.verts Φ then 2 else 0 := fun v => by
    by_cases hv : v ∈ T.verts Φ
    · simp only [hv, ite_true]
      exact T.card_at Φ hv
    · simp only [hv, ite_false]
      rw [Finset.card_eq_zero]
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
        not_and]
      exact fun h1 h2 => hv (h1 h2)
  have h3 : ∀ e, (Finset.univ.filter fun v => T.I e Φ ∧ v ∈ T.ends e).card
    = if T.I e Φ then 2 else 0 := fun e => by
    by_cases he : T.I e Φ
    · simp [he, hends]
    · simp [he]
  simp only [h2, h3] at h1
  rw [← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const, hthree,
    smul_eq_mul, smul_eq_mul] at h1
  have h4 : (Finset.univ.filter fun e => T.I e Φ).card = 3 := by omega
  convert h4

include T in
omit [Fintype V] in
/-- Each face has three edges and each edge has two faces. -/
theorem three_faces [Finite V] : 3 * Fintype.card F = 2 * Fintype.card E := by
  classical
  let := Fintype.ofFinite V
  have hfaces : ∀ e, (Finset.univ.filter fun Φ => T.I e Φ).card = 2 := fun e => by
    have h1 := T.two e
    have h2 : {Φ | T.ends e ⊆ T.verts Φ} = ↑(Finset.univ.filter fun Φ => T.I e Φ) := by
      ext v
      simp only [mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Iff.rfl
    rwa [h2, ncard_coe_finset] at h1
  have h1 : ∑ Φ, (Finset.univ.filter fun e => T.I e Φ).card = ∑ e, (Finset.univ.filter fun Φ
    => T.I e Φ).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  simp only [T.card_edges, hfaces, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h1
  omega

omit [Fintype V] [Fintype F] in
/-- The value of `M` on a function, in terms of the three edges of a face. -/
theorem sum_three [Finite V] [Finite F] (y : E → K) (Φ : F) {e₁ e₂ e₃ : E} (h₁ : T.I e₁ Φ)
  (h₂ : T.I e₂ Φ) (h₃ : T.I e₃ Φ) (h12 : e₁ ≠ e₂)
    (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃) : T.M.mulVec y Φ = y e₁ + y e₂ + y e₃ := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite F
  have hs : ({e₁, e₂, e₃} : Finset E) ⊆ Finset.univ.filter fun e => T.I e Φ := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl <;> simpa
  have hc : ({e₁, e₂, e₃} : Finset E).card = 3 := Finset.card_eq_three.mpr ⟨e₁, e₂, e₃, h12, h13,
    h23, rfl⟩
  have heq := Finset.eq_of_subset_of_card_le hs (by rw [T.card_edges, hc])
  have h1 : T.M.mulVec y Φ = ∑ e ∈ Finset.univ.filter (fun e => T.I e Φ), y e := by
    simp only [mulVec, dotProduct, M, Finset.sum_filter]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h : T.I e Φ <;> simp [h]
  rw [h1, ← heq, Finset.sum_insert (by simp [h12, h13]), Finset.sum_pair h23, add_assoc]

end TriCx

end GraphMinor.Surface
