/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Section3
import Mathlib.Topology.UniformSpace.OfCompactT2
import Mathlib.Topology.UniformSpace.Compact

/-!
# Homotopy classes of paths

Paths are taken up to homotopy with fixed ends (`Cl`), since in this way the products of paths are
associative. `Arw A f` says that the class `f` contains a path in `A`. A set is `Flat` if paths in
it with
the same ends are homotopic in the whole space.

`cl_induction` is induction along a path that is cut in pieces, and `exists_small_rel` is the
Lebesgue number
of an open cover of a compact space.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval Uniformity

universe u

variable {T : Type u} [TopologicalSpace T]

/-- The homotopy classes of paths from `a` to `b`, with the ends fixed. -/
abbrev Cl (a b : T) := Path.Homotopic.Quotient a b

/-- The class of a path. -/
abbrev Cl.mk {a b : T} (p : Path a b) : Cl a b := Path.Homotopic.Quotient.mk p

/-- The class of the constant path. -/
abbrev Cl.rf (a : T) : Cl a a := Path.Homotopic.Quotient.refl a

section Classes

variable {a b c d : T}

theorem cl_assoc (f : Cl a b) (g : Cl b c) (h : Cl c d) : (f.trans g).trans h = f.trans (g.trans h)
  := by
  induction f using Path.Homotopic.Quotient.ind with | mk f => ?_
  induction g using Path.Homotopic.Quotient.ind with | mk g => ?_
  induction h using Path.Homotopic.Quotient.ind with | mk h => ?_
  simp only [← Path.Homotopic.Quotient.mk_trans]
  exact Path.Homotopic.Quotient.eq.mpr (Path.Homotopic.trans_assoc f g h)

theorem cl_refl_trans (f : Cl a b) : (Cl.rf a).trans f = f := by
  induction f using Path.Homotopic.Quotient.ind with | mk f => ?_
  rw [Cl.rf, ← Path.Homotopic.Quotient.mk_refl, ← Path.Homotopic.Quotient.mk_trans]
  exact Path.Homotopic.Quotient.eq.mpr (Path.Homotopic.refl_trans f)

theorem cl_trans_refl (f : Cl a b) : f.trans (Cl.rf b) = f := by
  induction f using Path.Homotopic.Quotient.ind with | mk f => ?_
  rw [Cl.rf, ← Path.Homotopic.Quotient.mk_refl, ← Path.Homotopic.Quotient.mk_trans]
  exact Path.Homotopic.Quotient.eq.mpr (Path.Homotopic.trans_refl f)

theorem cl_trans_symm (f : Cl a b) : f.trans f.symm = Cl.rf a := by
  induction f using Path.Homotopic.Quotient.ind with | mk f => ?_
  rw [← Path.Homotopic.Quotient.mk_symm, ← Path.Homotopic.Quotient.mk_trans, Cl.rf,
    ← Path.Homotopic.Quotient.mk_refl]
  exact Path.Homotopic.Quotient.eq.mpr (Path.Homotopic.trans_symm f)

theorem cl_symm_trans (f : Cl a b) : f.symm.trans f = Cl.rf b := by
  induction f using Path.Homotopic.Quotient.ind with | mk f => ?_
  rw [← Path.Homotopic.Quotient.mk_symm, ← Path.Homotopic.Quotient.mk_trans, Cl.rf,
    ← Path.Homotopic.Quotient.mk_refl]
  exact Path.Homotopic.Quotient.eq.mpr (Path.Homotopic.symm_trans f)

theorem cl_symm_trans_left (f : Cl a b) (g : Cl b c) : f.symm.trans (f.trans g) = g := by
  rw [← cl_assoc, cl_symm_trans, cl_refl_trans]

/-- The class `f` contains a path in `A`. -/
def Arw (A : Set T) (f : Cl a b) : Prop := ∃ p : Path a b, (∀ u, p u ∈ A) ∧ f = Cl.mk p

theorem Arw.of_path {A : Set T} (p : Path a b) (hp : ∀ u, p u ∈ A) : Arw A (Cl.mk p) := ⟨p, hp, rfl⟩

theorem Arw.left_mem {A : Set T} {f : Cl a b} (h : Arw A f) : a ∈ A := by
  obtain ⟨p, hp, -⟩ := h
  simpa using hp 0

theorem Arw.right_mem {A : Set T} {f : Cl a b} (h : Arw A f) : b ∈ A := by
  obtain ⟨p, hp, -⟩ := h
  simpa using hp 1

theorem Arw.mono {A B : Set T} {f : Cl a b} (h : Arw A f) (hAB : A ⊆ B) : Arw B f := by
  obtain ⟨p, hp, rfl⟩ := h
  exact ⟨p, fun u => hAB (hp u), rfl⟩

theorem Arw.trans {A : Set T} {f : Cl a b} {g : Cl b c} (hf : Arw A f) (hg : Arw A g) :
    Arw A (f.trans g) := by
  obtain ⟨p, hp, rfl⟩ := hf
  obtain ⟨q, hq, rfl⟩ := hg
  refine ⟨p.trans q, fun u => ?_, (Path.Homotopic.Quotient.mk_trans p q).symm⟩
  have : (p.trans q) u ∈ range p ∪ range q := by
    rw [← Path.trans_range]
    exact mem_range_self u
  rcases this with ⟨v, hv⟩ | ⟨v, hv⟩
  · rw [← hv]
    exact hp v
  · rw [← hv]
    exact hq v

theorem Arw.symm {A : Set T} {f : Cl a b} (hf : Arw A f) : Arw A f.symm := by
  obtain ⟨p, hp, rfl⟩ := hf
  refine ⟨p.symm, fun u => ?_, (Path.Homotopic.Quotient.mk_symm p).symm⟩
  rw [Path.symm_apply]
  exact hp _

theorem arw_refl {A : Set T} (h : a ∈ A) : Arw A (Cl.rf a) :=
  ⟨Path.refl a, fun _ => h, (Path.Homotopic.Quotient.mk_refl a).symm⟩

end Classes

/-- Paths in `A` with the same ends are homotopic in the whole space. -/
def Flat (A : Set T) : Prop :=
  ∀ ⦃a b : T⦄ (p q : Path a b), (∀ u, p u ∈ A) → (∀ u, q u ∈ A) → p.Homotopic q

theorem Flat.mono {A B : Set T} (h : Flat B) (hAB : A ⊆ B) : Flat A :=
  fun _ _ p q hp hq => h p q (fun u => hAB (hp u)) fun u => hAB (hq u)

theorem Flat.eq {A : Set T} (h : Flat A) {a b : T} {f g : Cl a b} (hf : Arw A f) (hg : Arw A g) : f
  = g := by
  obtain ⟨p, hp, rfl⟩ := hf
  obtain ⟨q, hq, rfl⟩ := hg
  exact Path.Homotopic.Quotient.eq.mpr (h p q hp hq)

/-- A simply-connected set is flat. -/
theorem IsSimplyConnectedSet.flat {A : Set T} (hA : IsSimplyConnectedSet A) : Flat A := by
  intro a b p q hp hq
  have ha : a ∈ A := by simpa using hp 0
  have hb : b ∈ A := by simpa using hp 1
  let f : C(A, T) := ⟨Subtype.val, continuous_subtype_val⟩
  let p' : Path (⟨a, ha⟩ : A) ⟨b, hb⟩ :=
    ⟨⟨fun u => ⟨p u, hp u⟩, by fun_prop⟩, by simp, by simp⟩
  let q' : Path (⟨a, ha⟩ : A) ⟨b, hb⟩ :=
    ⟨⟨fun u => ⟨q u, hq u⟩, by fun_prop⟩, by simp, by simp⟩
  have h := (hA.pathsHomotopic p' q').map f
  exact h

/-- The Lebesgue number of a cover: a relation `R` for which each point has its `R`-neighbours in
one set of
the cover, and each point has an open neighbourhood whose points are all `R`-related. -/
theorem exists_small_rel [CompactSpace T] [T2Space T] {ι : Type*} (U : ι → Set T) (hU : ∀ i, IsOpen
  (U i))
    (hc : univ ⊆ ⋃ i, U i) :
    ∃ R : T → T → Prop, (∀ x, ∃ i, ∀ y, R x y → y ∈ U i) ∧
      ∀ x, ∃ N : Set T, IsOpen N ∧ x ∈ N ∧ ∀ a ∈ N, ∀ b ∈ N, R a b := by
  let _ : UniformSpace T := uniformSpaceOfCompactR1
  obtain ⟨V, hV, hball⟩ := lebesgue_number_lemma (isCompact_univ (X := T)) hU hc
  obtain ⟨W, hW, hsym, hcomp⟩ := comp_symm_mem_uniformity_sets hV
  refine ⟨fun x y => (y, x) ∈ V, fun x => ?_, fun x => ?_⟩
  · obtain ⟨i, hi⟩ := hball x (mem_univ x)
    exact ⟨i, fun y hy => hi hy⟩
  · have hn : SetRel.ball W x ∈ 𝓝 x := SetRel.ball_mem_nhds x hW
    refine ⟨interior (SetRel.ball W x), isOpen_interior, mem_interior_iff_mem_nhds.mpr hn, ?_⟩
    intro a ha b hb
    have h₁ : a ∈ SetRel.ball W x := interior_subset ha
    have h₂ : b ∈ SetRel.ball W x := interior_subset hb
    exact hcomp (SetRel.prodMk_mem_comp h₂ (SetRel.symm W h₁))

theorem cl_cancel {a b c d : T} (u : Cl a b) (v : Cl c d) {f g : Cl b c}
    (h : u.trans (f.trans v) = u.trans (g.trans v)) : f = g := by
  have key : ∀ k : Cl b c, u.symm.trans ((u.trans (k.trans v)).trans v.symm) = k := by
    intro k
    rw [← cl_assoc u.symm, cl_symm_trans_left, cl_assoc, cl_trans_symm, cl_trans_refl]
  rw [← key f, h, key g]

/-- **Induction along a path.** Each point of `γ` lies on an open set of the family, and `Q` passes
along
each piece of `γ` that lies in one set of the family. -/
theorem cl_induction {𝒞 : Set (Set T)} (h𝒞 : ∀ O ∈ 𝒞, IsOpen O) {a b : T} (γ : Path a b)
    (hcov : ∀ u, ∃ O ∈ 𝒞, γ u ∈ O) (Q : ∀ c : T, Cl a c → Prop) (h0 : Q a (Cl.rf a))
    (step : ∀ (c d : T) (f : Cl a c) (r : Path c d) (O : Set T), O ∈ 𝒞 → (∀ u, r u ∈ O) → Q c f →
      Q d (f.trans (Cl.mk r))) : Q b (Cl.mk γ) := by
  rcases γ with ⟨f, rfl, rfl⟩
  let γ : Path (f 0) (f 1) := ⟨f, rfl, rfl⟩
  have hcover : (univ : Set I) ⊆ ⋃ O : {O // O ∈ 𝒞}, (γ ⁻¹' O.1) := fun u _ => by
    obtain ⟨O, h₁, h₂⟩ := hcov u
    exact mem_iUnion.mpr ⟨⟨O, h₁⟩, h₂⟩
  obtain ⟨t, ht0, htmono, ⟨n₀, hn₀⟩, htO⟩ := exists_monotone_Icc_subset_open_cover_unitInterval
    (fun O : {O // O ∈ 𝒞} => (h𝒞 O.1 O.2).preimage γ.continuous) hcover
  have key : ∀ n, Q (γ (t n)) (Cl.mk (γ.subpath 0 (t n))) := by
    intro n
    induction n with
    | zero =>
      rw [ht0, Path.subpath_self]
      exact h0
    | succ n ih =>
      obtain ⟨O, hsub⟩ := htO n
      have hle : t n ≤ t (n + 1) := htmono (Nat.le_succ n)
      have hpiece : ∀ u, (γ.subpath (t n) (t (n + 1))) u ∈ O.1 := by
        intro u
        have : (γ.subpath (t n) (t (n + 1))) u ∈ γ '' uIcc (t n) (t (n + 1)) := by
          rw [← Path.range_subpath]
          exact mem_range_self u
        obtain ⟨v, hv, hv'⟩ := this
        rw [uIcc_of_le hle] at hv
        rw [← hv']
        exact hsub hv
      have h := step _ _ _ _ O.1 O.2 hpiece ih
      have e : (Cl.mk (γ.subpath 0 (t n))).trans (Cl.mk (γ.subpath (t n) (t (n + 1)))) =
          Cl.mk (γ.subpath 0 (t (n + 1))) := by
        rw [← Path.Homotopic.Quotient.mk_trans]
        exact Path.Homotopic.Quotient.eq.mpr (Path.Homotopic.subpath_trans_subpath _ _ _ _)
      rwa [e] at h
  have h := key n₀
  rw [hn₀ n₀ le_rfl, Path.subpath_zero_one] at h
  exact h

end GraphMinor.GM11
