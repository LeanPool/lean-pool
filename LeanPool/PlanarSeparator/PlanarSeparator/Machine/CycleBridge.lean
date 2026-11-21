/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.PlanarSeparator.Machine.Walk
public import LeanPool.PlanarSeparator.PlanarSeparator.Machine.Cotree

/-!
# The fundamental cycle search on the machine: the bridge to plane maps

A plane map `M` all of whose faces are triangles, with a spanning tree `T`, is *coded* for the
programs of `PlanarSeparator/Machine/Search.lean`, `Pass.lean`, `Walk.lean` by a numbering
`cd : D ≃ Fin (3k)` of its darts in which the face permutation is `phi3` (`Coded`): the darts of
a face get three consecutive numbers, the face of a dart `x` has index `cd x / 3`
(`face_eq_iff`), and the arrays `A` (reversal) and `Tm` (tree marks) are read through `cd`.

This file proves that the arrays of a coded map satisfy the assumptions of the programs
(`Coded.tri`), and identifies the numeric inside weights with the weights of the insides of
fundamental cycles.
-/

@[expose] public section

namespace PlanarSeparator

namespace CycleSearch

open Finset Map Map.SpTree WordRAM

variable {D P : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P] {M : Map D P}
  {T : M.SpTree} {k : ℕ}

/-- A coding of the darts in which the face permutation is `phi3`, with the reversal `A` and the
tree marks `Tm`. -/
structure Coded (M : Map D P) (T : M.SpTree) (k : ℕ) (cd : D ≃ Fin (3 * k)) (A Tm : ℕ → ℕ) :
    Prop where
  A_cd : ∀ x, A (cd x) = cd (M.α x)
  φ_cd : ∀ x, (cd (M.φ x) : ℕ) = phi3 (cd x)
  T_cd : ∀ x, Tm (cd x) = 0 ↔ ¬ T.IsTree x
  T_le : ∀ x, Tm (cd x) ≤ 1

theorem phi3_div (y : ℕ) : phi3 y / 3 = y / 3 := by unfold phi3; split_ifs <;> omega

/-- The three darts of a face, starting from any of them. -/
theorem three_sum (g : ℕ → ℕ) {p F : ℕ} (hp : p / 3 = F) (h0 : g p = 0) :
    g (3 * F) + g (3 * F + 1) + g (3 * F + 2) = g (phi3 p) + g (phi3 (phi3 p)) := by
  have : p = 3 * F ∨ p = 3 * F + 1 ∨ p = 3 * F + 2 := by omega
  rcases this with rfl | rfl | rfl
  · rw [show phi3 (3 * F) = 3 * F + 1 by unfold phi3; split_ifs <;> omega,
      show phi3 (3 * F + 1) = 3 * F + 2 by unfold phi3; split_ifs <;> omega, h0]; omega
  · rw [show phi3 (3 * F + 1) = 3 * F + 2 by unfold phi3; split_ifs <;> omega,
      show phi3 (3 * F + 2) = 3 * F by unfold phi3; split_ifs <;> omega, h0]; omega
  · rw [show phi3 (3 * F + 2) = 3 * F by unfold phi3; split_ifs <;> omega,
      show phi3 (3 * F) = 3 * F + 1 by unfold phi3; split_ifs <;> omega, h0]; omega

variable {cd : D ≃ Fin (3 * k)} {A Tm : ℕ → ℕ}

/-- The index of a face. -/
noncomputable def fi (cd : D ≃ Fin (3 * k)) (F : M.Face) : ℕ :=
  (cd (M.face_surjective F).choose : ℕ) / 3

namespace Coded

variable (hC : Coded M T k cd A Tm)
include hC

omit [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P] in
theorem tri : Tri k A Tm where
  A_lt x hx := by
    have := hC.A_cd (cd.symm ⟨x, hx⟩); simp only [Equiv.apply_symm_apply] at this
    rw [this]; exact (cd _).2
  A_A x hx := by
    have h1 := hC.A_cd (cd.symm ⟨x, hx⟩); simp only [Equiv.apply_symm_apply] at h1
    rw [h1, hC.A_cd, M.α_α, Equiv.apply_symm_apply]
  T_le x hx := by have := hC.T_le (cd.symm ⟨x, hx⟩); simpa using this
  T_A x hx := by
    have h1 := hC.A_cd (cd.symm ⟨x, hx⟩); simp only [Equiv.apply_symm_apply] at h1
    rw [h1]
    have e1 := hC.T_cd (M.α (cd.symm ⟨x, hx⟩))
    have e2 := hC.T_cd (cd.symm ⟨x, hx⟩)
    have l1 := hC.T_le (M.α (cd.symm ⟨x, hx⟩))
    have l2 := hC.T_le (cd.symm ⟨x, hx⟩)
    simp only [Equiv.apply_symm_apply] at e2 l2
    rw [T.isTree_α] at e1
    by_cases ht : T.IsTree (cd.symm ⟨x, hx⟩)
    · have a1 : Tm (cd (M.α (cd.symm ⟨x, hx⟩))) ≠ 0 := fun h => (e1.1 h) ht
      have a2 : Tm x ≠ 0 := fun h => (e2.1 h) ht
      omega
    · rw [e1.2 ht, e2.2 ht]

omit [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P] in
theorem cd_φ_pow (x : D) (n : ℕ) : (cd ((M.φ ^ n) x) : ℕ) / 3 = (cd x : ℕ) / 3 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, hC.φ_cd, phi3_div, ih]

omit [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P] in
/-- The face of a dart is the triple of its number. -/
theorem face_eq_iff {x y : D} : M.face x = M.face y ↔ (cd x : ℕ) / 3 = (cd y : ℕ) / 3 := by
  let : Fintype D := Fintype.ofEquiv (Fin (3 * k)) cd.symm
  constructor
  · intro h
    obtain ⟨n, hn⟩ := (M.face_eq_face_iff.1 h).exists_nat_pow_eq
    rw [← hn, hC.cd_φ_pow]
  · intro h
    have h1 := hC.φ_cd x
    have h2 := hC.φ_cd (M.φ x)
    rw [h1] at h2
    have hy : cd y = cd x ∨ cd y = cd (M.φ x) ∨ cd y = cd (M.φ (M.φ x)) := by
      simp only [Fin.ext_iff, h1, h2]
      unfold phi3 at *
      split_ifs at * <;> omega
    rcases hy with e | e | e <;> rw [cd.injective e]
    · exact (M.face_φ x).symm
    · rw [M.face_φ, M.face_φ]

omit [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P] in
theorem φ_ne (x : D) : M.φ x ≠ x := fun h => by
  have := hC.φ_cd x; rw [h] at this; unfold phi3 at this; split_ifs at this <;> omega

omit [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P] in
theorem fi_face (x : D) : fi cd (M.face x) = (cd x : ℕ) / 3 :=
  hC.face_eq_iff.1 (M.face_surjective (M.face x)).choose_spec

omit [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P] in
theorem fi_lt (F : M.Face) : fi cd F < k := by
  obtain ⟨x, rfl⟩ := M.face_surjective F
  rw [hC.fi_face]; have := (cd x).2; omega

omit [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P] in
theorem fi_inj {F G : M.Face} (h : fi cd F = fi cd G) : F = G := by
  obtain ⟨x, rfl⟩ := M.face_surjective F
  obtain ⟨y, rfl⟩ := M.face_surjective G
  rw [hC.fi_face, hC.fi_face] at h
  exact hC.face_eq_iff.2 h

omit [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P] in
theorem exists_fi {f : ℕ} (hf : f < k) : ∃ F : M.Face, fi cd F = f :=
  ⟨M.face (cd.symm ⟨3 * f, by omega⟩), by rw [hC.fi_face]; simp⟩

/-! ### The search reaches every face -/

variable {Fw : ℕ → ℕ} {W : ℕ} {o : List ℕ} {c₀ : Config}

omit [DecidableEq P] in
theorem search_all (hM : M.IsPlane) (hk : 0 < k) (hI : IS k A Tm Fw W o c₀)
    (hend : c₀.nreg 12 = c₀.nreg 11) : c₀.nreg 11 = k := by
  classical
  set Z : Finset M.Face := univ.filter fun F => ∃ i < c₀.nreg 11, qu k c₀.nmem i = fi cd F
  have hZ : Z = univ := by
    refine T.eq_univ_of_closed hM Z ?_ ?_
    · obtain ⟨F, hF⟩ := hC.exists_fi hk
      exact ⟨F, mem_filter.2 ⟨mem_univ _, 0, hI.q0.1, by rw [hI.q0.2, hF]⟩⟩
    · intro d hd hdZ
      obtain ⟨i, hi, hq⟩ := (mem_filter.1 hdZ).2
      rw [hC.fi_face] at hq
      have hsc := hI.closed i (by omega) ((cd d : ℕ) % 3) (Nat.mod_lt _ (by omega))
      have hcd : 3 * qu k c₀.nmem i + (cd d : ℕ) % 3 = cd d := by omega
      rw [hcd] at hsc
      have hT0 : Tm (cd d) = 0 := (hC.T_cd d).2 hd
      have hm := hsc hT0
      rw [hC.A_cd] at hm
      have hlt : (cd (M.α d) : ℕ) / 3 < k := by have := (cd (M.α d)).2; omega
      obtain ⟨i', hi', hq'⟩ := (hI.mk_iff _ hlt).1 hm
      exact mem_filter.2 ⟨mem_univ _, i', hi', by rw [hq', hC.fi_face]⟩
  refine le_antisymm hI.tail_le ?_
  have hsurj : ∀ f < k, ∃ i < c₀.nreg 11, qu k c₀.nmem i = f := by
    intro f hf
    obtain ⟨F, rfl⟩ := hC.exists_fi hf
    have : F ∈ Z := by rw [hZ]; exact mem_univ _
    exact (mem_filter.1 this).2
  have h := Finset.card_le_card_of_surjOn (qu k c₀.nmem) (s := range (c₀.nreg 11)) (t := range k)
    (fun f hf => by
      obtain ⟨i, hi, e⟩ := hsurj f (by simpa using hf)
      exact ⟨i, by simpa using hi, e⟩)
  simpa using h

/-! ### The search as a search of the dual tree -/

/-- The dart with number `x` (for `x < 3k`). -/
noncomputable def dartN (hk : 0 < k) (x : ℕ) : D :=
  if h : x < 3 * k then cd.symm ⟨x, h⟩ else cd.symm ⟨0, by omega⟩

omit [Fintype D] [DecidableEq D] hC in
theorem cd_dartN (hk : 0 < k) {x : ℕ} (hx : x < 3 * k) : (cd (dartN (cd := cd) hk x) : ℕ) = x := by
  simp [dartN, hx]

omit [Fintype D] [DecidableEq D] hC in
theorem dartN_cd (hk : 0 < k) (x : D) : dartN (cd := cd) hk (cd x) = x := by
  simp [dartN, (cd x).2]

variable (hk : 0 < k) (hS : SB k A Tm Fw W o c₀) (hall : c₀.nreg 11 = k)
include hk hS hall

omit [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P] hk in
/-- The position of a face in the search. -/
theorem exists_ord (F : M.Face) : ∃ i, i < k ∧ qu k c₀.nmem i = fi cd F := by
  obtain ⟨i, hi, e⟩ := hS.exists_pos hall (hC.fi_lt F); exact ⟨i, hi, e⟩

omit [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P] in
/-- The search of the machine is a search of the dual tree. -/
theorem isSearch : T.IsSearch (M.face (dartN (cd := cd) hk 0))
    (fun F => Nat.find (hC.exists_ord hS hall F))
    (fun F => dartN (cd := cd) hk (pd k c₀.nmem (fi cd F))) := by
  classical
  have hF0 : ∀ F : M.Face,
      F ≠ M.face (dartN (cd := cd) hk 0) → 1 ≤ Nat.find (hC.exists_ord hS hall F) := by
    intro F hF
    by_contra h
    have h0 : Nat.find (hC.exists_ord hS hall F) = 0 := by omega
    have := (Nat.find_spec (hC.exists_ord hS hall F)).2
    rw [h0, hS.q0.2] at this
    apply hF; apply hC.fi_inj; rw [← this, hC.fi_face, cd_dartN hk (by omega)]
  have spec : ∀ F : M.Face, F ≠ M.face (dartN (cd := cd) hk 0) →
      pd k c₀.nmem (fi cd F) / 3 = fi cd F ∧ pd k c₀.nmem (fi cd F) < 3 * k ∧
      Tm (pd k c₀.nmem (fi cd F)) = 0 ∧ ∃ i' < Nat.find (hC.exists_ord hS hall F),
        qu k c₀.nmem i' = A (pd k c₀.nmem (fi cd F)) / 3 := by
    intro F hF
    have h1 := hF0 F hF
    obtain ⟨hi, hq⟩ := Nat.find_spec (hC.exists_ord hS hall F)
    have := hS.pd_ok _ h1 (by omega)
    rw [hq] at this
    exact this
  refine ⟨fun F hF => ?_, fun F hF => ?_, fun F hF => ?_⟩
  · obtain ⟨a, b, -, -⟩ := spec F hF
    apply hC.fi_inj; rw [hC.fi_face, cd_dartN hk b, a]
  · obtain ⟨-, b, e, -⟩ := spec F hF
    rw [← hC.T_cd, cd_dartN hk b]; exact e
  · obtain ⟨-, b, -, i', hi', hq'⟩ := spec F hF
    refine lt_of_le_of_lt (Nat.find_min' _ ⟨by
      have := (Nat.find_spec (hC.exists_ord hS hall F)).1; omega, ?_⟩) hi'
    rw [hq', hC.fi_face, ← hC.A_cd, cd_dartN hk b]

omit [DecidableEq P] in
/-- **Every dart off the tree is a dart of the search**, numerically. -/
theorem pdor (hM : M.IsPlane) : ∀ y < 3 * k, Tm y = 0 →
    (y / 3 ≠ 0 ∧ pd k c₀.nmem (y / 3) = y) ∨ (A y / 3 ≠ 0 ∧ pd k c₀.nmem (A y / 3) = A y) := by
  classical
  intro y hy hT
  set x : D := dartN (cd := cd) hk y
  have hx : (cd x : ℕ) = y := cd_dartN hk hy
  have hnt : ¬ T.IsTree x := (hC.T_cd x).1 (by rw [hx]; exact hT)
  have hF0 : ∀ F : M.Face, F ≠ M.face (dartN (cd := cd) hk 0) ↔ fi cd F ≠ 0 := by
    intro F
    rw [not_iff_not]
    constructor
    · rintro rfl; rw [hC.fi_face, cd_dartN hk (by omega)]
    · intro h; apply hC.fi_inj; rw [h, hC.fi_face, cd_dartN hk (by omega)]
  have hpdlt : ∀ F : M.Face, fi cd F ≠ 0 → pd k c₀.nmem (fi cd F) < 3 * k := by
    intro F hF
    have h1 : 1 ≤ Nat.find (hC.exists_ord hS hall F) := by
      by_contra h
      have h0 : Nat.find (hC.exists_ord hS hall F) = 0 := by omega
      have := (Nat.find_spec (hC.exists_ord hS hall F)).2
      rw [h0, hS.q0.2] at this; exact hF this.symm
    obtain ⟨hi, hq⟩ := Nat.find_spec (hC.exists_ord hS hall F)
    have := (hS.pd_ok _ h1 (by omega)).2.1
    rwa [hq] at this
  rcases (hC.isSearch hk hS hall).pd_or hM hnt with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    rw [hF0, hC.fi_face, hx] at h1
    refine ⟨h1, ?_⟩
    have hlt := hpdlt (M.face x) (by rw [hC.fi_face, hx]; exact h1)
    rw [hC.fi_face, hx] at hlt
    have := congrArg (fun z => (cd z : ℕ)) h2
    simp only [hC.fi_face, hx] at this
    rwa [cd_dartN hk hlt] at this
  · right
    have hA : (cd (M.α x) : ℕ) = A y := by rw [← hC.A_cd, hx]
    rw [hF0, hC.fi_face, hA] at h1
    refine ⟨h1, ?_⟩
    have hlt := hpdlt (M.face (M.α x)) (by rw [hC.fi_face, hA]; exact h1)
    rw [hC.fi_face, hA] at hlt
    have := congrArg (fun z => (cd z : ℕ)) h2
    simp only [hC.fi_face, hA] at this
    rwa [cd_dartN hk hlt] at this

omit [DecidableEq P] in
theorem childOk (hM : M.IsPlane) : ChildOk k A Tm (pd k c₀.nmem) := by
  classical
  intro F hF hF0 j hj hne hT
  rcases hC.pdor hk hS hall hM (3 * F + j) (by omega) hT with ⟨-, h⟩ | h
  · exact absurd (by rw [show (3 * F + j) / 3 = F by omega] at h; exact h.symm) hne
  · exact h

omit [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P] hS hall in
theorem dartN_A {x : ℕ} (hx : x < 3 * k) :
    dartN (cd := cd) hk (A x) = M.α (dartN (cd := cd) hk x) := by
  apply cd.injective; apply Fin.ext
  rw [cd_dartN hk (hC.tri.A_lt x hx), ← hC.A_cd, cd_dartN hk hx]

omit [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P] hS hall in
theorem dartN_phi3 {x : ℕ} (hx : x < 3 * k) :
    dartN (cd := cd) hk (phi3 x) = M.φ (dartN (cd := cd) hk x) := by
  apply cd.injective; apply Fin.ext
  rw [cd_dartN hk (phi3_lt hx), hC.φ_cd, cd_dartN hk hx]

/-! ### The inside weights -/

variable (fw : M.Face → ℕ)

/-- The weight of the inside of a dart. -/
noncomputable def Iw (x : D) : ℕ := ∑ G ∈ T.inside x, fw G

/-- The inside weight of the dart `pd f` of face `f`. -/
noncomputable def Ival (f : ℕ) : ℕ := Iw (T := T) fw (dartN (cd := cd) hk (pd k c₀.nmem f))

omit [Fintype P] [DecidableEq P] hk hS hall in
theorem card_face : Fintype.card M.Face = k := by
  classical
  rw [← card_univ, ← card_range k]
  refine card_bij (fun G _ => fi cd G) (fun G _ => mem_range.2 (hC.fi_lt G))
    (fun G _ G' _ h => hC.fi_inj h) (fun f hf => ?_)
  obtain ⟨G, hG⟩ := hC.exists_fi (mem_range.1 hf)
  exact ⟨G, mem_univ _, hG⟩

omit [Fintype P] [DecidableEq P] hk hS hall in
theorem sum_fw (hFw : ∀ x, Fw ((cd x : ℕ) / 3) = fw (M.face x)) :
    ∑ G, fw G = ∑ f ∈ range k, Fw f := by
  classical
  refine sum_bij (fun G _ => fi cd G) (fun G _ => mem_range.2 (hC.fi_lt G))
    (fun G _ G' _ h => hC.fi_inj h) (fun f hf => ?_) (fun G _ => ?_)
  · obtain ⟨G, hG⟩ := hC.exists_fi (mem_range.1 hf)
    exact ⟨G, mem_univ _, hG⟩
  · obtain ⟨x, rfl⟩ := M.face_surjective G
    rw [hC.fi_face, hFw]

/-- A dart other than `pd F` of a face `F ≠ 0` contributes the inside weight of its reverse. -/
theorem childVal_eq (hM : M.IsPlane) {F x : ℕ} (hx : x < 3 * k) (hxF : x / 3 = F)
    (hne : x ≠ pd k c₀.nmem F) :
    childVal A Tm (Ival (T := T) (cd := cd) (c₀ := c₀) hk fw) (pd k c₀.nmem F) x =
      Iw (T := T) fw (M.α (dartN (cd := cd) hk x)) := by
  unfold childVal
  by_cases hT : Tm x = 0
  · rw [ite_eq_left ⟨hne, hT⟩]
    rcases hC.pdor hk hS hall hM x hx hT with ⟨-, h⟩ | ⟨-, h⟩
    · exact absurd (by rw [hxF] at h; exact h.symm) hne
    · unfold Ival; rw [h, hC.dartN_A hk hx]
  · rw [ite_eq_right (fun h => hT h.2)]
    have ht : T.IsTree (dartN (cd := cd) hk x) := by
      by_contra h; exact hT (by rw [← cd_dartN (cd := cd) hk hx]; exact (hC.T_cd _).2 h)
    unfold Iw
    rw [sum_inside_of_isTree T hM ((T.isTree_α).2 ht)]

omit [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P] hC hk in
theorem pd_spec {f : ℕ} (hf : f < k) (hf0 : f ≠ 0) :
    pd k c₀.nmem f / 3 = f ∧ pd k c₀.nmem f < 3 * k ∧ Tm (pd k c₀.nmem f) = 0 := by
  obtain ⟨i, hi, hq⟩ := hS.exists_pos hall hf
  have hi1 : 1 ≤ i := by
    by_contra h; obtain rfl : i = 0 := by omega
    rw [hS.q0.2] at hq; exact hf0 hq.symm
  have := hS.pd_ok i hi1 (by omega)
  rw [hq] at this
  exact ⟨this.1, this.2.1, this.2.2.1⟩

theorem recHolds (hM : M.IsPlane) (hT3 : ∀ δ, M.IsTriangle δ)
    (hFw : ∀ x, Fw ((cd x : ℕ) / 3) = fw (M.face x)) :
    RecHolds k A Tm Fw (pd k c₀.nmem) (Ival (T := T) (cd := cd) (c₀ := c₀) hk fw) := by
  intro F hF hF0
  obtain ⟨hpF, hlt, hT0⟩ := pd_spec hS hall hF hF0
  set pD := dartN (cd := cd) hk (pd k c₀.nmem F)
  have e0 : (cd pD : ℕ) = pd k c₀.nmem F := cd_dartN hk hlt
  have hnt : ¬ T.IsTree pD := (hC.T_cd pD).1 (by rw [e0]; exact hT0)
  have hrec := sum_inside_eq (T := T) hM (hT3 pD) hnt fw
  rw [← hC.dartN_phi3 hk hlt, ← hC.dartN_phi3 hk (phi3_lt hlt)] at hrec
  have hφ1 : phi3 (pd k c₀.nmem F) ≠ pd k c₀.nmem F := by unfold phi3; split_ifs <;> omega
  have hφ2 : phi3 (phi3 (pd k c₀.nmem F)) ≠ pd k c₀.nmem F := by unfold phi3; split_ifs <;> omega
  have c1 := hC.childVal_eq hk hS hall fw hM (F := F) (phi3_lt hlt) (by rw [phi3_div, hpF]) hφ1
  have c2 := hC.childVal_eq hk hS hall fw hM (F := F) (phi3_lt (phi3_lt hlt))
    (by rw [phi3_div, phi3_div, hpF]) hφ2
  have c0 : childVal A Tm (Ival (T := T) (cd := cd) (c₀ := c₀) hk fw) (pd k c₀.nmem F)
      (pd k c₀.nmem F) = 0 := by simp [childVal]
  have hfw : fw (M.face pD) = Fw F := by rw [← hFw, e0, hpF]
  have hI : Ival (T := T) (cd := cd) (c₀ := c₀) hk fw F = Iw (T := T) fw pD := rfl
  rw [hI]
  unfold Iw
  rw [hrec, hfw]
  unfold Iw at c1 c2
  rw [← c1, ← c2]
  have h3 := three_sum (childVal A Tm (Ival (T := T) (cd := cd) (c₀ := c₀) hk fw) (pd k c₀.nmem F))
    hpF c0
  omega

/-! ### The walk's assumptions -/

variable {J : ℕ → ℕ}

theorem Inum_eq (hM : M.IsPlane)
    (hJ : ∀ f < k, f ≠ 0 → J f = Ival (T := T) (cd := cd) (c₀ := c₀) hk fw f)
    {y : ℕ} (hy : y < 3 * k) (hT : Tm y = 0) :
    Inum A (pd k c₀.nmem) J (∑ G, fw G) y = Iw (T := T) fw (dartN (cd := cd) hk y) := by
  unfold Inum
  have hnt : ¬ T.IsTree (dartN (cd := cd) hk y) :=
      (hC.T_cd _).1 (by rw [cd_dartN hk hy]; exact hT)
  split_ifs with h
  · rw [hJ _ (by omega) h.1]; unfold Ival; rw [h.2]
  · rcases hC.pdor hk hS hall hM y hy hT with h' | ⟨h1, h2⟩
    · exact absurd h' h
    · have hA := hC.tri.A_lt y hy
      rw [hJ _ (by omega) h1]
      unfold Ival; rw [h2, hC.dartN_A hk hy]
      have := sum_inside_α (T := T) hM hnt fw
      unfold Iw; omega

theorem cvn_eq (hM : M.IsPlane)
    (hJ : ∀ f < k, f ≠ 0 → J f = Ival (T := T) (cd := cd) (c₀ := c₀) hk fw f)
    {z : ℕ} (hz : z < 3 * k) :
    cvn A Tm (pd k c₀.nmem) J (∑ G, fw G) z = Iw (T := T) fw (dartN (cd := cd) hk z) := by
  unfold cvn
  split_ifs with hT
  · exact hC.Inum_eq hk hS hall fw hM hJ hz hT
  · have ht : T.IsTree (dartN (cd := cd) hk z) := by
      by_contra h; exact hT (by rw [← cd_dartN (cd := cd) hk hz]; exact (hC.T_cd _).2 h)
    unfold Iw; rw [sum_inside_of_isTree T hM ht]

omit [Fintype P] hC hk hS hall in
theorem Iw_le (x : D) : Iw (T := T) fw x ≤ ∑ G, fw G :=
  sum_le_sum_of_subset (subset_univ _)

theorem wa (hM : M.IsPlane)
    (hJ : ∀ f < k, f ≠ 0 → J f = Ival (T := T) (cd := cd) (c₀ := c₀) hk fw f) :
    WA k A Tm (pd k c₀.nmem) J (∑ G, fw G) where
  tri := hC.tri
  pdor := hC.pdor hk hS hall hM
  J_le f hf hf0 := by rw [hJ f hf hf0]; exact Iw_le (T := T) fw _

theorem wh (hM : M.IsPlane) (hT3 : ∀ δ, M.IsTriangle δ)
    (hFw : ∀ x, Fw ((cd x : ℕ) / 3) = fw (M.face x))
    (hJ : ∀ f < k, f ≠ 0 → J f = Ival (T := T) (cd := cd) (c₀ := c₀) hk fw f) :
    WH k A Tm Fw (pd k c₀.nmem) J (∑ G, fw G)
      (fun y => #(T.inside (dartN (cd := cd) hk y))) where
  recI y hy hT := by
    have hnt : ¬ T.IsTree (dartN (cd := cd) hk y) :=
      (hC.T_cd _).1 (by rw [cd_dartN hk hy]; exact hT)
    have hφ := phi3_lt hy
    have hφφ := phi3_lt hφ
    rw [hC.Inum_eq hk hS hall fw hM hJ hy hT, hC.cvn_eq hk hS hall fw hM hJ (hC.tri.A_lt _ hφ),
      hC.cvn_eq hk hS hall fw hM hJ (hC.tri.A_lt _ hφφ), hC.dartN_A hk hφ, hC.dartN_A hk hφφ,
      hC.dartN_phi3 hk hφ, hC.dartN_phi3 hk hy]
    unfold Iw
    rw [sum_inside_eq hM (hT3 _) hnt fw, ← hFw, cd_dartN hk hy]
  dec₁ y hy hT _ := by
    have hnt : ¬ T.IsTree (dartN (cd := cd) hk y) :=
      (hC.T_cd _).1 (by rw [cd_dartN hk hy]; exact hT)
    rw [hC.dartN_A hk (phi3_lt hy), hC.dartN_phi3 hk hy]
    exact card_inside_lt₁ hM (hT3 _) hnt
  dec₂ y hy hT _ := by
    have hnt : ¬ T.IsTree (dartN (cd := cd) hk y) :=
      (hC.T_cd _).1 (by rw [cd_dartN hk hy]; exact hT)
    rw [hC.dartN_A hk (phi3_lt (phi3_lt hy)), hC.dartN_phi3 hk (phi3_lt hy), hC.dartN_phi3 hk hy]
    exact card_inside_lt₂ hM (hT3 _) hnt
  comp y hy hT := by
    have hnt : ¬ T.IsTree (dartN (cd := cd) hk y) :=
      (hC.T_cd _).1 (by rw [cd_dartN hk hy]; exact hT)
    have hA := hC.tri.A_lt y hy
    rw [hC.Inum_eq hk hS hall fw hM hJ hA (by rw [hC.tri.T_A y hy]; exact hT),
      hC.Inum_eq hk hS hall fw hM hJ hy hT, hC.dartN_A hk hy]
    exact sum_inside_α T hM hnt fw
  sz_le y _ := (card_le_univ _).trans hC.card_face.le

end Coded

end CycleSearch

end PlanarSeparator

namespace PlanarSeparator

namespace CycleSearch

open Finset Map Map.SpTree WordRAM WordRAM.Machine Coded

/-- **The fundamental cycle search**: the search of the dual tree, the pass, the total and the
walk. -/
def cycleSep : Machine.Stmt := .seq search (.seq pass (.seq totW walk))

variable {D P : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P] {M : Map D P}
  {T : M.SpTree} {k : ℕ} {cd : D ≃ Fin (3 * k)} {A Tm : ℕ → ℕ}

/-- The outcome of the cycle search, for face weights `fw` of total `tot`: either (mode `0`) a dart
`a` off the tree whose two sides weigh at most `2/3` each, or (mode `1`) a dart `δ` off the tree
and a dart `a ∈ {α (φ δ), α (φ² δ)}` such that the inside of `a` weighs at most `2/3`, and the
outside of `a` without the face of `δ` weighs at most `2/3`. -/
def CycleOut (M : Map D P) (T : M.SpTree) (fw : M.Face → ℕ) (cd : D ≃ Fin (3 * k))
    (mode δn an : ℕ) : Prop :=
  (mode = 0 ∧ ∃ a, (cd a : ℕ) = an ∧ ¬ T.IsTree a ∧
      3 * ∑ G ∈ T.inside a, fw G ≤ 2 * ∑ G, fw G ∧
      3 * ∑ G ∈ T.inside (M.α a), fw G ≤ 2 * ∑ G, fw G) ∨
    (mode = 1 ∧ ∃ δ a, (cd δ : ℕ) = δn ∧ (cd a : ℕ) = an ∧ ¬ T.IsTree δ ∧
      (a = M.α (M.φ δ) ∨ a = M.α (M.φ (M.φ δ))) ∧ 3 * ∑ G ∈ T.inside a, fw G ≤ 2 * ∑ G, fw G ∧
      3 * (∑ G, fw G - ∑ G ∈ T.inside a, fw G - fw (M.face δ)) ≤ 2 * ∑ G, fw G)

/-- **The separation given by the cycle search.** Let the face weights be carried by vertex
weights `w` through darts `first v` at the vertices (`fwt`). If the outcome of the cycle search
is `CycleOut`, then the vertices split into `S`, `A`, `B`, with `S` the two root paths of a dart
`a` together with at most three more vertices (the corners of the last triangle of the walk), no
edge between `A` and `B`, and `A`, `B` of weight at most `2/3` of the total. -/
theorem CycleOut.separation (hM : M.IsPlane) (hT3 : ∀ δ, M.IsTriangle δ) {first : P → D}
    (hfirst : ∀ v, M.vert (first v) = v) (w : P → ℕ) {mode δn an : ℕ}
    (h : CycleOut M T (fwt M first w) cd mode δn an) :
    ∃ (a : D) (X S A B : Finset P), (cd a : ℕ) = an ∧ #X ≤ 3 ∧ S = T.sep a ∪ X ∧
      S ∪ A ∪ B = univ ∧ Disjoint S A ∧ Disjoint S B ∧ Disjoint A B ∧
      (∀ d, M.vert d ∈ A → M.vert (M.α d) ∉ B) ∧
      3 * ∑ v ∈ A, w v ≤ 2 * ∑ v, w v ∧ 3 * ∑ v ∈ B, w v ≤ 2 * ∑ v, w v := by
  classical
  have htot := sum_fwt_univ (M := M) first w
  have hsep : ∀ (a : D) (X : Finset P), (T.sep a ∪ X) ∪ (T.inV a \ X) ∪ (T.outV a \ X) = univ ∧
      Disjoint (T.sep a ∪ X) (T.inV a \ X) ∧ Disjoint (T.sep a ∪ X) (T.outV a \ X) ∧
      Disjoint (T.inV a \ X) (T.outV a \ X) ∧
      (∀ d, M.vert d ∈ T.inV a \ X → M.vert (M.α d) ∉ T.outV a \ X) := by
    intro a X
    refine ⟨?_, ?_, ?_, ?_, fun d hd hd' => ?_⟩
    · ext v
      simp only [mem_union, mem_sdiff, mem_univ, iff_true, outV, mem_filter, true_and]
      tauto
    · rw [disjoint_left]; intro v h1 h2
      obtain ⟨h2, h3⟩ := mem_sdiff.1 h2
      rcases mem_union.1 h1 with h | h
      · exact notMem_sep_of_mem_inV h2 h
      · exact h3 h
    · rw [disjoint_left]; intro v h1 h2
      obtain ⟨h2, h3⟩ := mem_sdiff.1 h2
      rcases mem_union.1 h1 with h | h
      · exact (mem_filter.1 h2).2.1 h
      · exact h3 h
    · rw [disjoint_left]; intro v h1 h2
      exact (mem_filter.1 (mem_sdiff.1 h2).1).2.2 (mem_sdiff.1 h1).1
    · exact vert_α_ne_of_mem_inV hM (mem_sdiff.1 hd).1 (mem_sdiff.1 hd').1 rfl rfl
  rcases h with ⟨-, a, ha, hnt, h1, h2⟩ | ⟨-, δ, a, -, ha, hnt, hda, h1, h2⟩
  · obtain ⟨u, s1, s2, s3, s4⟩ := hsep a ∅
    refine ⟨a, ∅, _, _, _, ha, by simp, rfl, u, s1, s2, s3, s4, ?_, ?_⟩
    · have := sum_inV_le (T := T) w hM hfirst a
      simp only [sdiff_empty] at this ⊢
      omega
    · have := sum_inV_le (T := T) w hM hfirst (M.α a)
      rw [inV_α hM hnt] at this
      simp only [sdiff_empty] at this ⊢
      omega
  · set X : Finset P := {M.vert δ, M.vert (M.φ δ), M.vert (M.φ (M.φ δ))}
    obtain ⟨u, s1, s2, s3, s4⟩ := hsep a X
    have hX : #X ≤ 3 := card_le_three
    refine ⟨a, X, _, _, _, ha, hX, rfl, u, s1, s2, s3, s4, ?_, ?_⟩
    · have := sum_inV_le (T := T) w hM hfirst a
      have := sum_le_sum_of_subset (f := w) (sdiff_subset (s := T.inV a) (t := X))
      omega
    · have hout : M.face δ ∉ T.inside a := by
        rcases hda with rfl | rfl
        · intro hm
          have := inside_α_subset hM hnt (M.face_φ δ) (hT3 δ).edge_ne₁ hm
          simp at this
        · intro hm
          have := inside_α_subset hM hnt ((M.face_φ _).trans (M.face_φ δ)) (hT3 δ).edge_ne₂ hm
          simp at this
      have hle := sum_outV_le (T := T) w hM hfirst a (hT3 δ).φ_three hout
      have heq : (T.outV a \ X) = (T.outV a).filter fun v => v ≠ M.vert δ ∧
          v ≠ M.vert (M.φ δ) ∧ v ≠ M.vert (M.φ (M.φ δ)) := by
        ext v; simp only [X, mem_sdiff, mem_filter, mem_insert, mem_singleton, not_or, ne_eq]
      rw [heq]
      omega

end CycleSearch

end PlanarSeparator
