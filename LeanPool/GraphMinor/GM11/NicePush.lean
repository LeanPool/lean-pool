/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.LocalCone

/-!
# (3.1) of Graph Minors XI for closed nice sets

Let `X, Y` be closed and nice, with `X` simply-connected and `X ∩ Y` arc-wise connected. We show
that a curve
in `X ∪ Y` can be pushed into `Y`, which is (3.1) in the case that (7.8) and (8.8) need.

The paper's proof of (3.1) cuts the curve at the points where it meets `Y`, and each piece between
two such
points lies in `X`. That fails for a general curve, which may meet `Y` in a Cantor set, and (3.1) is
false for general closed sets (see the correction to (3.1) in `corrections/GM11.md`). For nice sets
the cones of `isLocalCone` make the step work. A
path is cut into short pieces, each in one cone, and each piece is homotopic to a path through the
apex. So
the path is homotopic to a finite product of paths, each of them in `X` or in `Y`, and now the
paper's step
applies: a stretch in `X` with ends in `X ∩ Y` is homotopic in `X` to a path in `X ∩ Y`.

The induction is on the number of pieces. `IsPushed` is the state after some pieces, and
`IsPushed.step` adds
one more path.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] {X Y : Set S}

private theorem trans_mem {A : Set S} {Z : Set S} {a b c : Z} {p : Path a b} {q : Path b c}
    (hp : ∀ u, (p u).1 ∈ A) (hq : ∀ u, (q u).1 ∈ A) (u : I) : ((p.trans q) u).1 ∈ A := by
  have : (p.trans q) u ∈ range p ∪ range q := by
    rw [← Path.trans_range]
    exact mem_range_self u
  rcases this with ⟨v, hv⟩ | ⟨v, hv⟩
  · rw [← hv]
    exact hp v
  · rw [← hv]
    exact hq v

/-- The state of the induction for a path `ω` from `a` to `c`: it is homotopic to a path in `Y`, or
to a path
in `Y` followed by a path in `X`. -/
private def IsPushed (X Y : Set S) {a c : (X ∪ Y : Set S)} (ω : Path a c) : Prop :=
  (∃ q : Path a c, ω.Homotopic q ∧ ∀ u, (q u).1 ∈ Y) ∨
    ∃ (e : (X ∪ Y : Set S)) (q : Path a e) (r : Path e c), ω.Homotopic (q.trans r) ∧
      (∀ u, (q u).1 ∈ Y) ∧ ∀ u, (r u).1 ∈ X

private theorem IsPushed.congr {a c : (X ∪ Y : Set S)} {ω ω' : Path a c} (h : IsPushed X Y ω)
    (hh : ω'.Homotopic ω) : IsPushed X Y ω' := by
  rcases h with ⟨q, h₁, h₂⟩ | ⟨e, q, r, h₁, h₂⟩
  · exact Or.inl ⟨q, hh.trans h₁, h₂⟩
  · exact Or.inr ⟨e, q, r, hh.trans h₁, h₂⟩

/-- A path in `X` with ends in `X ∩ Y` is homotopic in `X ∪ Y` to a path in `X ∩ Y`. This is the
step of the
paper's proof of (3.1). -/
private theorem flatten (hsc : IsSimplyConnectedSet X) (hL : IsPathConnected (X ∩ Y))
    {e c : (X ∪ Y : Set S)} (r : Path e c) (hr : ∀ u, (r u).1 ∈ X) (he : e.1 ∈ Y) (hc : c.1 ∈ Y) :
    ∃ r' : Path e c, r.Homotopic r' ∧ ∀ u, (r' u).1 ∈ Y := by
  have heX : e.1 ∈ X := by simpa using hr 0
  have hcX : c.1 ∈ X := by simpa using hr 1
  obtain ⟨c', hc'⟩ := hL.joinedIn _ ⟨heX, he⟩ _ ⟨hcX, hc⟩
  refine ⟨pathCod c' e.2 c.2 fun u => Or.inl (hc' u).1, ?_, fun u => (hc' u).2⟩
  exact homotopic_of_mem hsc subset_union_left _ _ heX hcX hr fun u => (hc' u).1

private theorem IsPushed.step (hsc : IsSimplyConnectedSet X) (hL : IsPathConnected (X ∩ Y))
    {a c d : (X ∪ Y : Set S)} {ω : Path a c} (h : IsPushed X Y ω) (s : Path c d)
    (hs : (∀ u, (s u).1 ∈ X) ∨ ∀ u, (s u).1 ∈ Y) : IsPushed X Y (ω.trans s) := by
  rcases h with ⟨q, h₁, h₂⟩ | ⟨e, q, r, h₁, h₂, h₃⟩
  · rcases hs with hs | hs
    · exact Or.inr ⟨c, q, s, h₁.hcomp (Path.Homotopic.refl s), h₂, hs⟩
    · exact Or.inl ⟨q.trans s, h₁.hcomp (Path.Homotopic.refl s), trans_mem h₂ hs⟩
  · have hassoc : (ω.trans s).Homotopic (q.trans (r.trans s)) :=
      (h₁.hcomp (Path.Homotopic.refl s)).trans (Path.Homotopic.trans_assoc q r s)
    rcases hs with hs | hs
    · exact Or.inr ⟨e, q, r.trans s, hassoc, h₂, trans_mem h₃ hs⟩
    · have heY : e.1 ∈ Y := by simpa using h₂ 1
      have hcY : c.1 ∈ Y := by simpa using hs 0
      obtain ⟨r', hr', hr'Y⟩ := flatten hsc hL r h₃ heY hcY
      refine Or.inl ⟨q.trans (r'.trans s), hassoc.trans ?_, trans_mem h₂ (trans_mem hr'Y hs)⟩
      exact (Path.Homotopic.refl q).hcomp (hr'.hcomp (Path.Homotopic.refl s))

/-- Each path of `X ∪ Y` with ends in `Y` is homotopic to a path in `Y`, when `X` and `Y` are cones
at each
point of `X ∪ Y`. -/
theorem exists_homotopic_path_of_cones (hsc : IsSimplyConnectedSet X) (hL : IsPathConnected (X ∩ Y))
    (hcone : ∀ z ∈ X ∪ Y, IsLocalCone X Y z) {a b : (X ∪ Y : Set S)} (p : Path a b) (ha : a.1 ∈ Y)
    (hb : b.1 ∈ Y) : ∃ q : Path a b, p.Homotopic q ∧ ∀ u, (q u).1 ∈ Y := by
  let good : Set I → Prop := fun O => IsOpen O ∧ ∃ K : Set S, IsSimplyConnectedSet K ∧ K ⊆ X ∪ Y ∧
    (∀ u ∈ O, (p u).1 ∈ K) ∧ ∃ z ∈ K, ∀ c ∈ K, JoinedIn (K ∩ X) c z ∨ JoinedIn (K ∩ Y) c z
  have hcont : Continuous fun u : I => (p u).1 := by fun_prop
  have hcover : (univ : Set I) ⊆ ⋃ O : {O : Set I // good O}, O.1 := by
    intro u _
    obtain ⟨O, K, hO, hzO, hsub, hK, hsc', hzK, hj⟩ := hcone _ (p u).2
    exact mem_iUnion.mpr ⟨⟨_, hO.preimage hcont, K, hsc', hK, fun w hw => hsub ⟨(p w).2, hw⟩, _,
      hzK, hj⟩, hzO⟩
  obtain ⟨t, ht0, htmono, ⟨n₀, hn₀⟩, htO⟩ := exists_monotone_Icc_subset_open_cover_unitInterval
    (fun O : {O : Set I // good O} => O.2.1) hcover
  have h0Y : (p 0).1 ∈ Y := by simpa using ha
  have key : ∀ n, IsPushed X Y (p.subpath 0 (t n)) := by
    intro n
    induction n with
    | zero =>
      rw [ht0, Path.subpath_self]
      exact Or.inl ⟨Path.refl _, Path.Homotopic.refl _, fun _ => h0Y⟩
    | succ n ih =>
      obtain ⟨⟨O, _, K, hK, hKZ, hKO, z, hzK, hj⟩, hsub⟩ := htO n
      have hle : t n ≤ t (n + 1) := htmono (Nat.le_succ n)
      let zT : (X ∪ Y : Set S) := ⟨z, hKZ hzK⟩
      have harm : ∀ x : (X ∪ Y : Set S), x.1 ∈ K → ∃ α : Path x zT, (∀ u, (α u).1 ∈ K) ∧
          ((∀ u, (α u).1 ∈ X) ∨ ∀ u, (α u).1 ∈ Y) := by
        intro x hx
        rcases hj x.1 hx with ⟨c, hc⟩ | ⟨c, hc⟩
        · exact ⟨pathCod c x.2 zT.2 fun u => hKZ (hc u).1, fun u => (hc u).1,
            Or.inl fun u => (hc u).2⟩
        · exact ⟨pathCod c x.2 zT.2 fun u => hKZ (hc u).1, fun u => (hc u).1,
            Or.inr fun u => (hc u).2⟩
      have hpK : ∀ w ∈ Icc (t n) (t (n + 1)), (p w).1 ∈ K := fun w hw => hKO w (hsub hw)
      obtain ⟨α, hαK, hα⟩ := harm (p (t n)) (hpK _ ⟨le_rfl, hle⟩)
      obtain ⟨β, hβK, hβ⟩ := harm (p (t (n + 1))) (hpK _ ⟨hle, le_rfl⟩)
      have hpiece : ∀ u, ((p.subpath (t n) (t (n + 1))) u).1 ∈ K := by
        intro u
        have : (p.subpath (t n) (t (n + 1))) u ∈ p '' uIcc (t n) (t (n + 1)) := by
          rw [← Path.range_subpath]
          exact mem_range_self u
        obtain ⟨v, hv, hv'⟩ := this
        rw [uIcc_of_le hle] at hv
        rw [← hv']
        exact hpK v hv
      have hβs : ∀ {A : Set S}, (∀ u, (β u).1 ∈ A) → ∀ u, (β.symm u).1 ∈ A := fun hA u => by
        rw [Path.symm_apply]
        exact hA _
      have hh : (p.subpath (t n) (t (n + 1))).Homotopic (α.trans β.symm) :=
        homotopic_of_mem hK hKZ _ _ (hpK _ ⟨le_rfl, hle⟩) (hpK _ ⟨hle, le_rfl⟩) hpiece
          (trans_mem hαK (hβs hβK))
      have h₁ := (ih.step hsc hL α hα).step hsc hL β.symm (hβ.imp hβs hβs)
      refine h₁.congr ?_
      refine (Path.Homotopic.subpath_trans_subpath p 0 (t n) (t (n + 1))).symm.trans ?_
      exact ((Path.Homotopic.refl _).hcomp hh).trans (Path.Homotopic.trans_assoc _ _ _).symm
  have hfin := key n₀
  rw [hn₀ n₀ le_rfl] at hfin
  have h1Y : (p 1).1 ∈ Y := by simpa using hb
  have hdone : ∃ q : Path (p 0) (p 1), (p.subpath 0 1).Homotopic q ∧ ∀ u, (q u).1 ∈ Y := by
    rcases hfin with h | ⟨e, q, r, h₁, h₂, h₃⟩
    · exact h
    · have heY : e.1 ∈ Y := by simpa using h₂ 1
      obtain ⟨r', hr', hr'Y⟩ := flatten hsc hL r h₃ heY h1Y
      exact ⟨q.trans r', h₁.trans ((Path.Homotopic.refl q).hcomp hr'), trans_mem h₂ hr'Y⟩
  obtain ⟨q, hq, hqY⟩ := hdone
  rw [Path.subpath_zero_one] at hq
  refine ⟨q.cast p.source.symm p.target.symm, ?_, fun w => ?_⟩
  · have e : (p.cast p.source p.target).cast p.source.symm p.target.symm = p := by
      ext w
      simp
    have h := Path.Homotopic.pathCast hq p.source.symm p.target.symm
    rwa [e] at h
  · simpa using hqY w

/-- **(3.1)** of Graph Minors XI (page 76), for closed nice sets. -/
theorem nice_31 : Nice31Statement.{u} := by
  intro S _ _ _ hS Γ X Y hX hY hXn hYn hsc hL
  exact exists_push_of_paths hsc hL fun p ha hb =>
    exists_homotopic_path_of_cones hsc hL (fun _ hz => isLocalCone hS hX hY hXn hYn hz) p ha hb

end GraphMinor.GM11
