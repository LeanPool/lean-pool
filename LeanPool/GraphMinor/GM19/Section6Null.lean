/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Collapse
public import LeanPool.GraphMinor.GM11.Section3
public import LeanPool.GraphMinor.GM12.Section2ArcHomotopy

/-!
# Null-homotopic curves under a collapse

Let `c` be a homotopy from the identity of a space to a map `φ`. If `φ ∘ ψ` is null-homotopic for a
closed curve `ψ` then so is `ψ` (`null_of_collapse`). If two arcs with common ends only are mapped
by `φ` to two loops at one point, and both loops are null-homotopic, then the `O`-arc made of the
two arcs is null-homotopic (`not_null_of_two_arcs`). These two facts are the topology behind
"`rep(H) ≤ rep(H')`" in the proof of Graph Minors XIX, (6.3) (page 340).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM12

local notation "𝕀" => unitInterval

variable {T : Type} [TopologicalSpace T]

/-- Null-homotopy of an `O`-arc does not depend on the way it is parametrized. -/
theorem null_of_param {F : Set T} (hnull : IsNullHomotopicOArc F) (γ : C(Circle, T))
    (hr : range γ = F) : ClosedCurveIsNullHomotopicIn univ γ := by
  obtain ⟨φ, x, hx, H, -, h0, h1⟩ := hnull
  have hγF : ∀ z, γ z ∈ F := fun z => hr ▸ mem_range_self z
  let r : C(Circle, Circle) := ⟨fun z => φ.symm ⟨γ z, hγF z⟩, by fun_prop⟩
  have hr' : ∀ z, (φ (r z)).1 = γ z := fun z => by simp [r]
  refine ⟨x, hx, ⟨fun q => H (r q.1, q.2), by fun_prop⟩, fun _ => mem_univ _, fun z => ?_,
    fun z => ?_⟩
  · exact (h0 (r z)).trans (hr' z)
  · exact h1 (r z)

/-- The range of an injective closed curve is an `O`-arc. -/
theorem isOArc_range [T2Space T] {γ : C(Circle, T)} (hγ : Function.Injective γ) : IsOArc (range γ)
  :=
  ⟨(γ.continuous.isClosedEmbedding hγ).isEmbedding.toHomeomorph⟩

/-- A closed curve with a null-homotopic image under the end of a homotopy from the identity is
null-homotopic. -/
theorem null_of_collapse (c : C(𝕀 × T, T)) (h0 : ∀ x, c (0, x) = x) {ψ ψ' : C(Circle, T)}
    (hψ : ∀ z, ψ' z = c (1, ψ z)) (hn : ClosedCurveIsNullHomotopicIn univ ψ') :
    ClosedCurveIsNullHomotopicIn univ ψ := by
  obtain ⟨x, hx, h⟩ := hn
  have h1 : ClosedCurvesHomotopicIn univ ψ ψ' :=
    ⟨⟨fun q => c (q.2, ψ q.1), by fun_prop⟩, fun _ => mem_univ _, fun z => h0 _, fun z =>
      (hψ z).symm⟩
  exact ⟨x, hx, h1.trans h⟩

/-- A loop that is null-homotopic as a closed curve is homotopic to the constant path. -/
theorem path_refl_of_null {w : T} (P : Path w w) {γ : C(Circle, T)} (hγ : ∀ t, γ (arcParam 1 t)
  = P t)
    (h : ClosedCurveIsNullHomotopicIn univ γ) : P.Homotopic (Path.refl w) := by
  obtain ⟨x, -, H, -, h0, h1⟩ := h
  let F : C(𝕀 × 𝕀, T) := ⟨fun q => H (arcParam 1 q.1, q.2), by fun_prop⟩
  refine loop_homotopic_refl P F (c := x) (fun s => ?_) (fun v => ?_) (fun s => ?_)
  · change H (arcParam 1 s, 0) = _
    rw [h0, hγ]
  · simp [F, arcParam_zero, arcParam_one]
  · exact h1 _

/-- Two arcs with common ends, each mapped to a null-homotopic loop at one point by the end of a
homotopy from the identity, are homotopic. -/
theorem paths_homotopic_of_collapse (c : C(𝕀 × T, T)) (h0 : ∀ x, c (0, x) = x) {u v w : T}
    (p q : Path u v) (hu : c (1, u) = w) (hv : c (1, v) = w) (P Q : Path w w)
    (hP : ∀ t, P t = c (1, p t)) (hQ : ∀ t, Q t = c (1, q t)) (hP' : P.Homotopic (Path.refl w))
    (hQ' : Q.Homotopic (Path.refl w)) : p.Homotopic q := by
  let l : Path u w := ⟨⟨fun t => c (t, u), by fun_prop⟩, by simp [h0], by simpa using hu⟩
  let r : Path v w := ⟨⟨fun t => c (t, v), by fun_prop⟩, by simp [h0], by simpa using hv⟩
  have key : ∀ (p : Path u v) (P : Path w w), (∀ t, P t = c (1, p t)) → P.Homotopic (Path.refl w) →
      (p.trans r).Homotopic (l.trans (Path.refl w)) := by
    intro p P hP hP'
    let F : C(𝕀 × 𝕀, T) := ⟨fun x => c (x.2, p x.1), by fun_prop⟩
    have h := homotopic_of_square F p r l P (fun s => h0 _) (fun t => by simp [F, r])
      (fun t => by simp [F, l]) (fun s => (hP s).symm)
    exact h.trans ((Path.Homotopic.refl l).hcomp hP')
  have h1 := (key p P hP hP').trans (key q Q hQ hQ').symm
  have cancel : ∀ p : Path u v, ((p.trans r).trans r.symm).Homotopic p := fun p =>
    (Path.Homotopic.trans_assoc p r r.symm).trans
      (((Path.Homotopic.refl p).hcomp (Path.Homotopic.trans_symm r)).trans
        (Path.Homotopic.trans_refl p))
  exact (cancel p).symm.trans ((h1.hcomp (Path.Homotopic.refl r.symm)).trans (cancel q))

/-- If an `O`-arc made of two arcs is not null-homotopic, and the end of a homotopy from the
identity maps the ends of the arcs to one point, then one of the two resulting loops is not
null-homotopic. -/
theorem not_null_of_two_arcs [T2Space T] (c : C(𝕀 × T, T)) (h0 : ∀ x, c (0, x) = x) {a b : 𝕀 → T}
    (h : IsTwoArcs a b) {w : T} (hu : c (1, a 0) = w) (hv : c (1, a 1) = w)
    (hn : ¬ IsNullHomotopicOArc (range a ∪ range b)) {γa γb : C(Circle, T)}
    (hγa : ∀ t, γa (arcParam 1 t) = c (1, a t)) (hγb : ∀ t, γb (arcParam 1 t) = c (1, b t)) :
    ¬ ClosedCurveIsNullHomotopicIn univ γa ∨ ¬ ClosedCurveIsNullHomotopicIn univ γb := by
  by_contra hc
  push Not at hc
  apply hn
  let p : Path (a 0) (a 1) := ⟨⟨a, h.arc_left.1⟩, rfl, rfl⟩
  let q : Path (a 0) (a 1) := ⟨⟨b, h.arc_right.1⟩, h.zero, h.one⟩
  let P : Path w w := ⟨⟨fun t => c (1, a t), by have := h.arc_left.1; fun_prop⟩, hu, hv⟩
  let Q : Path w w := ⟨⟨fun t => c (1, b t), by have := h.arc_right.1; fun_prop⟩,
    by change c (1, b 0) = w; rw [h.zero, hu], by change c (1, b 1) = w; rw [h.one, hv]⟩
  have hpq := paths_homotopic_of_collapse c h0 p q hu hv P Q (fun _ => rfl) (fun _ => rfl)
    (path_refl_of_null P hγa hc.1) (path_refl_of_null Q hγb hc.2)
  have := nullHomotopic_union_of_homotopic_arcs p q h.arc_left.2 h.arc_right.2 (fun s t he
    => h.meet s t he) hpq
  exact this

end GraphMinor.GM19
