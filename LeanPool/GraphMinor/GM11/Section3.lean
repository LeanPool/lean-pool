/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.TopologyStatements
import LeanPool.GraphMinor.Surface.InvarianceOfDomain
public import Mathlib.Topology.Subpath
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Section 3 of Graph Minors XI: homotopy, and the corrected form of (3.1)

Statement (3.1) of the paper is false as it stands (see the correction to (3.1) in
`corrections/GM11.md`). This file proves `theorem_3_1`, which adds one local hypothesis,
`IsLocalDeformationRetract`.

The proof follows the paper. It looks at the times when `φ` leaves `Y`, and on those intervals it
replaces `φ` by a path in `X ∩ Y`, using that `X` is simply-connected. The paper does this for all
of the infinitely many intervals at once, and that is the gap. We cut the circle into finitely many
pieces instead. On a piece that stays near one point of `X ∩ Y`, the local hypothesis pushes all
excursions of `φ` into `X ∩ Y` in one step. The remaining pieces are either in `Y` already, or are
single excursions in `X`, which are handled as in the paper.

The file also gives the tools on loops that this needs: a map from `[0, 1]` that agrees at the ends
gives a map from the circle (`loopLift`), and in a simply-connected set any two paths with the same
ends are homotopic (`IsSimplyConnectedSet.pathsHomotopic`).
-/

public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u v

/-! ## The circle as a quotient of `[0, 1]` -/

/-- The map `[0, 1] → S¹` that winds once around the circle, starting at `z`. -/
noncomputable def arcParam (z : Circle) : C(I, Circle) :=
  ⟨fun t => z * Circle.exp (2 * Real.pi * t), by fun_prop⟩

theorem arcParam_apply (z : Circle) (t : I) : arcParam z t = z * Circle.exp (2 * Real.pi * t) := by
  simp [arcParam]

@[simp] theorem arcParam_zero (z : Circle) : arcParam z 0 = z := by
  simp [arcParam]

@[simp] theorem arcParam_one (z : Circle) : arcParam z 1 = z := by
  simp [arcParam, Circle.exp_two_pi]

theorem arcParam_surjective (z : Circle) : Function.Surjective (arcParam z) := by
  intro w
  set θ : ℝ := Complex.arg (z⁻¹ * w : Circle) with hθ
  have hexp : Circle.exp θ = z⁻¹ * w := Circle.exp_arg _
  have hlo : -Real.pi < θ := Complex.neg_pi_lt_arg _
  have hhi : θ ≤ Real.pi := Complex.arg_le_pi _
  have hpi := Real.pi_pos
  by_cases h : 0 ≤ θ
  · refine ⟨⟨θ / (2 * Real.pi), by positivity, ?_⟩, ?_⟩
    · rw [div_le_one (by positivity)]
      linarith
    · have : 2 * Real.pi * (θ / (2 * Real.pi)) = θ := by field_simp
      simp [arcParam, this, hexp]
  · push Not at h
    refine ⟨⟨θ / (2 * Real.pi) + 1, ?_, ?_⟩, ?_⟩
    · have : -1 ≤ θ / (2 * Real.pi) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      linarith
    · have : θ / (2 * Real.pi) ≤ 0 := div_nonpos_of_nonpos_of_nonneg h.le (by positivity)
      linarith
    · have : 2 * Real.pi * (θ / (2 * Real.pi) + 1) = θ + 2 * Real.pi := by field_simp
      simp [arcParam, this, Circle.exp_add, Circle.exp_two_pi, hexp]

/-- Two parameters with the same image are equal, or they are the two ends of `[0, 1]`. -/
theorem arcParam_eq_iff (z : Circle) {s t : I} (h : arcParam z s = arcParam z t) :
    s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
  have h' : Circle.exp (2 * Real.pi * s) = Circle.exp (2 * Real.pi * t) :=
    mul_left_cancel (a := z) h
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h'
  have hpi := Real.pi_pos
  have hst : (s : ℝ) = t + m := by
    have : 2 * Real.pi * ((s : ℝ) - t - m) = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left (by positivity)
    linarith
  have hs0 := s.2.1
  have hs1 := s.2.2
  have ht0 := t.2.1
  have ht1 := t.2.2
  have hmle : (m : ℝ) ≤ 1 := by linarith
  have hmge : (-1 : ℝ) ≤ m := by linarith
  have h1 : m ≤ 1 := by exact_mod_cast hmle
  have h2 : -1 ≤ m := by exact_mod_cast hmge
  have hm3 : m = 0 ∨ m = 1 ∨ m = -1 := by omega
  rcases hm3 with rfl | rfl | rfl
  · left
    exact Subtype.ext (by simpa using hst)
  · right; right
    simp only [Int.cast_one] at hst
    exact ⟨Subtype.ext (show (s : ℝ) = 1 by linarith), Subtype.ext (show (t : ℝ) = 0 by linarith)⟩
  · right; left
    simp only [Int.cast_neg, Int.cast_one] at hst
    exact ⟨Subtype.ext (show (s : ℝ) = 0 by linarith), Subtype.ext (show (t : ℝ) = 1 by linarith)⟩

theorem isQuotientMap_arcParam (z : Circle) : IsQuotientMap (arcParam z) :=
  (arcParam z).continuous.isClosedMap.isQuotientMap (arcParam z).continuous
    (arcParam_surjective z)

theorem isQuotientMap_arcParam_prod (z : Circle) :
    IsQuotientMap ((arcParam z).prodMap (ContinuousMap.id I)) := by
  have hc := ((arcParam z).prodMap (ContinuousMap.id I)).continuous
  exact hc.isClosedMap.isQuotientMap hc ((arcParam_surjective z).prodMap Function.surjective_id)

private theorem loop_factors {T : Type*} (z : Circle) (f : I → T) (h : f 0 = f 1) :
    Function.FactorsThrough f (arcParam z) := by
  intro a b hab
  rcases arcParam_eq_iff z hab with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact h
  · exact h.symm

private theorem cylinder_factors {T : Type*} (z : Circle) (F : I × I → T)
    (h : ∀ v, F (0, v) = F (1, v)) :
    Function.FactorsThrough F ((arcParam z).prodMap (ContinuousMap.id I)) := by
  rintro ⟨a, u⟩ ⟨b, v⟩ hab
  have h₁ : arcParam z a = arcParam z b := (Prod.ext_iff.mp hab).1
  have h₂ : u = v := (Prod.ext_iff.mp hab).2
  subst h₂
  rcases arcParam_eq_iff z h₁ with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact h u
  · exact (h u).symm

/-- A map from `[0, 1]` that agrees at the two ends, seen as a map from the circle. -/
noncomputable def loopLift {T : Type*} [TopologicalSpace T] (z : Circle) (f : C(I, T))
    (h : f 0 = f 1) : C(Circle, T) :=
  (isQuotientMap_arcParam z).lift f (loop_factors z f h)

@[simp] theorem loopLift_apply {T : Type*} [TopologicalSpace T] (z : Circle) (f : C(I, T))
    (h : f 0 = f 1) (t : I) : loopLift z f h (arcParam z t) = f t :=
  DFunLike.congr_fun ((isQuotientMap_arcParam z).lift_comp f (loop_factors z f h)) t

/-- A map from `[0, 1] × [0, 1]` that agrees on the left and right sides, seen as a map from the
cylinder. -/
noncomputable def cylinderLift {T : Type*} [TopologicalSpace T] (z : Circle) (F : C(I × I, T))
    (h : ∀ v, F (0, v) = F (1, v)) : C(Circle × I, T) :=
  (isQuotientMap_arcParam_prod z).lift F (cylinder_factors z F h)

@[simp] theorem cylinderLift_apply {T : Type*} [TopologicalSpace T] (z : Circle) (F : C(I × I, T))
    (h : ∀ v, F (0, v) = F (1, v)) (t v : I) :
    cylinderLift z F h (arcParam z t, v) = F (t, v) :=
  DFunLike.congr_fun ((isQuotientMap_arcParam_prod z).lift_comp F (cylinder_factors z F h))
    (t, v)

/-! ## Paths and homotopy -/

section Paths

variable {T : Type*} [TopologicalSpace T]

/-- A square with sides `pb, pr, pl, pt` gives a homotopy between `pb + pr` and `pl + pt`. The
square is simply-connected, and the homotopy there is mapped forward. -/
theorem homotopic_of_square {a b c d : T} (F : C(I × I, T)) (pb : Path a b) (pr : Path b d)
    (pl : Path a c) (pt : Path c d) (hb : ∀ s, F (s, 0) = pb s) (hr : ∀ v, F (1, v) = pr v)
    (hl : ∀ v, F (0, v) = pl v) (ht : ∀ s, F (s, 1) = pt s) :
    (pb.trans pr).Homotopic (pl.trans pt) := by
  obtain rfl : F (0, 0) = a := by simpa using hb 0
  obtain rfl : F (1, 0) = b := by simpa using hb 1
  obtain rfl : F (0, 1) = c := by simpa using hl 1
  obtain rfl : F (1, 1) = d := by simpa using hr 1
  have : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  let idp : Path (0 : I) 1 := ⟨ContinuousMap.id I, rfl, rfl⟩
  let bottom : Path ((0, 0) : I × I) (1, 0) := idp.prod (Path.refl 0)
  let right : Path ((1, 0) : I × I) (1, 1) := (Path.refl 1).prod idp
  let left : Path ((0, 0) : I × I) (0, 1) := (Path.refl 0).prod idp
  let top : Path ((0, 1) : I × I) (1, 1) := idp.prod (Path.refl 1)
  have h := (SimplyConnectedSpace.paths_homotopic (bottom.trans right) (left.trans top)).map F
  rw [Path.map_trans, Path.map_trans] at h
  have e₁ : bottom.map F.continuous = pb := Path.ext (funext fun s => hb s)
  have e₂ : right.map F.continuous = pr := Path.ext (funext fun s => hr s)
  have e₃ : left.map F.continuous = pl := Path.ext (funext fun s => hl s)
  have e₄ : top.map F.continuous = pt := Path.ext (funext fun s => ht s)
  rwa [e₁, e₂, e₃, e₄] at h

/-- A loop is homotopic to the constant loop if there is a square with the loop at the bottom, a
constant top side, and the same path on the left and on the right. -/
theorem loop_homotopic_refl {a c : T} (γ : Path a a) (F : C(I × I, T))
    (hb : ∀ s, F (s, 0) = γ s) (hlr : ∀ v, F (0, v) = F (1, v)) (ht : ∀ s, F (s, 1) = c) :
    γ.Homotopic (Path.refl a) := by
  have h0 : F (0, 0) = a := by simpa using hb 0
  have h1 : F (0, 1) = c := ht 0
  let β : Path a c := ⟨⟨fun v => F (0, v), by fun_prop⟩, h0, h1⟩
  have h := homotopic_of_square F γ β β (Path.refl c) hb (fun v => (hlr v).symm) (fun _ => rfl)
    (fun s => by simpa using ht s)
  have e₁ : γ.Homotopic ((γ.trans β).trans β.symm) :=
    (Path.Homotopic.trans_refl γ).symm.trans
      (((Path.Homotopic.refl γ).hcomp (Path.Homotopic.trans_symm β)).symm.trans
        (Path.Homotopic.trans_assoc γ β β.symm).symm)
  exact e₁.trans ((h.hcomp (Path.Homotopic.refl β.symm)).trans
    (((Path.Homotopic.trans_refl β).hcomp (Path.Homotopic.refl β.symm)).trans
      (Path.Homotopic.trans_symm β)))

/-- If every loop is homotopic to a constant loop then any two paths with the same ends are
homotopic. -/
theorem paths_homotopic_of_loops (hl : ∀ (a : T) (γ : Path a a), γ.Homotopic (Path.refl a))
    {a b : T} (p q : Path a b) : p.Homotopic q :=
  (Path.Homotopic.trans_refl p).symm.trans
    (((Path.Homotopic.refl p).hcomp (Path.Homotopic.symm_trans q)).symm.trans
      ((Path.Homotopic.trans_assoc p q.symm q).symm.trans
        (((hl a (p.trans q.symm)).hcomp (Path.Homotopic.refl q)).trans
          (Path.Homotopic.refl_trans q))))

end Paths

section Sets

variable {S : Type u} [TopologicalSpace S]

/-- In a simply-connected set, any two paths with the same ends are homotopic. This is the fact
that the proof of (3.1) calls on when it says that a path in `X` is homotopic in `X` to a path in
`X ∩ Y` with the same ends. -/
theorem _root_.GraphMinor.Surface.IsSimplyConnectedSet.pathsHomotopic {X : Set S}
  (hX : IsSimplyConnectedSet X) {a b : X}
    (p q : Path a b) : p.Homotopic q := by
  refine paths_homotopic_of_loops (fun a γ => ?_) p q
  let f : C(I, S) := ⟨fun t => (γ t).1, by fun_prop⟩
  have hf : f 0 = f 1 := by simp [f]
  have hr : range (loopLift 1 f hf) ⊆ X := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨t, rfl⟩ := arcParam_surjective 1 w
    rw [loopLift_apply]
    exact (γ t).2
  obtain ⟨c, hc, ψ, hψ, h0, h1⟩ := hX.2 _ hr
  let F : C(I × I, X) :=
    ⟨fun p => ⟨ψ (arcParam 1 p.1, p.2), hψ _⟩, by
      refine Continuous.subtype_mk (ψ.continuous.comp ?_) _
      exact ((arcParam 1).continuous.comp continuous_fst).prodMk continuous_snd⟩
  refine loop_homotopic_refl (c := ⟨c, hc⟩) γ F (fun s => ?_) (fun v => ?_) (fun s => ?_)
  · apply Subtype.ext
    simp only [F, ContinuousMap.coe_mk]
    rw [h0, loopLift_apply]
    rfl
  · apply Subtype.ext
    simp [F]
  · apply Subtype.ext
    simp only [F, ContinuousMap.coe_mk]
    rw [h1]
    rfl

/-- A path in a set `Z` that stays in a subset of `Z`, seen as a path in the subset. -/
private def pathRestrict {Z W : Set S} {a b : Z} (p : Path a b) (ha : a.1 ∈ W) (hb : b.1 ∈ W)
    (h : ∀ u, (p u).1 ∈ W) : Path (⟨a.1, ha⟩ : W) ⟨b.1, hb⟩ where
  toFun u := ⟨(p u).1, h u⟩
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

/-- A path in `S` that stays in `Z`, seen as a path in `Z`. -/
@[expose] def pathCod {Z : Set S} {a b : S} (p : Path a b) (ha : a ∈ Z) (hb : b ∈ Z)
    (h : ∀ u, p u ∈ Z) : Path (⟨a, ha⟩ : Z) ⟨b, hb⟩ where
  toFun u := ⟨p u, h u⟩
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

/-- Two paths of `Z` that stay in the simply-connected set `X ⊆ Z` are homotopic in `Z`. -/
theorem homotopic_of_mem {X Z : Set S} (hX : IsSimplyConnectedSet X) (hXZ : X ⊆ Z)
    {a b : Z} (p q : Path a b) (ha : a.1 ∈ X) (hb : b.1 ∈ X) (hp : ∀ u, (p u).1 ∈ X)
    (hq : ∀ u, (q u).1 ∈ X) : p.Homotopic q := by
  have h := (hX.pathsHomotopic (pathRestrict p ha hb hp) (pathRestrict q ha hb hq)).map
    (f := (⟨inclusion hXZ, continuous_inclusion hXZ⟩ : C(X, Z)))
  have e₁ : (pathRestrict p ha hb hp).map
      (⟨inclusion hXZ, continuous_inclusion hXZ⟩ : C(X, Z)).continuous = p := by
    ext u
    rfl
  have e₂ : (pathRestrict q ha hb hq).map
      (⟨inclusion hXZ, continuous_inclusion hXZ⟩ : C(X, Z)).continuous = q := by
    ext u
    rfl
  rwa [e₁, e₂] at h

end Sets

/-! ## The local hypothesis, and the proof of (3.1) -/

variable {S : Type u} [TopologicalSpace S]

/-- The local hypothesis of the corrected (3.1). Each point `y` of `L` has an open neighbourhood `A`
such that `X ∩ A` can be deformed in `X` into `L`, with the points of `L ∩ A` kept fixed.

For example this holds when `X` is a closed disc and `L` its boundary, see
`IsClosedDisc.isLocalDeformationRetract`. It also holds for any `L ⊆ X` for which `X` and `L` look
like cones with one apex near each point of `L`, so for finite unions of points, lines and closed
discs that are drawn in a tame way. -/
def IsLocalDeformationRetract (X L : Set S) : Prop :=
  ∀ y ∈ L, ∃ A : Set S, IsOpen A ∧ y ∈ A ∧ ∃ h : C((X ∩ A : Set S) × I, S),
    (∀ p, h p ∈ X) ∧ (∀ x, h (x, 0) = x.1) ∧ (∀ x, h (x, 1) ∈ L) ∧
      ∀ x t, x.1 ∈ L → h (x, t) = x.1

section Push

variable {X Y : Set S}

/-- The subpath of `p` from time `s` to time `t` is homotopic to a path in `Y`. -/
private def Pushes {a b : (X ∪ Y : Set S)} (p : Path a b) (s t : I) : Prop :=
  ∃ q : Path (p s) (p t), (p.subpath s t).Homotopic q ∧ ∀ u, (q u).1 ∈ Y

private theorem Pushes.trans {a b : (X ∪ Y : Set S)} {p : Path a b} {s t r : I}
    (h₁ : Pushes p s t) (h₂ : Pushes p t r) : Pushes p s r := by
  obtain ⟨q₁, h₁, hq₁⟩ := h₁
  obtain ⟨q₂, h₂, hq₂⟩ := h₂
  refine ⟨q₁.trans q₂, ((Path.Homotopic.subpath_trans_subpath p s t r).symm).trans
    (h₁.hcomp h₂), fun u => ?_⟩
  obtain ⟨v, hv | hv⟩ : ∃ v, (q₁.trans q₂) u = q₁ v ∨ (q₁.trans q₂) u = q₂ v := by
    have : (q₁.trans q₂) u ∈ range q₁ ∪ range q₂ := by
      rw [← Path.trans_range]
      exact mem_range_self u
    rcases this with ⟨v, hv⟩ | ⟨v, hv⟩
    · exact ⟨v, Or.inl hv.symm⟩
    · exact ⟨v, Or.inr hv.symm⟩
  · rw [hv]; exact hq₁ v
  · rw [hv]; exact hq₂ v

private theorem pushes_refl {a b : (X ∪ Y : Set S)} (p : Path a b) (s : I) (hs : (p s).1 ∈ Y) :
    Pushes p s s := by
  refine ⟨Path.refl _, ?_, fun _ => hs⟩
  rw [Path.subpath_self]

/-- A piece of `p` that stays in `Y` already. -/
private theorem pushes_of_mem {a b : (X ∪ Y : Set S)} (p : Path a b) {s t : I} (hst : s ≤ t)
    (h : ∀ u ∈ Icc s t, (p u).1 ∈ Y) : Pushes p s t := by
  refine ⟨p.subpath s t, Path.Homotopic.refl _, fun u => ?_⟩
  have : (p.subpath s t) u ∈ p '' uIcc s t := by
    rw [← Path.range_subpath]
    exact mem_range_self u
  obtain ⟨v, hv, hv'⟩ := this
  rw [uIcc_of_le hst] at hv
  rw [← hv']
  exact h v hv

/-- A single excursion of `p` in `X`, with ends in `Y`: this is the step of the paper. The path is
homotopic in `X` to a path in `X ∩ Y` with the same ends, since `X` is simply-connected and `X ∩ Y`
is arc-wise connected. -/
private theorem pushes_of_excursion (hX : IsClosed X) (hsc : IsSimplyConnectedSet X)
    (hL : IsPathConnected (X ∩ Y)) {a b : (X ∪ Y : Set S)} (p : Path a b) {s t : I} (hst : s ≤ t)
    (hs : (p s).1 ∈ Y) (ht : (p t).1 ∈ Y) (hout : ∀ u ∈ Ioo s t, (p u).1 ∉ Y) : Pushes p s t := by
  rcases hst.eq_or_lt with rfl | hlt
  · exact pushes_refl p s hs
  have hclosed : IsClosed {u : I | (p u).1 ∈ X} :=
    hX.preimage (continuous_subtype_val.comp p.continuous)
  have hin : ∀ u ∈ Ioo s t, (p u).1 ∈ X := fun u hu =>
    ((p u).2).resolve_right (hout u hu)
  have hcl : Icc s t ⊆ {u : I | (p u).1 ∈ X} := by
    rw [← closure_Ioo hlt.ne]
    exact closure_minimal hin hclosed
  have hsX : (p s).1 ∈ X := hcl ⟨le_rfl, hst⟩
  have htX : (p t).1 ∈ X := hcl ⟨hst, le_rfl⟩
  obtain ⟨c, hc⟩ := hL.joinedIn _ ⟨hsX, hs⟩ _ ⟨htX, ht⟩
  let Z : Set S := X ∪ Y
  let r : Path (p s) (p t) := pathCod c (p s).2 (p t).2 fun u => Or.inl (hc u).1
  refine ⟨r, ?_, fun u => (hc u).2⟩
  refine homotopic_of_mem hsc subset_union_left _ _ hsX htX (fun u => ?_) (fun u => (hc u).1)
  have : (p.subpath s t) u ∈ p '' uIcc s t := by
    rw [← Path.range_subpath]
    exact mem_range_self u
  obtain ⟨v, hv, hv'⟩ := this
  rw [uIcc_of_le hst] at hv
  rw [← hv']
  exact hcl hv

/-- A piece of `p` near one point of `X ∩ Y`, with ends in `Y`. The local deformation is applied to
the points of the piece in `X`, and the points in `Y` stay fixed. -/
private theorem pushes_of_local (hX : IsClosed X) (hY : IsClosed Y) {a b : (X ∪ Y : Set S)}
    (p : Path a b) {s t : I} (hst : s ≤ t) (hs : (p s).1 ∈ Y) (ht : (p t).1 ∈ Y) {A : Set S}
    (hA : ∀ u ∈ Icc s t, (p u).1 ∈ A) (h : C((X ∩ A : Set S) × I, S))
    (h₁ : ∀ p, h p ∈ X) (h₂ : ∀ x, h (x, 0) = x.1) (h₃ : ∀ x, h (x, 1) ∈ X ∩ Y)
    (h₄ : ∀ x t, x.1 ∈ X ∩ Y → h (x, t) = x.1) : Pushes p s t := by
  classical
  let r := p.subpath s t
  have hrA : ∀ u, (r u).1 ∈ A := by
    intro u
    have : r u ∈ p '' uIcc s t := by
      rw [← Path.range_subpath]
      exact mem_range_self u
    obtain ⟨v, hv, hv'⟩ := this
    rw [uIcc_of_le hst] at hv
    rw [← hv']
    exact hA v hv
  let G : I × I → S := fun q =>
    if hq : (r q.2).1 ∈ X then h (⟨(r q.2).1, hq, hrA _⟩, q.1) else (r q.2).1
  have hGX : ∀ q, (r q.2).1 ∈ X → G q ∈ X := by
    intro q hq
    simp only [G, dite_eq_left hq]
    exact h₁ _
  have hcont : Continuous G := by
    have hc₁ : IsClosed {q : I × I | (r q.2).1 ∈ X} :=
      hX.preimage (by fun_prop)
    have hc₂ : IsClosed {q : I × I | (r q.2).1 ∈ Y} :=
      hY.preimage (by fun_prop)
    have hun : {q : I × I | (r q.2).1 ∈ X} ∪ {q : I × I | (r q.2).1 ∈ Y} = univ :=
      eq_univ_of_forall fun q => (r q.2).2
    rw [← continuousOn_univ, ← hun]
    refine ContinuousOn.union_of_isClosed ?_ ?_ hc₁ hc₂
    · rw [continuousOn_iff_continuous_domRestrict]
      have : ({q : I × I | (r q.2).1 ∈ X}.domRestrict G) = fun q =>
          h (⟨(r q.1.2).1, q.2, hrA _⟩, q.1.1) :=
        funext fun q => dite_eq_left q.2
      rw [this]
      exact h.continuous.comp (Continuous.prodMk (by fun_prop) (by fun_prop))
    · have heq : EqOn G (fun q => (r q.2).1) {q : I × I | (r q.2).1 ∈ Y} := by
        intro q hq
        by_cases hqX : (r q.2).1 ∈ X
        · simp only [G, dite_eq_left hqX]
          exact h₄ _ _ ⟨hqX, hq⟩
        · simp only [G, dite_eq_right hqX]
      exact (Continuous.continuousOn (by fun_prop)).congr heq
  have hZ : ∀ q, G q ∈ X ∪ Y := by
    intro q
    by_cases hq : (r q.2).1 ∈ X
    · exact Or.inl (hGX q hq)
    · right
      simp only [G, dite_eq_right hq]
      exact (r q.2).2.resolve_left hq
  have hend : ∀ (v : I) (u : I), (r u).1 ∈ Y → G (v, u) = (r u).1 := by
    intro v u hu
    by_cases hq : (r u).1 ∈ X
    · simp only [G, dite_eq_left hq]
      exact h₄ _ _ ⟨hq, hu⟩
    · simp only [G, dite_eq_right hq]
  have hr0 : (r 0).1 ∈ Y := by simpa [r] using hs
  have hr1 : (r 1).1 ∈ Y := by simpa [r] using ht
  let F : C(I × I, (X ∪ Y : Set S)) := ⟨fun q => ⟨G q, hZ q⟩, hcont.subtype_mk _⟩
  have F0 : ∀ u, F (0, u) = r u := by
    intro u
    apply Subtype.ext
    by_cases hq : (r u).1 ∈ X
    · simp only [F, G, ContinuousMap.coe_mk, dite_eq_left hq]
      exact h₂ _
    · simp only [F, G, ContinuousMap.coe_mk, dite_eq_right hq]
  let q : Path (p s) (p t) :=
    { toFun := fun u => F (1, u)
      continuous_toFun := by fun_prop
      source' := by
        apply Subtype.ext
        have : (r 0).1 = (p s).1 := by simp [r]
        simp only [F, ContinuousMap.coe_mk]
        rw [hend 1 0 hr0, this]
      target' := by
        apply Subtype.ext
        have : (r 1).1 = (p t).1 := by simp [r]
        simp only [F, ContinuousMap.coe_mk]
        rw [hend 1 1 hr1, this] }
  have hH : r.Homotopic q := by
    refine ⟨⟨⟨F, F0, fun u => rfl⟩, ?_⟩⟩
    rintro v u (rfl | hu)
    · apply Subtype.ext
      change G (v, 0) = (r 0).1
      exact hend v 0 hr0
    · obtain rfl : u = 1 := hu
      apply Subtype.ext
      change G (v, 1) = (r 1).1
      exact hend v 1 hr1
  refine ⟨q, hH, fun u => ?_⟩
  by_cases hq : (r u).1 ∈ X
  · change G (1, u) ∈ Y
    simp only [G, dite_eq_left hq]
    exact (h₃ _).2
  · change G (1, u) ∈ Y
    simp only [G, dite_eq_right hq]
    exact (r u).2.resolve_left hq

/-- Each path of `X ∪ Y` with ends in `Y` is homotopic in `X ∪ Y`, with its ends fixed, to a path in
`Y`. See the module docstring for the structure of the proof. -/
theorem exists_homotopic_path (hX : IsClosed X) (hY : IsClosed Y) (hsc : IsSimplyConnectedSet X)
    (hL : IsPathConnected (X ∩ Y)) (hloc : IsLocalDeformationRetract X (X ∩ Y))
    {a b : (X ∪ Y : Set S)} (p : Path a b) (ha : a.1 ∈ Y) (hb : b.1 ∈ Y) :
    ∃ q : Path a b, p.Homotopic q ∧ ∀ u, (q u).1 ∈ Y := by
  -- The good open subsets of `[0, 1]`: their points stay out of `Y`, or out of `X`, or near one
  -- point of `X ∩ Y` where the local hypothesis applies.
  let good : Set I → Prop := fun O => IsOpen O ∧ ((∀ u ∈ O, (p u).1 ∉ Y) ∨ (∀ u ∈ O, (p u).1 ∉ X) ∨
    ∃ A : Set S, (∀ u ∈ O, (p u).1 ∈ A) ∧ ∃ h : C((X ∩ A : Set S) × I, S),
      (∀ p, h p ∈ X) ∧ (∀ x, h (x, 0) = x.1) ∧ (∀ x, h (x, 1) ∈ X ∩ Y) ∧
        ∀ x t, x.1 ∈ X ∩ Y → h (x, t) = x.1)
  have hcont : Continuous fun u : I => (p u).1 := by fun_prop
  have hcover : (univ : Set I) ⊆ ⋃ O : {O : Set I // good O}, O.1 := by
    intro u _
    by_cases huY : (p u).1 ∈ Y
    · by_cases huX : (p u).1 ∈ X
      · obtain ⟨A, hAo, huA, h, h₁, h₂, h₃, h₄⟩ := hloc _ ⟨huX, huY⟩
        exact mem_iUnion.mpr ⟨⟨_, hAo.preimage hcont, Or.inr (Or.inr ⟨A, fun _ h
          => h, h, h₁, h₂, h₃,
          h₄⟩)⟩, huA⟩
      · exact mem_iUnion.mpr ⟨⟨_, hX.isOpen_compl.preimage hcont,
          Or.inr (Or.inl fun _ h => h)⟩, huX⟩
    · exact mem_iUnion.mpr ⟨⟨_, hY.isOpen_compl.preimage hcont, Or.inl fun _ h => h⟩, huY⟩
  obtain ⟨t, ht0, htmono, ⟨n₀, hn₀⟩, htO⟩ := exists_monotone_Icc_subset_open_cover_unitInterval
    (fun O : {O : Set I // good O} => O.2.1) hcover
  have hclosedY : IsClosed {u : I | (p u).1 ∈ Y} := hY.preimage hcont
  have h0Y : (p 0).1 ∈ Y := by simpa using ha
  have h1Y : (p 1).1 ∈ Y := by simpa using hb
  have key : ∀ n, ∃ u, u ≤ t n ∧ (p u).1 ∈ Y ∧ (∀ w, u < w → w ≤ t n → (p w).1 ∉ Y) ∧
      Pushes p 0 u := by
    intro n
    induction n with
    | zero =>
      refine ⟨0, by rw [ht0], h0Y, fun w hw hw' => ?_, pushes_refl p 0 h0Y⟩
      rw [ht0] at hw'
      exact absurd hw (not_lt.mpr hw')
    | succ n ih =>
      obtain ⟨u, hu, huY, hout, hpu⟩ := ih
      have hle : t n ≤ t (n + 1) := htmono (Nat.le_succ n)
      by_cases hne : ({u : I | (p u).1 ∈ Y} ∩ Icc (t n) (t (n + 1))).Nonempty
      · have hC : IsCompact ({u : I | (p u).1 ∈ Y} ∩ Icc (t n) (t (n + 1))) :=
          isCompact_Icc.inter_left hclosedY
        obtain ⟨c, hc, hcle⟩ := hC.exists_isLeast hne
        obtain ⟨d, hd, hdle⟩ := hC.exists_isGreatest hne
        have hcd : c ≤ d := hdle hc
        have huc : u ≤ c := hu.trans hc.2.1
        have hstep₁ : Pushes p u c := by
          refine pushes_of_excursion hX hsc hL p huc huY hc.1 fun w hw hwY => ?_
          by_cases hwn : w ≤ t n
          · exact hout w hw.1 hwn hwY
          · push Not at hwn
            have : c ≤ w := hcle ⟨hwY, hwn.le, hw.2.le.trans hc.2.2⟩
            exact absurd hw.2 (not_lt.mpr this)
        obtain ⟨⟨O, hOo, hO⟩, hsub⟩ := htO n
        have hstep₂ : Pushes p c d := by
          rcases hO with hO | hO | ⟨A, hA, h, h₁, h₂, h₃, h₄⟩
          · exact absurd hc.1 (hO c (hsub hc.2))
          · refine pushes_of_mem p hcd fun w hw => ?_
            exact (p w).2.resolve_left (hO w (hsub ⟨hc.2.1.trans hw.1, hw.2.trans hd.2.2⟩))
          · refine pushes_of_local hX hY p hcd hc.1 hd.1 (fun w hw => ?_) h h₁ h₂ h₃ h₄
            exact hA w (hsub ⟨hc.2.1.trans hw.1, hw.2.trans hd.2.2⟩)
        refine ⟨d, hd.2.2, hd.1, fun w hw hw' hwY => ?_, (hpu.trans hstep₁).trans hstep₂⟩
        have : w ≤ d := hdle ⟨hwY, hc.2.1.trans (hcd.trans hw.le), hw'⟩
        exact absurd hw (not_lt.mpr this)
      · refine ⟨u, hu.trans hle, huY, fun w hw hw' hwY => ?_, hpu⟩
        by_cases hwn : w ≤ t n
        · exact hout w hw hwn hwY
        · push Not at hwn
          exact hne ⟨w, hwY, hwn.le, hw'⟩
  obtain ⟨u, -, -, hout, hpu⟩ := key n₀
  have hu1 : u = 1 := by
    by_contra hne
    exact hout 1 (lt_of_le_of_ne le_top hne) (by rw [hn₀ n₀ le_rfl]) h1Y
  subst hu1
  obtain ⟨q, hq, hqY⟩ := hpu
  rw [Path.subpath_zero_one] at hq
  refine ⟨q.cast p.source.symm p.target.symm, ?_, fun w => ?_⟩
  · have e : (p.cast p.source p.target).cast p.source.symm p.target.symm = p := by
      ext w
      simp
    have h := Path.Homotopic.pathCast hq p.source.symm p.target.symm
    rwa [e] at h
  · simpa using hqY w

end Push

/-- A homotopy in `Z` from `φ` to `φ'`, read on `[0, 1] × [0, 1]`, gives closed curves homotopic in
`Z`. -/
theorem closedCurvesHomotopicIn_of_path {Z : Set S} {a : Z} (z : Circle) (φ φ' : C(Circle, S))
    (p q : Path a a) (hp : ∀ t, (p t).1 = φ (arcParam z t)) (hq : ∀ t, (q t).1 = φ' (arcParam z t))
    (h : p.Homotopic q) : ClosedCurvesHomotopicIn Z φ φ' := by
  obtain ⟨H⟩ := h
  let F : C(I × I, S) := ⟨fun w => (H (w.2, w.1)).1, by fun_prop⟩
  have hlr : ∀ v, F (0, v) = F (1, v) := by
    intro v
    have h0 : H (v, 0) = p 0 := H.eq_fst v (by simp)
    have h1 : H (v, 1) = p 1 := H.eq_fst v (by simp)
    simp [F, h0, h1]
  refine ⟨cylinderLift z F hlr, ?_, ?_, ?_⟩
  · rintro ⟨w, v⟩
    obtain ⟨t, rfl⟩ := arcParam_surjective z w
    rw [cylinderLift_apply]
    exact (H (v, t)).2
  · intro w
    obtain ⟨t, rfl⟩ := arcParam_surjective z w
    rw [cylinderLift_apply, ← hp]
    simp [F]
  · intro w
    obtain ⟨t, rfl⟩ := arcParam_surjective z w
    rw [cylinderLift_apply, ← hq]
    simp [F]

/-- Homotopy of closed curves in `Z` is transitive. -/
theorem _root_.GraphMinor.Surface.ClosedCurvesHomotopicIn.trans {Z : Set S} {φ₀ φ₁ φ₂ : C(Circle,
  S)}
    (h₁ : ClosedCurvesHomotopicIn Z φ₀ φ₁) (h₂ : ClosedCurvesHomotopicIn Z φ₁ φ₂) :
    ClosedCurvesHomotopicIn Z φ₀ φ₂ := by
  obtain ⟨ψ₁, h₁Z, h₁0, h₁1⟩ := h₁
  obtain ⟨ψ₂, h₂Z, h₂0, h₂1⟩ := h₂
  have hmem₀ : ∀ x, φ₀ x ∈ Z := fun x => h₁0 x ▸ h₁Z _
  have hmem₁ : ∀ x, φ₁ x ∈ Z := fun x => h₁1 x ▸ h₁Z _
  have hmem₂ : ∀ x, φ₂ x ∈ Z := fun x => h₂1 x ▸ h₂Z _
  let f₀ : C(Circle, Z) := ⟨fun x => ⟨φ₀ x, hmem₀ x⟩, by fun_prop⟩
  let f₁ : C(Circle, Z) := ⟨fun x => ⟨φ₁ x, hmem₁ x⟩, by fun_prop⟩
  let f₂ : C(Circle, Z) := ⟨fun x => ⟨φ₂ x, hmem₂ x⟩, by fun_prop⟩
  let H₁ : ContinuousMap.Homotopy f₀ f₁ :=
    { toFun := fun p => ⟨ψ₁ (p.2, p.1), h₁Z _⟩
      continuous_toFun := by fun_prop
      map_zero_left := fun x => Subtype.ext (h₁0 x)
      map_one_left := fun x => Subtype.ext (h₁1 x) }
  let H₂ : ContinuousMap.Homotopy f₁ f₂ :=
    { toFun := fun p => ⟨ψ₂ (p.2, p.1), h₂Z _⟩
      continuous_toFun := by fun_prop
      map_zero_left := fun x => Subtype.ext (h₂0 x)
      map_one_left := fun x => Subtype.ext (h₂1 x) }
  let H := H₁.trans H₂
  refine ⟨⟨fun p => (H (p.2, p.1)).1, by fun_prop⟩, fun p => (H (p.2, p.1)).2, fun x => ?_,
    fun x => ?_⟩
  · have := H.map_zero_left x
    exact congrArg Subtype.val this
  · have := H.map_one_left x
    exact congrArg Subtype.val this

/-- A homotopy in `Z` is a homotopy in any larger set. -/
theorem _root_.GraphMinor.Surface.ClosedCurvesHomotopicIn.mono {Z Z' : Set S}
  (hZ : Z ⊆ Z') {φ₀ φ₁ : C(Circle, S)}
    (h : ClosedCurvesHomotopicIn Z φ₀ φ₁) : ClosedCurvesHomotopicIn Z' φ₀ φ₁ := by
  obtain ⟨ψ, h₁, h₂⟩ := h
  exact ⟨ψ, fun p => hZ (h₁ p), h₂⟩

/-- The last step of (3.1). If each path of `X ∪ Y` with ends in `Y` is homotopic, with its ends
fixed, to a
path in `Y`, then each closed curve in `X ∪ Y` is homotopic in `X ∪ Y` to a closed curve in `Y`. -/
theorem exists_push_of_paths {X Y : Set S} (hsc : IsSimplyConnectedSet X) (hL : IsPathConnected
  (X ∩ Y))
    (hpath : ∀ {a b : (X ∪ Y : Set S)} (p : Path a b), a.1 ∈ Y → b.1 ∈ Y →
      ∃ q : Path a b, p.Homotopic q ∧ ∀ u, (q u).1 ∈ Y)
    (φ : C(Circle, S)) (hφ : range φ ⊆ X ∪ Y) :
    ∃ φ' : C(Circle, S), range φ' ⊆ Y ∧ ClosedCurvesHomotopicIn (X ∪ Y) φ φ' := by
  by_cases hin : ∃ z, φ z ∈ Y
  · obtain ⟨z, hz⟩ := hin
    let a : (X ∪ Y : Set S) := ⟨φ z, Or.inr hz⟩
    let p : Path a a :=
      { toFun := fun t => ⟨φ (arcParam z t), hφ (mem_range_self _)⟩
        continuous_toFun := by fun_prop
        source' := by simp [a]
        target' := by simp [a] }
    obtain ⟨q, hpq, hqY⟩ := hpath p hz hz
    let f : C(I, S) := ⟨fun t => (q t).1, by fun_prop⟩
    have hf : f 0 = f 1 := by simp [f]
    refine ⟨loopLift z f hf, ?_, ?_⟩
    · rintro _ ⟨w, rfl⟩
      obtain ⟨t, rfl⟩ := arcParam_surjective z w
      rw [loopLift_apply]
      exact hqY t
    · exact closedCurvesHomotopicIn_of_path z φ _ p q (fun _ => rfl)
        (fun t => by rw [loopLift_apply]; rfl) hpq
  · -- The curve stays in `X`, so it is null-homotopic there.
    push Not at hin
    have hrX : range φ ⊆ X := by
      rintro _ ⟨z, rfl⟩
      exact (hφ (mem_range_self z)).resolve_right (hin z)
    obtain ⟨c, hc, h⟩ := hsc.2 φ hrX
    obtain ⟨y, hy⟩ := hL.nonempty
    obtain ⟨β, hβ⟩ := hsc.1.joinedIn c hc y hy.1
    refine ⟨ContinuousMap.const Circle y, ?_, (h.mono subset_union_left).trans ?_⟩
    · rintro _ ⟨_, rfl⟩
      exact hy.2
    · exact ⟨⟨fun p => β p.2, by fun_prop⟩, fun p => Or.inl (hβ _), fun _ => by simp,
        fun _ => by simp⟩

/-- **Graph Minors XI, (3.1)**, corrected (page 76). If `X, Y ⊆ Σ` are closed, and `X` is
simply-connected and `X ∩ Y` is non-empty and arc-wise connected, and moreover `X` deforms locally
into `X ∩ Y` (`IsLocalDeformationRetract`), then any continuous `φ : S¹ → X ∪ Y` is homotopic in
`X ∪ Y` to a continuous `φ' : S¹ → Y`.

The paper has no local hypothesis, and without one the statement is false (see the correction to
(3.1) in `corrections/GM11.md`). The hypothesis holds in the paper's uses: there `X` is a closed
disc and `X ∩ Y` is its boundary (`IsClosedDisc.isLocalDeformationRetract`), except in (7.8) as used
in (8.8), where `X` and `Y` are unions of vertices, edges and regions of a drawing. The space need
not be a surface. -/
theorem theorem_3_1_proof {X Y : Set S} (hX : IsClosed X) (hY : IsClosed Y)
    (hsc : IsSimplyConnectedSet X) (hL : IsPathConnected (X ∩ Y))
    (hloc : IsLocalDeformationRetract X (X ∩ Y)) (φ : C(Circle, S)) (hφ : range φ ⊆ X ∪ Y) :
    ∃ φ' : C(Circle, S), range φ' ⊆ Y ∧ ClosedCurvesHomotopicIn (X ∪ Y) φ φ' :=
  exists_push_of_paths hsc hL (fun p ha hb => exists_homotopic_path hX hY hsc hL hloc p ha hb) φ hφ

/-- A closed disc deforms into its boundary circle, with the circle fixed, once its centre is
removed. So a closed disc and its boundary satisfy the local hypothesis of (3.1). -/
theorem IsClosedDisc.isLocalDeformationRetract_of_homeomorph [T1Space S] {Δ : Set S}
    (e : ClosedUnitDisc ≃ₜ Δ) :
    IsLocalDeformationRetract Δ ((fun x => (e x).1) '' {x | x.1 ∈ UnitCircle}) := by
  rintro y ⟨w, hw, rfl⟩
  have hnorm : ∀ x : ClosedUnitDisc, ‖x.1‖ ≤ 1 := fun x => mem_closedBall_zero_iff.mp x.2
  let c : ClosedUnitDisc := ⟨0, by simp [ClosedUnitDisc]⟩
  refine ⟨{(e c).1}ᶜ, isOpen_compl_singleton, ?_, ?_⟩
  · rintro hy
    have heq : e w = e c := Subtype.ext hy
    have hwc : w = c := e.injective heq
    have : ‖w.1‖ = 1 := mem_sphere_zero_iff_norm.mp hw
    simp [hwc, c] at this
  let u : (Δ ∩ {(e c).1}ᶜ : Set S) → EuclideanPlane := fun x => (e.symm ⟨x.1, x.2.1⟩).1
  have hu : Continuous u := by fun_prop
  have hu0 : ∀ x, ‖u x‖ ≠ 0 := by
    intro x h0
    have h1 : u x = 0 := norm_eq_zero.mp h0
    have h2 : e.symm ⟨x.1, x.2.1⟩ = c := Subtype.ext h1
    have h3 := e.apply_symm_apply ⟨x.1, x.2.1⟩
    rw [h2] at h3
    exact x.2.2 (congrArg Subtype.val h3).symm
  have hu1 : ∀ x, ‖u x‖ ≤ 1 := fun x => hnorm _
  let g : (Δ ∩ {(e c).1}ᶜ : Set S) × I → EuclideanPlane := fun p =>
    ((1 - (p.2 : ℝ)) + (p.2 : ℝ) / ‖u p.1‖) • u p.1
  have hgcont : Continuous g := by
    have h0 : Continuous fun p : (Δ ∩ {(e c).1}ᶜ : Set S) × I => u p.1 :=
      hu.comp continuous_fst
    have h1 : Continuous fun p : (Δ ∩ {(e c).1}ᶜ : Set S) × I => (p.2 : ℝ) :=
      continuous_subtype_val.comp continuous_snd
    have h2 : Continuous fun p : (Δ ∩ {(e c).1}ᶜ : Set S) × I => ‖u p.1‖ := h0.norm
    have h3 : Continuous fun p : (Δ ∩ {(e c).1}ᶜ : Set S) × I =>
        (1 - (p.2 : ℝ)) + (p.2 : ℝ) / ‖u p.1‖ :=
      (continuous_const.sub h1).add (h1.div h2 fun p => hu0 _)
    exact h3.smul h0
  have hgnorm : ∀ p, ‖g p‖ = (1 - (p.2 : ℝ)) * ‖u p.1‖ + p.2 := by
    intro p
    have h0 := hu0 p.1
    have ht0 := p.2.2.1
    have ht1 := p.2.2.2
    have hc : 0 ≤ (1 - (p.2 : ℝ)) + (p.2 : ℝ) / ‖u p.1‖ :=
      add_nonneg (by linarith) (div_nonneg ht0 (norm_nonneg _))
    simp only [g, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    field_simp
  have hgmem : ∀ p, g p ∈ ClosedUnitDisc := by
    intro p
    rw [ClosedUnitDisc, mem_closedBall_zero_iff, hgnorm]
    have ht0 := p.2.2.1
    have ht1 := p.2.2.2
    nlinarith [hu1 p.1]
  refine ⟨⟨fun p => (e ⟨g p, hgmem p⟩).1, by fun_prop⟩, fun p => (e _).2, fun x => ?_, fun x => ?_,
    fun x t hx => ?_⟩
  · have : g (x, 0) = u x := by simp [g]
    simp only [ContinuousMap.coe_mk]
    have h2 : (⟨g (x, 0), hgmem _⟩ : ClosedUnitDisc) = e.symm ⟨x.1, x.2.1⟩ := Subtype.ext this
    rw [h2, e.apply_symm_apply]
  · refine ⟨⟨g (x, 1), hgmem _⟩, ?_, rfl⟩
    change g (x, 1) ∈ UnitCircle
    rw [UnitCircle, mem_sphere_zero_iff_norm, hgnorm]
    simp
  · obtain ⟨w', hw', hxw⟩ := hx
    have hx' : e.symm ⟨x.1, x.2.1⟩ = w' := by
      rw [e.symm_apply_eq]
      exact Subtype.ext hxw.symm
    have hn : ‖u x‖ = 1 := by
      have : u x = w'.1 := by simp only [u, hx']
      rw [this]
      exact mem_sphere_zero_iff_norm.mp hw'
    have : g (x, t) = u x := by
      simp [g, hn]
    simp only [ContinuousMap.coe_mk]
    have h2 : (⟨g (x, t), hgmem _⟩ : ClosedUnitDisc) = e.symm ⟨x.1, x.2.1⟩ := Subtype.ext this
    rw [h2, e.apply_symm_apply]

/-- A closed disc and its boundary satisfy the local hypothesis of (3.1). -/
theorem IsClosedDisc.isLocalDeformationRetract [T1Space S]
    {Δ : Set S} (hΔ : IsClosedDisc Δ) : IsLocalDeformationRetract Δ (discBd Δ) := by
  obtain ⟨e⟩ := hΔ
  rw [disc_boundary Δ e]
  exact IsClosedDisc.isLocalDeformationRetract_of_homeomorph e

end GraphMinor.GM11
