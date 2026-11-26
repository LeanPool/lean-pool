/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.R434.RoleMatchings
public import Mathlib.Data.Sym.Card
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-! Shared midpoint hosts for a matching of role pairs in one bipartite layer. -/

@[expose] public section
namespace GapExtremal.R434.H54
open Finset

/-- An edge is indexed with its lower color first. -/
def orderedIndex (a b : Role) : Edge :=
  if a.1 < b.1 then (edgeKind a.1 b.1, a.2, b.2)
  else (edgeKind b.1 a.1, b.2, a.2)

/-- The edge kind and matching colour for a pair of roles. -/
def matchingClass (a b : Role) : Fin 3 × Fin 4 :=
  let e := orderedIndex a b
  (e.1, edgeColour e.1 e.2.1 e.2.2)

private theorem matchingClass_of_order {a b : Role} (h : a.1 < b.1) :
    matchingClass a b = (edgeKind a.1 b.1, edgeColour (edgeKind a.1 b.1) a.2 b.2) := by
  simp only [matchingClass, orderedIndex, ite_eq_left h]

theorem matchingClass_symm : ∀ a b : Role,
    roleGraph.Adj a b → matchingClass a b = matchingClass b a := by
  intro a b hab
  change orderedAdj a b ∨ orderedAdj b a at hab
  rcases hab with h | h
  · simp only [matchingClass, orderedIndex, ite_eq_left h.1, ite_eq_right (not_lt_of_gt h.1)]
  · simp only [matchingClass, orderedIndex, ite_eq_left h.1, ite_eq_right (not_lt_of_gt h.1)]

theorem matchingClass_parts : ∀ a b : Role, roleGraph.Adj a b →
    let k := (matchingClass a b).1
    (a.1 = lowerPart k ∧ b.1 = upperPart k) ∨ (a.1 = upperPart k ∧ b.1 = lowerPart k) := by
  intro a b hab
  dsimp only
  change orderedAdj a b ∨ orderedAdj b a at hab
  rcases hab with h | h
  · rw [matchingClass_of_order h.1]
    exact Or.inl ⟨(parts_of_order h.1).1.symm, (parts_of_order h.1).2.symm⟩
  · rw [matchingClass_symm a b (Or.inr h), matchingClass_of_order h.1]
    exact Or.inr ⟨(parts_of_order h.1).2.symm, (parts_of_order h.1).1.symm⟩

theorem matchingClass_partner : ∀ a b c : Role, roleGraph.Adj a b → roleGraph.Adj a c →
    matchingClass a b = matchingClass a c → b = c := by
  intro a b c hab hac heq
  have forward : ∀ {x y z : Role}, orderedAdj x y → orderedAdj x z →
      matchingClass x y = matchingClass x z → y = z := by
    intro x y z hxy hxz he
    rw [matchingClass_of_order hxy.1, matchingClass_of_order hxz.1] at he
    have hk := congrArg Prod.fst he
    have hcolor := congrArg Prod.snd he
    dsimp only at hk hcolor
    rw [← hk] at hcolor
    have hmem := hxz.2
    rw [← hk] at hmem
    exact Prod.ext ((parts_of_order hxy.1).2.symm.trans
      (hk.symm ▸ (parts_of_order hxz.1).2))
      (edgeColour_left _ _ _ _ hxy.2 hmem hcolor)
  have reverse : ∀ {x y z : Role}, orderedAdj y x → orderedAdj z x →
      matchingClass y x = matchingClass z x → y = z := by
    intro x y z hyx hzx he
    rw [matchingClass_of_order hyx.1, matchingClass_of_order hzx.1] at he
    have hk := congrArg Prod.fst he
    have hcolor := congrArg Prod.snd he
    dsimp only at hk hcolor
    rw [← hk] at hcolor
    have hmem := hzx.2
    rw [← hk] at hmem
    exact Prod.ext ((parts_of_order hyx.1).1.symm.trans
      (hk.symm ▸ (parts_of_order hzx.1).1))
      (edgeColour_right _ _ _ _ hyx.2 hmem hcolor)
  have incompatible : ∀ {x y z : Role}, orderedAdj x y → orderedAdj z x →
      matchingClass x y ≠ matchingClass z x := by
    intro x y z hxy hzx he
    rw [matchingClass_of_order hxy.1, matchingClass_of_order hzx.1] at he
    have hk := congrArg Prod.fst he
    dsimp only at hk
    exact (part_lt (edgeKind x.1 y.1)).ne
      ((parts_of_order hxy.1).1.trans (hk.symm ▸ (parts_of_order hzx.1).2.symm))
  change orderedAdj a b ∨ orderedAdj b a at hab
  change orderedAdj a c ∨ orderedAdj c a at hac
  rcases hab with hab | hab <;> rcases hac with hac | hac
  · exact forward hab hac heq
  · rw [matchingClass_symm a c (Or.inr hac)] at heq
    exact (incompatible hab hac heq).elim
  · rw [matchingClass_symm a b (Or.inr hab)] at heq
    exact (incompatible hac hab heq.symm).elim
  · rw [matchingClass_symm a b (Or.inr hab), matchingClass_symm a c (Or.inr hac)] at heq
    exact reverse hab hac heq

/-- An unordered pair of roles that is absent from the template edge set. -/
abbrev MissingRolePair := {p : Sym2 Role // p ∉ roleGraph.edgeSet}

noncomputable instance : Fintype MissingRolePair := Fintype.ofFinite _

private def rolePair (e : Edge) : Sym2 Role :=
  s((lowerPart e.1, e.2.1), (upperPart e.1, e.2.2))

private theorem rolePair_injective : Function.Injective rolePair := by
  intro ⟨k,a,b⟩ ⟨l,c,d⟩ he
  rcases Sym2.eq_iff.mp he with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · have hlo : lowerPart k = lowerPart l := congrArg Prod.fst ha
    have hup : upperPart k = upperPart l := congrArg Prod.fst hb
    have hk : k = l := by
      rw [← kind_of_parts k, ← kind_of_parts l, hlo, hup]
    have ha' : a = c := congrArg Prod.snd ha
    have hb' : b = d := congrArg Prod.snd hb
    subst l
    subst c
    subst d
    rfl
  · have hlo : lowerPart k = upperPart l := congrArg Prod.fst ha
    have hup : upperPart k = lowerPart l := congrArg Prod.fst hb
    have hlt := part_lt k
    rw [hlo, hup] at hlt
    exact ((part_lt l).asymm hlt).elim

private theorem role_edgeFinset : roleGraph.edgeFinset = edges.image rolePair := by
  classical
  ext p
  refine p.inductionOn (fun a b => ?_)
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  constructor
  · intro hab
    have ordered (u v : Role) (hlt : u.1 < v.1) (hmem : (edgeKind u.1 v.1,u.2,v.2) ∈ edges) :
        s(u,v) ∈ edges.image rolePair := by
      have hparts := parts_of_order hlt
      exact mem_image.mpr ⟨_,hmem, by
        simp [rolePair, hparts.1, hparts.2]⟩
    change orderedAdj a b ∨ orderedAdj b a at hab
    rcases hab with hab | hab
    · exact ordered a b hab.1 hab.2
    · rw [Sym2.eq_swap]
      exact ordered b a hab.1 hab.2
  · intro hp
    obtain ⟨e,he,heq⟩ := mem_image.mp hp
    have hadj : roleGraph.Adj (lowerPart e.1,e.2.1) (upperPart e.1,e.2.2) := by
      rw [roleGraph_ordered (part_lt e.1)]
      simpa [kind_of_parts] using he
    have hm : rolePair e ∈ roleGraph.edgeSet := hadj
    exact (SimpleGraph.mem_edgeSet (G := roleGraph)).mp (heq ▸ hm)

theorem missing_role_count : Fintype.card MissingRolePair = 66 := by
  have h : Fintype.card roleGraph.edgeSet = 54 := by
    rw [← SimpleGraph.edgeFinset_card, role_edgeFinset, card_image_of_injective _
      rolePair_injective,
      edge_count]
  rw [Fintype.card_subtype_compl (fun p => p ∈ roleGraph.edgeSet), h, Sym2.card]
  norm_num [Role, Nat.choose_two_right]

section
variable {R C : Type} [Fintype R] [DecidableEq R] [CommRing R]
variable (h : R)

/-- A grouped host index consisting of a role-pair label and an affine coordinate. -/
abbrev GroupedHost (R C : Type) := (MissingRolePair ⊕ ((Fin 3 × Fin 4) × C)) × R

/-- For a geometric role edge use a matching label. For any other pair keep its role type. -/
def groupedAssign (χ : R → C) (x y : Role × R) : GroupedHost R C :=
  (if ha : roleGraph.Adj x.1 y.1 then .inr (matchingClass x.1 y.1, χ (pairDirection (roleStep h) x
    y))
    else .inl ⟨s(x.1,y.1),fun hp => ha hp⟩, h * (x.2 + y.2))

omit [DecidableEq R] [Fintype R] in
theorem groupedAssign_symm (χ : R → C) (x y : Role × R) :
    groupedAssign h χ x y = groupedAssign h χ y x := by
  have ha : roleGraph.Adj y.1 x.1 ↔ roleGraph.Adj x.1 y.1 := ⟨fun h => h.symm, fun h => h.symm⟩
  by_cases hp : roleGraph.Adj x.1 y.1
  · simp [groupedAssign, ha, hp, matchingClass_symm _ _ hp,
      pairDirection_swap _ (roleStep_swap h), add_comm y.2 x.2]
  · simp [groupedAssign, ha, hp, Sym2.eq_swap (a := y.1), add_comm y.2 x.2]

/-- The vertices assigned to the given grouped host. -/
noncomputable def groupedPalette (A : Finset R) (χ : R → C) (k : GroupedHost R C) :
    Finset (Role × R) := by
  classical
  exact univ.filter fun x => ∃ y, x ≠ y ∧ ¬ (directionCore roleGraph (roleStep h) A (roleStep_swap
    h)).Adj x y ∧
    groupedAssign h χ x y = k

private theorem cross_colours {a a' b b' : Role}
    (ha : roleGraph.Adj a a') (hb : roleGraph.Adj b b') (hab : roleGraph.Adj a b)
    (eq : matchingClass a a' = matchingClass b b') : a.1 = b'.1 ∧ a'.1 = b.1 := by
  have hne : a.1 ≠ b.1 := by
    change orderedAdj a b ∨ orderedAdj b a at hab
    exact hab.elim (fun hu => ne_of_lt hu.1) (fun hv => ne_of_gt hv.1)
  have h₁ := matchingClass_parts _ _ ha
  have h₂ := matchingClass_parts _ _ hb
  rw [← eq] at h₂
  rcases h₁ with ⟨h₁,h₁'⟩ | ⟨h₁,h₁'⟩ <;>
    rcases h₂ with ⟨h₂,h₂'⟩ | ⟨h₂,h₂'⟩
  · exact False.elim (hne (h₁.trans h₂.symm))
  · exact ⟨h₁.trans h₂'.symm,h₁'.trans h₂.symm⟩
  · exact ⟨h₁.trans h₂'.symm,h₁'.trans h₂.symm⟩
  · exact False.elim (hne (h₁.trans h₂.symm))

omit [DecidableEq R] in
theorem grouped_host_hyp (A : Finset R) (hh : 2 * h = 1) (χ : R → C)
    (hχ : ∀ a b, a ∉ A → b ∉ A → χ a = χ b → h * (a + b) ∉ A) :
    HostHyp (directionCore roleGraph (roleStep h) A (roleStep_swap h))
      (groupedPalette h A χ) (groupedAssign h χ) := by
  classical
  constructor
  · intro k x hx y hy hxy
    obtain ⟨x', _, ha, hk⟩ := (mem_filter.mp hx).2
    obtain ⟨y', _, hb, hk'⟩ := (mem_filter.mp hy).2
    have eq := hk.trans hk'.symm
    have sameMid := congrArg Prod.snd eq
    change h * (x.2 + x'.2) = h * (y.2 + y'.2) at sameMid
    have groups := congrArg Prod.fst eq
    change roleGraph.Adj x.1 y.1 ∧ pairDirection (roleStep h) x y ∈ A at hxy
    by_cases hp : roleGraph.Adj x.1 x'.1 <;> by_cases hq : roleGraph.Adj y.1 y'.1
    · simp only [groupedAssign, dite_eq_left hp, dite_eq_left hq, Sum.inr.injEq, Prod.mk.injEq]
        at groups
      obtain ⟨hclass,hcolour⟩ := groups
      obtain ⟨hfirst,hsecond⟩ := cross_colours hp hq hxy.1 hclass
      have s₁ : roleStep h x.1 x'.1 = roleStep h x.1 y.1 := by unfold roleStep; rw [hsecond]
      have s₂ : roleStep h y.1 y'.1 = -roleStep h x.1 y.1 := by
        rw [← roleStep_swap]; unfold roleStep; rw [hfirst]
      have hm := congrArg (fun t : R => 2 * t) sameMid
      simp only [← mul_assoc, hh, one_mul] at hm
      have cross : pairDirection (roleStep h) x y =
          h * (pairDirection (roleStep h) x x' + pairDirection (roleStep h) y y') := by
        unfold pairDirection
        rw [s₁,s₂]
        calc
          _ = (2 * h) * (roleStep h x.1 y.1 * (y.2-x.2)) := by rw [hh,one_mul]
          _ = _ := by linear_combination -(h * roleStep h x.1 y.1) * hm
      exact hχ _ _ (fun ht => ha ⟨hp,ht⟩) (fun ht => hb ⟨hq,ht⟩) hcolour (cross ▸ hxy.2)
    · simp [groupedAssign, hp, hq] at groups
    · simp [groupedAssign, hp, hq] at groups
    · simp only [groupedAssign, dite_eq_right hp, dite_eq_right hq, Sum.inl.injEq,
      Subtype.mk.injEq] at groups
      rcases Sym2.eq_iff.mp groups with ⟨hr,_⟩ | ⟨_,hr⟩
      · exact roleGraph.loopless.irrefl _ (hr ▸ hxy.1)
      · exact hp (hr.symm ▸ hxy.1)
  · intro x y hne hno
    exact ⟨mem_filter.mpr ⟨mem_univ _, y, hne, hno, rfl⟩,
      mem_filter.mpr ⟨mem_univ _, x, hne.symm, fun hh => hno hh.symm, groupedAssign_symm h χ y x⟩⟩
  · exact groupedAssign_symm h χ
  · intro x y y' _ _ _ _ eq
    have groups := congrArg Prod.fst eq
    have hr : y.1 = y'.1 := by
      by_cases hp : roleGraph.Adj x.1 y.1 <;> by_cases hq : roleGraph.Adj x.1 y'.1
      · simp only [groupedAssign, dite_eq_left hp, dite_eq_left hq, Sum.inr.injEq, Prod.mk.injEq]
        at groups
        exact matchingClass_partner _ _ _ hp hq groups.1
      · simp [groupedAssign, hp, hq] at groups
      · simp [groupedAssign, hp, hq] at groups
      · simp only [groupedAssign, dite_eq_right hp, dite_eq_right hq, Sum.inl.injEq,
        Subtype.mk.injEq] at groups
        rcases Sym2.eq_iff.mp groups with ⟨_,he⟩ | ⟨he₁,he₂⟩
        · exact he
        · exact he₂.trans he₁
    exact Prod.ext hr (midpoint_partner_unique h x.2 y.2 y'.2 hh (congrArg Prod.snd eq))

end
end GapExtremal.R434.H54
