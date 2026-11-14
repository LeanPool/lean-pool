/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Data.ZMod.Basic

public import LeanPool.ApollonianSuperharmonic.SimpleGridCycle
public import Mathlib.Data.List.TakeWhile

-- [TABLET NODE: P3963T1MixedBoundaryCycle]

/-!
# P3963T1MixedBoundaryCycle

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace MixedBoundaryCycleProof

private theorem rotate_chain :
    ∀ (p : List GaussianInt), ∀ (k : Nat), ∀ (a : GaussianInt), ∀ (b : GaussianInt), (p.head? =
        some a) → ((p.getLast? = some b) → ((FourNeighborAdjacent b a) → ((p.IsChain
        FourNeighborAdjacent) → ((k < p.length) → ((p.rotate k).IsChain FourNeighborAdjacent)))))
            := by
  classical
  intro p k a b hh ht hc hchain hk
  by_cases hz : k = 0
  · simp only [hz, List.rotate_zero]
    exact hchain
  · have hp : 0 < k := Nat.pos_of_ne_zero hz
    rw [List.rotate_eq_drop_append_take (Nat.le_of_lt hk)]
    apply List.isChain_append.mpr
    refine ⟨hchain.drop k, hchain.take k, ?_⟩
    intro u hu v hv
    have hu' : u ∈ p.getLast? := by
      simpa only [List.getLast?_drop, ite_eq_right (Nat.not_le_of_gt hk)] using hu
    have hv' : v ∈ p.head? := by
      simpa only [List.head?_take, ite_eq_right (Nat.ne_of_gt hp)] using hv
    simp_all

private theorem sourceEdgeChain :
    ∀ (p : List GaussianInt), ∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (E : Set (Finset
        GaussianInt)), (p.head? = some a) → ((p.getLast? = some b) → ((({b, a} : Finset
        GaussianInt) ∈ E) → ((∀ u, ∀ v, ∀ l₁, ∀ l₂, p = l₁ ++ u :: v :: l₂ → ({u, v} : Finset
            GaussianInt)
        ∈ E) → (Cycle.Chain (fun u v => ({u, v} : Finset GaussianInt) ∈ E) (p : Cycle
        GaussianInt))))) := by
  classical
  intro p a b E hh ht hcloseE hedges
  have hsource : p.IsChain (fun u v => ({u, v} : Finset GaussianInt) ∈ E) := by
    rw [List.isChain_iff_forall_rel_of_append_cons_cons]
    intro u v l₁ l₂ heq
    exact hedges u v l₁ l₂ heq
  have hfull : (p ++ [a]).IsChain (fun u v => ({u, v} : Finset GaussianInt) ∈ E) := by
    apply List.IsChain.append hsource (by simp)
    intro u hu v hv
    have hu' : u = b := by simpa [ht] using hu.symm
    have hv' : v = a := by simpa using hv.symm
    subst u
    subst v
    exact hcloseE
  obtain ⟨tail, hshape⟩ := (List.head?_eq_some_iff).mp hh
  rw [hshape, Cycle.chain_coe_cons]
  simpa [hshape] using hfull

private theorem hc₁x :
    ∀ (p₁ : List GaussianInt), ∀ (x : GaussianInt), (x ∈ p₁) → (∀ (z : GaussianInt), (z ≠ x) → (
    let c₁ := p₁.rotate (p₁.idxOf z)
    (c₁.head? = some z) → (x ∈ c₁.tail))) := by
  classical
  intro p₁ x hx₁ z hzx c₁ hrot₁z
  have hmemx : x ∈ c₁ := by
    simpa [c₁] using
      (List.mem_rotate (l := p₁) (a := x) (n := p₁.idxOf z)).mpr hx₁
  obtain ⟨tl, ht⟩ := (List.head?_eq_some_iff).mp (by simpa [c₁] using hrot₁z)
  simp only [c₁] at hmemx
  rw [ht] at hmemx
  simp only [List.mem_cons] at hmemx
  rcases hmemx with h | h
  · exact (hzx h.symm).elim
  · simpa [c₁, ht] using h

private theorem rotatedPrefixesDisjoint {α : Type*} [DecidableEq α]
    (V : Set α) (p c : List α) (x z : α)
    (hV : V = (p.toFinset : Set α)) (hc : c = p.rotate (p.idxOf z))
    (hshape : c = z :: c.tail) (other : List α)
    (hx : x ∉ c.tail.takeWhile (fun w => decide (w ≠ x)))
    (hz : z ∉ c.tail.takeWhile (fun w => decide (w ≠ x))) :
    ∀ v ∈ x :: (other.takeWhile
      (fun w => @decide (w ∉ V) (Classical.propDecidable _)) ++ [z]),
      ∀ w ∈ c.tail.takeWhile (fun w => decide (w ≠ x)), v ≠ w := by
  classical
  intro v hv w hw heq
  subst w
  have hvV : v ∈ V := by
    have hvtail : v ∈ c.tail := List.takeWhile_subset _ hw
    have hvc : v ∈ c := by
      rw [hshape]
      exact List.mem_cons_of_mem z hvtail
    rw [hc] at hvc
    have hvp : v ∈ p := (List.mem_rotate (l := p) (a := v) (n := p.idxOf z)).mp hvc
    rw [hV]
    exact List.mem_toFinset.mpr hvp
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | hv | rfl
  · exact hx hw
  · have hvnot : v ∉ V := by simpa using List.mem_takeWhile_imp hv
    exact hvnot hvV
  · exact hz hw

private theorem parityStep :
    let parity (u : GaussianInt) : ZMod 2 := (u.re : ZMod 2) + (u.im : ZMod 2)
    ∀ {u : GaussianInt}, ∀ {w : GaussianInt}, (FourNeighborAdjacent u w) → (parity w = parity u +
        1) := by
  classical
  intro parity u w h
  have hneg : (-1 : ZMod 2) = 1 := by decide
  rcases h with h | h | h | h
  · rw [h]
    simp [parity, Zsqrtd.re_add, Zsqrtd.im_add]
    ring
  · rw [h]
    simp [parity, Zsqrtd.re_sub, Zsqrtd.im_sub]
    ring_nf
    rw [hneg]
  · rw [h]
    simp [parity, Zsqrtd.re_add, Zsqrtd.im_add]
    ring
  · rw [h]
    simp [parity, Zsqrtd.re_sub, Zsqrtd.im_sub]
    ring_nf
    rw [hneg]

private theorem hpNotTwo :
    ∀ (V₁ : Set GaussianInt),
      ∀ (E₁ : Set (Finset GaussianInt)),
        ∀ (E₂ : Set (Finset GaussianInt)),
          Disjoint E₁ E₂ →
            ∀ (p₁ : List GaussianInt),
              ∀ (p₂ : List GaussianInt),
                ∀ (x : GaussianInt),
                  let c₂ := p₂.rotate (p₂.idxOf x)
                  let good (z : GaussianInt) : Bool :=
                    @decide (z ∉ V₁) (Classical.propDecidable _)
                  ∀ (z : GaussianInt),
                    let c₁ := p₁.rotate (p₁.idxOf z)
                    let good₁ (w : GaussianInt) : Bool := decide (w ≠ x)
                    GaussianInt →
                      let R := z :: (c₁.tail.takeWhile good₁ ++ [x])
                      let prefix₂ := c₂.tail.takeWhile good
                      let prefix₁ := c₁.tail.takeWhile good₁
                      let Q := x :: (prefix₂ ++ [z])
                      (Q.IsChain fun u v => ({ u, v } : Finset GaussianInt) ∈ E₂) →
                        (R.IsChain fun u v => ({ u, v } : Finset GaussianInt) ∈ E₁) →
                          let p := Q ++ prefix₁
                          p.length ≠ 2 := by
  classical
  intro V₁ E₁ E₂ hdisjoint p₁ p₂ x c₂ good z c₁ good₁ w R prefix₂ prefix₁ Q hQedge hRedge p hlen
  have hlenparts : Q.length + prefix₁.length = 2 := by simpa [p, List.length_append] using hlen
  have hQlen : Q.length = prefix₂.length + 2 := by simp [Q]
  have hpref₂ : prefix₂ = [] := by
    have : prefix₂.length = 0 := by omega
    exact List.eq_nil_iff_length_eq_zero.mpr this
  have hpref₁ : prefix₁ = [] := by
    have : prefix₁.length = 0 := by omega
    exact List.eq_nil_iff_length_eq_zero.mpr this
  have hQeq : Q = [x, z] := by simp [Q, hpref₂]
  have hReq : R = [z, x] := by simp [R, prefix₁, hpref₁]
  have he₂ : ({x, z} : Finset GaussianInt) ∈ E₂ := by
    have hq : ([x, z] : List GaussianInt).IsChain
        (fun u w => ({u, w} : Finset GaussianInt) ∈ E₂) := by
      simpa [hQeq] using hQedge
    simpa using (List.isChain_pair.mp hq)
  have he₁ : ({x, z} : Finset GaussianInt) ∈ E₁ := by
    have hr : ([z, x] : List GaussianInt).IsChain
        (fun u w => ({u, w} : Finset GaussianInt) ∈ E₁) := by
      simpa [hReq] using hRedge
    simpa [Finset.pair_comm] using (List.isChain_pair.mp hr)
  exact (Set.disjoint_left.mp hdisjoint) he₁ he₂

private theorem hpNotThree :
    ∀ (V₁ : Set GaussianInt), ∀ (p₁ : List GaussianInt), ∀ (p₂ : List GaussianInt), ∀ (x :
        GaussianInt),
    let c₂ := p₂.rotate (p₂.idxOf x)
    let good (z : GaussianInt) : Bool := @decide (z ∉ V₁) (Classical.propDecidable _)
    ∀ (z : GaussianInt),
    let c₁ := p₁.rotate (p₁.idxOf z)
    let good₁ (w : GaussianInt) : Bool := decide (w ≠ x)
    (GaussianInt) → (
    let prefix₂ := c₂.tail.takeWhile good
    let prefix₁ := c₁.tail.takeWhile good₁
    let Q := x :: (prefix₂ ++ [z])
    let p := Q ++ prefix₁
    ∀ (hpne : p ≠ []), (FourNeighborAdjacent (p.getLast hpne) x) → ((p.head? = some x) → (
    let parity (u : GaussianInt) : ZMod 2 := (u.re : ZMod 2) + (u.im : ZMod 2)
    (∀ {u : GaussianInt}, ∀ {w : GaussianInt}, (FourNeighborAdjacent u w) → (parity w = parity u
        + 1)) → ((∀ a, ∀ b, ∀ l₁, ∀ l₂, p = l₁ ++ a :: b :: l₂ → FourNeighborAdjacent a b) →
            (p.length ≠
        3))))) := by
  classical
  intro V₁ p₁ p₂ x c₂ good z c₁ good₁ w prefix₂ prefix₁ Q p hpne hcloseP hphead parity parityStep
      hadjP hlen
  obtain ⟨u, w, t, hshape⟩ := List.length_eq_three.mp hlen
  have huw : FourNeighborAdjacent u w := hadjP u w [] [t] (by simp [hshape])
  have hwt : FourNeighborAdjacent w t := hadjP w t [u] [] (by simp [hshape])
  have hxu : x = u := by
    have hh := hphead
    rw [hshape] at hh
    exact (Option.some.inj hh).symm
  have htu : FourNeighborAdjacent t u := by simpa [hshape, hxu] using hcloseP
  have hparity : parity u = parity u + 1 := by
    calc
      parity u = parity t + 1 := parityStep htu
      _ = (parity w + 1) + 1 := by rw [parityStep hwt]
      _ = ((parity u + 1) + 1) + 1 := by rw [parityStep huw]
      _ = parity u + 1 := by
        have h31 : (3 : ZMod 2) = 1 := by decide
        ring_nf
        rw [h31]
  have hzero : (0 : ZMod 2) = 1 := by
    have h' : parity u + 0 = parity u + 1 := by simpa only [add_zero] using hparity
    exact add_left_cancel h'
  norm_num at hzero

private theorem hlastE₁ :
    ∀ (V₁ : Set GaussianInt), ∀ (E₁ : Set (Finset GaussianInt)), ∀ (p₁ : List GaussianInt), ∀ (p₂
        : List GaussianInt), ∀ (x : GaussianInt),
    let c₂ := p₂.rotate (p₂.idxOf x)
    let good (z : GaussianInt) : Bool := @decide (z ∉ V₁) (Classical.propDecidable _)
    ∀ (z : GaussianInt),
    let c₁ := p₁.rotate (p₁.idxOf z)
    let good₁ (w : GaussianInt) : Bool := decide (w ≠ x)
    (GaussianInt) → (
    let R := z :: (c₁.tail.takeWhile good₁ ++ [x])
    let prefix₂ := c₂.tail.takeWhile good
    let prefix₁ := c₁.tail.takeWhile good₁
    let Q := x :: (prefix₂ ++ [z])
    (Q.getLast? = some z) → ((R.tail.IsChain (fun u v => ({u, v} : Finset GaussianInt) ∈ E₁)) →
        ((∀ v ∈ R.tail.head?, ({z, v} : Finset GaussianInt) ∈ E₁) → (
    let p := Q ++ prefix₁
    ∀ (hpne : p ≠ []), (R.tail = prefix₁ ++ [x]) → (
    let v := p.getLast hpne
    ({v, x} : Finset GaussianInt) ∈ E₁))))) := by
  classical
  intro V₁ E₁ p₁ p₂ x c₂ good z c₁ good₁ w R prefix₂ prefix₁ Q hQlast hRtailE₁ hRstepE₁ p hpne
      hRtail v
  cases hpref : prefix₁ with
  | nil =>
      have hpLast? : p.getLast? = some z := by simpa [p, hpref] using hQlast
      have hpLast : p.getLast hpne = z :=
        (List.getLast_eq_iff_getLast?_eq_some hpne).2 hpLast?
      have hxheadR : x ∈ R.tail.head? := by simp [hRtail, hpref]
      have h := hRstepE₁ x hxheadR
      simpa [v, hpLast, Finset.pair_comm] using h
  | cons c cs =>
      have hpre : prefix₁ ≠ [] := by rw [hpref]; simp
      have htailChain : (prefix₁ ++ [x]).IsChain
          (fun u w => ({u, w} : Finset GaussianInt) ∈ E₁) := by
        simpa [hRtail] using hRtailE₁
      have hlastRel := htailChain.rel_getLast_head_of_append hpre (by simp)
      have hpLast : p.getLast hpne = prefix₁.getLast hpre := by
        apply (List.getLast_eq_iff_getLast?_eq_some hpne).2
        simpa [p, hpref] using (List.getLast?_eq_some_getLast hpre)
      simpa [v, hpLast] using hlastRel

end MixedBoundaryCycleProof

namespace MixedCycleDetails

private theorem hcommon :
    ∀ (V₁ : Set GaussianInt), ∀ (V₂ : Set GaussianInt), (¬(V₁ ∩ V₂).Subsingleton) → (∃ x y :
        GaussianInt, x ∈ V₁ ∩ V₂ ∧ y ∈ V₁ ∩ V₂ ∧ x ≠ y) := by
  classical
  intro V₁ V₂ hmultiple
  by_contra hn
  apply hmultiple
  intro x hx y hy
  by_contra hxy
  exact hn ⟨x, y, hx, hy, hxy⟩

private theorem hx₁ :
    ∀ (V₁ : Set GaussianInt), ∀ (V₂ : Set GaussianInt), ∀ (p₁ : List GaussianInt), (V₁ =
        (↑p₁.toFinset : Set GaussianInt)) → (∀ (x : GaussianInt), (x ∈ V₁ ∩ V₂) → (x ∈ p₁)) := by
  classical
  intro V₁ V₂ p₁ hV₁ x hx
  rw [hV₁] at hx
  exact List.mem_toFinset.mp hx.1

private theorem hx₂ :
    ∀ (V₁ : Set GaussianInt), ∀ (V₂ : Set GaussianInt), ∀ (p₂ : List GaussianInt), (V₂ =
        (↑p₂.toFinset : Set GaussianInt)) → (∀ (x : GaussianInt), (x ∈ V₁ ∩ V₂) → (x ∈ p₂)) := by
  classical
  intro V₁ V₂ p₂ hV₂ x hx
  rw [hV₂] at hx
  exact List.mem_toFinset.mp hx.2

private abbrev hy₂ := ApollonianSuperharmonic.MixedCycleDetails.hx₂

private theorem hrot₁x :
    ∀ (p₁ : List GaussianInt), ∀ (x : GaussianInt), (x ∈ p₁) → ((p₁.idxOf x < p₁.length) →
        ((p₁.rotate (p₁.idxOf x)).head? = some x)) := by
  classical
  intro p₁ x hx₁ hidx₁x
  rw [List.head?_rotate hidx₁x]
  exact List.getElem?_idxOf hx₁

private abbrev hrot₂x := ApollonianSuperharmonic.MixedCycleDetails.hrot₁x

private theorem cycle_chain :
    ∀ (p : List GaussianInt),
      (∀ u, ∀ v, ∀ l₁, ∀ l₂, p = l₁ ++ u :: v :: l₂ → FourNeighborAdjacent u v) →
        p.IsChain FourNeighborAdjacent := by
  classical
  intro p hadj
  rw [List.isChain_iff_forall_rel_of_append_cons_cons]
  intro u v l₁ l₂ heq
  exact hadj u v l₁ l₂ heq

private theorem takeArc :
    ∀ {α : Type}, ∀ (a : α), ∀ (b : α), ∀ (u : List α), ∀ (v : List α), a :: (u ++ [b]) =
        List.take (u.length + 2) (a :: (u ++ b :: v)) := by
  classical
  intro α a b u v
  congr 1
  induction u with
  | nil => simp
  | cons d u ih => simp [ih, Nat.add_assoc]

private theorem hc₂y :
    ∀ (p₂ : List GaussianInt), ∀ (x : GaussianInt), ∀ (y : GaussianInt), (y ∈ p₂) → (
    let c₂ := p₂.rotate (p₂.idxOf x)
    y ∈ c₂) := by
  classical
  intro p₂ x y hy₂ c₂
  rw [List.mem_rotate]
  exact hy₂

private theorem hc₂tail :
    ∀ (p₂ : List GaussianInt), ∀ (x : GaussianInt), ∀ (y : GaussianInt), (x ≠ y) → (((p₂.rotate
        (p₂.idxOf x)).head? = some x) → (
    let c₂ := p₂.rotate (p₂.idxOf x)
    (y ∈ c₂) → (y ∈ c₂.tail))) := by
  classical
  intro p₂ x y hxy hrot₂x c₂ hc₂y
  have hhead : c₂.head? = some x := by simpa [c₂] using hrot₂x
  obtain ⟨zs, hshape⟩ := (List.head?_eq_some_iff).mp hhead
  rw [hshape] at hc₂y
  simp only [List.mem_cons] at hc₂y
  rcases hc₂y with h | h
  · exact (hxy h.symm).elim
  · simpa [hshape] using h

private theorem hrest₂ne :
    ∀ (V₁ : Set GaussianInt), ∀ (V₂ : Set GaussianInt), ∀ (p₂ : List GaussianInt), ∀ (x :
        GaussianInt), ∀ (y : GaussianInt), (y ∈ V₁ ∩ V₂) → (
    let c₂ := p₂.rotate (p₂.idxOf x)
    (y ∈ c₂.tail) → (
    let good (z : GaussianInt) : Bool := @decide (z ∉ V₁) (Classical.propDecidable _)
    let rest₂ := c₂.tail.dropWhile good
    rest₂ ≠ [])) := by
  classical
  intro V₁ V₂ p₂ x y hy c₂ hc₂tail good rest₂ he
  have hall : ∀ z ∈ c₂.tail, good z := (List.dropWhile_eq_nil_iff).mp he
  have hgood := hall y hc₂tail
  simp [good, (show y ∈ V₁ from hy.1)] at hgood

private theorem hzV₁ :
    ∀ (V₁ : Set GaussianInt), ∀ (p₂ : List GaussianInt), ∀ (x : GaussianInt),
    let c₂ := p₂.rotate (p₂.idxOf x)
    let good (z : GaussianInt) : Bool := @decide (z ∉ V₁) (Classical.propDecidable _)
    let rest₂ := c₂.tail.dropWhile good
    ∀ (z : GaussianInt), ∀ (zs : List GaussianInt), (rest₂ = z :: zs) → (z ∈ V₁) := by
  classical
  intro V₁ p₂ x c₂ good rest₂ z zs hrest₂
  have hlenrest : 0 < rest₂.length := by rw [hrest₂]; simp
  have hnot := List.dropWhile_get_zero_not good c₂.tail (by simpa [rest₂] using hlenrest)
  have hznot : ¬ good z := by simpa [rest₂, hrest₂] using hnot
  simpa [good] using hznot

private theorem hzTail :
    ∀ (V₁ : Set GaussianInt), ∀ (p₂ : List GaussianInt), ∀ (x : GaussianInt),
    let c₂ := p₂.rotate (p₂.idxOf x)
    let good (z : GaussianInt) : Bool := @decide (z ∉ V₁) (Classical.propDecidable _)
    let rest₂ := c₂.tail.dropWhile good
    ∀ (z : GaussianInt), ∀ (zs : List GaussianInt), (rest₂ = z :: zs) → (z ∈ c₂.tail) := by
  classical
  intro V₁ p₂ x c₂ good rest₂ z zs hrest₂
  have hzRest : z ∈ rest₂ := by rw [hrest₂]; simp
  exact (List.dropWhile_subset good hzRest)

private theorem hxNotTail :
    ∀ (p₂ : List GaussianInt), ∀ (x : GaussianInt), ((p₂.rotate (p₂.idxOf x)).head? = some x) → (
    let c₂ := p₂.rotate (p₂.idxOf x)
    (c₂.Nodup) → (x ∉ c₂.tail)) := by
  classical
  intro p₂ x hrot₂x c₂ hc₂nodup
  have hhead : c₂.head? = some x := by simpa [c₂] using hrot₂x
  obtain ⟨tl, hshape⟩ := (List.head?_eq_some_iff).mp hhead
  have : c₂.Nodup := hc₂nodup
  rw [hshape] at this
  rw [hshape]
  exact (List.nodup_cons.mp this).1

private theorem hzx :
    ∀ (p₂ : List GaussianInt),
        ∀ (x : GaussianInt),
          let c₂ := p₂.rotate (p₂.idxOf x);
          ∀ (z : GaussianInt), z ∈ c₂.tail → x ∉ c₂.tail → z ≠ x := by
  classical
  intro p₂ x c₂ z hzTail hxNotTail h
  subst z
  exact hxNotTail hzTail

private theorem hrot₁z :
    ∀ (p₁ : List GaussianInt), ∀ (z : GaussianInt),
    let c₁ := p₁.rotate (p₁.idxOf z)
    (p₁.idxOf z < p₁.length) → (c₁.head? = some z) := by
  classical
  intro p₁ z c₁ hidx₁z
  rw [show c₁ = p₁.rotate (p₁.idxOf z) by rfl, List.head?_rotate hidx₁z]
  exact List.getElem?_idxOf (List.idxOf_lt_length_iff.mp hidx₁z)

private theorem hc₁shape :
    ∀ (p₁ : List GaussianInt), ∀ (z : GaussianInt),
    let c₁ := p₁.rotate (p₁.idxOf z)
    (c₁.head? = some z) → (c₁ = z :: c₁.tail) := by
  classical
  intro p₁ z c₁ hrot₁z
  obtain ⟨tl, ht⟩ := (List.head?_eq_some_iff).mp (by simpa [c₁] using hrot₁z)
  simp [c₁, ht]

private theorem hc₁nodup :
    ∀ (p₁ : List GaussianInt), (p₁.Nodup) → (∀ (z : GaussianInt),
    let c₁ := p₁.rotate (p₁.idxOf z)
    c₁.Nodup) := by
  classical
  intro p₁ hp₁ z c₁
  simpa [c₁] using
    (List.nodup_rotate (l := p₁) (n := p₁.idxOf z)).mpr hp₁

private theorem hrest₁ne :
    ∀ (p₁ : List GaussianInt), ∀ (x : GaussianInt), ∀ (z : GaussianInt),
    let c₁ := p₁.rotate (p₁.idxOf z)
    (x ∈ c₁.tail) → (
    let good₁ (w : GaussianInt) : Bool := decide (w ≠ x)
    let rest₁ := c₁.tail.dropWhile good₁
    rest₁ ≠ []) := by
  classical
  intro p₁ x z c₁ hc₁x good₁ rest₁ he
  have hall : ∀ w ∈ c₁.tail, good₁ w := (List.dropWhile_eq_nil_iff).mp (by simpa [rest₁] using he)
  have hbad := hall x hc₁x
  simp [good₁] at hbad

private theorem hwx :
    ∀ (p₁ : List GaussianInt), ∀ (x : GaussianInt), ∀ (z : GaussianInt),
    let c₁ := p₁.rotate (p₁.idxOf z)
    let good₁ (w : GaussianInt) : Bool := decide (w ≠ x)
    let rest₁ := c₁.tail.dropWhile good₁
    ∀ (w : GaussianInt), ∀ (ws : List GaussianInt), (rest₁ = w :: ws) → (w = x) := by
  classical
  intro p₁ x z c₁ good₁ rest₁ w ws hrest₁
  have hlenrest : 0 < rest₁.length := by rw [hrest₁]; simp
  have hnot := List.dropWhile_get_zero_not good₁ c₁.tail (by simpa [rest₁] using hlenrest)
  have hwgood : ¬ good₁ w := by simpa [rest₁, hrest₁] using hnot
  simpa [good₁] using hwgood

private theorem hc₂shape :
    ∀ (p₂ : List GaussianInt), ∀ (x : GaussianInt), ((p₂.rotate (p₂.idxOf x)).head? = some x) → (
    let c₂ := p₂.rotate (p₂.idxOf x)
    c₂ = x :: c₂.tail) := by
  classical
  intro p₂ x hrot₂x c₂
  obtain ⟨tl, ht⟩ := (List.head?_eq_some_iff).mp (by simpa [c₂] using hrot₂x)
  simp [c₂, ht]

private theorem hdecomp₂' :
    ∀ (V₁ : Set GaussianInt), ∀ (p₂ : List GaussianInt), ∀ (x : GaussianInt),
    let c₂ := p₂.rotate (p₂.idxOf x)
    let good (z : GaussianInt) : Bool := @decide (z ∉ V₁) (Classical.propDecidable _)
    let rest₂ := c₂.tail.dropWhile good
    ∀ (z : GaussianInt), ∀ (zs : List GaussianInt), (rest₂ = z :: zs) → ((c₂.tail.takeWhile good
        ++ rest₂ = c₂.tail) → (
    let prefix₂ := c₂.tail.takeWhile good
    c₂.tail = prefix₂ ++ z :: zs)) := by
  classical
  intro V₁ p₂ x c₂ good rest₂ z zs hrest₂ hdecomp₂ prefix₂
  calc
    c₂.tail = c₂.tail.takeWhile good ++ rest₂ := hdecomp₂.symm
    _ = prefix₂ ++ z :: zs := by simp [prefix₂, hrest₂]

private theorem sourceE₁ :
    ∀ (E₁ : Set (Finset GaussianInt)), ∀ (p₁ : List GaussianInt), ∀ (a₁ : GaussianInt), ∀ (b₁ :
        GaussianInt), (p₁.head? = some a₁) → ((p₁.getLast? = some b₁) → ((∀ (e : Finset
        GaussianInt), e ∈ E₁ ↔ e = {b₁, a₁} ∨ ∃ (a : GaussianInt) (b : GaussianInt) (l₁ : List
        GaussianInt) (l₂ : List GaussianInt), p₁ = l₁ ++ a :: b :: l₂ ∧ e = {a, b}) → ((∀ (p :
            List GaussianInt), ∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (E : Set (Finset
        GaussianInt)), (p.head? = some a) → ((p.getLast? = some b) → ((({b, a} : Finset
        GaussianInt) ∈ E) → ((∀ u, ∀ v, ∀ l₁, ∀ l₂, p = l₁ ++ u :: v :: l₂ → ({u, v} : Finset
            GaussianInt)
        ∈ E) → (Cycle.Chain (fun u v => ({u, v} : Finset GaussianInt) ∈ E) (p : Cycle
        GaussianInt)))))) → (Cycle.Chain (fun u v => ({u, v} : Finset GaussianInt) ∈ E₁)
      (p₁ : Cycle GaussianInt))))) := by
  classical
  intro E₁ p₁ a₁ b₁ hhead₁ hlast₁ hedge₁ sourceEdgeChain
  exact sourceEdgeChain p₁ a₁ b₁ E₁ hhead₁ hlast₁
    ((hedge₁ {b₁, a₁}).mpr (Or.inl rfl)) (by
      intro u v l₁ l₂ heq
      exact (hedge₁ {u, v}).mpr (Or.inr ⟨u, v, l₁, l₂, heq, rfl⟩))

private abbrev sourceE₂ :=
  ApollonianSuperharmonic.MixedCycleDetails.sourceE₁

private theorem hp₂cycleeq :
    ∀ (p₂ : List GaussianInt), ∀ (x : GaussianInt), (p₂.idxOf x < p₂.length) → (
    let c₂ := p₂.rotate (p₂.idxOf x)
    (p₂ : Cycle GaussianInt) = (c₂ : Cycle GaussianInt)) := by
  classical
  intro p₂ x hidx₂x c₂
  apply Cycle.coe_eq_coe.mpr
  exact (List.isRotated_iff_mod).2 ⟨p₂.idxOf x, Nat.le_of_lt hidx₂x, rfl⟩

private theorem hc₂edgeCycle :
    ∀ (E₂ : Set (Finset GaussianInt)), ∀ (p₂ : List GaussianInt), ∀ (x : GaussianInt),
    let c₂ := p₂.rotate (p₂.idxOf x)
    (Cycle.Chain (fun u v => ({u, v} : Finset GaussianInt) ∈ E₂) (p₂ : Cycle GaussianInt)) →
        (((p₂ : Cycle GaussianInt) = (c₂ : Cycle GaussianInt)) → (Cycle.Chain (fun u v => ({u, v}
        : Finset GaussianInt) ∈ E₂)
      (c₂ : Cycle GaussianInt))) := by
  classical
  intro E₂ p₂ x c₂ sourceE₂ hp₂cycleeq
  rw [← hp₂cycleeq]
  exact sourceE₂

private theorem hc₂edgeChain :
    ∀ (E₂ : Set (Finset GaussianInt)), ∀ (p₂ : List GaussianInt), ∀ (x : GaussianInt),
    let c₂ := p₂.rotate (p₂.idxOf x)
    (c₂ = x :: c₂.tail) → ((Cycle.Chain (fun u v => ({u, v} : Finset GaussianInt) ∈ E₂) (c₂ :
        Cycle GaussianInt)) → ((x :: (c₂.tail ++ [x])).IsChain
      (fun u v => ({u, v} : Finset GaussianInt) ∈ E₂))) := by
  classical
  intro E₂ p₂ x c₂ hc₂shape hc₂edgeCycle
  rw [hc₂shape] at hc₂edgeCycle
  exact (Cycle.chain_coe_cons (fun u v => ({u, v} : Finset GaussianInt) ∈ E₂)
    x c₂.tail).mp hc₂edgeCycle

private theorem hp₁cycleeq :
    ∀ (p₁ : List GaussianInt), ∀ (z : GaussianInt),
    let c₁ := p₁.rotate (p₁.idxOf z)
    (p₁.idxOf z < p₁.length) → ((p₁ : Cycle GaussianInt) = (c₁ : Cycle GaussianInt)) := by
  classical
  intro p₁ z c₁ hidx₁z
  apply Cycle.coe_eq_coe.mpr
  exact (List.isRotated_iff_mod).2 ⟨p₁.idxOf z, Nat.le_of_lt hidx₁z, rfl⟩

private abbrev hc₁edgeCycle := ApollonianSuperharmonic.MixedCycleDetails.hc₂edgeCycle

private abbrev hc₁edgeChain := ApollonianSuperharmonic.MixedCycleDetails.hc₂edgeChain

private theorem hQlast :
    ∀ (V₁ : Set GaussianInt), ∀ (p₂ : List GaussianInt), ∀ (x : GaussianInt),
    let c₂ := p₂.rotate (p₂.idxOf x)
    let good (z : GaussianInt) : Bool := @decide (z ∉ V₁) (Classical.propDecidable _)
    ∀ (z : GaussianInt),
    let prefix₂ := c₂.tail.takeWhile good
    let Q := x :: (prefix₂ ++ [z])
    Q.getLast? = some z := by
  classical
  intro V₁ p₂ x c₂ good z prefix₂ Q
  apply List.getLast?_eq_some_iff.mpr
  refine ⟨x :: prefix₂, ?_⟩
  simp [Q]

private theorem hQedgePrefix :
    ∀ (V₁ : Set GaussianInt), ∀ (p₂ : List GaussianInt), ∀ (x : GaussianInt), (∀ {α : Type}, ∀ (a
        : α), ∀ (b : α), ∀ (u : List α), ∀ (v : List α), a :: (u ++ [b]) = List.take (u.length +
        2) (a :: (u ++ b :: v))) → (
    let c₂ := p₂.rotate (p₂.idxOf x)
    let good (z : GaussianInt) : Bool := @decide (z ∉ V₁) (Classical.propDecidable _)
    ∀ (z : GaussianInt), ∀ (zs : List GaussianInt),
    let prefix₂ := c₂.tail.takeWhile good
    (c₂.tail = prefix₂ ++ z :: zs) → (
    let Q := x :: (prefix₂ ++ [z])
    Q = List.take (prefix₂.length + 2) (x :: (c₂.tail ++ [x])))) := by
  classical
  intro V₁ p₂ x takeArc c₂ good z zs prefix₂ hdecomp₂' Q
  calc
    Q = x :: (prefix₂ ++ [z]) := rfl
    _ = List.take (prefix₂.length + 2)
        (x :: (prefix₂ ++ z :: (zs ++ [x]))) := takeArc x z prefix₂ (zs ++ [x])
    _ = List.take (prefix₂.length + 2) (x :: (c₂.tail ++ [x])) := by
      rw [hdecomp₂']
      simp [List.append_assoc]

private theorem hQedge :
    ∀ (V₁ : Set GaussianInt), ∀ (E₂ : Set (Finset GaussianInt)), ∀ (p₂ : List GaussianInt), ∀ (x
        : GaussianInt),
    let c₂ := p₂.rotate (p₂.idxOf x)
    let good (z : GaussianInt) : Bool := @decide (z ∉ V₁) (Classical.propDecidable _)
    ∀ (z : GaussianInt),
    let prefix₂ := c₂.tail.takeWhile good
    ((x :: (c₂.tail ++ [x])).IsChain (fun u v => ({u, v} : Finset GaussianInt) ∈ E₂)) → (
    let Q := x :: (prefix₂ ++ [z])
    (Q = List.take (prefix₂.length + 2) (x :: (c₂.tail ++ [x]))) → (Q.IsChain (fun u v => ({u, v}
        : Finset GaussianInt) ∈ E₂))) := by
  classical
  intro V₁ E₂ p₂ x c₂ good z prefix₂ hc₂edgeChain Q hQedgePrefix
  rw [hQedgePrefix]
  exact hc₂edgeChain.take _

private theorem hdecomp₁' :
    ∀ (p₁ : List GaussianInt), ∀ (x : GaussianInt), ∀ (z : GaussianInt),
    let c₁ := p₁.rotate (p₁.idxOf z)
    let good₁ (w : GaussianInt) : Bool := decide (w ≠ x)
    let rest₁ := c₁.tail.dropWhile good₁
    ∀ (w : GaussianInt), ∀ (ws : List GaussianInt), (rest₁ = w :: ws) → ((w = x) →
        ((c₁.tail.takeWhile good₁ ++ rest₁ = c₁.tail) → (
    let prefix₁ := c₁.tail.takeWhile good₁
    c₁.tail = prefix₁ ++ x :: ws))) := by
  classical
  intro p₁ x z c₁ good₁ rest₁ w ws hrest₁ hwx hdecomp₁ prefix₁
  calc
    c₁.tail = c₁.tail.takeWhile good₁ ++ rest₁ := hdecomp₁.symm
    _ = prefix₁ ++ x :: ws := by simp [prefix₁, hrest₁, hwx]

private theorem hRedgePrefix :
    ∀ (p₁ : List GaussianInt),
      ∀ (x : GaussianInt),
        (∀ {α : Type},
            ∀ (a : α),
              ∀ (b : α),
                ∀ (u : List α),
                  ∀ (v : List α),
                    a :: (u ++ [b]) = List.take (u.length + 2) (a :: (u ++ b :: v))) →
          ∀ (z : GaussianInt),
            let c₁ := p₁.rotate (p₁.idxOf z);
            let good₁ (w : GaussianInt) : Bool := decide (w ≠ x);
            ∀ (ws : List GaussianInt),
              let R := z :: (c₁.tail.takeWhile good₁ ++ [x])
              let prefix₁ := c₁.tail.takeWhile good₁
              c₁.tail = prefix₁ ++ x :: ws →
                R = List.take (prefix₁.length + 2) (z :: (c₁.tail ++ [z])) := by
  classical
  intro p₁ x takeArc z c₁ good₁ ws R prefix₁ hdecomp₁'
  calc
    R = z :: (prefix₁ ++ [x]) := rfl
    _ = List.take (prefix₁.length + 2)
        (z :: (prefix₁ ++ x :: (ws ++ [z]))) := takeArc z x prefix₁ (ws ++ [z])
    _ = List.take (prefix₁.length + 2) (z :: (c₁.tail ++ [z])) := by
      rw [hdecomp₁']
      simp [List.append_assoc]

private theorem hRedge :
    ∀ (E₁ : Set (Finset GaussianInt)), ∀ (p₁ : List GaussianInt), ∀ (x : GaussianInt), ∀ (z :
        GaussianInt),
    let c₁ := p₁.rotate (p₁.idxOf z);
    let good₁ (w : GaussianInt) : Bool := decide (w ≠ x);
    (
    let R := z :: (c₁.tail.takeWhile good₁ ++ [x]);
    let prefix₁ := c₁.tail.takeWhile good₁;
    ((z :: (c₁.tail ++ [z])).IsChain (fun u v => ({u, v} : Finset GaussianInt) ∈ E₁)) → ((R =
        List.take (prefix₁.length + 2) (z :: (c₁.tail ++ [z]))) → (R.IsChain (fun u v => ({u, v}
        : Finset GaussianInt) ∈ E₁)))) := by
  classical
  intro E₁ p₁ x z c₁ good₁ R prefix₁ hc₁edgeChain hRedgePrefix
  rw [hRedgePrefix]
  exact hc₁edgeChain.take _

private theorem hPplusUnion :
    ∀ (V₁ : Set GaussianInt),
      ∀ (E₁ : Set (Finset GaussianInt)),
        ∀ (E₂ : Set (Finset GaussianInt)),
          ∀ (p₁ : List GaussianInt),
            ∀ (p₂ : List GaussianInt),
              ∀ (x : GaussianInt),
                let c₂ := p₂.rotate (p₂.idxOf x);
                let good (z : GaussianInt) : Bool :=
                  @decide (z ∉ V₁) (Classical.propDecidable _);
                ∀ (z : GaussianInt),
                  let c₁ := p₁.rotate (p₁.idxOf z);
                  let good₁ (w : GaussianInt) : Bool := decide (w ≠ x);
                  (let R := z :: (c₁.tail.takeWhile good₁ ++ [x]);
                  let prefix₂ := c₂.tail.takeWhile good;
                  let Q := x :: (prefix₂ ++ [z]);
                  (Q.getLast? = some z) →
                    ((∀ v ∈ R.tail.head?, ({ z, v } : Finset GaussianInt) ∈ E₁) →
                      (let edgeRel (u v : GaussianInt) : Prop :=
                        ({ u, v } : Finset GaussianInt) ∈ E₁ ∪ E₂;
                      (Q.IsChain edgeRel) →
                        ((R.tail.IsChain edgeRel) →
                          ((Q ++ R.tail).IsChain edgeRel))))) := by
  classical
  intro V₁ E₁ E₂ p₁ p₂ x c₂ good z c₁ good₁ R prefix₂ Q hQlast hRstepE₁ edgeRel hQunion
      hRtailUnion
  apply List.IsChain.append hQunion hRtailUnion
  intro u hu v hv
  have hu' : u = z := by simpa [hQlast] using hu.symm
  subst u
  exact Or.inl (hRstepE₁ v hv)

private theorem hQprefix :
    ∀ (V₁ : Set GaussianInt), ∀ (p₂ : List GaussianInt), ∀ (x : GaussianInt), (∀ {α : Type}, ∀ (a
        : α), ∀ (b : α), ∀ (u : List α), ∀ (v : List α), a :: (u ++ [b]) = List.take (u.length +
        2) (a :: (u ++ b :: v))) → (
    let c₂ := p₂.rotate (p₂.idxOf x)
    let good (z : GaussianInt) : Bool := @decide (z ∉ V₁) (Classical.propDecidable _)
    ∀ (z : GaussianInt), ∀ (zs : List GaussianInt),
    let prefix₂ := c₂.tail.takeWhile good
    (c₂ = x :: c₂.tail) → ((c₂.tail = prefix₂ ++ z :: zs) → (
    let Q := x :: (prefix₂ ++ [z])
    Q = c₂.take (prefix₂.length + 2)))) := by
  classical
  intro V₁ p₂ x takeArc c₂ good z zs prefix₂ hc₂shape hdecomp₂' Q
  rw [show Q = x :: (prefix₂ ++ [z]) by rfl, hc₂shape, hdecomp₂']
  exact takeArc x z prefix₂ zs

private theorem hQchain :
    ∀ (V₁ : Set GaussianInt), ∀ (p₂ : List GaussianInt), ∀ (x : GaussianInt), ((p₂.rotate
        (p₂.idxOf x)).IsChain FourNeighborAdjacent) → (
    let c₂ := p₂.rotate (p₂.idxOf x)
    let good (z : GaussianInt) : Bool := @decide (z ∉ V₁) (Classical.propDecidable _)
    ∀ (z : GaussianInt),
    let prefix₂ := c₂.tail.takeWhile good
    let Q := x :: (prefix₂ ++ [z])
    (Q = c₂.take (prefix₂.length + 2)) → (Q.IsChain FourNeighborAdjacent)) := by
  classical
  intro V₁ p₂ x hc₂chain c₂ good z prefix₂ Q hQprefix
  rw [hQprefix]
  exact hc₂chain.take _

private theorem hRprefix :
    ∀ (p₁ : List GaussianInt),
      ∀ (x : GaussianInt),
        (∀ {α : Type},
            ∀ (a : α),
              ∀ (b : α),
                ∀ (u : List α),
                  ∀ (v : List α),
                    a :: (u ++ [b]) = List.take (u.length + 2) (a :: (u ++ b :: v))) →
          ∀ (z : GaussianInt),
            let c₁ := p₁.rotate (p₁.idxOf z);
            c₁ = z :: c₁.tail →
              let good₁ (w : GaussianInt) : Bool := decide (w ≠ x);
              ∀ (ws : List GaussianInt),
                let R := z :: (c₁.tail.takeWhile good₁ ++ [x])
                let prefix₁ := c₁.tail.takeWhile good₁
                c₁.tail = prefix₁ ++ x :: ws → R = c₁.take (prefix₁.length + 2) := by
  classical
  intro p₁ x takeArc z c₁ hc₁shape good₁ ws R prefix₁ hdecomp₁'
  rw [show R = z :: (prefix₁ ++ [x]) by rfl, hc₁shape, hdecomp₁']
  exact takeArc z x prefix₁ ws

private theorem hRchain :
    ∀ (p₁ : List GaussianInt), ∀ (x : GaussianInt), ∀ (z : GaussianInt),
    let c₁ := p₁.rotate (p₁.idxOf z);
    let good₁ (w : GaussianInt) : Bool := decide (w ≠ x);
    (
    let R := z :: (c₁.tail.takeWhile good₁ ++ [x]);
    let prefix₁ := c₁.tail.takeWhile good₁;
    (c₁.IsChain FourNeighborAdjacent) → ((R = c₁.take (prefix₁.length + 2)) → (R.IsChain
        FourNeighborAdjacent))) := by
  classical
  intro p₁ x z c₁ good₁ R prefix₁ hc₁chain hRprefix
  rw [hRprefix]
  exact hc₁chain.take _

private theorem hQnodup :
    ∀ (V₁ : Set GaussianInt), ∀ (p₂ : List GaussianInt), ∀ (x : GaussianInt),
    let c₂ := p₂.rotate (p₂.idxOf x)
    (c₂.Nodup) → (
    let good (z : GaussianInt) : Bool := @decide (z ∉ V₁) (Classical.propDecidable _)
    ∀ (z : GaussianInt),
    let prefix₂ := c₂.tail.takeWhile good
    let Q := x :: (prefix₂ ++ [z])
    (Q = c₂.take (prefix₂.length + 2)) → (Q.Nodup)) := by
  classical
  intro V₁ p₂ x c₂ hc₂nodup good z prefix₂ Q hQprefix
  rw [hQprefix]
  exact (List.take_sublist _ c₂).nodup hc₂nodup

private theorem hznotprefix₁ :
    ∀ (p₁ : List GaussianInt),
      ∀ (x : GaussianInt),
        ∀ (z : GaussianInt),
          let c₁ := p₁.rotate (p₁.idxOf z);
          c₁.head? = some z →
            c₁.Nodup →
              let good₁ (w : GaussianInt) : Bool := decide (w ≠ x);
              let prefix₁ := c₁.tail.takeWhile good₁
              z ∉ prefix₁ := by
  classical
  intro p₁ x z c₁ hrot₁z hc₁nodup good₁ prefix₁ hzpre
  have hztail : z ∈ c₁.tail := List.takeWhile_subset good₁ hzpre
  have hhead : c₁.head? = some z := by simpa [c₁] using hrot₁z
  obtain ⟨tl, hshape⟩ := (List.head?_eq_some_iff).mp hhead
  have hnd : (z :: tl).Nodup := by simpa [c₁, hshape] using hc₁nodup
  have : z ∉ tl := (List.nodup_cons.mp hnd).1
  rw [hshape] at hztail
  exact this hztail

private theorem hpNodup :
    ∀ (V₁ : Set GaussianInt), ∀ (p₁ : List GaussianInt), ∀ (p₂ : List GaussianInt), ∀ (x :
        GaussianInt),
    let c₂ := p₂.rotate (p₂.idxOf x);
    let good (z : GaussianInt) : Bool := @decide (z ∉ V₁) (Classical.propDecidable _);
    ∀ (z : GaussianInt),
    let c₁ := p₁.rotate (p₁.idxOf z);
    let good₁ (w : GaussianInt) : Bool := decide (w ≠ x);
    (
    let prefix₂ := c₂.tail.takeWhile good;
    let prefix₁ := c₁.tail.takeWhile good₁;
    let Q := x :: (prefix₂ ++ [z]);
    (Q.Nodup) → ((prefix₁.Nodup) → ((∀ v ∈ Q, ∀ w ∈ prefix₁, v ≠ w) → ((Q ++ prefix₁).Nodup))))
        := by
  classical
  intro V₁ p₁ p₂ x c₂ good z c₁ good₁ prefix₂ prefix₁ Q hQnodup hprefix₁nodup hcross
  apply List.nodup_append.mpr
  exact ⟨hQnodup, hprefix₁nodup, hcross⟩

private theorem hRstep :
    ∀ (p₁ : List GaussianInt), ∀ (x : GaussianInt), ∀ (z : GaussianInt),
    let c₁ := p₁.rotate (p₁.idxOf z);
    let good₁ (w : GaussianInt) : Bool := decide (w ≠ x);
    (
    let R := z :: (c₁.tail.takeWhile good₁ ++ [x]);
    (R.IsChain FourNeighborAdjacent) → (∀ v ∈ R.tail.head?, FourNeighborAdjacent z v)) := by
  classical
  intro p₁ x z c₁ good₁ R hRchain
  have h := (List.isChain_cons.mp hRchain).1
  simpa [R] using h

private theorem hPplus :
    ∀ (V₁ : Set GaussianInt), ∀ (p₁ : List GaussianInt), ∀ (p₂ : List GaussianInt), ∀ (x :
        GaussianInt),
    let c₂ := p₂.rotate (p₂.idxOf x);
    let good (z : GaussianInt) : Bool := @decide (z ∉ V₁) (Classical.propDecidable _);
    ∀ (z : GaussianInt),
    let c₁ := p₁.rotate (p₁.idxOf z);
    let good₁ (w : GaussianInt) : Bool := decide (w ≠ x);
    (
    let R := z :: (c₁.tail.takeWhile good₁ ++ [x]);
    let prefix₂ := c₂.tail.takeWhile good;
    let Q := x :: (prefix₂ ++ [z]);
    (Q.getLast? = some z) → ((Q.IsChain FourNeighborAdjacent) → ((R.IsChain FourNeighborAdjacent)
        → ((∀ v ∈ R.tail.head?, FourNeighborAdjacent z v) → ((Q ++ R.tail).IsChain
        FourNeighborAdjacent))))) := by
  classical
  intro V₁ p₁ p₂ x c₂ good z c₁ good₁ R prefix₂ Q hQlast hQchain hRchain hRstep
  apply List.IsChain.append hQchain (List.isChain_cons.mp hRchain).2
  intro u hu v hv
  have hu' : u = z := by simpa [hQlast] using hu.symm
  subst u
  exact hRstep v hv

private theorem hpChain :
    ∀ (V₁ : Set GaussianInt), ∀ (p₁ : List GaussianInt), ∀ (p₂ : List GaussianInt), ∀ (x :
        GaussianInt),
    let c₂ := p₂.rotate (p₂.idxOf x);
    let good (z : GaussianInt) : Bool := @decide (z ∉ V₁) (Classical.propDecidable _);
    ∀ (z : GaussianInt),
    let c₁ := p₁.rotate (p₁.idxOf z);
    let good₁ (w : GaussianInt) : Bool := decide (w ≠ x);
    (
    let prefix₂ := c₂.tail.takeWhile good;
    let prefix₁ := c₁.tail.takeWhile good₁;
    let Q := x :: (prefix₂ ++ [z]);
    let p := Q ++ prefix₁;
    ((p ++ [x]).IsChain FourNeighborAdjacent) → (p.IsChain FourNeighborAdjacent)) := by
  classical
  intro V₁ p₁ p₂ x c₂ good z c₁ good₁ prefix₂ prefix₁ Q p hPplusX
  have h := hPplusX.left_of_append
  simpa using h

private theorem hcloseP :
    ∀ (V₁ : Set GaussianInt), ∀ (p₁ : List GaussianInt), ∀ (p₂ : List GaussianInt), ∀ (x :
        GaussianInt),
    let c₂ := p₂.rotate (p₂.idxOf x);
    let good (z : GaussianInt) : Bool := @decide (z ∉ V₁) (Classical.propDecidable _);
    ∀ (z : GaussianInt),
    let c₁ := p₁.rotate (p₁.idxOf z);
    let good₁ (w : GaussianInt) : Bool := decide (w ≠ x);
    (
    let prefix₂ := c₂.tail.takeWhile good;
    let prefix₁ := c₁.tail.takeWhile good₁;
    let Q := x :: (prefix₂ ++ [z]);
    let p := Q ++ prefix₁;
    ∀ (hpne : p ≠ []), ((p ++ [x]).IsChain FourNeighborAdjacent) → (FourNeighborAdjacent
        (p.getLast hpne) x)) := by
  classical
  intro V₁ p₁ p₂ x c₂ good z c₁ good₁ prefix₂ prefix₁ Q p hpne hPplusX
  have h := hPplusX.rel_getLast_head_of_append hpne (by simp)
  simpa using h

private theorem hadjP :
    ∀ (V₁ : Set GaussianInt), ∀ (p₁ : List GaussianInt), ∀ (p₂ : List GaussianInt), ∀ (x :
        GaussianInt),
    let c₂ := p₂.rotate (p₂.idxOf x);
    let good (z : GaussianInt) : Bool := @decide (z ∉ V₁) (Classical.propDecidable _);
    ∀ (z : GaussianInt),
    let c₁ := p₁.rotate (p₁.idxOf z);
    let good₁ (w : GaussianInt) : Bool := decide (w ≠ x);
    (
    let prefix₂ := c₂.tail.takeWhile good;
    let prefix₁ := c₁.tail.takeWhile good₁;
    let Q := x :: (prefix₂ ++ [z]);
    let p := Q ++ prefix₁;
    (p.IsChain FourNeighborAdjacent) → (∀ a, ∀ b, ∀ l₁, ∀ l₂, p = l₁ ++ a :: b :: l₂ →
        FourNeighborAdjacent a b)) := by
  classical
  intro V₁ p₁ p₂ x c₂ good z c₁ good₁ prefix₂ prefix₁ Q p hpChain
  rw [List.isChain_iff_forall_rel_of_append_cons_cons] at hpChain
  exact hpChain

private theorem hpLenTwo :
    ∀ (V₁ : Set GaussianInt), ∀ (p₁ : List GaussianInt), ∀ (p₂ : List GaussianInt), ∀ (x :
        GaussianInt),
        (
    let c₂ := p₂.rotate (p₂.idxOf x);
    let good (z : GaussianInt) : Bool := @decide (z ∉ V₁) (Classical.propDecidable _);
    ∀ (z : GaussianInt),
    let c₁ := p₁.rotate (p₁.idxOf z);
    let good₁ (w : GaussianInt) : Bool := decide (w ≠ x);
    (
    let prefix₂ := c₂.tail.takeWhile good;
    let prefix₁ := c₁.tail.takeWhile good₁;
    let Q := x :: (prefix₂ ++ [z]);
    let p := Q ++ prefix₁;
    2 ≤ p.length)) := by
  classical
  intro V₁ p₁ p₂ x c₂ good z c₁ good₁ prefix₂ prefix₁ Q p
  have hQlen : 2 ≤ Q.length := by simp [Q]
  simp [p, List.length_append]
  omega

private theorem hsimple :
    ∀ (V₁ : Set GaussianInt),
      ∀ (p₁ : List GaussianInt),
        ∀ (p₂ : List GaussianInt),
          ∀ (x : GaussianInt),
            let c₂ := p₂.rotate (p₂.idxOf x);
            let good (z : GaussianInt) : Bool :=
              @decide (z ∉ V₁) (Classical.propDecidable _);
            ∀ (z : GaussianInt),
              let c₁ := p₁.rotate (p₁.idxOf z);
              let good₁ (w : GaussianInt) : Bool := decide (w ≠ x);
              (let prefix₂ := c₂.tail.takeWhile good;
              let prefix₁ := c₁.tail.takeWhile good₁;
              let Q := x :: (prefix₂ ++ [z]);
              ((Q ++ prefix₁).Nodup) →
                (let p := Q ++ prefix₁;
                ∀ (hpne : p ≠ []),
                  (FourNeighborAdjacent (p.getLast hpne) x) →
                    ((p.head? = some x) →
                      ((p.getLast? = some (p.getLast hpne)) →
                        (let v := p.getLast hpne;
                        (∀ a,
                            ∀ b,
                              ∀ l₁,
                                ∀ l₂,
                                  p = l₁ ++ a :: b :: l₂ →
                                    FourNeighborAdjacent a b) →
                          ((4 ≤ p.length) →
                            (let W : Set GaussianInt :=
                              (p.toFinset : Set GaussianInt);
                            let F : Set (Finset GaussianInt) :=
                              {e |
                                e = { v, x } ∨
                                  ∃ a b l₁ l₂,
                                    p = l₁ ++ a :: b :: l₂ ∧ e = { a, b }};
                            SimpleGridCycle W F))))))) := by
  classical
  intro V₁ p₁ p₂ x c₂ good z c₁ good₁ prefix₂ prefix₁ Q hpNodup p hpne hcloseP hphead hplast v
      hadjP hpLength W F
  refine ⟨p, x, v, hpNodup, hpLength, hphead, hplast, ?_, hcloseP, ?_, ?_⟩
  · rfl
  · exact hadjP
  · intro e
    simp [F, v, Set.mem_ofPred_eq]

private theorem hE₂At769 :
    ∀ (V₁ : Set GaussianInt), ∀ (E₂ : Set (Finset GaussianInt)), ∀ (p₂ : List GaussianInt), ∀ (x
        : GaussianInt),
    let c₂ := p₂.rotate (p₂.idxOf x)
    let good (z : GaussianInt) : Bool := @decide (z ∉ V₁) (Classical.propDecidable _)
    ∀ (z : GaussianInt),
    let prefix₂ := c₂.tail.takeWhile good
    let Q := x :: (prefix₂ ++ [z])
    (Q.IsChain (fun u v => ({u, v} : Finset GaussianInt) ∈ E₂)) → ((prefix₂ = []) → (({x, z} :
        Finset GaussianInt) ∈ E₂)) := by
  classical
  intro V₁ E₂ p₂ x c₂ good z prefix₂ Q hQedge hpref₂
  have hq : ([x, z] : List GaussianInt).IsChain
      (fun u w => ({u, w} : Finset GaussianInt) ∈ E₂) := by
    simpa [Q, hpref₂] using hQedge
  exact (List.isChain_pair.mp hq)

private theorem hFfAt774 :
    ∀ (V₁ : Set GaussianInt), ∀ (p₁ : List GaussianInt), ∀ (p₂ : List GaussianInt), ∀ (x :
        GaussianInt),
    let c₂ := p₂.rotate (p₂.idxOf x);
    let good (z : GaussianInt) : Bool := @decide (z ∉ V₁) (Classical.propDecidable _);
    ∀ (z : GaussianInt),
    let c₁ := p₁.rotate (p₁.idxOf z);
    let good₁ (w : GaussianInt) : Bool := decide (w ≠ x);
    (
    let prefix₂ := c₂.tail.takeWhile good;
    let prefix₁ := c₁.tail.takeWhile good₁;
    let Q := x :: (prefix₂ ++ [z]);
    let p := Q ++ prefix₁;
    ∀ (hpne : p ≠ []),
    let v := p.getLast hpne;
    let F : Set (Finset GaussianInt) := {e | e = {v, x} ∨
      ∃ a b l₁ l₂, p = l₁ ++ a :: b :: l₂ ∧ e = {a, b}};
    (prefix₂ = []) → (({x, z} : Finset GaussianInt) ∈ F)) := by
  classical
  intro V₁ p₁ p₂ x c₂ good z c₁ good₁ prefix₂ prefix₁ Q p hpne v F hpref₂
  simp only [F, Set.mem_ofPred_eq]
  right
  refine ⟨x, z, [], prefix₁, ?_, rfl⟩
  simp [p, Q, hpref₂]

private theorem hE₂At785 :
    ∀ (V₁ : Set GaussianInt), ∀ (E₂ : Set (Finset GaussianInt)), ∀ (p₂ : List GaussianInt), ∀ (x
        : GaussianInt),
    let c₂ := p₂.rotate (p₂.idxOf x)
    let good (z : GaussianInt) : Bool := @decide (z ∉ V₁) (Classical.propDecidable _)
    ∀ (z : GaussianInt),
    let prefix₂ := c₂.tail.takeWhile good
    let Q := x :: (prefix₂ ++ [z])
    (Q.IsChain (fun u v => ({u, v} : Finset GaussianInt) ∈ E₂)) → (∀ (c : GaussianInt), ∀ (cs :
        List GaussianInt), (prefix₂ = c :: cs) → (({x, c} : Finset GaussianInt) ∈ E₂)) := by
  classical
  intro V₁ E₂ p₂ x c₂ good z prefix₂ Q hQedge c cs hpref₂
  have hq : (x :: c :: (cs ++ [z])).IsChain
      (fun u w => ({u, w} : Finset GaussianInt) ∈ E₂) := by
    simpa [Q, hpref₂] using hQedge
  exact (List.isChain_cons_cons.mp hq).1

private theorem hFfAt790 :
    ∀ (V₁ : Set GaussianInt),
      ∀ (p₁ : List GaussianInt),
        ∀ (p₂ : List GaussianInt),
          ∀ (x : GaussianInt),
            let c₂ := p₂.rotate (p₂.idxOf x);
            let good (z : GaussianInt) : Bool :=
              @decide (z ∉ V₁) (Classical.propDecidable _);
            ∀ (z : GaussianInt),
              let c₁ := p₁.rotate (p₁.idxOf z);
              let good₁ (w : GaussianInt) : Bool := decide (w ≠ x);
              (let prefix₂ := c₂.tail.takeWhile good;
              let prefix₁ := c₁.tail.takeWhile good₁;
              let Q := x :: (prefix₂ ++ [z]);
              let p := Q ++ prefix₁;
              ∀ (hpne : p ≠ []),
                let v := p.getLast hpne;
                let F : Set (Finset GaussianInt) :=
                  {e |
                    e = { v, x } ∨
                      ∃ a b l₁ l₂, p = l₁ ++ a :: b :: l₂ ∧ e = { a, b }};
                ∀ (c : GaussianInt),
                  ∀ (cs : List GaussianInt),
                    (prefix₂ = c :: cs) → (({ x, c } : Finset GaussianInt) ∈ F)) := by
  classical
  intro V₁ p₁ p₂ x c₂ good z c₁ good₁ prefix₂ prefix₁ Q p hpne v F c cs hpref₂
  simp only [F, Set.mem_ofPred_eq]
  right
  refine ⟨x, c, [], (cs ++ [z]) ++ prefix₁, ?_, rfl⟩
  simp [p, Q, hpref₂, List.append_assoc]

end MixedCycleDetails

namespace MixedClosingEdges

private theorem hE₂ :
    ∀ (V₁ : Set GaussianInt), ∀ (E₂ : Set (Finset GaussianInt)), ∀ (p₂ : List GaussianInt), ∀ (x
        : GaussianInt),
    let c₂ := p₂.rotate (p₂.idxOf x)
    let good (z : GaussianInt) : Bool := @decide (z ∉ V₁) (Classical.propDecidable _)
    ∀ (z : GaussianInt),
    let prefix₂ := c₂.tail.takeWhile good
    (List.IsChain (fun (u v : GaussianInt) => {u, v} ∈ E₂) (x :: (List.takeWhile (fun (z :
        GaussianInt) => @decide (z ∉ V₁) (Classical.propDecidable _)) (p₂.rotate (List.idxOf x
            p₂)).tail ++ [z]))) → (({x,
        prefix₂.headD z} : Finset GaussianInt) ∈ E₂) := by
  classical
  intro V₁ E₂ p₂ x c₂ good z prefix₂ hQedge
  cases hpref₂ : prefix₂ with
  | nil =>
      simpa only [List.headD] using
        MixedCycleDetails.hE₂At769 V₁ E₂ p₂ x z hQedge hpref₂
  | cons c cs =>
      simpa only [List.headD] using
        MixedCycleDetails.hE₂At785 V₁ E₂ p₂ x z hQedge c cs hpref₂

private theorem hFf :
    ∀ (V₁ : Set GaussianInt),
      ∀ (p₁ : List GaussianInt),
        ∀ (p₂ : List GaussianInt),
          ∀ (x : GaussianInt),
            let c₂ := p₂.rotate (p₂.idxOf x);
            let good (z : GaussianInt) : Bool :=
              @decide (z ∉ V₁) (Classical.propDecidable _);
            ∀ (z : GaussianInt),
              let c₁ := p₁.rotate (p₁.idxOf z);
              let good₁ (w : GaussianInt) : Bool := decide (w ≠ x);
              let prefix₂ := c₂.tail.takeWhile good
              let prefix₁ := c₁.tail.takeWhile good₁
              let Q := x :: (prefix₂ ++ [z])
              let p := Q ++ prefix₁
              ∀ (hpne : p ≠ []),
                let v := p.getLast hpne
                let F : Set (Finset GaussianInt) :=
                  {e | e = { v, x } ∨ ∃ a b l₁ l₂, p = l₁ ++ a :: b :: l₂ ∧ e = { a, b }}
                ({x, prefix₂.headD z} : Finset GaussianInt) ∈ F := by
  classical
  intro V₁ p₁ p₂ x c₂ good z c₁ good₁ prefix₂ prefix₁ Q p hpne v F
  cases hpref₂ : prefix₂ with
  | nil =>
      simpa only [List.headD] using
        MixedCycleDetails.hFfAt774 V₁ p₁ p₂ x z hpne hpref₂
  | cons c cs =>
      simpa only [List.headD] using
        MixedCycleDetails.hFfAt790 V₁ p₁ p₂ x z hpne c cs hpref₂

end MixedClosingEdges

theorem P3963T1MixedBoundaryCycle
    (V₁ V₂ : Set GaussianInt) (E₁ E₂ : Set (Finset GaussianInt))
    (h₁ : SimpleGridCycle V₁ E₁) (h₂ : SimpleGridCycle V₂ E₂)
    (hdisjoint : Disjoint E₁ E₂)
    (hmultiple : ¬ (V₁ ∩ V₂).Subsingleton) :
    ∃ (W : Set GaussianInt) (F : Set (Finset GaussianInt))
      (x : GaussianInt) (e f : Finset GaussianInt),
      SimpleGridCycle W F ∧ F ⊆ E₁ ∪ E₂ ∧
      x ∈ e ∧ x ∈ f ∧ e ∈ F ∩ E₁ ∧ f ∈ F ∩ E₂ := by
-- BODY
  classical
  obtain ⟨p₁, a₁, b₁, hp₁, hlen₁, hhead₁, hlast₁, hV₁, hclose₁,
    hadj₁, hedge₁⟩ := h₁
  obtain ⟨p₂, a₂, b₂, hp₂, hlen₂, hhead₂, hlast₂, hV₂, hclose₂,
    hadj₂, hedge₂⟩ := h₂
  have hcommon := MixedCycleDetails.hcommon V₁ V₂ hmultiple
  obtain ⟨x, y, hx, hy, hxy⟩ := hcommon
  have hx₁ := MixedCycleDetails.hx₁ V₁ V₂ p₁ hV₁ x hx
  have hx₂ := MixedCycleDetails.hx₂ V₁ V₂ p₂ hV₂ x hx
  have hy₂ := MixedCycleDetails.hy₂ V₁ V₂ p₂ hV₂ y hy
  have hidx₂x : p₂.idxOf x < p₂.length := List.idxOf_lt_length_iff.mpr hx₂
  have hrot₂x := MixedCycleDetails.hrot₂x p₂ x hx₂ hidx₂x
  have cycle_chain (p : List GaussianInt) (a b : GaussianInt)
      (hh : p.head? = some a) (ht : p.getLast? = some b)
      (hc : FourNeighborAdjacent b a)
      (hadj : ∀ u v l₁ l₂, p = l₁ ++ u :: v :: l₂ → FourNeighborAdjacent u v) :=
          MixedCycleDetails.cycle_chain p hadj
  have rotate_chain (p : List GaussianInt) (k : Nat) (a b : GaussianInt)
      (hh : p.head? = some a) (ht : p.getLast? = some b)
      (hc : FourNeighborAdjacent b a)
      (hchain : p.IsChain FourNeighborAdjacent) (hk : k < p.length) :
      (p.rotate k).IsChain FourNeighborAdjacent := MixedBoundaryCycleProof.rotate_chain p k a b
          hh ht hc hchain hk
  have takeArc {α : Type} (a b : α) (u v : List α) := MixedCycleDetails.takeArc (α := α) a b u v
  have hp₁chain : p₁.IsChain FourNeighborAdjacent :=
    cycle_chain p₁ a₁ b₁ hhead₁ hlast₁ hclose₁ hadj₁
  have hp₂chain : p₂.IsChain FourNeighborAdjacent :=
    cycle_chain p₂ a₂ b₂ hhead₂ hlast₂ hclose₂ hadj₂
  have sourceEdgeChain (p : List GaussianInt) (a b : GaussianInt)
      (E : Set (Finset GaussianInt))
      (hh : p.head? = some a) (ht : p.getLast? = some b)
      (hcloseE : ({b, a} : Finset GaussianInt) ∈ E)
      (hedges : ∀ u v l₁ l₂, p = l₁ ++ u :: v :: l₂ → ({u, v} : Finset GaussianInt) ∈ E) :
      Cycle.Chain (fun u v => ({u, v} : Finset GaussianInt) ∈ E) (p : Cycle GaussianInt) :=
          MixedBoundaryCycleProof.sourceEdgeChain p a b E hh ht hcloseE hedges
  have hc₂chain : (p₂.rotate (p₂.idxOf x)).IsChain FourNeighborAdjacent :=
    rotate_chain p₂ (p₂.idxOf x) a₂ b₂ hhead₂ hlast₂ hclose₂ hp₂chain hidx₂x
  let c₂ := p₂.rotate (p₂.idxOf x)
  have hc₂y := MixedCycleDetails.hc₂y p₂ x y hy₂
  have hc₂nodup : c₂.Nodup := (List.nodup_rotate).2 hp₂
  have hc₂tail := MixedCycleDetails.hc₂tail p₂ x y hxy hrot₂x hc₂y
  let good (z : GaussianInt) : Bool := @decide (z ∉ V₁) (Classical.propDecidable _)
  let rest₂ := c₂.tail.dropWhile good
  have hrest₂ne := MixedCycleDetails.hrest₂ne V₁ V₂ p₂ x y hy hc₂tail
  obtain ⟨z, zs, hrest₂⟩ : ∃ z zs, rest₂ = z :: zs := by
    cases h : rest₂ with
    | nil => exact (hrest₂ne h).elim
    | cons z zs => exact ⟨z, zs, rfl⟩
  have hzV₁ := MixedCycleDetails.hzV₁ V₁ p₂ x z zs hrest₂
  have hdecomp₂ : c₂.tail.takeWhile good ++ rest₂ = c₂.tail :=
    List.takeWhile_append_dropWhile
  have hzTail := MixedCycleDetails.hzTail V₁ p₂ x z zs hrest₂
  have hxNotTail := MixedCycleDetails.hxNotTail p₂ x hrot₂x hc₂nodup
  have hzx := MixedCycleDetails.hzx p₂ x z hzTail hxNotTail
  let c₁ := p₁.rotate (p₁.idxOf z)
  have hidx₁z : p₁.idxOf z < p₁.length :=
    List.idxOf_lt_length_iff.mpr (by rw [hV₁] at hzV₁; exact List.mem_toFinset.mp hzV₁)
  have hrot₁z := MixedCycleDetails.hrot₁z p₁ z hidx₁z
  have hc₁shape := MixedCycleDetails.hc₁shape p₁ z hrot₁z
  have hc₁x : x ∈ c₁.tail := MixedBoundaryCycleProof.hc₁x p₁ x hx₁ z hzx hrot₁z
  have hc₁nodup := MixedCycleDetails.hc₁nodup p₁ hp₁ z
  let good₁ (w : GaussianInt) : Bool := decide (w ≠ x)
  let rest₁ := c₁.tail.dropWhile good₁
  have hrest₁ne := MixedCycleDetails.hrest₁ne p₁ x z hc₁x
  obtain ⟨w, ws, hrest₁⟩ : ∃ w ws, rest₁ = w :: ws := by
    cases h : rest₁ with
    | nil => exact (hrest₁ne h).elim
    | cons w ws => exact ⟨w, ws, rfl⟩
  have hwx := MixedCycleDetails.hwx p₁ x z w ws hrest₁
  have hdecomp₁ : c₁.tail.takeWhile good₁ ++ rest₁ = c₁.tail :=
    List.takeWhile_append_dropWhile
  let R := z :: (c₁.tail.takeWhile good₁ ++ [x])
  let prefix₂ := c₂.tail.takeWhile good
  have hc₂shape := MixedCycleDetails.hc₂shape p₂ x hrot₂x
  have hdecomp₂' := MixedCycleDetails.hdecomp₂' V₁ p₂ x z zs
      hrest₂ hdecomp₂
  let prefix₁ := c₁.tail.takeWhile good₁
  have hc₁chain : c₁.IsChain FourNeighborAdjacent :=
    rotate_chain p₁ (p₁.idxOf z) a₁ b₁ hhead₁ hlast₁ hclose₁ hp₁chain hidx₁z
  have sourceE₁ := MixedCycleDetails.sourceE₁ E₁ p₁ a₁ b₁ hhead₁ hlast₁ hedge₁
          sourceEdgeChain
  have sourceE₂ := MixedCycleDetails.sourceE₂ E₂ p₂ a₂ b₂ hhead₂ hlast₂ hedge₂
          sourceEdgeChain
  have hp₂cycleeq := MixedCycleDetails.hp₂cycleeq p₂ x hidx₂x
  have hc₂edgeCycle := MixedCycleDetails.hc₂edgeCycle E₂ p₂ x sourceE₂ hp₂cycleeq
  have hc₂edgeChain := MixedCycleDetails.hc₂edgeChain E₂ p₂ x
          hc₂shape hc₂edgeCycle
  have hp₁cycleeq := MixedCycleDetails.hp₁cycleeq p₁ z hidx₁z
  have hc₁edgeCycle := MixedCycleDetails.hc₁edgeCycle E₁ p₁ z sourceE₁ hp₁cycleeq
  have hc₁edgeChain := MixedCycleDetails.hc₁edgeChain E₁ p₁ z
          hc₁shape hc₁edgeCycle
  let Q := x :: (prefix₂ ++ [z])
  have hQlast := MixedCycleDetails.hQlast V₁ p₂ x z
  have hQedgePrefix := MixedCycleDetails.hQedgePrefix V₁ p₂ x takeArc z zs hdecomp₂'
  have hQedge := MixedCycleDetails.hQedge V₁ E₂ p₂ x z hc₂edgeChain hQedgePrefix
  have hdecomp₁' := MixedCycleDetails.hdecomp₁' p₁ x z w ws hrest₁
      hwx hdecomp₁
  have hRedgePrefix := MixedCycleDetails.hRedgePrefix p₁ x takeArc z ws hdecomp₁'
  have hRedge : R.IsChain (fun u v => ({u, v} : Finset GaussianInt) ∈ E₁) :=
      MixedCycleDetails.hRedge E₁ p₁ x z hc₁edgeChain hRedgePrefix
  have hRtailE₁ : R.tail.IsChain (fun u v => ({u, v} : Finset GaussianInt) ∈ E₁) := by
    simpa [R, prefix₁] using (List.isChain_cons.mp hRedge).2
  have hRstepE₁ : ∀ v ∈ R.tail.head?, ({z, v} : Finset GaussianInt) ∈ E₁ :=
    by simpa [R, prefix₁] using (List.isChain_cons.mp hRedge).1
  let edgeRel (u v : GaussianInt) : Prop :=
    ({u, v} : Finset GaussianInt) ∈ E₁ ∪ E₂
  have hQunion : Q.IsChain edgeRel := hQedge.imp (fun _ _ huv => Or.inr huv)
  have hRtailUnion : R.tail.IsChain edgeRel := hRtailE₁.imp (fun _ _ huv => Or.inl huv)
  have hPplusUnion : (Q ++ R.tail).IsChain edgeRel := MixedCycleDetails.hPplusUnion V₁ E₁ E₂ p₁
      p₂ x z hQlast hRstepE₁ hQunion hRtailUnion
  have hQprefix := MixedCycleDetails.hQprefix V₁ p₂ x takeArc
      z zs hc₂shape hdecomp₂'
  have hQchain := MixedCycleDetails.hQchain V₁ p₂ x hc₂chain z
      hQprefix
  have hRprefix := MixedCycleDetails.hRprefix p₁ x takeArc z
      hc₁shape ws hdecomp₁'
  have hRchain := MixedCycleDetails.hRchain p₁ x z hc₁chain
      hRprefix
  have hQnodup := MixedCycleDetails.hQnodup V₁ p₂ x hc₂nodup z hQprefix
  have hprefix₁nodup : prefix₁.Nodup :=
    (List.takeWhile_sublist good₁).nodup hc₁nodup.tail
  have hxnotprefix₁ : x ∉ prefix₁ := by
    intro hxpre
    simpa [good₁] using List.mem_takeWhile_imp hxpre
  have hznotprefix₁ := MixedCycleDetails.hznotprefix₁ p₁ x z hrot₁z hc₁nodup
  have hcross : ∀ v ∈ Q, ∀ w ∈ prefix₁, v ≠ w :=
    MixedBoundaryCycleProof.rotatedPrefixesDisjoint V₁ p₁ c₁ x z hV₁ rfl
      hc₁shape c₂.tail hxnotprefix₁ hznotprefix₁
  have hpNodup := MixedCycleDetails.hpNodup V₁ p₁ p₂ x z hQnodup
      hprefix₁nodup hcross
  let p := Q ++ prefix₁
  have hpne : p ≠ [] := by simp [p, Q]
  have hRtail : R.tail = prefix₁ ++ [x] := by simp [R, prefix₁]
  have hRstep := MixedCycleDetails.hRstep p₁ x z
      hRchain
  have hPplus : (Q ++ R.tail).IsChain FourNeighborAdjacent := MixedCycleDetails.hPplus V₁ p₁ p₂ x
      z hQlast hQchain hRchain hRstep
  have hPplusX : (p ++ [x]).IsChain FourNeighborAdjacent := by
    simpa [p, hRtail, List.append_assoc] using hPplus
  have hpChain := MixedCycleDetails.hpChain V₁ p₁ p₂ x z hPplusX
  have hcloseP := MixedCycleDetails.hcloseP V₁ p₁ p₂ x
      z hpne hPplusX
  have hpPlusUnion : (p ++ [x]).IsChain edgeRel := by
    simpa [p, R, prefix₁, List.append_assoc] using hPplusUnion
  have hpUnionChain : p.IsChain edgeRel := by
    simpa using hpPlusUnion.left_of_append
  have hcloseUnion : edgeRel (p.getLast hpne) x := by
    simpa using hpPlusUnion.rel_getLast_head_of_append hpne (by simp)
  have hadjUnion : ∀ a b l₁ l₂, p = l₁ ++ a :: b :: l₂ → edgeRel a b :=
    List.isChain_iff_forall_rel_of_append_cons_cons.mp hpUnionChain
  have hphead : p.head? = some x := by simp [p, Q]
  have hplast : p.getLast? = some (p.getLast hpne) := List.getLast?_eq_some_getLast hpne
  let v := p.getLast hpne
  let parity (u : GaussianInt) : ZMod 2 := (u.re : ZMod 2) + (u.im : ZMod 2)
  have parityStep {u w : GaussianInt} (h : FourNeighborAdjacent u w) :
      parity w = parity u + 1 := MixedBoundaryCycleProof.parityStep (u := u) (w := w) h
  have hadjP := MixedCycleDetails.hadjP V₁ p₁ p₂ x z hpChain
  have hpLenTwo : 2 ≤ p.length := MixedCycleDetails.hpLenTwo V₁ p₁ p₂ x z
  have hpNotTwo : p.length ≠ 2 := MixedBoundaryCycleProof.hpNotTwo V₁ E₁ E₂ hdisjoint p₁ p₂ x z
      w hQedge hRedge
  have hpNotThree : p.length ≠ 3 := MixedBoundaryCycleProof.hpNotThree V₁ p₁ p₂ x z w hpne
      hcloseP hphead parityStep hadjP
  have hpLength : 4 ≤ p.length := by omega
  let W : Set GaussianInt := (p.toFinset : Set GaussianInt)
  let F : Set (Finset GaussianInt) := {e | e = {v, x} ∨
    ∃ a b l₁ l₂, p = l₁ ++ a :: b :: l₂ ∧ e = {a, b}}
  have hsimple := MixedCycleDetails.hsimple V₁ p₁ p₂ x z hpNodup hpne
      hcloseP hphead hplast hadjP hpLength
  have hlastE₁ : ({v, x} : Finset GaussianInt) ∈ E₁ := MixedBoundaryCycleProof.hlastE₁ V₁ E₁ p₁
      p₂ x z w hQlast hRtailE₁ hRstepE₁ hpne hRtail
  have hwrapF : ({v, x} : Finset GaussianInt) ∈ F := by simp [F]
  have hFsubset : F ⊆ E₁ ∪ E₂ := by
    rintro e (rfl | ⟨a, b, l₁, l₂, hp, rfl⟩)
    · simpa [v, edgeRel] using hcloseUnion
    · exact hadjUnion a b l₁ l₂ hp
  have hE₂ : ({x, prefix₂.headD z} : Finset GaussianInt) ∈ E₂ := MixedClosingEdges.hE₂ V₁ E₂ p₂ x
      z hQedge
  have hFf : ({x, prefix₂.headD z} : Finset GaussianInt) ∈ F := MixedClosingEdges.hFf V₁ p₁ p₂ x
      z hpne
  exact ⟨W, F, x, {v, x}, {x, prefix₂.headD z}, hsimple, hFsubset,
    by simp, by simp, ⟨hwrapF, hlastE₁⟩, ⟨hFf, hE₂⟩⟩

end ApollonianSuperharmonic

end
