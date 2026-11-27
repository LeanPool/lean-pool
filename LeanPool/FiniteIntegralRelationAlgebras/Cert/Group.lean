/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

-- Modified for Lean Pool, including adaptations to its Lean module layout.

module

public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Enc
public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Prim
public import LeanPool.FiniteIntegralRelationAlgebras.Theory.AutEquiv
public import LeanPool.FiniteIntegralRelationAlgebras.Theory.Orbits
public import Mathlib.Data.List.GetD

/-!
# Burnside's lemma over a certified list of group elements

An element of `IntegralAtom.Aut s n` is coded by a list `l` of `numAtoms s n` atom codes, meaning
that the atom with code `c` is sent to the atom with code `l[c]`. This file provides

* `RACert.validPerm s n l`: a Boolean check that `l` codes an element of `Aut s n`,
* `RACert.autOfList s n l`: the element of `Aut s n` coded by a valid list,
* `RACert.checkGroup s n reps elems`: a Boolean check of a certificate listing every element of
  `Aut s n` exactly once, each together with a conjugacy class representative and a conjugator,
* `RACert.card_ofSymmNsymm_of_groupCert`: Burnside's lemma, with the sum over the group
  replaced by a sum over the certificate of one fixed-point count per conjugacy class.

All Boolean checks are structurally recursive functions on lists of naturals built from the raw
functions `Nat.beq` and `Nat.blt`, so they evaluate by kernel reduction (`decide +kernel`) on
literals.
-/

@[expose] public section

namespace RACert

open FiniteIntegralRelationAlgebras.RelationAlgebra IntegralAtom

variable {s n : ℕ} {l t r : List ℕ}

/-! ### Boolean checks -/

/-- A Boolean check that a list of naturals has no duplicates. -/
def nodupN : List ℕ → Bool
  | [] => true
  | x :: xs => !(xs.any (Nat.beq x)) && nodupN xs

/-- A Boolean check that a list of naturals has no duplicates, with a linear-time fast path for
strictly increasing lists. -/
def distinctN (l : List ℕ) : Bool := increasing l || nodupN l

/-- `l` codes an element of `Aut s n`: length `k = numAtoms s n`, `l[0] = 0`, all entries `< k`,
no duplicates, and commutes with converse (`l[cvN s c] = cvN s l[c]` for all `c < k`). -/
def validPerm (s n : ℕ) (l : List ℕ) : Bool :=
  Nat.beq l.length (numAtoms s n) && Nat.beq (l.getD 0 0) 0 &&
    l.all (fun x => Nat.blt x (numAtoms s n)) && nodupN l &&
    (List.range (numAtoms s n)).all fun c => Nat.beq (l.getD (cvN s c) 0) (cvN s (l.getD c 0))

/-- The check of a single entry `(l, i, t)` of a group certificate: `l` and `t` are valid,
`i < reps.length`, and `l ∘ t = t ∘ reps[i]` as maps on codes. -/
def checkElem (s n : ℕ) (reps : List (List ℕ)) (e : List ℕ × ℕ × List ℕ) : Bool :=
  validPerm s n e.1 && validPerm s n e.2.2 && Nat.blt e.2.1 reps.length &&
    (List.range (numAtoms s n)).all fun c =>
      Nat.beq (e.1.getD (e.2.2.getD c 0) 0) (e.2.2.getD ((reps.getD e.2.1 []).getD c 0) 0)

/-- Certificate check. `reps` are the conjugacy class representatives; each entry `(l, i, t)` of
`elems` says: `l` is a group element, conjugate to `reps[i]` via `t`, i.e. `l ∘ t = t ∘ reps[i]`
as maps on codes (`∀ c < k, l[t[c]] = t[reps[i][c]]`). Checks: every `l` and `t` is `validPerm`,
every rep is `validPerm`, `i < reps.length`, the conjugation equations, the `l`'s are pairwise
distinct, and `elems.length = s! * n! * 2^n`.

Distinctness is checked on the base-`k` codes `codeL k l` of the `l`'s; this takes linear time if
`elems` is sorted lexicographically by `l` and quadratic time otherwise. -/
def checkGroup (s n : ℕ) (reps : List (List ℕ)) (elems : List (List ℕ × ℕ × List ℕ)) : Bool :=
  reps.all (validPerm s n) && elems.all (checkElem s n reps) &&
    distinctN (elems.map fun e => codeL (numAtoms s n) e.1) &&
    Nat.beq elems.length (s.factorial * n.factorial * 2 ^ n)

/-- `∑` over the certificate of the count attached to each element's class. -/
def weightedSum (counts : List ℕ) (elems : List (List ℕ × ℕ × List ℕ)) : ℕ :=
  (elems.map fun e => counts.getD e.2.1 0).sum

/-! ### Specifications of the Boolean checks -/

theorem nodupN_iff {l : List ℕ} : nodupN l = true ↔ l.Nodup := by
  induction l with
  | nil => simp [nodupN]
  | cons x xs ih =>
    simp only [nodupN, Bool.and_eq_true, Bool.not_eq_true', List.nodup_cons, ih]
    refine and_congr_left' ?_
    rw [← Bool.not_eq_true, List.any_eq_true]
    simp [Nat.beq_eq]

theorem nodup_of_distinctN {l : List ℕ} (h : distinctN l = true) : l.Nodup := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact (increasing_spec h).imp Nat.ne_of_lt
  · exact nodupN_iff.mp h

theorem validPerm_iff :
    validPerm s n l = true ↔
      l.length = numAtoms s n ∧ l.getD 0 0 = 0 ∧ (∀ x ∈ l, x < numAtoms s n) ∧ l.Nodup ∧
        ∀ c < numAtoms s n, l.getD (cvN s c) 0 = cvN s (l.getD c 0) := by
  simp only [validPerm, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, Nat.blt_eq,
    nodupN_iff, List.mem_range, and_assoc]

theorem checkElem_iff {reps : List (List ℕ)} {e : List ℕ × ℕ × List ℕ} :
    checkElem s n reps e = true ↔
      validPerm s n e.1 = true ∧ validPerm s n e.2.2 = true ∧ e.2.1 < reps.length ∧
        ∀ c < numAtoms s n,
          e.1.getD (e.2.2.getD c 0) 0 = e.2.2.getD ((reps.getD e.2.1 []).getD c 0) 0 := by
  simp only [checkElem, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, Nat.blt_eq,
    List.mem_range, and_assoc]

theorem checkGroup_spec {reps : List (List ℕ)} {elems : List (List ℕ × ℕ × List ℕ)}
    (h : checkGroup s n reps elems = true) :
    (∀ r ∈ reps, validPerm s n r = true) ∧ (∀ e ∈ elems, checkElem s n reps e = true) ∧
      (elems.map fun e => e.1).Nodup ∧ elems.length = s.factorial * n.factorial * 2 ^ n := by
  simp only [checkGroup, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, and_assoc] at h
  obtain ⟨hreps, helems, hnd, hlen⟩ := h
  refine ⟨hreps, helems, List.Nodup.of_map (codeL (numAtoms s n)) ?_, hlen⟩
  rw [List.map_map]
  exact nodup_of_distinctN hnd

/-! ### The atom map of a valid list -/

theorem validPerm_length (h : validPerm s n l = true) : l.length = numAtoms s n :=
  (validPerm_iff.mp h).1

theorem validPerm_getD_lt (h : validPerm s n l = true) {c : ℕ} (hc : c < numAtoms s n) :
    l.getD c 0 < numAtoms s n := by
  obtain ⟨hlen, -, hlt, -, -⟩ := validPerm_iff.mp h
  rw [List.getD_eq_getElem l 0 (hlen ▸ hc)]
  exact hlt _ (List.getElem_mem _)

theorem validPerm_getD_inj (h : validPerm s n l = true) {c d : ℕ} (hc : c < numAtoms s n)
    (hd : d < numAtoms s n) (hcd : l.getD c 0 = l.getD d 0) : c = d := by
  obtain ⟨hlen, -, -, hnd, -⟩ := validPerm_iff.mp h
  rw [List.getD_eq_getElem l 0 (hlen ▸ hc), List.getD_eq_getElem l 0 (hlen ▸ hd)] at hcd
  exact (hnd.getElem_inj_iff).mp hcd

/-- For a valid list, the code of the image of `a` is the entry at the code of `a`. -/
theorem enc_permFun (h : validPerm s n l = true) (a : IntegralAtom (Fin s) (Fin n)) :
    enc (permFun s n l a) = l.getD (enc a) 0 :=
  enc_dec (validPerm_getD_lt h (enc_lt a))

theorem permFun_one (h : validPerm s n l = true) : permFun s n l one = one := by
  rw [permFun, enc_one, (validPerm_iff.mp h).2.1, dec_zero]

theorem permFun_conv (h : validPerm s n l = true) (a : IntegralAtom (Fin s) (Fin n)) :
    permFun s n l (conv a) = conv (permFun s n l a) := by
  rw [permFun, permFun, enc_conv, (validPerm_iff.mp h).2.2.2.2 _ (enc_lt a),
    dec_cvN (validPerm_getD_lt h (enc_lt a))]

theorem permFun_injective (h : validPerm s n l = true) :
    Function.Injective (permFun s n l) := fun a b hab => by
  have := congrArg enc hab
  rw [enc_permFun h, enc_permFun h] at this
  exact enc_injective (validPerm_getD_inj h (enc_lt a) (enc_lt b) this)

theorem permFun_bijective (h : validPerm s n l = true) :
    Function.Bijective (permFun s n l) :=
  Finite.injective_iff_bijective.mp (permFun_injective h)

/-- The element of `Aut s n` coded by a list (the identity if the list is not valid). -/
noncomputable def autOfList (s n : ℕ) (l : List ℕ) : Aut s n :=
  if h : validPerm s n l = true then
    ⟨Equiv.ofBijective (permFun s n l) (permFun_bijective h),
      mem_aut_iff.mpr ⟨permFun_one h, permFun_conv h⟩⟩
  else 1

theorem autOfList_apply (h : validPerm s n l = true) (a : IntegralAtom (Fin s) (Fin n)) :
    (autOfList s n l).val a = permFun s n l a := by
  unfold autOfList
  split
  · rfl
  · contradiction

/-- Valid lists coding the same element of `Aut s n` are equal. -/
theorem autOfList_inj (hl : validPerm s n l = true) (ht : validPerm s n t = true)
    (h : autOfList s n l = autOfList s n t) : l = t := by
  refine List.ext_getElem ((validPerm_length hl).trans (validPerm_length ht).symm)
    fun c hc hc' => ?_
  have hck : c < numAtoms s n := validPerm_length hl ▸ hc
  have := congrArg (fun σ : Aut s n => enc (σ.val (dec s n c))) h
  simp only [autOfList_apply hl, autOfList_apply ht, enc_permFun hl, enc_permFun ht,
    enc_dec hck] at this
  rwa [List.getD_eq_getElem l 0 hc, List.getD_eq_getElem t 0 hc'] at this

/-- The conjugation equation on codes gives a conjugation in `Aut s n`. -/
theorem autOfList_eq_conj (hl : validPerm s n l = true) (ht : validPerm s n t = true)
    (hr : validPerm s n r = true)
    (h : ∀ c < numAtoms s n, l.getD (t.getD c 0) 0 = t.getD (r.getD c 0) 0) :
    autOfList s n l = autOfList s n t * autOfList s n r * (autOfList s n t)⁻¹ := by
  refine eq_mul_inv_of_mul_eq (Subtype.ext (Equiv.ext fun a => enc_injective ?_))
  change enc ((autOfList s n l).val ((autOfList s n t).val a)) =
    enc ((autOfList s n t).val ((autOfList s n r).val a))
  rw [autOfList_apply hl, autOfList_apply ht, autOfList_apply ht, autOfList_apply hr,
    enc_permFun hl, enc_permFun ht, enc_permFun ht, enc_permFun hr]
  exact h _ (enc_lt a)

/-! ### Fixed-point counts are class functions -/

/-- The number of lawful cycle sets invariant under `σ`. -/
noncomputable def fixCount (σ : Aut s n) : ℕ :=
  Nat.card {T : Set (Cycle (Fin s) (Fin n)) // IsLawfulCycles T ∧
    ∀ a b c, (σ.val a, σ.val b, σ.val c) ∈ T ↔ (a, b, c) ∈ T}

theorem fixCountL_eq_fixCount (h : validPerm s n l = true) :
    fixCountL s n l = fixCount (autOfList s n l) := by
  simp only [fixCountL, fixCount, autOfList_apply h]

theorem fixCount_eq_card_fixedBy (σ : Aut s n) :
    fixCount σ =
      Nat.card (MulAction.fixedBy {T : Set (Cycle (Fin s) (Fin n)) // IsLawfulCycles T} σ) :=
  Nat.card_congr (fixedByEquiv σ).symm

/-- The fixed-point count is a class function. -/
theorem fixCount_conj (σ τ : Aut s n) : fixCount (τ * σ * τ⁻¹) = fixCount σ := by
  rw [fixCount_eq_card_fixedBy, fixCount_eq_card_fixedBy]
  refine (Nat.card_congr ((MulAction.toPerm τ).subtypeEquiv fun T => ?_)).symm
  simp only [MulAction.mem_fixedBy, MulAction.toPerm_apply, mul_smul, inv_smul_smul,
    smul_left_cancel_iff]

/-- Conjugate valid lists have the same fixed-point count. -/
theorem fixCountL_eq_of_conj (hl : validPerm s n l = true) (ht : validPerm s n t = true)
    (hr : validPerm s n r = true)
    (h : ∀ c < numAtoms s n, l.getD (t.getD c 0) 0 = t.getD (r.getD c 0) 0) :
    fixCountL s n l = fixCountL s n r := by
  rw [fixCountL_eq_fixCount hl, fixCountL_eq_fixCount hr, autOfList_eq_conj hl ht hr h,
    fixCount_conj]

/-! ### Enumerating the group by a list -/

/-- A duplicate-free list of `|Aut s n|` valid lists enumerates `Aut s n` exactly once. -/
theorem sum_aut_eq_sum_map [Fintype (Aut s n)] {ls : List (List ℕ)}
    (hvalid : ∀ l ∈ ls, validPerm s n l = true) (hnd : ls.Nodup)
    (hlen : ls.length = s.factorial * n.factorial * 2 ^ n) (F : Aut s n → ℕ) :
    ∑ σ : Aut s n, F σ = (ls.map fun l => F (autOfList s n l)).sum := by
  classical
  have hnd' : (ls.map (autOfList s n)).Nodup :=
    hnd.map_on fun x hx y hy hxy => autOfList_inj (hvalid x hx) (hvalid y hy) hxy
  have huniv : (ls.map (autOfList s n)).toFinset = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [List.toFinset_card_of_nodup hnd', List.length_map, hlen, ← card_aut,
      Nat.card_eq_fintype_card]
  rw [← huniv, List.sum_toFinset _ hnd', List.map_map]
  rfl

/-! ### Burnside's lemma over a certificate -/

/-- Burnside's lemma over a group certificate: if `checkGroup` accepts `reps` and `elems`, the
`i`-th representative fixes `counts[i]` lawful cycle sets, and the counts summed over the
certificate give `N * |Aut s n|`, then there are `N` isomorphism classes. -/
theorem card_ofSymmNsymm_of_groupCert (s n N : ℕ) (reps : List (List ℕ))
    (elems : List (List ℕ × ℕ × List ℕ)) (counts : List ℕ)
    (hcert : checkGroup s n reps elems = true)
    (hcounts : ∀ i < reps.length, fixCountL s n (reps.getD i []) = counts.getD i 0)
    (hsum : weightedSum counts elems = N * (s.factorial * n.factorial * 2 ^ n)) :
    Nat.card (IntegralAtom.IsoClass.ofSymmNsymm s n) = N := by
  classical
  obtain ⟨hreps, helems, hnd, hlen⟩ := checkGroup_spec hcert
  let _ : Fintype (Aut s n) := Fintype.ofFinite _
  refine IntegralAtom.IsoClass.card_ofSymmNsymm_eq_of_sum' s n N ?_
  rw [card_aut, ← hsum]
  change ∑ σ : Aut s n, fixCount σ = _
  rw [sum_aut_eq_sum_map (ls := elems.map fun e => e.1) ?_ hnd (by rw [List.length_map, hlen]),
    List.map_map, weightedSum]
  · refine congrArg List.sum (List.map_congr_left fun e he => ?_)
    obtain ⟨hl, ht, hi, hconj⟩ := checkElem_iff.mp (helems e he)
    have hr : validPerm s n (reps.getD e.2.1 []) = true :=
      hreps _ (List.getD_eq_getElem reps [] hi ▸ List.getElem_mem hi)
    rw [Function.comp_apply, ← hcounts _ hi, ← fixCountL_eq_fixCount hl,
      fixCountL_eq_of_conj hl ht hr hconj]
  · intro l hl
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hl
    exact (checkElem_iff.mp (helems e he)).1

/-- A version of `card_ofSymmNsymm_of_groupCert` with the fixed-point counts of the
representatives given as a `List.Forall₂`, i.e. one hypothesis `fixCountL s n rᵢ = cᵢ` per
conjugacy class. -/
theorem card_ofSymmNsymm_of_groupCert' (s n N : ℕ) (reps : List (List ℕ))
    (elems : List (List ℕ × ℕ × List ℕ)) (counts : List ℕ)
    (hcert : checkGroup s n reps elems = true)
    (hcounts : List.Forall₂ (fun r c => fixCountL s n r = c) reps counts)
    (hsum : weightedSum counts elems = N * (s.factorial * n.factorial * 2 ^ n)) :
    Nat.card (IntegralAtom.IsoClass.ofSymmNsymm s n) = N := by
  refine card_ofSymmNsymm_of_groupCert s n N reps elems counts hcert (fun i hi => ?_) hsum
  obtain ⟨hlen, h⟩ := List.forall₂_iff_get.mp hcounts
  have hi' : i < counts.length := hlen ▸ hi
  rw [List.getD_eq_getElem reps [] hi, List.getD_eq_getElem counts 0 hi']
  exact h i hi hi'

end RACert
