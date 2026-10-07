/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Thue.Matiyasevich.Padding
public import Mathlib.Data.List.Chain

/-!
The binary coding stage in Section 2.3 of Matiyasevich (1995).  If the
source alphabet has `N` letters, the (zero-based) form of (18) is

`a_j ↦ a a b^(j+1) a b^(N-j)`.

Thus every codeword has length `N + 4`, begins with the synchronizing marker
`aa`, and ends in `b`.
-/

@[expose] public section

namespace Undecidability
namespace Thue
namespace Matiyasevich1993
namespace Binary

variable {N r : ℕ}

/-- The first letter of the binary alphabet used in the first coding stage. -/
abbrev binaryLetterA : Fin 2 := 0
/-- The second letter of the binary alphabet used in the first coding stage. -/
abbrev binaryLetterB : Fin 2 := 1

/-- The letter code `ρ₁(a_j)` from (18), with `j` represented zero-based. -/
def rho₁Letter (N : ℕ) (j : Fin N) : List (Fin 2) :=
  [binaryLetterA, binaryLetterA] ++ List.replicate (j.val + 1) binaryLetterB ++
    [binaryLetterA] ++ List.replicate (N - j.val) binaryLetterB

/-- The homomorphic extension of `ρ₁` to words. -/
def rho₁ (N : ℕ) (W : List (Fin N)) : List (Fin 2) :=
  W.flatMap (rho₁Letter N)

@[simp] theorem rho₁_cons (j : Fin N) (W : List (Fin N)) :
    rho₁ N (j :: W) = rho₁Letter N j ++ rho₁ N W := by
  simp [rho₁]

@[simp] theorem rho₁_append (X Y : List (Fin N)) :
    rho₁ N (X ++ Y) = rho₁ N X ++ rho₁ N Y := by
  simp [rho₁]

@[simp] theorem rho₁Letter_length (j : Fin N) :
    (rho₁Letter N j).length = N + 4 := by
  simp only [rho₁Letter, List.length_append, List.length_cons,
    List.length_nil, List.length_replicate]
  omega

@[simp] theorem rho₁_length (W : List (Fin N)) :
    (rho₁ N W).length = W.length * (N + 4) := by
  induction W with
  | nil =>
      unfold rho₁
      simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | cons j W ih => simp [ih, Nat.add_mul, Nat.add_comm]

theorem rho₁_computable (N : ℕ) : Computable (rho₁ N) :=
  (Primrec.list_flatMap Primrec.id
    ((Primrec.dom_finite (rho₁Letter N)).comp₂ Primrec₂.right)).to_comp

/-- Read the length of the first `b`-run after the initial marker. -/
def indexRun (W : List (Fin 2)) : ℕ :=
  ((W.drop 2).takeWhile fun x => x == binaryLetterB).length

@[simp] theorem indexRun_rho₁Letter (j : Fin N) :
    indexRun (rho₁Letter N j) = j.val + 1 := by
  simp [indexRun, rho₁Letter, binaryLetterA, binaryLetterB]

theorem rho₁Letter_injective : Function.Injective (rho₁Letter N) := by
  intro i j h
  have hrun := congrArg indexRun h
  simp only [indexRun_rho₁Letter] at hrun
  exact Fin.ext (by omega)

theorem rho₁Letter_ends_b (j : Fin N) :
    ∃ init, rho₁Letter N j = init ++ [(1 : Fin 2)] := by
  let k := N - j.val - 1
  refine ⟨[binaryLetterA, binaryLetterA] ++ List.replicate (j.val + 1) binaryLetterB ++
    [binaryLetterA] ++ List.replicate k binaryLetterB, ?_⟩
  have hm : N - j.val = k + 1 := by dsimp [k]; omega
  rw [rho₁Letter, hm]
  simp only [List.append_assoc, List.append_cancel_left_eq]
  exact List.replicate_succ'

private theorem rho₁Letter_tail_chain (j : Fin N) :
    (rho₁Letter N j).tail.IsChain
      (fun x y : Fin 2 => x ≠ binaryLetterA ∨ y ≠ binaryLetterA) := by
  have hba : ∀ k : ℕ,
      (binaryLetterB :: List.replicate k binaryLetterB ++ [binaryLetterA]).IsChain
        (fun x y : Fin 2 => x ≠ binaryLetterA ∨ y ≠ binaryLetterA) := by
    intro k
    induction k with
    | zero => simp [binaryLetterA, binaryLetterB]
    | succ k ih => simpa [List.replicate_succ, binaryLetterA, binaryLetterB] using ih
  have hbb : ∀ k : ℕ,
      (binaryLetterB :: List.replicate k binaryLetterB).IsChain
        (fun x y : Fin 2 => x ≠ binaryLetterA ∨ y ≠ binaryLetterA) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => simpa [List.replicate_succ, binaryLetterA, binaryLetterB] using ih
  have hm : N - j.val = Nat.succ (N - j.val - 1) := by omega
  simp only [rho₁Letter]
  rw [show j.val + 1 = Nat.succ j.val by omega, hm]
  simpa [List.replicate_succ, binaryLetterA, binaryLetterB] using
    And.intro (hba j.val) (hbb (N - j.val - 1))

private theorem rho₁Letter_getLast (j : Fin N) :
    (rho₁Letter N j).getLast? = some binaryLetterB := by
  have hm : N - j.val ≠ 0 := by omega
  have hrep : List.replicate (N - j.val) binaryLetterB ≠ [] := by simpa using hm
  rw [rho₁Letter, List.getLast?_append_of_ne_nil _ hrep]
  simp [List.getLast?_replicate, hm, binaryLetterB]

/-- An occurrence of `aa` cannot start strictly inside a codeword. -/
private theorem rho₁_boundary_edge
    (j : Fin N) (l bs tail : List (Fin 2)) (W : List (Fin N))
    (hc : rho₁Letter N j = l ++ bs)
    (heq : [binaryLetterA, binaryLetterA] ++ tail = bs ++ rho₁ N W) :
    l = [] ∨ bs = [] := by
  cases l with
  | nil => exact Or.inl rfl
  | cons z l =>
      cases bs with
      | nil => exact Or.inr rfl
      | cons x bs =>
          cases bs with
          | nil =>
              exfalso
              have hlast : (rho₁Letter N j).getLast? = some x := by
                rw [hc, List.getLast?_append_of_ne_nil (z :: l) (by simp)]
                simp
              rw [rho₁Letter_getLast] at hlast
              injection hlast with hbx
              have heq' : binaryLetterA :: binaryLetterA :: tail = x :: rho₁ N W := by
                simpa only [List.cons_append, List.nil_append] using heq
              injection heq' with hx _
              exact (by decide : binaryLetterB ≠ binaryLetterA) (hbx.trans hx.symm)
          | cons y bs =>
              exfalso
              have htail : (rho₁Letter N j).tail = l ++ x :: y :: bs := by
                simpa only [List.cons_append, List.tail_cons] using
                  congrArg List.tail hc
              have hchain := rho₁Letter_tail_chain j
              rw [htail, List.isChain_append_cons_cons] at hchain
              have hxy := hchain.2.1
              have heq' : binaryLetterA :: binaryLetterA :: tail = x :: y :: (bs ++ rho₁ N W) := by
                simpa only [List.cons_append, List.nil_append, List.append_assoc]
                  using heq
              injection heq' with hx hrest
              injection hrest with hy _
              subst x
              subst y
              simp at hxy

/-- Every synchronizing marker `aa` in an encoded word is at a codeword
boundary. -/
private theorem rho₁_marker_boundary {W : List (Fin N)}
    {l tail : List (Fin 2)}
    (h : rho₁ N W = l ++ [binaryLetterA, binaryLetterA] ++ tail) :
    ∃ L R, W = L ++ R ∧ l = rho₁ N L := by
  induction W generalizing l tail with
  | nil => simp [rho₁] at h
  | cons j W ih =>
      rw [rho₁_cons] at h
      have h' : rho₁Letter N j ++ rho₁ N W =
          l ++ ([binaryLetterA, binaryLetterA] ++ tail) := by
        simpa only [List.append_assoc] using h
      rcases List.append_eq_append_iff.mp h' with
        ⟨as, hl, hs⟩ | ⟨bs, hc, ht⟩
      · obtain ⟨L, R, hW, has⟩ := ih (by
          simpa only [List.append_assoc] using hs)
        refine ⟨j :: L, R, ?_, ?_⟩
        · simp [hW]
        · simp [hl, has]
      · have hedge : l = [] ∨ bs = [] :=
          rho₁_boundary_edge j l bs tail W hc ht
        rcases hedge with rfl | rfl
        · exact ⟨[], j :: W, by simp, by simp [rho₁]⟩
        · exact ⟨[j], W, by simp, by simpa [rho₁] using hc.symm⟩

/-- The binary code reflects prefixes. -/
private theorem rho₁_prefix {X W : List (Fin N)} {s : List (Fin 2)}
    (h : rho₁ N W = rho₁ N X ++ s) :
    ∃ R, W = X ++ R ∧ s = rho₁ N R := by
  induction X generalizing W s with
  | nil => exact ⟨W, by simp, by simpa [rho₁] using h.symm⟩
  | cons j X ih =>
      cases W with
      | nil =>
          have hlen := congrArg List.length h
          simp at hlen
          omega
      | cons k W =>
          rw [rho₁_cons, rho₁_cons, List.append_assoc] at h
          have hparts := List.append_inj h
            (show (rho₁Letter N k).length = (rho₁Letter N j).length by simp)
          have hkj : k = j := rho₁Letter_injective hparts.1
          subst k
          obtain ⟨R, hW, hs⟩ := ih hparts.2
          exact ⟨R, by simp [hW], hs⟩

theorem rho₁_injective : Function.Injective (rho₁ N) := by
  intro X Y h
  obtain ⟨R, hY, hR⟩ :=
    rho₁_prefix (W := Y) (X := X) (s := []) (by simpa using h.symm)
  have hRnil : R = [] := by
    have hlen := congrArg List.length hR
    simp only [List.length_nil, rho₁_length] at hlen
    have hmul : R.length * (N + 4) = 0 := hlen.symm
    rcases Nat.mul_eq_zero.mp hmul with hzero | hzero
    · exact List.eq_nil_of_length_eq_zero hzero
    · omega
  subst R
  simpa using hY.symm

/-- Every nonempty encoded word begins with the synchronizing marker. -/
theorem rho₁_starts_aa {W : List (Fin N)} (hW : W ≠ []) :
    ∃ tail, rho₁ N W = (0 : Fin 2) :: 0 :: tail := by
  cases W with
  | nil => contradiction
  | cons j W =>
      refine ⟨List.replicate (j.val + 1) binaryLetterB ++ [binaryLetterA] ++
        List.replicate (N - j.val) binaryLetterB ++ rho₁ N W, ?_⟩
      simp [rho₁Letter, binaryLetterA, List.append_assoc]

/-- The code language contains no run `aaa`. -/
theorem rho₁_noAAA (W : List (Fin N)) :
    ¬ ∃ l s, rho₁ N W = l ++ [(0 : Fin 2), 0, 0] ++ s := by
  rintro ⟨l, s, h⟩
  have hm : rho₁ N W = l ++ [binaryLetterA, binaryLetterA] ++ (binaryLetterA :: s) := by
    simpa [binaryLetterA, List.append_assoc] using h
  obtain ⟨L, R, hW, hl⟩ := rho₁_marker_boundary hm
  subst W
  rw [rho₁_append, hl] at h
  have hR : rho₁ N R = [binaryLetterA, binaryLetterA, binaryLetterA] ++ s := by
    simpa only [List.append_assoc, List.append_cancel_left_eq] using h
  cases R with
  | nil => simp [rho₁] at hR
  | cons j R =>
      rw [rho₁_cons] at hR
      have hk : j.val + 1 = Nat.succ j.val := by omega
      rw [rho₁Letter, hk, List.replicate_succ] at hR
      simp [binaryLetterA, binaryLetterB] at hR

/-- A nonempty encoded word can occur inside another encoded word only at
codeword boundaries. -/
private theorem rho₁_occurrence {W X : List (Fin N)} {l s : List (Fin 2)}
    (hX : X ≠ []) (h : rho₁ N W = l ++ rho₁ N X ++ s) :
    ∃ L R, W = L ++ X ++ R ∧ l = rho₁ N L ∧ s = rho₁ N R := by
  cases X with
  | nil => contradiction
  | cons j X =>
      rw [rho₁_cons, ← List.append_assoc] at h
      have hm : rho₁ N W = l ++ [binaryLetterA, binaryLetterA] ++
          ((rho₁Letter N j).drop 2 ++ rho₁ N X ++ s) := by
        simpa [rho₁Letter, List.drop, List.append_assoc] using h
      obtain ⟨L, W', hW, hl⟩ := rho₁_marker_boundary hm
      subst W
      rw [hl] at h
      have hp : rho₁ N W' = rho₁ N (j :: X) ++ s := by
        simpa only [rho₁_cons, rho₁_append, List.append_assoc,
          List.append_cancel_left_eq] using h
      obtain ⟨R, hW', hs⟩ := rho₁_prefix hp
      exact ⟨L, R, by simp [hW'], hl, hs⟩

/-- The two sides of the binary system `T₂'`. -/
def stage₂PrimeF (F : Fin r → List (Fin N)) (i : Fin r) : List (Fin 2) :=
  rho₁ N (F i)

/-- The right-hand rule words after the first binary alphabet encoding. -/
def stage₂PrimeE (E : Fin r → List (Fin N)) (i : Fin r) : List (Fin 2) :=
  rho₁ N (E i)

/-- The Thue system obtained by applying the first binary alphabet encoding to all rules. -/
def stage₂PrimeSystem (F E : Fin r → List (Fin N)) : ThueSystem (Fin 2) :=
  finiteSystem (stage₂PrimeF F) (stage₂PrimeE E)

@[simp] theorem stage₂PrimeF_length (F : Fin r → List (Fin N)) (i : Fin r) :
    (stage₂PrimeF F i).length = (F i).length * (N + 4) := by
  simp [stage₂PrimeF]

@[simp] theorem stage₂PrimeE_length (E : Fin r → List (Fin N)) (i : Fin r) :
    (stage₂PrimeE E i).length = (E i).length * (N + 4) := by
  simp [stage₂PrimeE]

/-- Common source-side lengths become common binary-side lengths. -/
theorem stage₂PrimeF_common_length (F : Fin r → List (Fin N)) (p : ℕ)
    (hF : ∀ i, (F i).length = p) (i : Fin r) :
    (stage₂PrimeF F i).length = p * (N + 4) := by
  simp [hF]

theorem stage₂PrimeE_common_length (E : Fin r → List (Fin N)) (q : ℕ)
    (hE : ∀ i, (E i).length = q) (i : Fin r) :
    (stage₂PrimeE E i).length = q * (N + 4) := by
  simp [hE]

private theorem thueStep_encode (F E : Fin r → List (Fin N))
    {X Y : List (Fin N)}
    (h : ThueStep (finiteSystem F E) X Y) :
    ThueStep (stage₂PrimeSystem F E) (rho₁ N X) (rho₁ N Y) := by
  rcases h with ⟨l, s, x, y, ⟨i, hxy⟩, hwords⟩
  injection hxy with hx hy
  subst x
  subst y
  refine ⟨rho₁ N l, rho₁ N s, stage₂PrimeF F i,
    stage₂PrimeE E i, ⟨i, rfl⟩, ?_⟩
  rcases hwords with ⟨hX, hY⟩ | ⟨hX, hY⟩
  · exact Or.inl ⟨by
      simpa [stage₂PrimeF, rho₁_append] using congrArg (rho₁ N) hX,
    by simpa [stage₂PrimeE, rho₁_append] using congrArg (rho₁ N) hY⟩
  · exact Or.inr ⟨by
      simpa [stage₂PrimeE, rho₁_append] using congrArg (rho₁ N) hX,
    by simpa [stage₂PrimeF, rho₁_append] using congrArg (rho₁ N) hY⟩

/-- A rewrite out of an encoded word is aligned and uniquely reflects to one
source rewrite.  Positivity of all rule sides is the only hypothesis. -/
theorem decode_step (F E : Fin r → List (Fin N))
    (hF : ∀ i, F i ≠ []) (hE : ∀ i, E i ≠ []) {X : List (Fin N)}
    {W : List (Fin 2)}
    (h : ThueStep (stage₂PrimeSystem F E) (rho₁ N X) W) :
    ∃ Y, W = rho₁ N Y ∧ ThueStep (finiteSystem F E) X Y := by
  rcases h with ⟨l, s, x, y, ⟨i, hxy⟩, hwords⟩
  injection hxy with hx hy
  subst x
  subst y
  rcases hwords with ⟨hX, hW⟩ | ⟨hX, hW⟩
  · obtain ⟨L, R, hX', hl, hs⟩ :=
      rho₁_occurrence (hF i) hX
    refine ⟨L ++ E i ++ R, ?_, ?_⟩
    · calc
        W = l ++ stage₂PrimeE E i ++ s := hW
        _ = rho₁ N (L ++ E i ++ R) := by
          simp [stage₂PrimeE, rho₁_append, hl, hs]
    · exact ⟨L, R, F i, E i, ⟨i, rfl⟩, Or.inl ⟨hX', rfl⟩⟩
  · obtain ⟨L, R, hX', hl, hs⟩ :=
      rho₁_occurrence (hE i) hX
    refine ⟨L ++ F i ++ R, ?_, ?_⟩
    · calc
        W = l ++ stage₂PrimeF F i ++ s := hW
        _ = rho₁ N (L ++ F i ++ R) := by
          simp [stage₂PrimeF, rho₁_append, hl, hs]
    · exact ⟨L, R, F i, E i, ⟨i, rfl⟩, Or.inr ⟨hX', rfl⟩⟩

/-- Every derivation starting at an encoded word stays encoded and reflects
to a source derivation. -/
theorem decode_thueEq (F E : Fin r → List (Fin N))
    (hF : ∀ i, F i ≠ []) (hE : ∀ i, E i ≠ []) {X : List (Fin N)}
    {W : List (Fin 2)}
    (h : ThueEq (stage₂PrimeSystem F E) (rho₁ N X) W) :
    ∃ Y, W = rho₁ N Y ∧ ThueEq (finiteSystem F E) X Y := by
  induction h with
  | refl => exact ⟨X, rfl, Relation.ReflTransGen.refl⟩
  | tail _ hstep ih =>
      obtain ⟨Y, rfl, hXY⟩ := ih
      obtain ⟨Z, rfl, hYZ⟩ := decode_step F E hF hE hstep
      exact ⟨Z, rfl, hXY.tail hYZ⟩

/-- Equivalence (19): the binary many-rule system is equivalent to the
positive-side source system on encoded words. -/
theorem thueEq_iff (F E : Fin r → List (Fin N))
    (hF : ∀ i, F i ≠ []) (hE : ∀ i, E i ≠ []) (X Y : List (Fin N)) :
    ThueEq (finiteSystem F E) X Y ↔
      ThueEq (stage₂PrimeSystem F E) (rho₁ N X) (rho₁ N Y) := by
  constructor
  · intro h
    exact h.lift (rho₁ N) (fun _ _ hstep => thueStep_encode F E hstep)
  · intro h
    obtain ⟨Z, hYZ, hXZ⟩ := decode_thueEq F E hF hE h
    have : Y = Z := rho₁_injective hYZ
    simpa [this] using hXZ

/-- Section 2.3 packaged as an `Embedding`, under the common positive side
length hypotheses supplied by the padding stage. -/
def embedding (F E : Fin r → List (Fin N)) (p q : ℕ)
    (hp : 0 < p) (hq : 0 < q)
    (hF : ∀ i, (F i).length = p) (hE : ∀ i, (E i).length = q) :
    Embedding (finiteSystem F E) (stage₂PrimeSystem F E) where
  encode := rho₁ N
  encode_computable := rho₁_computable N
  thueEq_iff := fun X Y => thueEq_iff F E
    (fun i hnil => by have := hF i; simp [hnil] at this; omega)
    (fun i hnil => by have := hE i; simp [hnil] at this; omega) X Y

end Binary
end Matiyasevich1993
end Thue
end Undecidability
