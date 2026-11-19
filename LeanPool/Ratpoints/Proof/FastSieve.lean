/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Int.ModEq
public import LeanPool.Ratpoints.Fast.Sieve
public import LeanPool.Ratpoints.Spec.Basic
public import LeanPool.Ratpoints.Spec.Region
public import LeanPool.Ratpoints.Proof.SturmTheorem

import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import LeanPool.Ratpoints.Mathlib.Algebra.Order.Field.Basic
import LeanPool.Ratpoints.Proof.BruteForce
import LeanPool.Ratpoints.Proof.Containers
import LeanPool.Ratpoints.Proof.Divisors
import LeanPool.Ratpoints.Proof.FastDenominators
import LeanPool.Ratpoints.Proof.Jacobi
import LeanPool.Ratpoints.Proof.Double
import LeanPool.Ratpoints.Proof.SturmCoverage

/-!
# The fast search finds exactly the points

`Ratpoints.Fast.fastPoints c H bLow bHigh tu` lists only normalized points of height at most `H` on
`y ^ 2 = F(x, z)` whose denominator is `0` or lies in the range of `bLow` and `bHigh`
(`Ratpoints.Fast.isPoint_and_inRegion_of_mem_fastPoints`), each once
(`Ratpoints.Fast.nodup_fastPoints`), and includes all such points
(`Ratpoints.Fast.mem_fastPoints_iff`), for every setting `tu` of its parameters.
The completeness argument uses `Ratpoints.sturmTheorem` for interval pruning.

The sieve is a sound filter: a point `(a, y, b)` makes `(a, b)` a candidate
(`Ratpoints.Fast.IsCandidate`), and the residues of a candidate modulo every `m` pass the table
`Ratpoints.Fast.admitTable` (`Ratpoints.Fast.admitTable_spec`; a row prime to `m` is row `1`
permuted, `Ratpoints.Fast.getElem!_admitTable`, `Ratpoints.Fast.getElem!_permRow`), so the bit of
`a` survives in the row of every family (`Ratpoints.Fast.Family.IsSound`,
`Ratpoints.Fast.mkFamily_isSound`), in that row shifted to the start of each chunk and moved to the
part of the chunk that is searched (`Ratpoints.Fast.Family.IsSound.testBit_shiftRight`) and in the
sieve (`Ratpoints.Fast.testBit_sieve`); `Ratpoints.Fast.setBits` lists the bits that survive
(`Ratpoints.Fast.mem_setBits`), and the exact check of `Ratpoints.BruteForce.pointsOfDen` keeps the
points among them. The slots, the chunks of the classes modulo `G`, cover each numerator once
(`Ratpoints.Fast.exists_mem_slots`, `Ratpoints.Fast.pairwise_slots`), and the part of a chunk holds
the numerators of the chunk within the bounds of the region (`Ratpoints.Fast.exists_part_eq_some`,
`Ratpoints.Fast.add_le_and_dvd_of_part_eq_some`), so the search of a part
(`Ratpoints.Fast.of_mem_partPoints`, `Ratpoints.Fast.mem_partPoints`), of a denominator
(`Ratpoints.Fast.of_mem_denPoints`, `Ratpoints.Fast.mem_denPoints_of`,
`Ratpoints.Fast.nodup_denPoints`) and the whole search list the points of its denominators with
their numerators within the bounds, each once (`Ratpoints.Fast.of_mem_search`,
`Ratpoints.Fast.mem_search_of`, `Ratpoints.Fast.nodup_search`); a denominator for which a family has
the row `0` carries no candidate (`Ratpoints.Fast.any_rows_eq_false`).

Assuming Sturm's theorem, the bounds of the region hold the numerator `a` of every point
(`Ratpoints.Fast.exists_bounds_region`): one of the intervals that the Sturm step keeps holds
`a / b` (`Ratpoints.Fast.exists_mem_sturmIntervals`, from `Ratpoints.Sturm.covers_computeSturm`),
and the bounds that `Ratpoints.Fast.endFrac` makes of the ends of the interval
(`Ratpoints.Fast.div_le_of_endFrac_eq_some`, `Ratpoints.Fast.le_div_of_endFrac_eq_some`) bound `a`
(`Ratpoints.Fast.fst_numRange_le`, `Ratpoints.Fast.le_snd_numRange`,
`Ratpoints.Fast.exists_bounds_of_mem`). The denominators that the search leaves out carry no point
(`Ratpoints.Fast.mem_denominators_of_isCandidate`): for odd degree it takes those of the form
`s k ^ 2` with `s` dividing the leading coefficient, which `Ratpoints.Fast.squareDens` marks
(`Ratpoints.Fast.getElem!_squareDens_of_isCandidate`, from
`Ratpoints.exists_eq_mul_mul_of_sq_eq_binaryForm_of_odd`), and for even degree it leaves out those
that `Ratpoints.Fast.forbiddenDens` marks, multiples of an odd `q` with `J(c_d | q) = -1`
(`Ratpoints.Fast.exists_dvd_of_getElem!_forbiddenDens_ne_zero`), while the symbol is `1` on every
divisor of the denominator of a point prime to `c_d`
(`Ratpoints.Sieve.jacobiSym_eq_one_of_sq_eq_binaryForm`,
`Ratpoints.Fast.getElem!_forbiddenDens_eq_zero`).

When no range of the denominators is given, `Ratpoints.Fast.fastPoints` runs
`Ratpoints.Fast.sievePoints` on the coefficients that `Ratpoints.Fast.reversed` hands on: when it
reverses them, the region is the whole box and the binary form is that of `c` with `x` and `z`
exchanged (`Ratpoints.Fast.isFullBox_and_binaryForm_eq_of_reversed_eq`), so that
`Ratpoints.Sieve.swapPoint` maps the points of the reversed list one to one onto those of `c`
(`Ratpoints.Sieve.isPoint_swapPoint`, `Ratpoints.Sieve.swapPoint_inj`), which all lie in the whole
box (`Ratpoints.IsNormalizedPair.inRegion_of_isFullBox`).

## Main statements

* `Ratpoints.Fast.isPoint_and_inRegion_of_mem_fastPoints`: the list holds only points of the region.
* `Ratpoints.Fast.mem_fastPoints_iff`: the list holds exactly the points of the region.
* `Ratpoints.Fast.nodup_fastPoints`: each of them once.
-/

@[expose] public section

namespace Ratpoints.Fast

open BruteForce

/-! ### The positions of the bits -/

/-- The bits of a positive number are its highest bit, at `Nat.log2 n`, and the bits of the
rest. -/
theorem testBit_iff_eq_log2_or {n t : ℕ} (h : n ≠ 0) :
    n.testBit t ↔ t = n.log2 ∨ (n - 2 ^ n.log2).testBit t := by
  have h1 : 2 ^ n.log2 ≤ n := Nat.log2_self_le h
  have h2 : n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
  generalize n.log2 = j at h1 h2
  obtain ⟨r, rfl⟩ : ∃ r, n = 2 ^ j + r := ⟨n - 2 ^ j, by lia⟩
  have hr : r < 2 ^ j := by rw [pow_succ] at h2; lia
  rw [Nat.add_sub_cancel_left]
  rcases lt_trichotomy t j with htj | rfl | htj
  · simp [Nat.testBit_two_pow_add_gt htj, htj.ne]
  · simp [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hr]
  · have : 2 ^ j + r < 2 ^ t := by
      calc 2 ^ j + r < 2 ^ (j + 1) := by rw [pow_succ]; lia
        _ ≤ 2 ^ t := Nat.pow_le_pow_right two_pos htj
    simp [Nat.testBit_lt_two_pow this, htj.ne',
      Nat.testBit_lt_two_pow (hr.trans (Nat.pow_lt_pow_right one_lt_two htj))]

theorem mem_setBitsSmall {n t : ℕ} : t ∈ setBitsSmall n ↔ n.testBit t := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [setBitsSmall]
    split_ifs with h
    · simp [h]
    · rw [List.mem_cons, ih _ (Nat.sub_lt (Nat.pos_of_ne_zero h) (Nat.two_pow_pos _)),
        testBit_iff_eq_log2_or h]

theorem nodup_setBitsSmall (n : ℕ) : (setBitsSmall n).Nodup := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [setBitsSmall]
    split_ifs with h
    · exact List.nodup_nil
    · refine List.nodup_cons.mpr ⟨fun hm ↦ ?_, ih _ (Nat.sub_lt (Nat.pos_of_ne_zero h)
        (Nat.two_pow_pos _))⟩
      rw [mem_setBitsSmall, Nat.testBit_lt_two_pow] at hm
      · exact Bool.false_ne_true hm
      · have := Nat.lt_log2_self (n := n)
        rw [pow_succ] at this
        lia

theorem or_testBit_iff {o h n t : ℕ} :
    (o + h ≤ t ∧ n.testBit (h + (t - (o + h))) = true) ∨
      (o ≤ t ∧ t - o < h ∧ n.testBit (t - o) = true) ↔ o ≤ t ∧ n.testBit (t - o) = true := by
  constructor
  · rintro (⟨ho, hb⟩ | ⟨ho, -, hb⟩)
    · exact ⟨by lia, by rwa [show h + (t - (o + h)) = t - o by lia] at hb⟩
    · exact ⟨ho, hb⟩
  · intro ⟨ho, hb⟩
    by_cases ht : t - o < h
    · exact .inr ⟨ho, ht, hb⟩
    · exact .inl ⟨by lia, by rwa [show h + (t - (o + h)) = t - o by lia]⟩

theorem mem_setBitsAux {o n k t : ℕ} : t ∈ setBitsAux o n k ↔ o ≤ t ∧ n.testBit (t - o) := by
  induction k generalizing o n with
  | zero =>
    simp only [setBitsAux, List.mem_map, mem_setBitsSmall]
    constructor
    · rintro ⟨s, hs, rfl⟩
      simpa using hs
    · intro ⟨ho, hb⟩
      exact ⟨t - o, hb, by lia⟩
  | succ k ih =>
    rw [setBitsAux]
    split_ifs with h
    · simp [h]
    · rw [List.mem_append, ih, ih, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact or_testBit_iff

theorem nodup_setBitsAux (o n k : ℕ) : (setBitsAux o n k).Nodup := by
  induction k generalizing o n with
  | zero => exact (nodup_setBitsSmall n).map fun _ _ h ↦ Nat.add_left_cancel h
  | succ k ih =>
    rw [setBitsAux]
    split_ifs
    · exact List.nodup_nil
    · refine List.nodup_append.mpr ⟨ih .., ih .., fun a ha b hb ↦ ?_⟩
      rw [mem_setBitsAux] at ha hb
      rw [Nat.testBit_mod_two_pow] at hb
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      lia

theorem mem_setBits {n t : ℕ} : t ∈ setBits n ↔ n.testBit t := by
  simp [setBits, mem_setBitsAux]

theorem nodup_setBits (n : ℕ) : (setBits n).Nodup := nodup_setBitsAux ..

/-! ### The residues that allow a point -/

/-- `(a, b)` can carry a point: `gcd(a, b) = 1` and `F(a, b)` is a square. -/
def IsCandidate (c : List ℤ) (a : ℤ) (b : ℕ) : Prop :=
  Int.gcd a b = 1 ∧ ∃ y : ℤ, y ^ 2 = binaryForm c a b

theorem hornerMod_modEq {m : ℕ} {w w' : List ℤ} (hw : List.Forall₂ (Int.ModEq m) w w') {x x' : ℤ}
    (hx : x ≡ x' [ZMOD m]) : hornerMod w x m ≡ horner w' x' [ZMOD m] := by
  induction hw with
  | nil => rfl
  | cons ha _ ih =>
    simp only [hornerMod, horner, List.foldr_cons] at ih ⊢
    exact (Int.mod_modEq _ _).trans (ha.add (hx.mul ih))

theorem powMod_eq (r m e : ℕ) : powMod r m e = r ^ e % m := by
  induction e with
  | zero => rfl
  | succ e ih => rw [powMod, ih, pow_succ, Nat.mod_mul_mod]

theorem forall₂_scaledCoeffsMod (c : List ℤ) (d m r : ℕ) :
    List.Forall₂ (Int.ModEq m) (scaledCoeffsMod c d m r) (scaledCoeffs c d r) := by
  rw [scaledCoeffsMod, scaledCoeffs, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.mpr fun k _ ↦ (Int.mod_modEq _ _).mul ?_
  rw [powMod_eq]
  push_cast [Int.natCast_mod]
  exact Int.mod_modEq _ _

theorem hornerMod_scaledCoeffsMod_modEq (c : List ℤ) (m r x : ℕ) :
    hornerMod (scaledCoeffsMod c (BruteForce.degree c) m r) x m *
      (if BruteForce.degree c % 2 = 1 then (r : ℤ) else 1) ≡ binaryForm c x r [ZMOD m] := by
  rw [← horner_scaledCoeffs_mul]
  exact (hornerMod_modEq (forall₂_scaledCoeffsMod c _ m r) (Int.ModEq.refl _)).mul_right _

theorem binaryForm_modEq (c : List ℤ) {m : ℕ} {a a' b b' : ℤ} (ha : a ≡ a' [ZMOD m])
    (hb : b ≡ b' [ZMOD m]) : binaryForm c a b ≡ binaryForm c a' b' [ZMOD m] := by
  rw [← ZMod.intCast_eq_intCast_iff] at ha hb ⊢
  simp only [binaryForm]
  push_cast
  rw [ha, hb]

/-- The binary form is homogeneous of degree `D = d + d % 2`. -/
theorem binaryForm_mul_self (c : List ℤ) (u b : ℤ) :
    binaryForm c (u * b) b = b ^ (degree c + degree c % 2) * binaryForm c u 1 := by
  simp only [binaryForm, one_pow, mul_one, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have : i ≤ degree c + degree c % 2 := by have := Finset.mem_range.mp hi; lia
  calc c.getD i 0 * (u * b) ^ i * b ^ (degree c + degree c % 2 - i)
      = c.getD i 0 * u ^ i * (b ^ i * b ^ (degree c + degree c % 2 - i)) := by ring
    _ = b ^ (degree c + degree c % 2) * (c.getD i 0 * u ^ i) := by
      rw [← pow_add, Nat.add_sub_cancel' this]
      ring

theorem sqTable_sq {m : ℕ} (hm : 0 < m) (y : ℤ) : (sqTable m)[(y ^ 2 % m).toNat]! = true := by
  have hm' : (0 : ℤ) < m := Int.natCast_pos.mpr hm
  have hy : (y % m).toNat < m := by have := Int.emod_lt_of_pos y hm'; lia
  have heq : (y % m).toNat * (y % m).toNat % m = (y ^ 2 % m).toNat := by
    rw [← Int.natCast_inj]
    push_cast [Int.toNat_of_nonneg (Int.emod_nonneg _ hm'.ne'), Int.natCast_mod]
    rw [← Int.mul_emod, sq]
  refine Array.getElem!_foldl_set!_eq_true _ _ (by simpa [← heq] using Nat.mod_lt _ hm)
    (.inr ⟨_, List.mem_range.mpr hy, heq⟩)

theorem natGcd_eq (a b : ℕ) : natGcd a b = Nat.gcd a b := by
  fun_induction natGcd a b with
  | case1 => simp
  | case2 _ _ _ ih => rw [ih, Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]

theorem coprimeWith_of_gcd_eq_one {a : ℤ} {b m : ℕ} (hm : 0 < m) (hab : Int.gcd a b = 1) :
    coprimeWith (Nat.gcd (b % m) m) (a % (m : ℤ)).toNat = true := by
  simp only [coprimeWith, natGcd_eq, Bool.or_eq_true, beq_iff_eq]
  right
  set g := Nat.gcd (a % (m : ℤ)).toNat (Nat.gcd (b % m) m)
  have h1 : g ∣ (a % (m : ℤ)).toNat := Nat.gcd_dvd_left _ _
  have h2 : g ∣ b % m := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
  have h3 : g ∣ m := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  have ha : (g : ℤ) ∣ a := by
    rw [← Int.emod_add_mul_ediv a m]
    refine dvd_add ?_ (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr h3) _)
    rw [← Int.toNat_of_nonneg (Int.emod_nonneg a (by lia))]
    exact Int.natCast_dvd_natCast.mpr h1
  have hb : g ∣ b := by
    rw [← Nat.mod_add_div b m]
    exact dvd_add h2 (dvd_mul_of_dvd_left h3 _)
  have := Int.dvd_gcd ha (Int.natCast_dvd_natCast.mpr hb)
  rw [hab] at this
  exact Nat.dvd_one.mp this

theorem getElem!_map_range {α : Type*} [Inhabited α] (f : ℕ → α) {n i : ℕ} (hi : i < n) :
    ((List.range n).toArray.map f)[i]! = f i := by
  simp [getElem!_pos, hi]

theorem sqTable_of_modEq {m : ℕ} (hm : 0 < m) {v y : ℤ} (h : v ≡ y ^ 2 [ZMOD m]) :
    (sqTable m)[(v % m).toNat]! = true := by
  rw [show v % m = y ^ 2 % m from h]
  exact sqTable_sq hm y

theorem getElem!_admitRow {c : List ℤ} {m r x : ℕ} (hm : 0 < m) (hx : x < m)
    (hg : coprimeWith (Nat.gcd r m) x = true) {y : ℤ} (hy : binaryForm c x r ≡ y ^ 2 [ZMOD m]) :
    (admitRow c (BruteForce.degree c) m (sqTable m) r)[x]! = true := by
  rw [admitRow, getElem!_map_range _ hx, natGcd_eq, hg, Bool.true_and]
  exact sqTable_of_modEq hm ((hornerMod_scaledCoeffsMod_modEq c m r x).trans hy)

theorem intCast_mul_modEq_one {b u m : ℕ} (h : b % m * u % m = 1 % m) :
    (b : ℤ) * u ≡ 1 [ZMOD m] := by
  have := congr(((($h : ℕ)) : ℤ))
  push_cast [Int.natCast_mod] at this
  exact ((Int.mod_modEq _ _).mul_right _).symm.trans this

/-- For `b u ≡ 1` modulo `m`, `F(x u, 1)` is a square modulo `m` for every `x ≡ a` with
`F(a, b)` a square, `F` being homogeneous of even degree (`Ratpoints.Fast.binaryForm_mul_self`). -/
theorem binaryForm_mul_modEq_sq {c : List ℤ} {m : ℕ} {a y : ℤ} {b u x : ℕ}
    (hy : y ^ 2 = binaryForm c a b) (hxa : (x : ℤ) ≡ a [ZMOD m]) (hru : b % m * u % m = 1 % m) :
    binaryForm c ((x * u % m : ℕ) : ℤ) ((1 : ℕ) : ℤ) ≡
      (y * u ^ ((degree c + degree c % 2) / 2)) ^ 2 [ZMOD m] := by
  have hD : degree c + degree c % 2 = 2 * ((degree c + degree c % 2) / 2) := by lia
  have hbu := intCast_mul_modEq_one hru
  have hv : ((x * u % m : ℕ) : ℤ) * b ≡ a [ZMOD m] := by
    push_cast [Int.natCast_mod]
    calc (x * u % m : ℤ) * b ≡ x * u * b [ZMOD m] := (Int.mod_modEq _ _).mul_right _
      _ = x * (b * u) := by ring
      _ ≡ x * 1 [ZMOD m] := hbu.mul_left _
      _ = x := mul_one _
      _ ≡ a [ZMOD m] := hxa
  calc binaryForm c ((x * u % m : ℕ) : ℤ) ((1 : ℕ) : ℤ)
      ≡ binaryForm c ((x * u % m : ℕ) : ℤ) 1 * (b * u) ^ (degree c + degree c % 2) [ZMOD m] := by
        simpa using ((hbu.pow (degree c + degree c % 2)).mul_left _).symm
    _ = binaryForm c (((x * u % m : ℕ) : ℤ) * b) b * u ^ (degree c + degree c % 2) := by
        rw [binaryForm_mul_self]
        ring
    _ ≡ binaryForm c a b * u ^ (degree c + degree c % 2) [ZMOD m] :=
        (binaryForm_modEq c hv (Int.ModEq.refl _)).mul_right _
    _ = (y * u ^ ((degree c + degree c % 2) / 2)) ^ 2 := by
        rw [← hy, mul_pow, ← pow_mul, mul_comm _ 2, ← hD]

/-- The loop of `Ratpoints.Fast.admitTable` appends the rows from `r` on to `acc`. -/
theorem admitTable.go_eq_append (c : List ℤ) (d m : ℕ) (sq one : Array Bool) (inv : Array ℕ)
    (r : ℕ) (acc : Array (Array Bool)) :
    admitTable.go c d m sq one inv r acc = acc ++ ((List.range' r (m - r)).map fun r ↦
      if r * inv[r]! % m == 1 % m && inv[r]! < m then permRow one m inv[r]!
      else admitRow c d m sq r).toArray := by
  fun_induction admitTable.go c d m sq one inv r acc with
  | case1 r _ hr u ih =>
    rw [dite_eq_ite] at ih
    rw [ih, show m - r = m - (r + 1) + 1 by lia, List.range'_succ]
    simp [u]
  | case2 r _ hr => simp [show m - r = 0 by lia]

/-- The index `i = x u` modulo `m`, stepped by `u < m` with one conditional subtraction, is
`(x + 1) u` modulo `m`. -/
theorem ite_add_lt_eq_mul_mod {m u x i : ℕ} (hi : i = x * u % m) (hu : u < m) :
    (if i + u < m then i + u else i + u - m) = (x + 1) * u % m := by
  rw [Nat.ite_add_lt_eq_add_mod (hi ▸ Nat.mod_lt _ (by lia)) hu, hi, Nat.mod_add_mod, Nat.succ_mul]

/-- The loop of `Ratpoints.Fast.permRow` appends the entries from `x` on to `acc`, for the index
`i = x u` modulo `m`. -/
theorem permRow.go_eq_append (one : Array Bool) {m u : ℕ} (hu : u < m) (x i : ℕ)
    (acc : Array Bool) (hi : i = x * u % m) :
    permRow.go one m u x i acc =
      acc ++ ((List.range' x (m - x)).map fun x ↦ one[x * u % m]!).toArray := by
  fun_induction permRow.go one m u x i acc with
  | case1 x i _ hx ih =>
    simp only [dite_eq_ite] at ih
    rw [ih (ite_add_lt_eq_mul_mod hi hu), show m - x = m - (x + 1) + 1 by lia, List.range'_succ]
    simp [hi]
  | case2 x _ _ hx => simp [show m - x = 0 by lia]

theorem getElem!_permRow (one : Array Bool) {m u x : ℕ} (hu : u < m) (hx : x < m) :
    (permRow one m u)[x]! = one[x * u % m]! := by
  rw [permRow, permRow.go_eq_append one hu 0 0 _ (by simp)]
  simp [hx]

theorem getElem!_admitTable (c : List ℤ) (d : ℕ) {m r : ℕ} (hr : r < m) :
    (admitTable c d m)[r]! =
      if r * (invTable m)[r]! % m == 1 % m && (invTable m)[r]! < m then
        permRow (admitRow c d m (sqTable m) 1) m (invTable m)[r]!
      else admitRow c d m (sqTable m) r := by
  rw [admitTable, admitTable.go_eq_append]
  simp [hr]

theorem admitTable_spec {c : List ℤ} {m : ℕ} (hm : 0 < m) {a : ℤ} {b : ℕ}
    (h : IsCandidate c a b) :
    ((admitTable c (BruteForce.degree c) m)[b % m]!)[(a % (m : ℤ)).toNat]! = true := by
  obtain ⟨hab, y, hy⟩ := h
  have hm' : (0 : ℤ) < m := Int.natCast_pos.mpr hm
  have hx : (a % (m : ℤ)).toNat < m := by have := Int.emod_lt_of_pos a hm'; lia
  have hxa : ((a % (m : ℤ)).toNat : ℤ) ≡ a [ZMOD m] := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg a hm'.ne')]
    exact Int.mod_modEq a m
  rw [getElem!_admitTable _ _ (Nat.mod_lt _ hm)]
  split_ifs with hu
  · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hu
    rw [getElem!_permRow _ hu.2 hx]
    exact getElem!_admitRow hm (Nat.mod_lt _ hm) (by simp [coprimeWith])
      (binaryForm_mul_modEq_sq hy hxa (by simpa using hu.1))
  · refine getElem!_admitRow (y := y) hm hx (coprimeWith_of_gcd_eq_one hm hab) ?_
    refine (binaryForm_modEq c hxa ?_).trans (by rw [hy])
    push_cast [Int.natCast_mod]
    exact Int.mod_modEq _ _

/-! ### Bit masks -/

theorem testBit_foldl_pattern (f : ℕ → Bool) (l : List ℕ) (P j : ℕ) :
    (l.foldl (fun P j' ↦ if f j' then P ||| 1 <<< j' else P) P).testBit j =
      (P.testBit j || decide (j ∈ l) && f j) := by
  induction l generalizing P with
  | nil => simp
  | cons j' l ih =>
    rw [List.foldl_cons, ih]
    by_cases hf : f j' <;> by_cases hj : j = j' <;>
      simp [hf, hj, Nat.testBit_or, Nat.one_shiftLeft, eq_comm]

theorem testBit_pattern (m : ℕ) (f : ℕ → Bool) (j : ℕ) :
    (pattern m f).testBit j = (decide (j < m) && f j) := by
  simp [pattern, testBit_foldl_pattern]

theorem testBit_repeatPattern {P m j : ℕ} (k : ℕ) (hj : j < m * 2 ^ k)
    (h : P.testBit (j % m) = true) : (repeatPattern P m k).testBit j = true := by
  induction k generalizing j with
  | zero =>
    rw [pow_zero, mul_one] at hj
    rwa [Nat.mod_eq_of_lt hj] at h
  | succ k ih =>
    rw [repeatPattern, Nat.testBit_or, Bool.or_eq_true]
    by_cases hjk : j < m * 2 ^ k
    · exact .inl (ih hjk h)
    · refine .inr ?_
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + m * 2 ^ k := ⟨j - m * 2 ^ k, by lia⟩
      rw [Nat.testBit_shiftLeft, Nat.add_sub_cancel]
      simp only [ge_iff_le, Nat.le_add_left, decide_true, Bool.true_and]
      refine ih (by rw [pow_succ] at hj; lia) ?_
      rwa [Nat.add_mul_mod_self_left] at h

theorem le_mul_two_pow_doublings {m : ℕ} (hm : 0 < m) (N : ℕ) : N < m * 2 ^ doublings m N := by
  calc N < m * (N / m + 1) := Nat.lt_mul_div_succ N hm
    _ ≤ m * 2 ^ doublings m N := Nat.mul_le_mul_left m Nat.lt_log2_self

theorem testBit_baseRow {T : Array (Array Bool)} {m G N r j : ℕ} (hm : 0 < m) (hj : j < N)
    (h : (T[r]!)[G * j % m]! = true) : (baseRow T m G N r).testBit j = true := by
  refine testBit_repeatPattern _ ((le_mul_two_pow_doublings hm N).trans' hj) ?_
  rwa [testBit_pattern, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Bool.and_eq_true,
    decide_eq_true_eq, and_iff_right (Nat.mod_lt _ hm)]

/-! ### Families -/

/-- The family `F` is sound for the step `G` and chunks of at most `L` numerators: it has a row for
every residue modulo `F.M > 0`, `F.ginv` inverts `G` modulo `F.M`, and the row of `b` has the bit
`j < L + 8 F.M` set for every candidate `(a, b)` with `a ≡ G j` modulo `F.M`. -/
structure Family.IsSound (c : List ℤ) (G L : ℕ) (F : Family) : Prop where
  /-- A row for every residue. -/
  size_eq : F.rows.size = F.M
  /-- The modulus is positive. -/
  pos : 0 < F.M
  /-- `F.ginv` inverts `G`. -/
  mul_ginv : G * F.ginv % F.M = 1 % F.M
  /-- The row of `b` keeps the bit `j` of every candidate `(a, b)` with `a ≡ G j`. -/
  testBit : ∀ (a : ℤ) (b j : ℕ), j < L + 8 * F.M → IsCandidate c a b → (F.M : ℤ) ∣ a - G * j →
    (F.rows[b % F.M]!).testBit j = true

theorem foldl_mul_fst {α : Type*} (ts : List (ℕ × α)) (k : ℕ) :
    ts.foldl (· * ·.1) k = k * (ts.map (·.1)).prod := by
  induction ts generalizing k with
  | nil => simp
  | cons t ts ih => simp [ih, mul_assoc]

theorem testBit_foldl_and {α : Type*} (g : α → ℕ) (l : List α) {init j : ℕ}
    (hi : init.testBit j = true) (hl : ∀ x ∈ l, (g x).testBit j = true) :
    (l.foldl (fun acc x ↦ acc &&& g x) init).testBit j = true := by
  induction l generalizing init with
  | nil => exact hi
  | cons x l ih =>
    exact ih (by simp [Nat.testBit_and, hi, hl x (by simp)]) fun y hy ↦ hl y (by simp [hy])

theorem natMod_eq_toNat_of_dvd {m : ℕ} {a : ℤ} {k : ℕ} (h : (m : ℤ) ∣ a - k) :
    k % m = (a % (m : ℤ)).toNat := by
  have := Int.modEq_iff_dvd.mpr h
  rw [Int.ModEq] at this
  rw [← this, ← Int.natCast_mod, Int.toNat_natCast]

theorem foldl_mul_fst_pos {α : Type*} {ts : List (ℕ × α)} (h : ∀ t ∈ ts, 0 < t.1) :
    0 < ts.foldl (· * ·.1) 1 := by
  rw [foldl_mul_fst, one_mul]
  exact List.prod_pos fun x hx ↦ by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    exact h t ht

theorem dvd_foldl_mul_fst {α : Type*} {ts : List (ℕ × α)} {t : ℕ × α} (ht : t ∈ ts) :
    t.1 ∣ ts.foldl (· * ·.1) 1 := by
  rw [foldl_mul_fst, one_mul]
  exact List.dvd_prod (List.mem_map.mpr ⟨_, ht, rfl⟩)

/-- The rows of one modulus `m ∣ M` keep the bit `j` of every candidate `(a, b)` with
`a ≡ G j` modulo `M`. -/
theorem testBit_baseRows {c : List ℤ} {m M G N j : ℕ} (hm : 0 < m) (hmM : m ∣ M) (hj : j < N)
    {a : ℤ} {b : ℕ} (hc : IsCandidate c a b) (hdvd : (M : ℤ) ∣ a - G * j) :
    (((List.range m).toArray.map
      (baseRow (admitTable c (BruteForce.degree c) m) m G N))[b % M % m]!).testBit j = true := by
  rw [Nat.mod_mod_of_dvd _ hmM, getElem!_map_range _ (Nat.mod_lt _ hm)]
  refine testBit_baseRow hm hj ?_
  rw [natMod_eq_toNat_of_dvd (k := G * j)
    ((Int.natCast_dvd_natCast.mpr hmM).trans (by simpa using hdvd))]
  exact admitTable_spec hm hc

theorem mkFamily_isSound {c : List ℤ} {G L : ℕ} {ts : List (ℕ × Array (Array Bool))}
    (hts : ∀ t ∈ ts, t.2 = admitTable c (BruteForce.degree c) t.1) {F : Family}
    (h : mkFamily G L ts = some F) :
    F.IsSound c G L := by
  rw [mkFamily] at h
  split_ifs at h with hpos
  dsimp only at h
  split at h
  · simp at h
  rename_i ginv hginv
  obtain rfl := (Option.some.inj h).symm
  have hpos' : ∀ t ∈ ts, 0 < t.1 := by simpa using hpos
  have hM := foldl_mul_fst_pos hpos'
  refine ⟨by simp, hM, by simpa using List.find?_some hginv, fun a b j hj hc hdvd ↦ ?_⟩
  rw [getElem!_map_range _ (Nat.mod_lt _ hM)]
  refine testBit_foldl_and _ _ (by simp [Nat.testBit_two_pow_sub_one, hj]) fun x hx ↦ ?_
  obtain ⟨⟨m, T⟩, ht, rfl⟩ := List.mem_map.mp hx
  obtain rfl : T = admitTable c (BruteForce.degree c) m := hts _ ht
  exact testBit_baseRows (hpos' _ ht) (dvd_foldl_mul_fst ht) hj hc hdvd

/-! ### The shift -/

theorem Family.shift_lt (F : Family) (hF : 0 < F.M) (a₀ : ℤ) : F.shift a₀ < 8 * F.M := by
  have hs : (a₀ * F.ginv % (F.M : ℤ)).toNat < F.M := by
    lia [Int.emod_lt_of_pos (a₀ * F.ginv) (Int.natCast_pos.mpr hF)]
  simp only [Family.shift]
  generalize (a₀ * F.ginv % (F.M : ℤ)).toNat = s at hs ⊢
  have h7 : (8 - s % 8) * F.M % 8 ≤ 7 := Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
  lia [Nat.mul_le_mul_left F.M h7]

theorem Family.IsSound.dvd_sub_shift {c : List ℤ} {G L : ℕ} {F : Family}
    (hF : F.IsSound c G L) (a₀ : ℤ) :
    (F.M : ℤ) ∣ a₀ - G * F.shift a₀ := by
  have hg : (G : ℤ) * F.ginv ≡ 1 [ZMOD F.M] := by
    have := congr((($hF.mul_ginv : ℕ) : ℤ))
    push_cast [Int.natCast_mod] at this
    exact this
  have hs : (G : ℤ) * (a₀ * F.ginv % F.M) ≡ a₀ [ZMOD F.M] :=
    calc (G : ℤ) * (a₀ * F.ginv % F.M) ≡ G * (a₀ * F.ginv) [ZMOD F.M] :=
          (Int.mod_modEq _ _).mul_left _
      _ = a₀ * (G * F.ginv) := by ring
      _ ≡ a₀ * 1 [ZMOD F.M] := hg.mul_left _
      _ = a₀ := mul_one a₀
  obtain ⟨k, hk⟩ : ∃ k, F.shift a₀ = (a₀ * F.ginv % (F.M : ℤ)).toNat + F.M * k := ⟨_, rfl⟩
  have h0 : 0 ≤ a₀ * F.ginv % (F.M : ℤ) := Int.emod_nonneg _ (by lia [hF.pos])
  rw [hk]
  push_cast [Int.toNat_of_nonneg h0]
  refine Int.modEq_iff_dvd.mp ?_
  rw [mul_add, mul_left_comm]
  exact Int.modEq_add_fac_self.trans hs

/-- The row of `b`, shifted to the chunk that starts at `a₀` and moved by `o`, keeps the bit `t` of
every candidate `(a₀ + G (o + t), b)` with `o + t < L`. -/
theorem Family.IsSound.testBit_shiftRight {c : List ℤ} {G L : ℕ} {F : Family}
    (hF : F.IsSound c G L) {a₀ : ℤ} {b o t : ℕ} (ht : o + t < L)
    (hc : IsCandidate c (a₀ + G * (o + t)) b) :
    (F.rows[b % F.M]! >>> (F.shift a₀ + o)).testBit t = true := by
  rw [Nat.testBit_shiftRight]
  refine hF.testBit _ b _ (by lia [F.shift_lt hF.pos a₀]) hc ?_
  have := hF.dvd_sub_shift a₀
  rwa [show a₀ + G * (o + t) - G * (F.shift a₀ + o + t : ℕ) = a₀ - G * F.shift a₀ by
    push_cast; ring]

theorem Family.IsSound.rows_ne_zero {c : List ℤ} {G L : ℕ} {F : Family} (hF : F.IsSound c G L)
    {a : ℤ} {b : ℕ} (hc : IsCandidate c a b) :
    F.rows[b % F.M]! ≠ 0 := by
  intro h0
  have := hF.testBit a b (F.shift a) (by lia [F.shift_lt hF.pos a]) hc (hF.dvd_sub_shift a)
  simp [h0] at this

/-! ### The sieve -/

theorem testBit_foldl_sieve {α : Type*} (g : α → ℕ) (l : List α) {mask t : ℕ}
    (hmask : mask.testBit t = true) (hl : ∀ x ∈ l, (g x).testBit t = true) :
    (l.foldl (fun acc x ↦ if acc == 0 then 0 else acc &&& g x) mask).testBit t = true := by
  induction l generalizing mask with
  | nil => exact hmask
  | cons x l ih =>
    refine ih ?_ fun y hy ↦ hl y (by simp [hy])
    have h0 : mask ≠ 0 := fun h ↦ by simp [h] at hmask
    simp [h0, Nat.testBit_and, hmask, hl x (by simp)]

theorem testBit_of_testBit_foldl_sieve {α : Type*} {g : α → ℕ} {l : List α} {mask t : ℕ}
    (h : (l.foldl (fun acc x ↦ if acc == 0 then 0 else acc &&& g x) mask).testBit t = true) :
    mask.testBit t = true := by
  induction l generalizing mask with
  | nil => exact h
  | cons x l ih =>
    have := ih h
    dsimp only at this
    split_ifs at this with h0
    · simp at this
    · rw [Nat.testBit_and, Bool.and_eq_true] at this
      exact this.1

theorem testBit_sieve {rs sh : Array ℕ} {o mask t : ℕ} (hmask : mask.testBit t = true)
    (h : ∀ i < rs.size, (rs[i]! >>> (sh[i]! + o)).testBit t = true) :
    (sieve rs sh o mask).testBit t = true :=
  testBit_foldl_sieve (fun i ↦ rs[i]! >>> (sh[i]! + o)) _ hmask fun i hi ↦
    h i (List.mem_range.mp hi)

theorem testBit_of_testBit_sieve {rs sh : Array ℕ} {o mask t : ℕ}
    (h : (sieve rs sh o mask).testBit t = true) :
    mask.testBit t = true :=
  testBit_of_testBit_foldl_sieve h

/-! ### The points of a chunk -/

theorem of_mem_chunkPoints {c : List ℤ} {G : ℕ} {rs sh : Array ℕ} {o : ℕ} {a₀ : ℤ} {len b : ℕ}
    {p : ℤ × ℤ × ℤ} (h : p ∈ chunkPoints c (BruteForce.degree c) G rs sh o a₀ len b) :
    p.2.2 = b ∧ (∃ t < len, p.1 = a₀ + G * t) ∧ Int.gcd p.1 p.2.2 = 1 ∧
      p.2.1 ^ 2 = binaryForm c p.1 p.2.2 := by
  simp only [chunkPoints] at h
  split_ifs at h
  · simp at h
  rw [mem_pointsOfDen_iff, horner_scaledCoeffs_mul] at h
  obtain ⟨hx, hz, hg, hy⟩ := h
  obtain ⟨t, ht, hx⟩ := List.mem_map.mp hx
  have := testBit_of_testBit_sieve (mem_setBits.mp ht)
  rw [Nat.testBit_two_pow_sub_one, decide_eq_true_eq] at this
  exact ⟨hz, ⟨t, this, hx.symm⟩, hz ▸ hg, hz ▸ hy⟩

theorem mem_chunkPoints {c : List ℤ} {G : ℕ} {rs sh : Array ℕ} {o : ℕ} {a₀ : ℤ} {len b : ℕ}
    (hrs : ∀ t < len, IsCandidate c (a₀ + G * t) b →
      ∀ i < rs.size, (rs[i]! >>> (sh[i]! + o)).testBit t = true) {p : ℤ × ℤ × ℤ} :
    p ∈ chunkPoints c (BruteForce.degree c) G rs sh o a₀ len b ↔
      p.2.2 = b ∧ (∃ t < len, p.1 = a₀ + G * t) ∧ Int.gcd p.1 p.2.2 = 1 ∧
        p.2.1 ^ 2 = binaryForm c p.1 p.2.2 := by
  refine ⟨of_mem_chunkPoints, fun ⟨hz, ⟨t, ht, hx⟩, hg, hy⟩ ↦ ?_⟩
  have hbit := testBit_sieve (rs := rs) (sh := sh) (o := o) (mask := 2 ^ len - 1)
    (by simp [Nat.testBit_two_pow_sub_one, ht]) (hrs t ht ⟨hx ▸ hz ▸ hg, p.2.1, hx ▸ hz ▸ hy⟩)
  have h0 : sieve rs sh o (2 ^ len - 1) ≠ 0 := fun h ↦ by simp [h] at hbit
  simp only [chunkPoints, beq_iff_eq, h0, ↓reduceIte]
  rw [mem_pointsOfDen_iff, horner_scaledCoeffs_mul]
  exact ⟨List.mem_map.mpr ⟨t, mem_setBits.mpr hbit, hx.symm⟩, hz, hz ▸ hg, hz ▸ hy⟩

theorem nodup_chunkPoints (c : List ℤ) {G : ℕ} (hG : 0 < G) (rs sh : Array ℕ) (o : ℕ) (a₀ : ℤ)
    (len b : ℕ) :
    (chunkPoints c (BruteForce.degree c) G rs sh o a₀ len b).Nodup := by
  simp only [chunkPoints]
  split_ifs
  · exact List.nodup_nil
  · refine nodup_pointsOfDen _ _ _ ((nodup_setBits _).map fun t t' h ↦ ?_)
    have : (G : ℤ) * t = G * t' := by simpa using h
    exact_mod_cast mul_left_cancel₀ (by lia : (G : ℤ) ≠ 0) this

/-! ### The parts of the chunks -/

/-- The part of a chunk lies in the chunk, starts at a multiple of `64` and ends at the end of the
chunk or at a multiple of `64`. -/
theorem add_le_and_dvd_of_part_eq_some {G : ℕ} {lo hi a₀ : ℤ} {len t₁ len₁ : ℕ}
    (h : part G lo hi a₀ len = some (t₁, len₁)) :
    t₁ + len₁ ≤ len ∧ 64 ∣ t₁ ∧ (t₁ + len₁ = len ∨ 64 ∣ t₁ + len₁) := by
  simp only [part] at h
  generalize (lo - a₀ + G - 1) / (G : ℤ) = u at h
  generalize (hi - a₀) / (G : ℤ) = v at h
  split_ifs at h <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  · have h1 : (max 0 u).toNat ≤ (min (len - 1 : ℤ) v).toNat := by lia
    have h2 : (min (len - 1 : ℤ) v).toNat < len := by lia
    generalize (max 0 u).toNat = T₁ at *
    generalize (min (len - 1 : ℤ) v).toNat = T₂ at *
    refine ⟨by lia, Nat.dvd_mul_right 64 _, ?_⟩
    rcases le_total len (64 * (T₂ / 64 + 1)) with h | h
    · exact .inl (by rw [min_eq_left h]; lia)
    · exact .inr (by rw [min_eq_right h, Nat.add_sub_cancel' (by lia)]; exact Nat.dvd_mul_right ..)
  · exact ⟨by lia, dvd_zero 64, .inl (zero_add len)⟩

/-- Every numerator of the chunk from `lo` to `hi` lies in the part of the chunk. -/
theorem exists_part_eq_some {G : ℕ} (hG : 0 < G) {lo hi a₀ : ℤ} {len t : ℕ} (ht : t < len)
    (hlo : lo ≤ a₀ + G * t) (hhi : a₀ + G * t ≤ hi) :
    ∃ t₁ len₁, part G lo hi a₀ len = some (t₁, len₁) ∧ t₁ ≤ t ∧ t < t₁ + len₁ := by
  have h1 : (lo - a₀ + G - 1) / (G : ℤ) < t + 1 := (Int.ediv_lt_iff_lt_mul (by lia)).mpr (by lia)
  have h2 : (t : ℤ) ≤ (hi - a₀) / G := (Int.le_ediv_iff_mul_le (by lia)).mpr (by lia)
  simp only [part]
  generalize (lo - a₀ + G - 1) / (G : ℤ) = u at h1 ⊢
  generalize (hi - a₀) / (G : ℤ) = v at h2 ⊢
  split_ifs <;> first | exact ⟨_, _, rfl, by lia, by lia⟩ | lia

/-! ### Chunks and classes -/

theorem mem_chunks_iff {cnt L t₀ len : ℕ} :
    (t₀, len) ∈ chunks cnt L ↔ ∃ k < (cnt + L - 1) / L, t₀ = k * L ∧ len = min L (cnt - k * L) := by
  simp only [chunks, List.mem_map, List.mem_range, Prod.mk.injEq]
  grind

theorem exists_mem_chunks {cnt L u : ℕ} (hL : 0 < L) (hu : u < cnt) :
    ∃ t₀ len, (t₀, len) ∈ chunks cnt L ∧ t₀ = u / L * L ∧ u % L < len := by
  refine ⟨u / L * L, min L (cnt - u / L * L), mem_chunks_iff.mpr ⟨u / L, ?_, rfl, rfl⟩, rfl, ?_⟩
  · have := Nat.div_mul_le_self u L
    exact (Nat.le_div_iff_mul_le hL).mpr (by rw [Nat.succ_mul]; lia)
  · have := Nat.mod_lt u hL
    have := Nat.div_add_mod u L
    lia

theorem le_of_mem_chunks {cnt L t₀ len : ℕ} (h : (t₀, len) ∈ chunks cnt L) :
    t₀ + len ≤ cnt ∧ len ≤ L ∧ t₀ % L = 0 := by
  obtain ⟨k, hk, rfl, rfl⟩ := mem_chunks_iff.mp h
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp at hk
  have := (Nat.le_div_iff_mul_le hL).mp hk
  rw [Nat.succ_mul] at this
  exact ⟨by lia, by lia, Nat.mul_mod_left k L⟩

theorem add_mul_lt_of_lt_classCount {n G ρ u : ℕ} (hG : 0 < G) (h : u < classCount n G ρ) :
    ρ + G * u < n := by
  have := (Nat.le_div_iff_mul_le hG).mp h
  rw [Nat.succ_mul, mul_comm] at this
  lia

theorem lt_classCount {n G ρ u : ℕ} (hG : 0 < G) (h : ρ + G * u < n) : u < classCount n G ρ :=
  (Nat.le_div_iff_mul_le hG).mpr (by rw [Nat.succ_mul, mul_comm]; lia)

/-- The numerator `x` with `x + H = i` in the chunk of the class `i % G` that holds it. -/
theorem eq_sub_add_mul_of_natCast_eq {i G L H : ℕ} {x : ℤ} (hi : (i : ℤ) = x + H) :
    x = ((i % G + G * (i / G / L * L) : ℕ) : ℤ) - H + G * ((i / G % L : ℕ) : ℤ) := by
  have h1 : ((i % G : ℕ) : ℤ) + G * ((i / G : ℕ) : ℤ) = i := mod_cast Nat.mod_add_div i G
  have h2 : (L : ℤ) * ((i / G / L : ℕ) : ℤ) + ((i / G % L : ℕ) : ℤ) = ((i / G : ℕ) : ℤ) :=
    mod_cast Nat.div_add_mod (i / G) L
  simp only [Nat.cast_add, Nat.cast_mul]
  linear_combination (-1 : ℤ) * hi - h1 - (G : ℤ) * h2

theorem eq_of_add_mul_eq {G ρ ρ' u u' : ℕ} (hρ : ρ < G) (hρ' : ρ' < G)
    (h : ρ + G * u = ρ' + G * u') : ρ = ρ' ∧ u = u' := by
  have h1 := congrArg (· % G) h
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hρ, Nat.mod_eq_of_lt hρ'] at h1
  subst h1
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (n := G) (by lia) (by lia)⟩

theorem eq_of_add_mul_add_eq {G L ρ k k' t t' : ℕ} (hG : 0 < G) (hL : 0 < L) (ht : t < L)
    (ht' : t' < L) (h : ρ + G * (k * L + t) = ρ + G * (k' * L + t')) : k = k' := by
  have := congrArg (· / L) (Nat.eq_of_mul_eq_mul_left hG (Nat.add_left_cancel h))
  simpa [Nat.mul_comm k L, Nat.mul_comm k' L, Nat.mul_add_div hL, Nat.div_eq_of_lt ht,
    Nat.div_eq_of_lt ht'] using this

/-! ### The slots -/

theorem le_of_mem_slots {H G L r len : ℕ} {a₀ : ℤ} (h : (r, a₀, len) ∈ slots H G L) : len ≤ L := by
  simp only [slots, List.mem_flatMap, List.mem_range, List.mem_map, Prod.exists,
    Prod.mk.injEq] at h
  obtain ⟨_, -, _, _, hch, -, -, rfl⟩ := h
  exact (le_of_mem_chunks hch).2.1

theorem abs_add_mul_le_of_mem_slots {H G L r len : ℕ} {a₀ : ℤ} (hG : 0 < G)
    (h : (r, a₀, len) ∈ slots H G L) {t : ℕ} (ht : t < len) :
    |a₀ + G * t| ≤ H := by
  simp only [slots, List.mem_flatMap, List.mem_range, List.mem_map, Prod.exists,
    Prod.mk.injEq] at h
  obtain ⟨ρ, -, t₀, _, hch, -, rfl, rfl⟩ := h
  have := add_mul_lt_of_lt_classCount (n := 2 * H + 1) (ρ := ρ) (u := t₀ + t) hG
    (by lia [(le_of_mem_chunks hch).1])
  rw [abs_le]
  push_cast
  constructor <;> lia

/-- Every numerator `x` with `|x| ≤ H` lies in a slot, with the residue of `x` modulo `G`. -/
theorem exists_mem_slots {H G L : ℕ} (hG : 0 < G) (hL : 0 < L) {x : ℤ} (hx : |x| ≤ H) :
    ∃ a₀ len, ((x % G).toNat, a₀, len) ∈ slots H G L ∧ ∃ t < len, x = a₀ + G * t := by
  obtain ⟨i, hi⟩ : ∃ i : ℕ, (i : ℤ) = x + H := ⟨(x + H).toNat, by rw [abs_le] at hx; lia⟩
  have hu : i / G < classCount (2 * H + 1) G (i % G) :=
    lt_classCount hG (by rw [abs_le] at hx; lia [Nat.mod_add_div i G])
  obtain ⟨t₀, len, hch, rfl, hlen⟩ := exists_mem_chunks hL hu
  refine ⟨_, len, ?_, i / G % L, hlen, eq_sub_add_mul_of_natCast_eq hi⟩
  simp only [slots, List.mem_flatMap, List.mem_range, List.mem_map, Prod.exists, Prod.mk.injEq]
  refine ⟨i % G, Nat.mod_lt _ hG, _, len, hch, ?_, rfl, rfl⟩
  have := (Int.mod_modEq (i : ℤ) G).sub_right (H : ℤ)
  rw [show (i : ℤ) - H = x by lia] at this
  push_cast [Int.natCast_mod]
  rw [this]

/-- Two slots have no numerator in common. -/
theorem pairwise_slots (H : ℕ) {G L : ℕ} (hG : 0 < G) (hL : 0 < L) :
    (slots H G L).Pairwise fun (s s' : ℕ × ℤ × ℕ) ↦
      ∀ t < s.2.2, ∀ t' < s'.2.2, s.2.1 + G * t ≠ s'.2.1 + G * t' := by
  rw [slots, List.pairwise_flatMap]
  refine ⟨fun ρ _ ↦ ?_, List.nodup_range.pairwise_of_forall_ne
    fun ρ hρ ρ' hρ' hne s hs s' hs' t _ t' _ h ↦ hne ?_⟩
  · rw [chunks, List.map_map, List.pairwise_map]
    refine List.nodup_range.pairwise_of_forall_ne fun k _ k' _ hne t ht t' ht' h ↦ hne ?_
    dsimp only [Function.comp_apply] at ht ht' h
    exact eq_of_add_mul_add_eq (ρ := ρ) hG hL (ht.trans_le (min_le_left _ _))
      (ht'.trans_le (min_le_left _ _)) (by lia)
  · simp only [List.mem_map, Prod.exists] at hs hs'
    obtain ⟨t₀, len, -, rfl⟩ := hs
    obtain ⟨t₀', len', -, rfl⟩ := hs'
    exact (eq_of_add_mul_eq (u := t₀ + t) (u' := t₀' + t') (List.mem_range.mp hρ)
      (List.mem_range.mp hρ') (by lia)).1

/-! ### The region -/

/-- The bound `n / q` that `Ratpoints.Fast.endFrac` makes of a lower end `x` lies below every `v`
with `|v| ≤ H` above the value of `x`: it is that value when it lies in `[-H, H]`, `-(H + 1)` when
it lies below, and `H + 1` only when it lies above `H`, where no such `v` is. -/
theorem div_le_of_endFrac_eq_some {H : ℕ} {x : Double} {n : ℤ} {q : ℕ}
    (h : endFrac H x = some (n, q)) {v : ℚ} (hv : |v| ≤ H)
    (hx : doubleValue x.bits ≤ (v : WithBotTop ℚ)) : (n : ℚ) / q ≤ v := by
  rw [abs_le] at hv
  rcases hd : x.toDyadic with ⟨m, e⟩
  simp only [endFrac, hd] at h
  split_ifs at h with hf _ _ _ hs <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  · rwa [Double.doubleValue_eq_of_toDyadic_eq hf hd, WithBotTop.coe_le_coe,
      ← intCast_ediv_gcd_div_natCast_div_gcd] at hx
  · push_cast
    linarith
  · rw [Double.doubleValue_eq_of_toDyadic_eq hf hd, WithBotTop.coe_le_coe,
      div_le_iff₀ (by positivity)] at hx
    have : (m * 2 ^ e.toNat : ℤ) ≤ (H : ℤ) * ((2 ^ (-e).toNat : ℕ) : ℤ) :=
      mod_cast hx.trans (mul_le_mul_of_nonneg_right hv.2 (by positivity))
    lia
  · push_cast
    linarith
  · rw [Double.doubleValue_bits, ite_eq_left (by simpa [Double.isFinite] using hf),
      ite_eq_right hs] at hx
    simp at hx

/-- The bound `n / q` that `Ratpoints.Fast.endFrac` makes of an upper end `x` lies above every `v`
with `|v| ≤ H` below the value of `x`: it is that value when it lies in `[-H, H]`, `H + 1` when it
lies above, and `-(H + 1)` only when it lies below `-H`, where no such `v` is. -/
theorem le_div_of_endFrac_eq_some {H : ℕ} {x : Double} {n : ℤ} {q : ℕ}
    (h : endFrac H x = some (n, q)) {v : ℚ} (hv : |v| ≤ H)
    (hx : (v : WithBotTop ℚ) ≤ doubleValue x.bits) : v ≤ (n : ℚ) / q := by
  rw [abs_le] at hv
  rcases hd : x.toDyadic with ⟨m, e⟩
  simp only [endFrac, hd] at h
  split_ifs at h with hf _ _ _ hs <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  · rwa [Double.doubleValue_eq_of_toDyadic_eq hf hd, WithBotTop.coe_le_coe,
      ← intCast_ediv_gcd_div_natCast_div_gcd] at hx
  · rw [Double.doubleValue_eq_of_toDyadic_eq hf hd, WithBotTop.coe_le_coe,
      le_div_iff₀ (by positivity)] at hx
    have : -(H : ℤ) * ((2 ^ (-e).toNat : ℕ) : ℤ) ≤ (m * 2 ^ e.toNat : ℤ) :=
      mod_cast (mul_le_mul_of_nonneg_right hv.1 (by positivity)).trans hx
    lia
  · push_cast
    linarith
  · rw [Double.doubleValue_bits, ite_eq_left (by simpa [Double.isFinite] using hf),
      ite_eq_left hs] at hx
    simp at hx
  · push_cast
    linarith

/-- The denominator of the bound that `Ratpoints.Fast.endFrac` makes of an end is positive: a power
of `2` divided by a divisor of it, or `1`. -/
theorem pos_of_endFrac_eq_some {H : ℕ} {x : Double} {n : ℤ} {q : ℕ}
    (h : endFrac H x = some (n, q)) : 0 < q := by
  rcases hd : x.toDyadic with ⟨m, e⟩
  simp only [endFrac, hd] at h
  split_ifs at h <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  · exact Nat.div_pos (Nat.le_of_dvd (Nat.two_pow_pos _) (Nat.gcd_dvd_right _ _))
      (Nat.gcd_pos_of_pos_right _ (Nat.two_pow_pos _))
  all_goals exact Nat.one_pos

/-- The first numerator of the range of an interval lies below every `a` with `|a| ≤ H` and `a / b`
above the lower end of the interval. -/
theorem fst_numRange_le {H b : ℕ} (hb : 0 < b) {a : ℤ} (ha : |a| ≤ H) {l : Double}
    (hl : doubleValue l.bits ≤ (((a : ℚ) / b : ℚ) : WithBotTop ℚ)) (e : Option (ℤ × ℕ)) :
    (numRange H b (endFrac H l, e)).1 ≤ a := by
  rcases he : endFrac H l with _ | ⟨n, q⟩ <;> simp only [numRange]
  · lia [abs_le.mp ha]
  have hab := abs_intCast_div_natCast_le (α := ℚ) ha b
  have hv := div_le_of_endFrac_eq_some he hab hl
  have hq : (0 : ℚ) < q := mod_cast pos_of_endFrac_eq_some he
  split_ifs with h1 h2
  · exact max_le (by lia [abs_le.mp ha]) (Int.neg_ediv_neg_le_of_div_le hb hv)
  · have : (H : ℚ) < n / q := (lt_div_iff₀ hq).mpr (mod_cast (by lia))
    linarith [le_abs_self ((a : ℚ) / b)]
  · lia [abs_le.mp ha]

/-- The last numerator of the range of an interval lies above every `a` with `|a| ≤ H` and `a / b`
below the upper end of the interval. -/
theorem le_snd_numRange {H b : ℕ} (hb : 0 < b) {a : ℤ} (ha : |a| ≤ H) {u : Double}
    (hu : (((a : ℚ) / b : ℚ) : WithBotTop ℚ) ≤ doubleValue u.bits) (e : Option (ℤ × ℕ)) :
    a ≤ (numRange H b (e, endFrac H u)).2 := by
  rcases he : endFrac H u with _ | ⟨n, q⟩ <;> simp only [numRange]
  · lia [abs_le.mp ha]
  have hab := abs_intCast_div_natCast_le (α := ℚ) ha b
  have hv := le_div_of_endFrac_eq_some he hab hu
  have hq : (0 : ℚ) < q := mod_cast pos_of_endFrac_eq_some he
  split_ifs with h1 h2
  · exact le_min (by lia [abs_le.mp ha]) (Int.le_ediv_of_div_le hb hv)
  · lia [abs_le.mp ha]
  · have : (n : ℚ) / q < -H := (div_lt_iff₀ hq).mpr (mod_cast (by lia))
    linarith [neg_abs_le ((a : ℚ) / b)]

/-- The hull of the ranges of the intervals holds every numerator of the range of one of them. -/
theorem exists_bounds_of_mem {H b : ℕ} {a : ℤ} {ivs : Array (Option (ℤ × ℕ) × Option (ℤ × ℕ))}
    {iv : Option (ℤ × ℕ) × Option (ℤ × ℕ)} (hiv : iv ∈ ivs) (h1 : (numRange H b iv).1 ≤ a)
    (h2 : a ≤ (numRange H b iv).2) :
    ∃ lo hi, bounds H b (some ivs) = some (lo, hi) ∧ lo ≤ a ∧ a ≤ hi := by
  obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp hiv
  rw [bounds]
  refine Array.foldl_induction (motive := fun i acc ↦ k < i →
    ∃ lo hi, acc = some (lo, hi) ∧ lo ≤ a ∧ a ≤ hi) (by simp) (fun i acc ih hki ↦ ?_) hk
  simp only [Fin.getElem_fin]
  rcases Nat.lt_succ_iff_lt_or_eq.mp hki with hki | hki
  · obtain ⟨lo, hi, rfl, h3, h4⟩ := ih hki
    split_ifs
    · exact ⟨_, _, rfl, by lia, by lia⟩
    · exact ⟨_, _, rfl, h3, h4⟩
  · obtain rfl : k = i.1 := hki
    simp only [h1.trans h2, ↓reduceIte]
    rcases acc with _ | ⟨lo, hi⟩
    · exact ⟨_, _, rfl, h1, h2⟩
    · exact ⟨_, _, rfl, by lia, by lia⟩

/-- Assuming Sturm's theorem, the intervals of the Sturm step on the whole line hold every `a / b`
with `|a| ≤ H`, `b > 0` and `F(a, b) ≥ 0` (`Ratpoints.Sturm.covers_computeSturm`). -/
theorem exists_mem_sturmIntervals (hS : SturmTheorem) {c : List ℤ} {H depth : ℕ}
    {ivs : Array (Double × Double)} (h : sturmIntervals c (degree c) H depth = some ivs) {a : ℤ}
    {b : ℕ} (hb : 0 < b) (ha : |a| ≤ H) (hF : 0 ≤ binaryForm c a b) :
    ∃ iv ∈ ivs, doubleValue iv.1.bits ≤ (((a : ℚ) / b : ℚ) : WithBotTop ℚ) ∧
      (((a : ℚ) / b : ℚ) : WithBotTop ℚ) ≤ doubleValue iv.2.bits := by
  simp only [sturmIntervals] at h
  split_ifs at h with hc
  obtain ⟨hd, hd57, hH, hdep⟩ := hc
  have hab : |(a : ℚ) / b| ≤ 2 ^ 63 := (abs_intCast_div_natCast_le ha b).trans (mod_cast hH.le)
  obtain ⟨_, hi, hl, hu⟩ := Sturm.covers_computeSturm hS hd (getD_degree_ne_zero_of_pos hd) hd57
    hdep (by decide) h (Sturm.eval_chainPoly_nonneg hb hF) (by simpa using hab)
    ⟨_, List.mem_singleton_self _, by simp [Double.doubleValue_huge, Double.doubleValue_huge_neg]⟩
  obtain ⟨iv, hiv, rfl⟩ := List.mem_map.mp hi
  exact ⟨iv, Array.mem_toList_iff.mp hiv, hl, hu⟩

/-- Assuming Sturm's theorem, the numerators of the denominator `b > 0` that the search takes
(`Ratpoints.Fast.bounds`) include every `a` with `|a| ≤ H` and `F(a, b) ≥ 0`. -/
theorem exists_bounds_region (hS : SturmTheorem) {c : List ℤ} {H depth b : ℕ} (hb : 0 < b)
    {a : ℤ} (ha : |a| ≤ H) (hF : 0 ≤ binaryForm c a b) :
    ∃ lo hi, bounds H b (region c (degree c) H depth) = some (lo, hi) ∧ lo ≤ a ∧ a ≤ hi := by
  rcases h : sturmIntervals c (degree c) H depth with _ | ivs
  · simp only [region, h, Option.map_none, bounds]
    exact ⟨_, _, rfl, by lia [abs_le.mp ha]⟩
  · obtain ⟨iv, hiv, hl, hu⟩ := exists_mem_sturmIntervals hS h hb ha hF
    simp only [region, h, Option.map_some]
    exact exists_bounds_of_mem (Array.mem_map_of_mem hiv) (fst_numRange_le hb ha hl _)
      (le_snd_numRange hb ha hu _)

/-! ### The search -/

/-- The rows of sound families for the denominator `b`, shifted to the chunk that starts at `a₀` and
moved by `o`, keep the bit `t` of every candidate `(a₀ + G (o + t), b)` with `o + t < L`. -/
theorem testBit_rows_shiftRight {c : List ℤ} {G L : ℕ} {fams : Array Family}
    (hfams : ∀ F ∈ fams, F.IsSound c G L) {a₀ : ℤ} {b o t : ℕ} (ht : o + t < L)
    (hc : IsCandidate c (a₀ + G * (o + t)) b) {i : ℕ}
    (hi : i < (fams.map fun F ↦ F.rows[b % F.M]!).size) :
    ((fams.map fun F ↦ F.rows[b % F.M]!)[i]! >>>
      ((fams.map (Family.shift · a₀))[i]! + o)).testBit t = true := by
  simp only [Array.size_map] at hi
  simp only [getElem!_pos, Array.size_map, hi, Array.getElem_map]
  exact (hfams _ (Array.getElem_mem hi)).testBit_shiftRight ht hc

theorem of_mem_partPoints {c : List ℤ} {G : ℕ} {rs sh : Array ℕ} {lo hi a₀ : ℤ} {len b : ℕ}
    {p : ℤ × ℤ × ℤ} (h : p ∈ partPoints c (BruteForce.degree c) G rs sh lo hi a₀ len b) :
    p.2.2 = b ∧ (∃ t < len, p.1 = a₀ + G * t) ∧ Int.gcd p.1 p.2.2 = 1 ∧
      p.2.1 ^ 2 = binaryForm c p.1 p.2.2 := by
  simp only [partPoints] at h
  split at h
  · simp at h
  · rename_i t₁ len₁ hpart
    obtain ⟨hz, ⟨t, ht, hx⟩, hg, hy⟩ := of_mem_chunkPoints h
    refine ⟨hz, ⟨t₁ + t, by lia [(add_le_and_dvd_of_part_eq_some hpart).1], ?_⟩, hg, hy⟩
    rw [hx]
    push_cast
    ring

/-- A point of the chunk with its numerator from `lo` to `hi` lies in the part of the chunk. -/
theorem mem_partPoints {c : List ℤ} {G L : ℕ} (hG : 0 < G) {fams : Array Family}
    (hfams : ∀ F ∈ fams, F.IsSound c G L) {lo hi a₀ : ℤ} {len b t : ℕ} (hlen : len ≤ L)
    (ht : t < len) {p : ℤ × ℤ × ℤ} (hx : p.1 = a₀ + G * t) (hlo : lo ≤ p.1) (hhi : p.1 ≤ hi)
    (hz : p.2.2 = b) (hg : Int.gcd p.1 p.2.2 = 1) (hy : p.2.1 ^ 2 = binaryForm c p.1 p.2.2) :
    p ∈ partPoints c (BruteForce.degree c) G (fams.map fun F ↦ F.rows[b % F.M]!)
      (fams.map (Family.shift · a₀)) lo hi a₀ len b := by
  obtain ⟨t₁, len₁, hpart, h1, h2⟩ := exists_part_eq_some hG ht (hx ▸ hlo) (hx ▸ hhi)
  have hle := (add_le_and_dvd_of_part_eq_some hpart).1
  simp only [partPoints, hpart]
  refine (mem_chunkPoints fun t' ht' hc' i hi ↦ testBit_rows_shiftRight hfams (by lia) ?_ hi).mpr
    ⟨hz, ⟨t - t₁, by lia, ?_⟩, hg, hy⟩
  · rwa [show a₀ + ((G * t₁ : ℕ) : ℤ) + G * t' = a₀ + G * (t₁ + t') by push_cast; ring] at hc'
  · rw [hx]
    push_cast [Nat.cast_sub h1]
    ring

theorem nodup_partPoints (c : List ℤ) {G : ℕ} (hG : 0 < G) (rs sh : Array ℕ) (lo hi a₀ : ℤ)
    (len b : ℕ) : (partPoints c (BruteForce.degree c) G rs sh lo hi a₀ len b).Nodup := by
  rw [partPoints]
  split
  · exact List.nodup_nil
  · exact nodup_chunkPoints c hG ..

theorem of_mem_denPoints {c : List ℤ} {H G : ℕ} {fams : Array Family}
    {reg : Option (Array (Option (ℤ × ℕ) × Option (ℤ × ℕ)))} {sl : List (ℕ × ℤ × ℕ × Array ℕ)}
    {b : ℕ} {p : ℤ × ℤ × ℤ} (h : p ∈ denPoints c (BruteForce.degree c) H G fams reg sl b) :
    p.2.2 = b ∧ (∃ s ∈ sl, ∃ t < s.2.2.1, p.1 = s.2.1 + G * t) ∧ Int.gcd p.1 p.2.2 = 1 ∧
      p.2.1 ^ 2 = binaryForm c p.1 p.2.2 := by
  simp only [denPoints] at h
  split_ifs at h
  · simp at h
  split at h
  · simp at h
  split_ifs at h
  all_goals obtain ⟨⟨r, a₀, len, sh⟩, hs, hp⟩ := List.mem_flatMap.mp h
  · obtain ⟨hz, ⟨t, ht, hx⟩, hg, hy⟩ := of_mem_chunkPoints hp
    exact ⟨hz, ⟨_, hs, t, ht, hx⟩, hg, hy⟩
  · obtain ⟨hz, ⟨t, ht, hx⟩, hg, hy⟩ := of_mem_partPoints hp
    exact ⟨hz, ⟨_, hs, t, ht, hx⟩, hg, hy⟩

/-- No row of sound families is `0` for the denominator of a candidate
(`Ratpoints.Fast.Family.IsSound.rows_ne_zero`). -/
theorem any_rows_eq_false {c : List ℤ} {G L : ℕ} {fams : Array Family}
    (hfams : ∀ F ∈ fams, F.IsSound c G L) {a : ℤ} {b : ℕ} (hc : IsCandidate c a b) :
    (fams.map fun F ↦ F.rows[b % F.M]!).any (· == 0) = false := by
  refine Bool.eq_false_iff.mpr fun h ↦ ?_
  obtain ⟨_, hx, h0⟩ := Array.any_eq_true'.mp h
  obtain ⟨F, hF, rfl⟩ := Array.mem_map.mp hx
  exact (hfams F hF).rows_ne_zero hc (beq_iff_eq.mp h0)

/-- A point of a chunk of `sl` with its numerator within the bounds of the region lies in the
search of its denominator. -/
theorem mem_denPoints_of {c : List ℤ} {H G L : ℕ} (hG : 0 < G) {fams : Array Family}
    (hfams : ∀ F ∈ fams, F.IsSound c G L)
    {reg : Option (Array (Option (ℤ × ℕ) × Option (ℤ × ℕ)))} {sl : List (ℕ × ℤ × ℕ × Array ℕ)}
    {r len t b : ℕ} {a₀ : ℤ} (hs : (r, a₀, len, fams.map (Family.shift · a₀)) ∈ sl)
    (hlen : len ≤ L) (ht : t < len) {p : ℤ × ℤ × ℤ} (hx : p.1 = a₀ + G * t) (hz : p.2.2 = b)
    (hg : Int.gcd p.1 p.2.2 = 1) (hy : p.2.1 ^ 2 = binaryForm c p.1 p.2.2) {lo hi : ℤ}
    (hbd : bounds H b reg = some (lo, hi)) (hlo : lo ≤ p.1) (hhi : p.1 ≤ hi) :
    p ∈ denPoints c (BruteForce.degree c) H G fams reg sl b := by
  simp only [denPoints, any_rows_eq_false hfams ⟨hz ▸ hg, p.2.1, hz ▸ hy⟩, Bool.false_eq_true,
    ↓reduceIte, hbd]
  split_ifs
  all_goals refine List.mem_flatMap.mpr ⟨_, hs, ?_⟩
  · exact (mem_chunkPoints fun t' ht' hc' i hi ↦ testBit_rows_shiftRight hfams (by lia)
      (by simpa using hc') hi).mpr ⟨hz, ⟨t, ht, hx⟩, hg, hy⟩
  · exact mem_partPoints hG hfams hlen ht hx hlo hhi hz hg hy

/-- The points of chunks without a numerator in common, chunk by chunk, each once, when the points
of each chunk are without duplicates and lie in the chunk. -/
theorem nodup_flatMap_of_pairwise {α β : Type*} {G : ℕ} {l : List (α × ℤ × ℕ × β)}
    (hl : l.Pairwise fun (s s' : α × ℤ × ℕ × β) ↦
      ∀ t < s.2.2.1, ∀ t' < s'.2.2.1, s.2.1 + G * t ≠ s'.2.1 + G * t')
    {g : α × ℤ × ℕ × β → List (ℤ × ℤ × ℤ)} (hg : ∀ s ∈ l, (g s).Nodup)
    (hs : ∀ s ∈ l, ∀ p ∈ g s, ∃ t < s.2.2.1, p.1 = s.2.1 + G * t) : (l.flatMap g).Nodup := by
  refine List.nodup_flatMap.mpr ⟨hg, hl.imp_of_mem fun hx hy h p hp hp' ↦ ?_⟩
  obtain ⟨t, ht, hx⟩ := hs _ hx p hp
  obtain ⟨t', ht', hx'⟩ := hs _ hy p hp'
  exact h t ht t' ht' (hx.symm.trans hx')

theorem nodup_denPoints (c : List ℤ) (H : ℕ) {G : ℕ} (hG : 0 < G) (fams : Array Family)
    (reg : Option (Array (Option (ℤ × ℕ) × Option (ℤ × ℕ)))) {sl : List (ℕ × ℤ × ℕ × Array ℕ)}
    (hsl : sl.Pairwise fun (s s' : ℕ × ℤ × ℕ × Array ℕ) ↦
      ∀ t < s.2.2.1, ∀ t' < s'.2.2.1, s.2.1 + G * t ≠ s'.2.1 + G * t')
    (b : ℕ) : (denPoints c (BruteForce.degree c) H G fams reg sl b).Nodup := by
  rw [denPoints]
  split_ifs
  · exact List.nodup_nil
  split
  · exact List.nodup_nil
  split_ifs
  · exact nodup_flatMap_of_pairwise hsl (fun _ _ ↦ nodup_chunkPoints c hG ..)
      fun _ _ _ hp ↦ (of_mem_chunkPoints hp).2.1
  · exact nodup_flatMap_of_pairwise hsl (fun _ _ ↦ nodup_partPoints c hG ..)
      fun _ _ _ hp ↦ (of_mem_partPoints hp).2.1

theorem of_mem_search {c : List ℤ} {H G L : ℕ} {fams : Array Family}
    {reg : Option (Array (Option (ℤ × ℕ) × Option (ℤ × ℕ)))} {dens : List ℕ} (hG : 0 < G)
    {p : ℤ × ℤ × ℤ} (h : p ∈ search c (BruteForce.degree c) H G L fams reg dens) :
    (∃ b ∈ dens, p.2.2 = b) ∧ |p.1| ≤ H ∧ Int.gcd p.1 p.2.2 = 1 ∧
      p.2.1 ^ 2 = binaryForm c p.1 p.2.2 := by
  simp only [search, List.mem_flatMap, List.mem_filter] at h
  obtain ⟨b, ⟨hb, -⟩, hp⟩ := h
  obtain ⟨hz, ⟨s, hs, t, ht, hx⟩, hg, hy⟩ := of_mem_denPoints hp
  simp only [getElem!_map_range _ (Nat.mod_lt _ hG), List.mem_filter, List.mem_map] at hs
  obtain ⟨⟨⟨r, a₀, len⟩, hs, rfl⟩, -⟩ := hs
  exact ⟨⟨b, hb, hz⟩, hx ▸ abs_add_mul_le_of_mem_slots hG hs ht, hg, hy⟩

theorem mem_search_of {c : List ℤ} {H G L : ℕ} {fams : Array Family}
    {reg : Option (Array (Option (ℤ × ℕ) × Option (ℤ × ℕ)))} {dens : List ℕ}
    (hG : 0 < G) (hL : 0 < L) (hfams : ∀ F ∈ fams, F.IsSound c G L) {p : ℤ × ℤ × ℤ} {b : ℕ}
    (hb : b ∈ dens) (hz : p.2.2 = b) (ha : |p.1| ≤ H) (hg : Int.gcd p.1 p.2.2 = 1)
    (hy : p.2.1 ^ 2 = binaryForm c p.1 p.2.2) {lo hi : ℤ} (hbd : bounds H b reg = some (lo, hi))
    (hlo : lo ≤ p.1) (hhi : p.1 ≤ hi) :
    p ∈ search c (BruteForce.degree c) H G L fams reg dens := by
  have hc : IsCandidate c p.1 b := ⟨hz ▸ hg, p.2.1, hz ▸ hy⟩
  have hF (F) (h : F ∈ fams.filter fun F ↦ F.rows.size == F.M && 0 < F.M) : F.IsSound c G L :=
    hfams F (Array.mem_filter.mp h).1
  obtain ⟨a₀, len, hs, t, ht, hx⟩ := exists_mem_slots hG hL ha
  simp only [search, List.mem_flatMap, List.mem_filter]
  refine ⟨b, and_assoc.mpr ⟨hb, (and_iff_right_of_imp fun hp ↦ ?_).mpr (mem_denPoints_of hG hF
    (r := (p.1 % G).toNat) ?_ (le_of_mem_slots hs) ht hx hz hg hy hbd hlo hhi)⟩⟩
  · obtain ⟨-, ⟨s, hs', -⟩, -⟩ := of_mem_denPoints hp
    simpa using List.ne_nil_of_mem hs'
  rw [getElem!_map_range _ (Nat.mod_lt _ hG)]
  exact List.mem_filter.mpr ⟨List.mem_map.mpr ⟨_, hs, rfl⟩, by simpa using admitTable_spec hG hc⟩

theorem nodup_search (c : List ℤ) (H : ℕ) {G L : ℕ} (fams : Array Family)
    (reg : Option (Array (Option (ℤ × ℕ) × Option (ℤ × ℕ)))) {dens : List ℕ}
    (hG : 0 < G) (hL : 0 < L) (hdens : dens.Nodup) :
    (search c (BruteForce.degree c) H G L fams reg dens).Nodup := by
  rw [search]
  refine List.nodup_flatMap.mpr ⟨fun b _ ↦ nodup_denPoints c H hG _ reg ?_ b,
    (hdens.filter _).pairwise_of_forall_ne fun b _ b' _ hne p hp hp' ↦ hne ?_⟩
  · rw [getElem!_map_range _ (Nat.mod_lt _ hG)]
    exact List.Pairwise.filter _ (List.pairwise_map.mpr ((pairwise_slots H hG hL).imp fun h ↦ h))
  · exact_mod_cast (of_mem_denPoints hp).1.symm.trans (of_mem_denPoints hp').1

/-! ### The denominators -/

theorem getElem!_forbiddenDens_eq_zero {c : List ℤ} (hd : degree c % 2 = 0) {a : ℤ} {b : ℕ}
    (hc : IsCandidate c a b) (hi : ℕ) : (forbiddenDens (c.getD (degree c) 0) hi)[b]! = 0 := by
  by_contra h
  obtain ⟨q, hq, hqb, hJ⟩ := exists_dvd_of_getElem!_forbiddenDens_ne_zero h
  obtain ⟨hab, y, hy⟩ := hc
  have hg : Int.gcd (c.getD (degree c) 0) q = 1 := by
    by_contra hg
    rw [jacobiSym.eq_zero_iff.mpr ⟨by lia, hg⟩] at hJ
    exact absurd hJ (by decide)
  rw [Sieve.jacobiSym_eq_one_of_sq_eq_binaryForm hab hd hy hqb hg] at hJ
  exact absurd hJ (by decide)

/-- For odd degree, the denominator `b` of a candidate is `s k ^ 2` with `s` dividing the leading
coefficient (`Ratpoints.exists_eq_mul_mul_of_sq_eq_binaryForm_of_odd`), which
`Ratpoints.Fast.squareDens` marks. -/
theorem getElem!_squareDens_of_isCandidate {c : List ℤ} (hd : degree c % 2 = 1) {a : ℤ}
    {b hi : ℕ} (hb : 1 ≤ b) (hbhi : b ≤ hi) (hc : IsCandidate c a b) :
    (squareDens (c.getD (degree c) 0).natAbs hi)[b]! = 1 := by
  obtain ⟨hab, y, hy⟩ := hc
  obtain ⟨s, k, -, hs, rfl⟩ := exists_eq_mul_mul_of_sq_eq_binaryForm_of_odd hd hab hy
  have hk : 0 < k := Nat.pos_of_ne_zero fun h ↦ by simp [h] at hb
  exact getElem!_squareDens (Int.natAbs_ne_zero.mpr (getD_degree_ne_zero_of_pos (by lia))) hs hk
    hbhi

/-- The denominators of the search lie in the range of `bLow`, `bHigh` and `H`, in ascending
order. -/
theorem denominators_sublist (c : List ℤ) (d H : ℕ) (bLow bHigh : ℤ) :
    (denominators c d H bLow bHigh).Sublist (List.range' (max 1 bLow.toNat)
      ((denominatorBound bHigh H) + 1 - max 1 bLow.toNat)) := by
  simp only [denominators]
  generalize denominatorBound bHigh H = hi
  split_ifs <;> first | exact collectMarked_sublist _ _ (le_max_left _ _) _ | exact .refl _

private theorem mem_denominatorRange {H b : ℕ} {bLow bHigh : ℤ} :
    b ∈ List.range' (max 1 bLow.toNat) (denominatorBound bHigh H + 1 - max 1 bLow.toNat) ↔
      1 ≤ b ∧ b ≤ H ∧ bLow ≤ b ∧ (bHigh < 1 ∨ (b : ℤ) ≤ bHigh) := by
  rw [List.mem_range'_1, denominatorBound]
  split_ifs <;> lia

theorem mem_denominators {c : List ℤ} {d H : ℕ} {bLow bHigh : ℤ} {b : ℕ}
    (h : b ∈ denominators c d H bLow bHigh) :
    1 ≤ b ∧ b ≤ H ∧ bLow ≤ b ∧ (bHigh < 1 ∨ (b : ℤ) ≤ bHigh) :=
  mem_denominatorRange.mp ((denominators_sublist ..).subset h)

theorem mem_denominators_of_isCandidate {c : List ℤ} {H : ℕ} {bLow bHigh : ℤ} {a : ℤ} {b : ℕ}
    (h1 : 1 ≤ b) (h2 : b ≤ H) (h3 : bLow ≤ b) (h4 : bHigh < 1 ∨ (b : ℤ) ≤ bHigh)
    (hc : IsCandidate c a b) : b ∈ denominators c (BruteForce.degree c) H bLow bHigh := by
  have hr := mem_denominatorRange.mpr ⟨h1, h2, h3, h4⟩
  simp only [denominators]
  generalize denominatorBound bHigh H = hi at hr ⊢
  have hbhi : b ≤ hi := by lia [List.mem_range'_1.mp hr]
  split_ifs with hd
  · exact (mem_collectMarked_iff (le_max_left _ _)).mpr
      ⟨hr, getElem!_squareDens_of_isCandidate hd h1 hbhi hc⟩
  · exact hr
  · exact (mem_collectMarked_iff (le_max_left _ _)).mpr
      ⟨hr, getElem!_forbiddenDens_eq_zero (Nat.mod_two_ne_one.mp hd) hc hi⟩

theorem nodup_denominators (c : List ℤ) (d H : ℕ) (bLow bHigh : ℤ) :
    (denominators c d H bLow bHigh).Nodup :=
  (List.nodup_range' ..).sublist (denominators_sublist ..)

/-! ### The parameters -/

theorem mem_of_mem_groupModuli {Mmax : ℕ} {l : List (ℕ × Array (Array Bool))}
    {g : List (ℕ × Array (Array Bool))} (hg : g ∈ groupModuli Mmax l) {t : ℕ × Array (Array Bool)}
    (ht : t ∈ g) : t ∈ l := by
  induction l generalizing g with
  | nil => simp [groupModuli] at hg
  | cons t' ts ih =>
    rw [groupModuli] at hg
    split at hg
    · rename_i g' gs heq
      split_ifs at hg
      · rcases List.mem_cons.mp hg with rfl | hg
        · rcases List.mem_cons.mp ht with rfl | ht
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih (heq ▸ List.mem_cons_self) ht)
        · exact List.mem_cons_of_mem _ (ih (heq ▸ List.mem_cons_of_mem _ hg) ht)
      · rcases List.mem_cons.mp hg with rfl | hg
        · rw [List.mem_singleton.mp ht]
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih (heq ▸ hg) ht)
    · rw [List.mem_singleton.mp hg, List.mem_singleton] at ht
      rw [ht]
      exact List.mem_cons_self

theorem choose_G_pos (tu : Tuning) (c : List ℤ) (d H B : ℕ) : 0 < (choose tu c d H B).G := by
  simp only [choose, orDefault]
  split_ifs <;> lia

theorem choose_L_pos (tu : Tuning) (c : List ℤ) (d H B : ℕ) : 0 < (choose tu c d H B).L := by
  simp only [choose]
  lia

theorem eq_admitTable_of_mem_takeModuli {c : List ℤ} {d κ : ℕ} {ms : List ℕ} {E : ℕ}
    {t : ℕ × Array (Array Bool)} (ht : t ∈ takeModuli c d κ ms E) : t.2 = admitTable c d t.1 := by
  induction ms generalizing E with
  | nil => simp [takeModuli] at ht
  | cons m ms ih =>
    rw [takeModuli] at ht
    split_ifs at ht
    · exact (List.mem_cons.mp ht).elim (· ▸ rfl) ih
    · simp at ht

theorem eq_admitTable_of_mem_moduliTables {tu : Tuning} {c : List ℤ} {d H B : ℕ}
    {t : ℕ × Array (Array Bool)} (ht : t ∈ moduliTables tu c d H B) : t.2 = admitTable c d t.1 :=
  eq_admitTable_of_mem_takeModuli ht

theorem eq_admitTable_of_mem_sortedGroups {tu : Tuning} {c : List ℤ} {d H B : ℕ}
    {g : List (ℕ × Array (Array Bool))} (hg : g ∈ sortedGroups tu c d H B)
    {t : ℕ × Array (Array Bool)} (ht : t ∈ g) : t.2 = admitTable c d t.1 := by
  simp only [sortedGroups, List.mem_map, List.mem_mergeSort] at hg
  obtain ⟨⟨g, s⟩, ⟨g', hg', hgs⟩, rfl⟩ := hg
  obtain rfl : g' = g := congr(Prod.fst $hgs)
  exact eq_admitTable_of_mem_moduliTables (mem_of_mem_groupModuli hg' ht)

theorem isSound_of_mem_choose {tu : Tuning} {c : List ℤ} {H B : ℕ} {F : Family}
    (hF : F ∈ (choose tu c (BruteForce.degree c) H B).fams) :
    F.IsSound c (choose tu c (BruteForce.degree c) H B).G
      (choose tu c (BruteForce.degree c) H B).L := by
  simp only [choose, List.mem_toArray, List.mem_filterMap] at hF ⊢
  obtain ⟨g, hg, hF⟩ := hF
  exact mkFamily_isSound (fun t ht ↦ eq_admitTable_of_mem_sortedGroups hg ht) hF

/-! ### The points -/

theorem isPoint_and_inRegion_of_mem_sievePoints {c : List ℤ} {H : ℕ} {bLow bHigh : ℤ}
    {tu : Tuning} {p : ℤ × ℤ × ℤ} (h : p ∈ sievePoints c H bLow bHigh tu) :
    IsPoint c H p ∧ InRegion [] bLow bHigh p := by
  obtain ⟨x, y, z⟩ := p
  simp only [sievePoints, List.mem_append, List.mem_ite_nil_right, mem_pointsOfDen_iff,
    horner_scaledCoeffs_mul, List.mem_singleton] at h
  simp only [IsPoint, IsNormalizedPair, InRegion]
  rcases h with ⟨hH, rfl, rfl, hg, hy⟩ | h
  · exact ⟨⟨hy, hg, .inr ⟨rfl, rfl⟩, by simpa using hH, by simp⟩, .inl rfl⟩
  · obtain ⟨⟨b, hb, rfl⟩, hx, hg, hy⟩ := of_mem_search (choose_G_pos ..) h
    obtain ⟨h1, h2, h3, h4⟩ := mem_denominators hb
    exact ⟨⟨hy, hg, .inl (by lia), hx, by lia⟩, .inr ⟨h3, h4, .inl trivial⟩⟩

/-- The search without the reversal lists every point of the region, assuming Sturm's theorem, on
which the region of the numerators rests (`Ratpoints.Fast.exists_bounds_region`). -/
theorem mem_sievePoints_of_isPoint (hS : SturmTheorem) {c : List ℤ} {H : ℕ} {bLow bHigh : ℤ}
    {tu : Tuning} {p : ℤ × ℤ × ℤ} (hp : IsPoint c H p) (hr : InRegion [] bLow bHigh p) :
    p ∈ sievePoints c H bLow bHigh tu := by
  obtain ⟨x, y, z⟩ := p
  obtain ⟨hy, hg, hz | ⟨rfl, rfl⟩, hx, hzH⟩ := hp
  · obtain ⟨b, rfl⟩ : ∃ b : ℕ, z = b := ⟨z.toNat, by lia⟩
    obtain ⟨h3, h4⟩ : bLow ≤ b ∧ (bHigh < 1 ∨ (b : ℤ) ≤ bHigh) := by
      rcases hr with h | ⟨h3, h4, -⟩
      · simp at h
        lia
      · exact ⟨h3, h4⟩
    obtain ⟨lo, hi, hbd, hlo, hhi⟩ := exists_bounds_region hS (depth := orDefault tu.sturm 10)
      (by lia) hx (hy ▸ sq_nonneg y)
    exact List.mem_append_right _ (mem_search_of (choose_G_pos ..) (choose_L_pos ..)
      (fun F hF ↦ isSound_of_mem_choose hF) (mem_denominators_of_isCandidate (by lia) (by lia)
        h3 h4 ⟨hg, y, hy⟩) rfl hx hg hy hbd hlo hhi)
  · refine List.mem_append_left _ ?_
    simp only [show 1 ≤ H by simpa using hx, ↓reduceIte]
    exact mem_pointsOfDen_iff.mpr
      ⟨List.mem_singleton_self _, rfl, hg, by rwa [horner_scaledCoeffs_mul]⟩

theorem nodup_sievePoints (c : List ℤ) (H : ℕ) (bLow bHigh : ℤ) (tu : Tuning) :
    (sievePoints c H bLow bHigh tu).Nodup := by
  rw [sievePoints]
  refine List.Nodup.append ?_ (nodup_search _ _ _ _ (choose_G_pos ..) (choose_L_pos ..)
    (nodup_denominators ..)) fun p hp hp' ↦ ?_
  · split_ifs
    · exact nodup_pointsOfDen _ _ _ (List.nodup_singleton 1)
    · exact List.nodup_nil
  · have h0 : p.2.2 = 0 := by
      split_ifs at hp
      · exact (mem_pointsOfDen_iff.mp hp).2.1
      · simp at hp
    obtain ⟨⟨b, hb, hz⟩, -⟩ := of_mem_search (choose_G_pos ..) hp'
    have := (mem_denominators hb).1
    lia

/-- `Ratpoints.Fast.reversed` reverses only for the whole box, and then the binary form of the
reversed list is that of `c` with `x` and `z` exchanged
(`Ratpoints.Setup.binaryForm_eq_of_reversal_eq_ok`). -/
theorem isFullBox_and_binaryForm_eq_of_reversed_eq {c c' : List ℤ} {H : ℕ} {bLow bHigh : ℤ}
    (h : reversed c H bLow bHigh = (c', true)) :
    IsFullBox ([] : List (WithBotTop ℚ × WithBotTop ℚ)) bLow bHigh H ∧
      ∀ x z, binaryForm c' x z = binaryForm c z x := by
  simp only [reversed] at h
  split_ifs at h with hb
  · split at h
    · obtain rfl := congr(Prod.fst $h)
      exact ⟨⟨rfl, hb⟩, Setup.binaryForm_eq_of_reversal_eq_ok ‹_›⟩
    · simp at h
  · simp at h

/-- **The fast search lists only points** of height at most `H` with their denominator in the range
of `bLow` and `bHigh`, for every coefficient list, every height bound, every range and every setting
of the parameters: when the coefficients are reversed, the search of the reversed list lists only
points, which `Ratpoints.Sieve.swapPoint` maps to points (`Ratpoints.Sieve.isPoint_swapPoint`), of
the whole box. -/
theorem isPoint_and_inRegion_of_mem_fastPoints {c : List ℤ} {H : ℕ} {bLow bHigh : ℤ}
    {tu : Tuning} {p : ℤ × ℤ × ℤ} (h : p ∈ fastPoints c H bLow bHigh tu) :
    IsPoint c H p ∧ InRegion [] bLow bHigh p := by
  rw [fastPoints] at h
  split at h
  · obtain ⟨hb, hsw⟩ := isFullBox_and_binaryForm_eq_of_reversed_eq ‹_›
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
    have hp := Sieve.isPoint_swapPoint hsw (isPoint_and_inRegion_of_mem_sievePoints hq).1
    exact ⟨hp, hp.2.inRegion_of_isFullBox hb⟩
  · exact isPoint_and_inRegion_of_mem_sievePoints h

/-- **The fast search lists every point** of height at most `H` with its denominator in the range
of `bLow` and `bHigh`, assuming Sturm's theorem, on which the region of the search rests
(`Ratpoints.Fast.exists_bounds_region`): when the coefficients are reversed, the point mapped by
`Ratpoints.Sieve.swapPoint` is a point of the reversed list, of the whole box. -/
theorem mem_fastPoints_of_isPoint (hS : SturmTheorem) {c : List ℤ} {H : ℕ} {bLow bHigh : ℤ}
    {tu : Tuning} {p : ℤ × ℤ × ℤ} (hp : IsPoint c H p) (hr : InRegion [] bLow bHigh p) :
    p ∈ fastPoints c H bLow bHigh tu := by
  rw [fastPoints]
  split
  · obtain ⟨-, hsw⟩ := isFullBox_and_binaryForm_eq_of_reversed_eq ‹_›
    have hq := Sieve.isPoint_swapPoint (fun x z ↦ (hsw z x).symm) hp
    exact List.mem_map.mpr ⟨_, mem_sievePoints_of_isPoint hS hq
      (hq.2.inRegion_of_isFullBox ⟨rfl, le_rfl, .inl one_pos⟩), Sieve.swapPoint_swapPoint hp.2.2.1⟩
  · exact mem_sievePoints_of_isPoint hS hp hr

/-- **The fast search lists exactly the points** of height at most `H` with their denominator in
the range of `bLow` and `bHigh`, for every coefficient list, every height bound, every range and
every setting of the parameters, assuming Sturm's theorem. -/
theorem mem_fastPoints_iff_of_sturmTheorem {c : List ℤ} {H : ℕ} {bLow bHigh : ℤ} {tu : Tuning}
    {p : ℤ × ℤ × ℤ} (hS : SturmTheorem) :
    p ∈ fastPoints c H bLow bHigh tu ↔ IsPoint c H p ∧ InRegion [] bLow bHigh p :=
  ⟨isPoint_and_inRegion_of_mem_fastPoints, fun ⟨hp, hr⟩ ↦ mem_fastPoints_of_isPoint hS hp hr⟩

/-- Fast-search membership is equivalent to being a point in the specified height and
denominator range, for any tuning parameters. -/
theorem mem_fastPoints_iff {c : List ℤ} {H : ℕ} {bLow bHigh : ℤ} {tu : Tuning}
    {p : ℤ × ℤ × ℤ} :
    p ∈ fastPoints c H bLow bHigh tu ↔ IsPoint c H p ∧ InRegion [] bLow bHigh p :=
  mem_fastPoints_iff_of_sturmTheorem sturmTheorem

/-- **The fast search lists each point once**: when the coefficients are reversed,
`Ratpoints.Sieve.swapPoint` is injective on the points of the reversed list
(`Ratpoints.Sieve.swapPoint_inj`). -/
theorem nodup_fastPoints (c : List ℤ) (H : ℕ) (bLow bHigh : ℤ) (tu : Tuning) :
    (fastPoints c H bLow bHigh tu).Nodup := by
  rw [fastPoints]
  split
  · refine (nodup_sievePoints ..).map_on fun q hq q' hq' ↦ (Sieve.swapPoint_inj ?_ ?_).mp
    exacts [(isPoint_and_inRegion_of_mem_sievePoints hq).1.2.2.1,
      (isPoint_and_inRegion_of_mem_sievePoints hq').1.2.2.1]
  · exact nodup_sievePoints ..

end Ratpoints.Fast

end
