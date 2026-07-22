import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Combinatorics.Derangements.Finite

namespace Nat

def chooseImpl (n k : ℕ) :=
  if n < k then 0 else
  if k = 0 then 1 else
  if k = 1 then n else
  chooseImpl n (k / 2) * chooseImpl (n - k / 2) (k - k / 2) / chooseImpl k (k / 2)
termination_by k

@[csimp] theorem choose_eq_chooseImpl : choose = chooseImpl := by
  ext n k; induction k using Nat.strong_induction_on generalizing n
  rename_i k ih; unfold chooseImpl; split_ifs
  · rwa [choose_eq_zero_of_lt]
  · subst k; simp
  · subst k; simp
  rw [← ih, ← ih, ← ih] <;> try omega
  apply Nat.eq_div_of_mul_eq_left (choose_ne_zero (k.div_le_self 2))
  exact choose_mul (k.div_le_self 2)

def multichooseImpl (n k : ℕ) := choose (n + k - 1) k

@[csimp] theorem multichoose_eq_multichooseImpl : @multichoose = @multichooseImpl :=
  funext₂ multichoose_eq

def centralBinomImpl (n : ℕ) := choose (2 * n) n

@[csimp] theorem centralBinom_eq_centralBinomImpl : @centralBinom = @centralBinomImpl := rfl

def catalanImpl (n : ℕ) := centralBinom n / (n + 1)

@[csimp] theorem catalan_eq_catalanImpl : @catalan = @catalanImpl :=
  funext catalan_eq_centralBinom_div

def _root_.numDerangementsImpl (n : ℕ) : ℕ := Id.run do
  let mut d := 1
  for i in 1...=n do d := bif i.testBit 0 then i * d - 1 else i * d + 1
  return d

@[csimp]
theorem numDerangements_eq_numDerangementsImpl : @numDerangements = @numDerangementsImpl := by
  ext n; simp only [numDerangementsImpl, forIn, Std.Rcc.forIn'_eq_forIn'_toList]; simp
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.toList_rcc_succ_right_eq_append (by simp), List.foldl_concat, ← ih, ← Int.ofNat_inj,
      numDerangements_succ, Bool.cond_eq_ite]; split
    · rename_i h; rw [Int.ofNat_sub]
      · simp; simp [succ_mod_two_eq_one_iff] at h; rw [Even.neg_one_pow]; simpa [even_iff]
      rcases n with (- | - | n); simp; simp at h
      clear h ih; apply one_le_mul; simp; induction n with
      | zero => simp [numDerangements]
      | succ n ih => unfold numDerangements; grind
    · rename_i h; simp [succ_mod_two_eq_zero_iff] at h; rw [← odd_iff] at h; simp [h]
