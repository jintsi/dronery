import Mathlib.Data.Nat.BinaryRec
import Batteries.Tactic.Alias

/-- Number of bits needed to write `n`, with `bitLength 0 = 0`. -/
def Nat.bitLength (n : Nat) := if n = 0 then 0 else n.log2 + 1

theorem Nat.lt_two_pow_bitLength (n : Nat) : n < 2 ^ n.bitLength := by
  rw [bitLength]; split
  · subst n; simp
  · exact lt_log2_self

/-- The ruler sequence, or highest power of 2 dividing `n`, or the number of zeroes at the end of
`n`'s binary representation: 0 1 0 2 0 1 0 3 0 1 0 2 0 1 0 4... (A007814, starting from n = 1). -/
def Nat.ruler (n : Nat) : Nat := n.binaryRec 0 fun b _ ih => bif b then 0 else ih + 1

alias A007814 := Nat.ruler

theorem Nat.ruler_zero : ruler 0 = 0 := rfl

theorem Nat.ruler_even (h : n ≠ 0) : ruler (2 * n) = ruler n + 1 := by
  rw [ruler, ← bit_false_apply, binaryRec_eq]; rfl; simpa

theorem Nat.ruler_odd : ruler (2 * n + 1) = 0 := by
  rw [ruler, ← bit_true_apply, binaryRec_eq]; rfl; simp

def A211667 (n : Nat) := if n ≤ 1 then 0 else 1 + n.log2.log2

/-- In the compiler, this is a noop. -/
def Nat.toBitVec (n : Nat) := BitVec.ofNatLT n n.lt_two_pow_bitLength

theorem Nat.toNat_toBitVec {n : Nat} : n.toBitVec.toNat = n := rfl

def Nat.binaryRev (n : Nat) := n.toBitVec.reverse.toNat

alias A030101 := Nat.binaryRev
