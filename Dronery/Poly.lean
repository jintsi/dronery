import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Finset.Sort

open scoped DirectSum

abbrev CPoly (R) [Semiring R] := ⨁ _ : ℕ, R

scoped[Poly] notation:9000 R "[X]" => CPoly R

namespace Poly

open DFinsupp

instance instOne [Semiring R] : One R[X] := ⟨.single 0 1⟩

theorem one_def [Semiring R] : (1 : R[X]) = .single 0 1 := rfl

abbrev X [Semiring R] : R[X] := .single 1 1

@[irreducible]
def mul' [Semiring R] (p q : R[X]) : R[X] :=
  p.sumZeroHom fun i => ⟨fun a => q.sumZeroHom fun j =>
    ⟨fun b => .single (i + j) (a * b), by simp⟩, by classical simp [sumZeroHom_apply]⟩

instance instMul [Semiring R] : Mul R[X] := ⟨mul'⟩

theorem mul_def' [Semiring R] (p q : R[X]) : p * q =
    p.sumZeroHom fun i => ⟨fun a => q.sumZeroHom fun j =>
      ⟨fun b => .single (i + j) (a * b), by simp⟩, by classical simp [sumZeroHom_apply]⟩ := by
  with_unfolding_all rfl

/-- Multiplication becomes easier to state under decidability assumption. -/
theorem mul_def [Semiring R] [DecidableEq R] (p q : R[X]) :
    p * q = p.sum fun i a => q.sum fun j b => .single (i + j) (a * b) := by
  simp [mul_def', sumZeroHom_apply]

instance semiring [Semiring R] : Semiring R[X] where
  mul_assoc p q r := by
    classical
    simp [mul_def]
    rw [sum_sum_index (by simp) (by simp [add_mul])]
    conv =>
      enter [1, 2, i, a]
      rw [sum_sum_index (by simp) (by simp [add_mul])]
      enter [2, j, b]; rw [sum_single_index (by simp)]
    conv =>
      enter [2, 2, i, a]
      rw [sum_sum_index (by simp) (by simp [mul_add])]
      enter [2, j, b]
      rw [sum_sum_index (by simp) (by simp [mul_add])]
      enter [2, k, c]
      rw [sum_single_index (by simp), ← add_assoc, ← mul_assoc]
  one_mul p := by
    classical simp [mul_def, one_def, sum_single_index]; exact sum_single
  mul_one p := by
    classical simp [mul_def, one_def, sum_single_index]; exact sum_single
  zero_mul p := by classical simp [mul_def, sum_zero_index]
  mul_zero p := by classical simp [mul_def, sum_zero_index]
  left_distrib p q r := by
    classical
    simp [mul_def]
    conv => enter [1, 2, i, a]; rw [sum_add_index (by simp) (by simp [mul_add])]
    simp
  right_distrib p q r := by
    classical rw [mul_def, mul_def, mul_def, sum_add_index] <;> simp [add_mul]

instance commSemiring [CommSemiring R] : CommSemiring R[X] where
  mul_comm p q := by classical rw [mul_def, mul_def, sum_comm]; simp [add_comm, mul_comm]

instance ring [Ring R] : Ring R[X] where

instance commRing [CommRing R] : CommRing R[X] where

@[simp]
theorem X_ne_zero [Semiring R] [Nontrivial R] : (X : R[X]) ≠ 0 := by
  rw [ne_eq, DFinsupp.ext_iff]; simp

instance nontrivial [Semiring R] [Nontrivial R] : Nontrivial R[X] :=
  ⟨⟨X, 0, X_ne_zero⟩⟩

@[simps! apply]
def monomial [Semiring R] (n : ℕ) : R →ₗ[R] R[X] :=
  DirectSum.lof _ _ (fun _ => R) n

def C [Semiring R] : R →+* R[X] where
  toAddMonoidHom := (monomial 0).toAddMonoidHom
  map_mul' := by classical simp [mul_def, sum_single_index]
  map_one' := rfl

theorem C_ofNat [Semiring R] (n : ℕ) [n.AtLeastTwo] : C ofNat(n) = (ofNat(n) : R[X]) :=
  map_ofNat C n

def equivPolynomial [Semiring R] [DecidableEq R] : R[X] ≃+* Polynomial R where
  toFun p := .ofFinsupp (.ofCoeff p.toFinsupp)
  invFun P := P.toFinsupp.coeff.toDFinsupp
  map_mul' p q := by
    simp [mul_def, ← Polynomial.ofFinsupp_mul]; ext m
    simp [AddMonoidAlgebra.coeff_mul, sum, Finsupp.sum]
  map_add' p q := by rw [toFinsupp_add]; rfl

unsafe instance repr {R} [Semiring R] [Repr R] [DecidableEq R] : Repr (CPoly R) where
  reprPrec p prec :=
    let l : List (ℕ × Std.Format) := p.support.sort.map fun
    | 0 => (max_prec, f!"C {reprArg (p 0)}")
    | 1 => if p 1 = 1 then (max_prec, f!"X") else (73, f!"{reprPrec (p 1) 73} • X")
    | n => if p n = 1 then (80, f!"X ^ {n.repr}") else (73, f!"{reprPrec (p n) 73} • X ^ {n.repr}")
    match l with
    | [] => "0"
    | [(tp, t)] => if tp ≤ prec then t.paren else t
    | ts => (if prec ≥ 65 then .paren else id)
        (Std.Format.joinSep (ts.map Prod.snd) (" +" ++ .line)).fill
