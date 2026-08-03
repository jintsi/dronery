import Dronery.LFinsupp
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Coeff
import Dronery.List

/-! # Computable polynomials -/

abbrev CPoly (R) [Zero R] := LFinsupp R

namespace CPoly

open LFinsupp

scoped notation:9000 R "[X]" => CPoly R

abbrev mk [Zero R] (l : List R) : R[X] := LFinsupp.mk l

theorem mk_def [Zero R] {l : List R} : mk l = LFinsupp.mk l := rfl

@[cases_eliminator, elab_as_elim]
theorem casesOn [Zero R] {motive : R[X] → Prop} (p : R[X]) (mk : (l : List R) → motive (mk l)) :
    motive p := p.inductionOn mk

theorem eq_iff [Zero R] {x y : List R} : mk x = mk y ↔
    ∃ n, x = y ++ List.replicate n 0 ∨ y = x ++ List.replicate n 0 := LFinsupp.eq_iff

/-- `p.coeff n` is the coefficient of `X ^ n` in `p`. -/
def coeff [Zero R] (p : R[X]) (n : ℕ) : R := p n

@[simp]
theorem apply_eq_coeff [Zero R] {p : R[X]} : p n = p.coeff n := rfl

@[simp]
theorem coeff_mk [Zero R] {l : List R} : (mk l).coeff n = l.getD n 0 := rfl

@[ext]
theorem ext [Zero R] {p q : R[X]} : (∀ n, p.coeff n = q.coeff n) → p = q :=
  DFunLike.ext p q

@[simp]
theorem coeff_zero [Zero R] : (0 : R[X]).coeff n = 0 := zero_apply n

instance [Zero R] [One R] : One R[X] := ⟨single 0 1⟩

theorem one_def [Zero R] [One R] : (1 : R[X]) = single 0 1 := rfl

theorem coeff_one [Zero R] [One R] : (1 : R[X]).coeff n = if n = 0 then 1 else 0 :=
  single_apply

def X [Zero R] [One R] : R[X] := single 1 1

theorem X_def [Zero R] [One R] : (X : R[X]) = single 1 1 := rfl

@[simp]
theorem coeff_add [AddZeroClass R] {p q : R[X]} : (p + q).coeff n = p.coeff n + q.coeff n :=
  add_apply p q n

@[simp]
theorem coeff_neg [NegZeroClass R] {p : R[X]} : (-p).coeff n = -p.coeff n := neg_apply p n

@[simp]
theorem coeff_sub [SubNegZeroMonoid R] {p q : R[X]} : (p - q).coeff n = p.coeff n - q.coeff n :=
  sub_apply p q n

theorem coeff_list_sum [AddZeroClass R] {l : List R[X]} :
    l.sum.coeff n = (l.map fun p => p.coeff n).sum := by induction l <;> simp_all

instance [AddMonoidWithOne R] : AddMonoidWithOne R[X] where
  natCast n := single 0 n
  natCast_zero := by ext; simp
  natCast_succ n := by ext; simp [one_def]

instance [AddCommMonoidWithOne R] : AddCommMonoidWithOne R[X] where

theorem natCast_def [AddMonoidWithOne R] {n : ℕ} : (n : R[X]) = single 0 (n : R) := rfl

instance [AddGroupWithOne R] : AddGroupWithOne R[X] where
  intCast z := single 0 z
  intCast_ofNat n := by simp [natCast_def]
  intCast_negSucc n := by rw [natCast_def]; ext; simp [-neg_add_rev]

instance [AddCommGroupWithOne R] : AddCommGroupWithOne R[X] where

theorem intCast_def [AddGroupWithOne R] {z : ℤ} : (z : R[X]) = single 0 (z : R) := rfl

@[simp]
theorem coeff_smul [Zero R] [SMulZeroClass S R] {c : S} {p : R[X]} :
    (c • p).coeff n = c • p.coeff n := smul_apply c p n

/-- `p <<< n` is defined as `p * X ^ n`, analogous to how `n <<< m = n * 2 ^ m`. -/
def shiftLeft [Zero R] (p : R[X]) : ℕ → R[X]
| 0 => p
| n + 1 => p.liftOn (fun l => mk (0 :: l)) (by intro l _ rfl; apply Quot.sound; simp)
  |>.shiftLeft n

instance [Zero R] : HShiftLeft R[X] ℕ R[X] := ⟨shiftLeft⟩

theorem shiftLeft_mk [Zero R] {l : List R} : mk l <<< n = mk (List.replicate n 0 ++ l) := by
  change (mk l).shiftLeft n = _
  induction n generalizing l with
  | zero => rfl
  | succ n ih => rw [shiftLeft, mk, Quot.liftOn_mk, ih]; simp [List.replicate_succ']

theorem coeff_shiftLeft [Zero R] {p : R[X]} :
    coeff (p <<< i) n = if n < i then 0 else p.coeff (n - i) := by
  cases p; simp [shiftLeft_mk, List.getElem?_append]; split <;> simp

@[simp]
theorem zero_shiftLeft [Zero R] {n : ℕ} : (0 : R[X]) <<< n = 0 := by
  ext; simp [coeff_shiftLeft]

@[simp]
theorem shiftLeft_zero [Zero R] {p : R[X]} : p <<< 0 = p := rfl

instance [NonUnitalNonAssocSemiring R] : Mul R[X] where
  mul p q := p.liftOn (fun l => l.foldlIdx (fun i acc a => acc + (a • q) <<< i) 0) (by
    intro a _ rfl; simp [List.foldlIdx_eq_foldl_zipIdx, List.zipIdx_append])

theorem mk_mul [NonUnitalNonAssocSemiring R] {l : List R} {q : R[X]} :
    mk l * q = (l.mapIdx fun i a => (a • q) <<< i).sum := by
  unfold HMul.hMul instHMul Mul.mul instMul mk
  simp [List.sum_eq_foldl, List.mapIdx_eq_zipIdx_map, List.foldl_map, List.foldlIdx_eq_foldl_zipIdx]

open Finset in
theorem coeff_mul [NonUnitalNonAssocSemiring R] {p q : R[X]} : (p * q).coeff n =
    ∑ x ∈ antidiagonal n, p.coeff x.1 * q.coeff x.2 := by
  cases p; cases q; rename_i p q; calc (mk p * mk q).coeff n
  _ = ((p.mapIdx (fun i a ↦ (a • mk q) <<< i)).map fun p => p.coeff n).sum := by
    simp [mk_mul, coeff_list_sum]
  _ = ∑ i : Fin p.length, ((p[i] • mk q) <<< (i : ℕ)).coeff n := by
    rw [← Fin.sum_univ_fun_getElem]; simp; congr! <;> simp
  _ = ∑ i : Fin p.length, if n < i then 0 else (mk p).coeff i * (mk q).coeff (n - i) := by
    simp [coeff_shiftLeft]
  _ = ∑ i ∈ range p.length, if n < i then 0 else (mk p).coeff i * (mk q).coeff (n - i) := by
    rw [← Fin.sum_univ_eq_sum_range]
  _ = ∑ i ∈ range (n + 1), if n < i then 0 else (mk p).coeff i * (mk q).coeff (n - i) := by
    rcases le_total p.length (n + 1) with (h | h)
    · rw [← Nat.add_sub_cancel' h, sum_range_add]; simp
    · rw [← Nat.add_sub_cancel' h, sum_range_add]; simp [add_assoc]
  _ = ∑ i ∈ range (n + 1), (mk p).coeff i * (mk q).coeff (n - i) := by congr! 1; simp_all
  _ = ∑ x ∈ antidiagonal n, (mk p).coeff x.1 * (mk q).coeff x.2 := by
    rw [Nat.sum_antidiagonal_eq_sum_range_succ (f := fun i j => (mk p).coeff i * (mk q).coeff j)]

instance [NonUnitalNonAssocSemiring R] : NonUnitalNonAssocSemiring R[X] where
  left_distrib p q r := by ext; simp [coeff_mul, mul_add, Finset.sum_add_distrib]
  right_distrib p q r := by ext; simp [coeff_mul, add_mul, Finset.sum_add_distrib]
  zero_mul p := by ext; simp [coeff_mul]
  mul_zero p := by ext; simp [coeff_mul]

open Finset in
instance [NonUnitalSemiring R] : NonUnitalSemiring R[X] where
  mul_assoc p q r := by
    ext n; simp [coeff_mul, sum_mul, mul_sum, mul_assoc]
    change ∑ x ∈ antidiagonal n, ∑ i ∈ antidiagonal x.1, p.coeff (i.1 + 0) * _ =
           ∑ x ∈ antidiagonal n, ∑ i ∈ antidiagonal x.2, p.coeff (x.1 + 0) * _
    generalize 0 = k
    induction n generalizing k with
    | zero => simp
    | succ n ih => simp [Nat.sum_antidiagonal_succ, sum_add_distrib, add_assoc, ih]

instance [NonAssocSemiring R] : NonAssocSemiring R[X] where
  one_mul p := by cases p; simp [one_def, mk_mul, single_def]; ext; simp
  mul_one c := by
    ext; simp [coeff_mul, coeff_one]; rw [← Finset.Nat.sum_antidiagonal_swap]
    simp [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

instance [Semiring R] : Semiring R[X] where

instance [NonUnitalNonAssocCommSemiring R] : NonUnitalNonAssocCommSemiring R[X] where
  mul_comm p q := by
    ext; rw [coeff_mul, coeff_mul, ← Finset.Nat.sum_antidiagonal_swap]; simp [mul_comm]

instance [NonUnitalCommSemiring R] : NonUnitalCommSemiring R[X] where

instance [NonAssocCommSemiring R] : NonAssocCommSemiring R[X] where

instance [CommSemiring R] : CommSemiring R[X] where

instance [NonUnitalRing R] : NonUnitalRing R[X] where

instance [NonAssocRing R] : NonAssocRing R[X] where

instance [Ring R] : Ring R[X] where

instance [NonUnitalNonAssocCommRing R] : NonUnitalNonAssocCommRing R[X] where

instance [NonUnitalCommRing R] : NonUnitalCommRing R[X] where

instance [NonAssocCommRing R] : NonAssocCommRing R[X] where

instance [CommRing R] : CommRing R[X] where

instance [AddMonoidWithOne R] [CharZero R] : CharZero R[X] where
  cast_injective n m := by
    simp [natCast_def, CPoly.ext_iff]; intro h; simpa [← apply_eq_coeff] using h 0

instance [AddMonoidWithOne R] [CharP R p] : CharP R[X] p where
  cast_eq_zero_iff n := by
    simp [natCast_def, ← single_zero 0, -single_zero, CharP.cast_eq_zero_iff]

instance [NonUnitalNonAssocSemiring R] [DistribSMul S R] [IsScalarTower S R R] :
    IsScalarTower S R[X] R[X] where
  smul_assoc c p q := by ext; simp [coeff_mul, Finset.smul_sum, smul_mul_assoc]

def equivPolynomial (R) [Semiring R] [DecidableEq R] : R[X] ≃+* Polynomial R where
  toFun p := ⟨⟨equivFinsupp R p⟩⟩
  invFun P := (equivFinsupp R).symm P.toFinsupp.coeff
  left_inv p := by simp
  right_inv P := by simp
  map_mul' p q := by ext; simp [coeff_mul, Polynomial.coeff_mul]
  map_add' p q := by ext; simp

def linearEquivPolynomial (R) [Semiring R] [DecidableEq R] : R[X] ≃ₗ[R] Polynomial R where
  toFun p := ⟨⟨equivFinsupp R p⟩⟩
  map_add' p q := by ext; simp
  map_smul' c p := by ext; simp
  invFun P := (equivFinsupp R).symm P.toFinsupp.coeff
  left_inv p := by simp
  right_inv P := by simp

def out [Zero R] [DecidableEq R] : R[X] → List R := LFinsupp.out

theorem mk_out [Zero R] [DecidableEq R] (p : R[X]) : mk p.out = p := LFinsupp.mk_out p

/-- Remove trailing zeros from the polynomial's internal representation. Propositionally it has no
effect (see `trim_eq`), but may improve performance in algorithms. -/
def trim [Zero R] [DecidableEq R] (p : R[X]) : R[X] := mk p.out

@[simp]
theorem trim_eq [Zero R] [DecidableEq R] (p : R[X]) : p.trim = p := p.mk_out

instance repr [Zero R] [One R] [DecidableEq R] [Repr R] : Repr R[X] where
  reprPrec p prec :=
    let l : List (ℕ × Std.Format) := p.liftOn (fun l => l.filterMapIdx fun n (a : R) =>
      if a = 0 then none else some <| match n with
      | 0 => (max_prec, f!"C {reprArg a}")
      | 1 => if a = 1 then (max_prec, f!"X") else (73, f!"{reprPrec a 73} • X")
      | n => if a = 1 then (80, f!"X ^ {n.repr}") else (73, f!"{reprPrec a 73} • X ^ {n.repr}"))
      (by intro l _ rfl; simp [List.zipIdx_append])
    match l with
    | [] => "0"
    | [(tp, t)] => if tp ≤ prec then t.paren else t
    | ts => (if prec ≥ 65 then .paren else id)
        (Std.Format.joinSep (ts.map Prod.snd) (" +" ++ .line)).fill

#min_imports
