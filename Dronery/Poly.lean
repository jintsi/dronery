import Dronery.LFinsupp
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Coeff
import Dronery.List

/-! # Computable univariate polynomials -/

/-- `CPoly R` is the type of univariate polynomials over `R`, denoted `R[X]` within the `CPoly`
namespace.

Just like `Polynomial R`, it features `X` and `C` as constructors, but unlike `Polynomial R`, it is
computable, represented internally as a `List` of coefficients (via `LFinsupp`). -/
structure CPoly (R) [Semiring R] where
  coeff : LFinsupp R
deriving Inhabited, DecidableEq

namespace CPoly

open LFinsupp

scoped notation:9000 R "[X]" => CPoly R

@[ext]
theorem ext [Semiring R] {p q : R[X]} (h : ∀ n, p.coeff n = q.coeff n) : p = q :=
  (mk.injEq _ _).mpr (DFunLike.ext p.coeff q.coeff h)

@[simp]
theorem eta [Semiring R] {p : R[X]} : ⟨p.coeff⟩ = p := rfl

theorem coeff_injective [Semiring R] : (@coeff R _).Injective := fun ⟨_⟩ ⟨_⟩ => congrArg mk

@[simp]
theorem coeff_inj [Semiring R] {p q : R[X]} : p.coeff = q.coeff ↔ p = q := coeff_injective.eq_iff

/-! # Copy instances from `LFinsupp` -/

instance [Semiring R] : Zero R[X] := ⟨⟨0⟩⟩

instance [Semiring R] : One R[X] := ⟨⟨single 0 1⟩⟩

instance [Semiring R] : Add R[X] := ⟨fun ⟨f⟩ ⟨g⟩ => ⟨f + g⟩⟩

instance [Ring R] : Neg R[X] := ⟨fun ⟨f⟩ => ⟨-f⟩⟩

instance [Ring R] : Sub R[X] := ⟨fun ⟨f⟩ ⟨g⟩ => ⟨f - g⟩⟩

instance [Semiring R] : NSMul R[X] := ⟨fun n ⟨f⟩ => ⟨n • f⟩⟩

instance [Ring R] : ZSMul R[X] := ⟨fun z ⟨f⟩ => ⟨z • f⟩⟩

instance [Semiring R] [SMulZeroClass S R] : SMulZeroClass S R[X] where
  smul := fun c ⟨f⟩ => ⟨c • f⟩
  smul_zero _ := rfl

@[simp]
theorem mk_zero [Semiring R] : (mk 0 : R[X]) = 0 := rfl

theorem one_def [Semiring R] : (1 : R[X]) = ⟨single 0 1⟩ := rfl

@[simp]
theorem mk_add [Semiring R] {f g : LFinsupp R} : mk (f + g) = ⟨f⟩ + ⟨g⟩ := rfl

@[simp]
theorem mk_neg [Ring R] {f : LFinsupp R} : mk (-f) = -⟨f⟩ := rfl

@[simp]
theorem mk_sub [Ring R] {f g : LFinsupp R} : mk (f - g) = ⟨f⟩ - ⟨g⟩ := rfl

@[simp]
theorem mk_nsmul [Semiring R] {n : ℕ} {f : LFinsupp R} : mk (n • f) = n • ⟨f⟩ := rfl

@[simp]
theorem mk_zsmul [Ring R] {z : ℤ} {f : LFinsupp R} : mk (z • f) = z • ⟨f⟩ := rfl

@[simp]
theorem mk_smul [Semiring R] [SMulZeroClass S R] {c : S} {f : LFinsupp R} :
    mk (c • f) = c • ⟨f⟩ := rfl

@[simp]
theorem fun_coeff_zero [Semiring R] : (0 : R[X]).coeff = 0 := rfl

@[simp]
theorem fun_coeff_one [Semiring R] : (1 : R[X]).coeff = single 0 1 := rfl

@[simp]
theorem fun_coeff_add [Semiring R] (p q : R[X]) : (p + q).coeff = p.coeff + q.coeff := rfl

@[simp]
theorem fun_coeff_neg [Ring R] (p : R[X]) : (-p).coeff = -p.coeff := rfl

@[simp]
theorem fun_coeff_sub [Ring R] (p q : R[X]) : (p - q).coeff = p.coeff - q.coeff := rfl

@[simp]
theorem fun_coeff_nsmul [Semiring R] (p : R[X]) (n : ℕ) : (n • p).coeff = n • p.coeff := rfl

@[simp]
theorem fun_coeff_zsmul [Ring R] (p : R[X]) (z : ℤ) : (z • p).coeff = z • p.coeff := rfl

@[simp]
theorem fun_coeff_smul [Semiring R] [SMulZeroClass S R] (c : S) (p : R[X]) :
    (c • p).coeff = c • p.coeff := rfl

theorem coeff_zero [Semiring R] : (0 : R[X]).coeff n = 0 := rfl

theorem coeff_one [Semiring R] : (1 : R[X]).coeff n = if n = 0 then 1 else 0 := by simp [single_apply]

theorem coeff_one_zero [Semiring R] : (1 : R[X]).coeff 0 = 1 := rfl

theorem coeff_add [Semiring R] (p q : R[X]) : (p + q).coeff n = p.coeff n + q.coeff n :=
  add_apply p.coeff q.coeff n

theorem coeff_neg [Ring R] (p : R[X]) : (-p).coeff n = -p.coeff n := neg_apply p.coeff n

theorem coeff_sub [Ring R] (p q : R[X]) : (p - q).coeff n = p.coeff n - q.coeff n :=
  sub_apply p.coeff q.coeff n

theorem coeff_nsmul [Semiring R] (p : R[X]) (n : ℕ) : (n • p).coeff m = n • p.coeff m :=
  nsmul_apply n p.coeff m

theorem coeff_zsmul [Ring R] (p : R[X]) (z : ℤ) : (z • p).coeff n = z • p.coeff n :=
  zsmul_apply z p.coeff n

theorem coeff_smul [Semiring R] [SMulZeroClass S R] (c : S) (p : R[X]) :
    (c • p).coeff n = c • p.coeff n := smul_apply c p.coeff n

theorem coeff_list_sum [Semiring R] (l : List R[X]) :
    l.sum.coeff n = (l.map fun p => p.coeff n).sum := by induction l <;> simp_all

@[simp]
theorem default_eq_zero [Semiring R] : (default : R[X]) = 0 := rfl

@[simp]
theorem mk_eq_zero [Semiring R] {f : LFinsupp R} : mk f = 0 ↔ f = 0 := by simp [← mk_zero]

@[simp]
theorem fun_coeff_eq_zero [Semiring R] {p : R[X]} : p.coeff = 0 ↔ p = 0 := by
  simp [← fun_coeff_zero]

instance [Semiring R] : AddCommMonoidWithOne R[X] where
  toAddCommMonoid := coeff_injective.addCommMonoid _ fun_coeff_zero fun_coeff_add fun_coeff_nsmul
  natCast n := ⟨single 0 n⟩
  natCast_zero := by simp
  natCast_succ n := by simp [one_def]

theorem natCast_def [Semiring R] (n : ℕ) : (n : R[X]) = ⟨single 0 n⟩ := rfl

@[simp]
theorem fun_coeff_natCast [Semiring R] (n : ℕ) : coeff n = single 0 (n : R) := rfl

theorem coeff_natCast_zero [Semiring R] (n : ℕ) : coeff n 0 = (n : R) := rfl

instance [Ring R] : AddCommGroupWithOne R[X] where
  toAddCommGroup := fast_instance% coeff_injective.addCommGroup _ fun_coeff_zero fun_coeff_add
    fun_coeff_neg fun_coeff_sub fun_coeff_nsmul fun_coeff_zsmul
  natCast_zero := Nat.cast_zero
  natCast_succ := Nat.cast_succ
  intCast z := ⟨single 0 z⟩
  intCast_ofNat n := by simp [natCast_def]
  intCast_negSucc n := by ext; simp

theorem intCast_def [Ring R] (z : ℤ) : (z : R[X]) = ⟨single 0 z⟩ := rfl

@[simp]
theorem fun_coeff_intCast [Ring R] (z : ℤ) : coeff z = single 0 (z : R) := rfl

instance [Semiring R] [DistribSMul S R] : DistribSMul S R[X] where
  smul_add c p q := by ext; simp

instance [Semiring R] [Monoid S] [DistribMulAction S R] : DistribMulAction S R[X] := fast_instance%
    coeff_injective.distribMulAction ⟨⟨coeff, fun_coeff_zero⟩, fun_coeff_add⟩ fun_coeff_smul

instance [Semiring R] [SMulZeroClass S R] [FaithfulSMul S R] : FaithfulSMul S R[X] where
  eq_of_smul_eq_smul h := eq_of_smul_eq_smul fun a => by simpa [← mk_smul] using h ⟨a⟩

instance [Semiring R] [SMulZeroClass S₁ R] [SMulZeroClass S₂ R] [SMulCommClass S₁ S₂ R] :
    SMulCommClass S₁ S₂ R[X] where
  smul_comm c d p := by ext; simp [smul_comm]

instance [Semiring R] [SMul S₁ S₂] [SMulZeroClass S₁ R] [SMulZeroClass S₂ R]
    [IsScalarTower S₁ S₂ R] : IsScalarTower S₁ S₂ R[X] where
  smul_assoc c d p := by ext; simp

instance [Semiring R] [SMulZeroClass S R] [SMulZeroClass Sᵐᵒᵖ R] [IsCentralScalar S R] :
    IsCentralScalar S R[X] where
  op_smul_eq_smul c p := by ext; simp

instance [Semiring R] [Semiring S] [Module S R] : Module S R[X] := fast_instance%
    coeff_injective.module S ⟨⟨coeff, fun_coeff_zero⟩, fun_coeff_add⟩ fun_coeff_smul

instance [Semiring R] [Semiring S] [Module S R] [Module.IsTorsionFree S R] :
    Module.IsTorsionFree S R[X] where
  isSMulRegular c h p q := by simp [CPoly.ext_iff, h]

instance [Semiring R] [Subsingleton R] : Unique R[X] where
  uniq _ := ext fun _ ↦ Subsingleton.elim _ _

instance [Semiring R] [Nontrivial R] : Nontrivial R[X] where
  exists_pair_ne := by have ⟨f, g, h⟩ := exists_pair_ne (LFinsupp R); use ⟨f⟩, ⟨g⟩; simpa

/-! ## Multiplication -/

/-- `p <<< n` is defined as `p * X ^ n`, analogous to how `n <<< m = n * 2 ^ m`. -/
def shiftLeft [Semiring R] (p : R[X]) : ℕ → R[X]
| 0 => p
| n + 1 => p.coeff.liftOn (fun l => mk (.mk (0 :: l))) (by
    intro l _ rfl; simp; apply Quot.sound; simp) |>.shiftLeft n

instance [Semiring R] : HShiftLeft R[X] ℕ R[X] := ⟨shiftLeft⟩

theorem shiftLeft_mk [Semiring R] {l : List R} :
    mk (.mk l) <<< n = mk (.mk (List.replicate n 0 ++ l)) := by
  change shiftLeft _ n = _
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [shiftLeft]; simp [LFinsupp.mk]; rw [Quot.liftOn_mk]; simp_all [List.replicate_succ']

theorem coeff_shiftLeft [Semiring R] {p : R[X]} :
    coeff (p <<< i) n = if n < i then 0 else p.coeff (n - i) := by
  rcases p with ⟨f⟩; cases f; simp [shiftLeft_mk, List.getElem?_append]; split <;> simp

@[simp]
theorem zero_shiftLeft [Semiring R] {n : ℕ} : (0 : R[X]) <<< n = 0 := by
  ext; simp [coeff_shiftLeft]

@[simp]
theorem shiftLeft_zero [Semiring R] {p : R[X]} : p <<< 0 = p := rfl

instance [Semiring R] : Mul R[X] where
  mul p q := p.coeff.liftOn (fun l => l.foldlIdx (fun i acc a => acc + (a • q) <<< i) 0) (by
    intro a _ rfl; simp [List.foldlIdx_eq_foldl_zipIdx, List.zipIdx_append])

theorem mk_mul [Semiring R] {l : List R} {q : R[X]} :
  mk (.mk l) * q = (l.mapIdx fun i a => (a • q) <<< i).sum := by
  unfold HMul.hMul instHMul Mul.mul instMul LFinsupp.mk; simp; rw [Quot.liftOn_mk]
  simp [List.sum_eq_foldl, List.mapIdx_eq_zipIdx_map, List.foldl_map, List.foldlIdx_eq_foldl_zipIdx]

open Finset in
theorem coeff_mul [Semiring R] {p q : R[X]} : (p * q).coeff n =
    ∑ x ∈ antidiagonal n, p.coeff x.1 * q.coeff x.2 := by
  rcases p with ⟨f⟩; rcases q with ⟨g⟩; cases f; cases g; rename_i f g
  calc (mk (.mk f) * mk (.mk g)).coeff n
  _ = ((f.mapIdx (fun i a ↦ (a • mk (.mk g)) <<< i)).map fun p => p.coeff n).sum := by
    simp [mk_mul, coeff_list_sum]
  _ = ∑ i : Fin f.length, ((f[i] • mk (.mk g)) <<< (i : ℕ)).coeff n := by
    rw [← Fin.sum_univ_fun_getElem]; simp; congr! <;> simp
  _ = ∑ i : Fin f.length, if n < i then 0 else LFinsupp.mk f i * LFinsupp.mk g (n - i) := by
    simp [coeff_shiftLeft]
  _ = ∑ i ∈ range f.length, if n < i then 0 else LFinsupp.mk f i * LFinsupp.mk g (n - i) := by
    rw [← Fin.sum_univ_eq_sum_range]
  _ = ∑ i ∈ range (n + 1), if n < i then 0 else LFinsupp.mk f i * LFinsupp.mk g (n - i) := by
    rcases le_total f.length (n + 1) with (h | h)
    · rw [← Nat.add_sub_cancel' h, sum_range_add]; simp
    · rw [← Nat.add_sub_cancel' h, sum_range_add]; simp [add_assoc]
  _ = ∑ i ∈ range (n + 1), LFinsupp.mk f i * LFinsupp.mk g (n - i) := by congr! 1; simp_all
  _ = ∑ x ∈ antidiagonal n, LFinsupp.mk f x.1 * LFinsupp.mk g x.2 := by
    rw [Nat.sum_antidiagonal_eq_sum_range_succ (f := fun i j => LFinsupp.mk f i * LFinsupp.mk g j)]

open Finset in
instance [Semiring R] : Semiring R[X] where
  mul_assoc p q r := by
    ext n; simp [coeff_mul, sum_mul, mul_sum, mul_assoc]
    change ∑ x ∈ antidiagonal n, ∑ i ∈ antidiagonal x.1, p.coeff (i.1 + 0) * _ =
           ∑ x ∈ antidiagonal n, ∑ i ∈ antidiagonal x.2, p.coeff (x.1 + 0) * _
    generalize 0 = k
    induction n generalizing k with
    | zero => simp
    | succ n ih => simp [Nat.sum_antidiagonal_succ, sum_add_distrib, add_assoc, ih]
  one_mul p := by cases p; simp [one_def, single_def, mk_mul]
  mul_one c := by
    ext; simp [coeff_mul, single_apply]; rw [← Finset.Nat.sum_antidiagonal_swap]
    simp [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  zero_mul p := by ext; simp [coeff_mul]
  mul_zero p := by ext; simp [coeff_mul]
  left_distrib p q r := by ext; simp [coeff_mul, mul_add, Finset.sum_add_distrib]
  right_distrib p q r := by ext; simp [coeff_mul, add_mul, Finset.sum_add_distrib]

instance [CommSemiring R] : CommSemiring R[X] where
  mul_comm p q := by
    ext; rw [coeff_mul, coeff_mul, ← Finset.Nat.sum_antidiagonal_swap]; simp [mul_comm]

instance [Ring R] : Ring R[X] where

instance [CommRing R] : CommRing R[X] where

instance [Semiring R] [CharZero R] : CharZero R[X] where
  cast_injective n m := by simp [natCast_def, CPoly.ext_iff]; intro h; simpa using h 0

instance [Semiring R] [CharP R p] : CharP R[X] p where
  cast_eq_zero_iff n := by simp [natCast_def, CharP.cast_eq_zero_iff]

instance [Semiring R] [DistribSMul S R] [IsScalarTower S R R] : IsScalarTower S R[X] R[X] where
  smul_assoc c p q := by ext; simp [coeff_mul, Finset.smul_sum, smul_mul_assoc]

/-- The nth coefficient, as a linear map. -/
@[simps]
def lcoeff (R) [Semiring R] (n : ℕ) : R[X] →ₗ[R] R where
  toFun p := p.coeff n
  map_add' := coeff_add
  map_smul' := coeff_smul

def monomial [Semiring R] (n : ℕ) : R →ₗ[R] R[X] where
  toFun a := ⟨single n a⟩
  map_add' := by simp
  map_smul' := by simp [← mk_smul]

@[simp]
theorem fun_coeff_monomial [Semiring R] {a : R} : (monomial n a).coeff = single n a := rfl

theorem coeff_monomial [Semiring R] {a : R} : (monomial n a).coeff m = if m = n then a else 0 :=
  single_apply

theorem coeff_monomial_same [Semiring R] {a : R} : (monomial n a).coeff n = a := single_apply_same

theorem coeff_monomial_of_ne [Semiring R] {a : R} (h : m ≠ n) : (monomial n a).coeff m = 0 :=
  single_apply_of_ne h

@[simp]
theorem mk_single [Semiring R] {a : R} : ⟨single n a⟩ = monomial n a := rfl

theorem monomial_zero_right [Semiring R] : monomial n (0 : R) = 0 := by simp

@[simp]
theorem monomial_zero_one [Semiring R] : monomial 0 (1 : R) = 1 := rfl

@[simp]
theorem smul_monomial [Semiring R] [SMulZeroClass S R] {a : S} {b : R} :
    a • monomial n b = monomial n (a • b) := by ext; simp

theorem shiftLeft_monomial [Semiring R] {a : R} : monomial n a <<< i = monomial (n + i) a := by
  ext k; simp [coeff_shiftLeft, single_apply]; grind

theorem monomial_mul_monomial [Semiring R] {a b : R} :
    monomial m a * monomial n b = monomial (m + n) (a * b) := by
  simp [← mk_single]; rw [single_def, mk_mul]; simp
  rw [(List.mapIdx_eq_replicate_iff (b := 0)).mpr (by simp)]; simp [shiftLeft_monomial, add_comm]

@[simp]
theorem monomial_pow [Semiring R] {a : R} : monomial n a ^ k = monomial (n * k) (a ^ k) := by
  induction k <;> simp_all [pow_succ, monomial_mul_monomial, mul_add_one]

/-- `C a` is the constant polynomial `a`. -/
def C [Semiring R] : R →+* R[X] where
  toFun := monomial 0
  map_one' := monomial_zero_one
  map_mul' := by simp [monomial_mul_monomial]
  map_zero' := map_zero _
  map_add' := map_add _

@[simp]
theorem monomial_zero_left [Semiring R] {a : R} : monomial 0 a = C a := rfl

@[simp]
theorem fun_coeff_C [Semiring R] {a : R} : (C a).coeff = single 0 a := rfl

theorem coeff_C_zero [Semiring R] {a : R} : (C a).coeff 0 = a := rfl

theorem coeff_C_of_ne_zero [Semiring R] {a : R} (h : n ≠ 0) : (C a).coeff n = 0 := by simp [h]

theorem coeff_C_succ [Semiring R] {a : R} : (C a).coeff (n + 1) = 0 := rfl

@[simp]
theorem C_mul_eq_smul [Semiring R] {a : R} {p : R[X]} : C a * p = a • p := by
  rw [← monomial_zero_left, ← mk_single, single_def, mk_mul]; simp

/-- `X` is the polynomial indeterminate. -/
def X [Semiring R] : R[X] := monomial 1 1

@[simp]
theorem monomial_one_one [Semiring R] : monomial 1 (1 : R) = X := rfl

@[simp]
theorem fun_coeff_X [Semiring R] : X.coeff = single 1 (1 : R) := rfl

@[simp]
theorem X_ne_zero [Semiring R] [Nontrivial R] : (X : R[X]) ≠ 0 := by
  apply_fun fun p => p.coeff 1; simp

example [Semiring R] : (X : R[X]) = ⟨.mk [0, 1]⟩ := rfl

theorem monomial_one_right [Semiring R]: monomial n (1 : R) = X ^ n := by
  simp [← monomial_one_one]

theorem X_mul [Semiring R] {p : R[X]} : X * p = p * X := by
  ext; simp [coeff_mul, single_apply]; rw [← Finset.Nat.sum_antidiagonal_swap]; simp

theorem X_pow_mul [Semiring R] {p : R[X]} : X ^ n * p = p * X ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_assoc, ih, ← mul_assoc, X_mul, mul_assoc]

@[simp]
theorem leftShift_eq_mul_X_pow [Semiring R] {p : R[X]} : p <<< n = p * X ^ n := by
  rw [← X_pow_mul, ← monomial_one_right, ← mk_single, single_def, mk_mul]; simp
  rw [(List.mapIdx_eq_replicate_iff (b := 0)).mpr (by simp)]; simp

def equivPolynomial (R) [Semiring R] [DecidablePred fun x : R => x ≠ 0] : R[X] ≃+* Polynomial R where
  toFun p := ⟨⟨equivFinsupp R p.coeff⟩⟩
  invFun P := ⟨(equivFinsupp R).symm P.toFinsupp.coeff⟩
  left_inv p := by simp
  right_inv P := by simp
  map_mul' p q := by ext; simp [coeff_mul, Polynomial.coeff_mul]
  map_add' p q := by ext; simp

@[simp]
theorem coeff_equivPolynomial_apply [Semiring R] [DecidablePred fun x : R => x ≠ 0] {p : R[X]} :
    (equivPolynomial R p).coeff n = p.coeff n := by simp [equivPolynomial]

@[simp]
theorem coeff_equivPolynomial_symm_apply [Semiring R]
    [DecidablePred fun x : R => x ≠ 0] {p : Polynomial R} :
    ((equivPolynomial R).symm p).coeff n = p.coeff n := by simp [equivPolynomial]; rfl

@[simp]
theorem equivPolynomial_monomial [Semiring R] [DecidablePred fun x : R => x ≠ 0] {a : R} :
    equivPolynomial R (monomial n a) = Polynomial.monomial n a := by
  ext; simp [Polynomial.coeff_monomial, single_apply]; congr 1; exact propext Eq.comm

@[simp]
theorem equivPolynomial_C [Semiring R] [DecidablePred fun x : R => x ≠ 0] {a : R} :
    equivPolynomial R (C a) = Polynomial.C a := equivPolynomial_monomial

@[simp]
theorem equivPolynomial_X [Semiring R] [DecidablePred fun x : R => x ≠ 0] :
    equivPolynomial R (X : R[X]) = Polynomial.X := equivPolynomial_monomial

@[simp]
theorem equivPolynomial_symm_monomial [Semiring R] [DecidablePred fun x : R => x ≠ 0] {a : R} :
    (equivPolynomial R).symm (Polynomial.monomial n a) = monomial n a := by
  ext; simp [Polynomial.coeff_monomial, single_apply]; congr 1; exact propext Eq.comm

@[simp]
theorem equivPolynomial_symm_C [Semiring R] [DecidablePred fun x : R => x ≠ 0] {a : R} :
    (equivPolynomial R).symm (Polynomial.C a) = C a := equivPolynomial_symm_monomial

@[simp]
theorem equivPolynomial_symm_X [Semiring R] [DecidablePred fun x : R => x ≠ 0] :
    (equivPolynomial R).symm Polynomial.X = (X : R[X]) := equivPolynomial_symm_monomial

def linearEquivPolynomial (R) [Semiring R] [DecidablePred fun x : R => x ≠ 0] : R[X] ≃ₗ[R] Polynomial R where
  toFun p := ⟨⟨equivFinsupp R p.coeff⟩⟩
  map_add' p q := by ext; simp
  map_smul' c p := by ext; simp
  invFun P := ⟨(equivFinsupp R).symm P.toFinsupp.coeff⟩
  left_inv p := by simp
  right_inv P := by simp

@[simp]
theorem coe_linearEquivPolynomial_apply [Semiring R] [DecidablePred fun x : R => x ≠ 0] :
    ⇑(linearEquivPolynomial R) = equivPolynomial R := rfl

@[simp]
theorem coe_linearEquivPolynomial_symm_apply [Semiring R] [DecidablePred fun x : R => x ≠ 0] :
    ⇑(linearEquivPolynomial R).symm = (equivPolynomial R).symm := rfl

instance [Semiring R] [NoZeroDivisors R] : NoZeroDivisors R[X] := by
  classical exact (equivPolynomial R).noZeroDivisors

instance [Semiring R] [IsCancelAdd R] [IsLeftCancelMulZero R] : IsLeftCancelMulZero R[X] := by
  classical exact (equivPolynomial R).isLeftCancelMulZero_iff.mpr inferInstance

instance [Semiring R] [IsCancelAdd R] [IsRightCancelMulZero R] : IsRightCancelMulZero R[X] := by
  classical exact (equivPolynomial R).isRightCancelMulZero_iff.mpr inferInstance

instance [Semiring R] [IsCancelAdd R] [IsCancelMulZero R] : IsCancelMulZero R[X] where

instance [Semiring R] [IsCancelAdd R] [IsDomain R] : IsDomain R[X] where

def out [Semiring R] [DecidablePred fun x : R => x = 0] (p : R[X]) : List R := p.coeff.out

theorem mk_out [Semiring R] [DecidablePred fun x : R => x = 0] (p : R[X]) : mk (.mk p.out) = p := by
  simp [out, LFinsupp.mk_out]

/-- Remove trailing zeros from the polynomial's internal representation. Propositionally it has no
effect (see `trim_eq`), but may improve performance in algorithms. -/
def trim [Semiring R] [DecidablePred fun x : R => x = 0] (p : R[X]) : R[X] := mk (.mk p.out)

@[simp]
theorem trim_eq [Semiring R] [DecidablePred fun x : R => x = 0] (p : R[X]) : p.trim = p := p.mk_out

instance repr [Semiring R] [DecidablePred fun x : R => x = 0] [DecidablePred fun x : R => x = 1]
    [Repr R] : Repr R[X] where
  reprPrec p prec :=
    let l : List (ℕ × Std.Format) := p.coeff.liftOn (fun l => l.filterMapIdx fun n (a : R) =>
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
