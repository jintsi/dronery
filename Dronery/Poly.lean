import Mathlib.Data.List.GetD
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.List.ToFinsupp
import Mathlib.Data.List.DropRight
import Dronery.List

/-! # Computable polynomials -/

def CPoly (R) [Zero R] := Quot (fun x y : List R => y = x.concat 0)

namespace CPoly

scoped notation:9000 R "[X]" => CPoly R

def mk [Zero R] (l : List R) : R[X] := Quot.mk _ l

@[cases_eliminator, elab_as_elim]
theorem casesOn [Zero R] {motive : R[X] → Prop} (p : R[X]) (mk : (l : List R) → motive (mk l)) : motive p :=
  p.inductionOn mk

theorem eq_iff [Zero R] {x y : List R} : mk x = mk y ↔
    ∃ n, x = y ++ List.replicate n 0 ∨ y = x ++ List.replicate n 0 := by
  unfold mk CPoly; rw [Quot.eq]; constructor
  · intro h; induction h with
    | rel x y h => use 1; right; simpa using h
    | refl x => simp
    | symm x y h ih => exact ih.imp fun _ => Or.symm
    | trans x y z h h' ih ih' =>
      rcases ih with ⟨n, rfl | rfl⟩
      · rcases ih' with ⟨m, rfl | rfl⟩ <;> simp
        by_cases h : n ≤ m
        · use m - n; omega
        · use n - m; omega
      · rcases ih' with ⟨m, ih | rfl⟩; swap; simp
        by_cases h : n ≤ m
        · use m - n; left; rw [← Nat.sub_add_cancel h] at ih
          simpa [← List.replicate_append_replicate, ← List.append_assoc] using ih
        · use n - m; right; rw [← Nat.sub_add_cancel (Nat.le_of_not_ge h)] at ih
          symm; simpa [← List.replicate_append_replicate, ← List.append_assoc] using ih
  · rintro ⟨n, rfl | rfl⟩
    · induction n with
      | zero => simp; exact .refl y
      | succ n ih =>
        rw [List.replicate_succ', ← List.append_assoc]
        exact .trans _ _ _ (symm <| .rel _ _ List.concat_eq_append.symm) ih
    · induction n with
      | zero => simp; exact .refl x
      | succ n ih =>
        rw [List.replicate_succ', ← List.append_assoc]
        exact ih.trans _ _ _ (.rel _ _ List.concat_eq_append.symm)

/-- `p.coeff n` is the coefficient of `X ^ n` in `p`. -/
def coeff [Zero R] (p : R[X]) (n : ℕ) : R :=
  p.liftOn (fun l => l.getD n 0) (by
    intro a _ rfl; simp [List.getElem?_append, List.getElem?_singleton]; split_ifs
    · rfl
    · rw [List.getElem?_eq_none]; rfl; omega
    · rw [List.getElem?_eq_none]; omega)

@[simp]
theorem coeff_mk [Zero R] {l : List R} : (mk l).coeff n = l.getD n 0 := rfl

@[ext]
theorem ext [Zero R] {p q : R[X]} : (∀ n, p.coeff n = q.coeff n) → p = q := by
  cases p; cases q; rename_i p q; simp [eq_iff]; intro h
  rcases Nat.le_total p.length q.length with (h' | h')
  · use q.length - p.length; right; apply List.ext_getElem?; intro i; specialize h i
    simp [getElem?_def, h', List.getElem_append] at ⊢ h; split_ifs at ⊢ h <;> simp_all
  · use p.length - q.length; left; apply List.ext_getElem?; intro i; specialize h i
    simp [getElem?_def, h', List.getElem_append] at ⊢ h; split_ifs at ⊢ h <;> simp_all

instance [Zero R] : Zero R[X] := ⟨mk []⟩

theorem zero_def [Zero R] : (0 : R[X]) = mk [] := rfl

theorem zero_def' [Zero R] : (0 : R[X]) = mk [0] := Quot.sound rfl

@[simp]
theorem coeff_zero [Zero R] : (0 : R[X]).coeff n = 0 := by simp [zero_def]

instance [Zero R] [One R] : One R[X] := ⟨mk [1]⟩

theorem one_def [Zero R] [One R] : (1 : R[X]) = mk [1] := rfl

theorem coeff_one [Zero R] [One R] : (1 : R[X]).coeff n = if n = 0 then 1 else 0 := by
  simp [one_def, List.getElem?_singleton]; split <;> rfl

def X [Zero R] [One R] : R[X] := mk [0, 1]

theorem X_def [Zero R] [One R] : (X : R[X]) = mk [0, 1] := rfl

instance [Zero R] : Inhabited R[X] := ⟨0⟩

instance [Zero R] [Nontrivial R] : Nontrivial R[X] where
  exists_pair_ne := by
    have ⟨x, y, h⟩ := exists_pair_ne R
    use mk [x], mk [y]; simp [CPoly.ext_iff]; use 0; simpa

instance [Zero R] [Subsingleton R] : Unique R[X] where
  uniq p := by ext; apply Subsingleton.elim

instance [Zero R] [DecidableEq R] : DecidableEq R[X] :=
  fun p q => Quot.recOnSubsingleton₂ p q decRel where
  decRel : (l l' : List R) → Decidable (mk l = mk l')
  | [], l => decidable_of_iff (∀ x ∈ l, x = 0) (by
    simp [eq_iff, ← List.eq_replicate_length]; constructor
    · intro h; use l.length; right; exact h
    · rintro ⟨n, ⟨rfl, rfl⟩ | rfl⟩ <;> simp)
  | l, [] => decidable_of_iff (∀ x ∈ l, x = 0) (by
    simp [eq_iff, ← List.eq_replicate_length]; constructor
    · intro h; use l.length; left; exact h
    · rintro ⟨n, rfl | ⟨rfl, rfl⟩⟩ <;> simp)
  | a :: l, b :: l' => match decEq a b with
    | isFalse nab => isFalse (by simp [CPoly.ext_iff]; use 0; simpa)
    | isTrue hab => match decRel l l' with
      | isFalse h => isFalse (by simpa [eq_iff, hab] using h)
      | isTrue h => isTrue (by simpa [eq_iff, hab] using h)

/-! ## Addition -/

theorem _root_.List.zipWithAll_of_le {f : Option α → Option β → γ} (hab : a.length ≤ b.length) :
    List.zipWithAll f a b = List.zipWith (fun x y => f (some x) (some y)) a b
      ++ (b.drop (a.length)).map fun y => f none (some y) := by
  induction a generalizing b with
  | nil => simp
  | cons x a ih => induction b with
    | nil => simp at hab
    | cons y b ih => simp_all

theorem _root_.List.zipWithAll_of_ge {f : Option α → Option β → γ} (hab : b.length ≤ a.length) :
    List.zipWithAll f a b = List.zipWith (fun x y => f (some x) (some y)) a b
      ++ (a.drop (b.length)).map fun x => f (some x) none := by
  induction a generalizing b with
  | nil => simpa using hab
  | cons x a ih => induction b with
    | nil => simp
    | cons y b ih => simp_all

@[simp]
theorem _root_.List.zipWithAll_of_eq {f : Option α → Option β → γ} (hab : a.length = b.length) :
    List.zipWithAll f a b = List.zipWith (fun x y => f (some x) (some y)) a b := by
  rw [List.zipWithAll_of_le (Nat.le_of_eq hab)]; simp [hab]

instance [AddZeroClass R] : Add R[X] where
  add := Quot.lift₂ (fun a b => mk <| .zipWithAll (fun x y => x.getD 0 + y.getD 0) a b) (by
    intro a b _ rfl; ext
    simp [List.getElem?_zipWithAll, List.getElem?_append, List.getElem?_singleton]
    (repeat' split) <;> simp_all) (by
    intro a _ b rfl; ext
    simp [List.getElem?_zipWithAll, List.getElem?_append, List.getElem?_singleton]
    (repeat' split) <;> simp_all)

theorem add_def [AddZeroClass R] {a b : List R} :
    mk a + mk b = mk (.zipWithAll (·.getD 0 + ·.getD 0) a b) := rfl

@[simp]
theorem coeff_add [AddZeroClass R] {p q : R[X]} : (p + q).coeff n = p.coeff n + q.coeff n := by
  cases p; cases q; simp [add_def, List.getElem?_zipWithAll]; split <;> simp_all

theorem coeff_list_sum [AddZeroClass R] {l : List R[X]} :
    l.sum.coeff n = (l.map fun p => p.coeff n).sum := by induction l <;> simp_all

instance [AddZeroClass R] : AddZeroClass R[X] where
  zero_add p := by ext; simp
  add_zero p := by ext; simp

instance [AddMonoid R] : AddMonoid R[X] where
  add_assoc p q r := by ext; simp [add_assoc]
  nsmul n := Quot.lift (fun l => mk (l.map (n • ·))) (by intro l _ rfl; apply Quot.sound; simp)
  nsmul_zero p := by
    cases p; rename_i l; change mk (l.map (0 • ·)) = mk []; simp [List.map_const', eq_iff]
  nsmul_succ n p := by
    cases p; rename_i l; change mk (l.map ((n + 1) • ·)) = mk (l.map (n • ·)) + mk l
    simp [succ_nsmul, add_def, List.zipWith_map_left];

instance [AddCommMonoid R] : AddCommMonoid R[X] where
  add_comm p q := by ext; simp [add_comm]

instance [AddMonoidWithOne R] : AddMonoidWithOne R[X] where
  natCast n := mk [n]
  natCast_zero := by simp [zero_def']
  natCast_succ := by simp [one_def, add_def]

instance [AddCommMonoidWithOne R] : AddCommMonoidWithOne R[X] where

theorem natCast_def [AddMonoidWithOne R] {n : ℕ} : n = mk [(n : R)] := rfl

instance [NegZeroClass R] : Neg R[X] := ⟨Quot.lift (fun l => mk (l.map (-·))) (by
  intro a _ rfl; apply Quot.sound; simp)⟩

theorem neg_def [NegZeroClass R] {l : List R} : -mk l = mk (l.map (-·)) := rfl

@[simp]
theorem coeff_neg [NegZeroClass R] {p : R[X]} : (-p).coeff n = -p.coeff n := by
  cases p; simp [neg_def, ← Option.getD_map (α := R) (-·)]

instance [NegZeroClass R] : NegZeroClass R[X] where
  neg_zero := by ext; simp

instance [SubNegZeroMonoid R] : Sub R[X] where
  sub := Quot.lift₂ (fun a b => mk <| .zipWithAll (fun x y => x.getD 0 - y.getD 0) a b) (by
    intro a b _ rfl; ext
    simp [List.getElem?_zipWithAll, List.getElem?_append, List.getElem?_singleton]
    (repeat' split) <;> simp_all) (by
    intro a _ b rfl; ext
    simp [List.getElem?_zipWithAll, List.getElem?_append, List.getElem?_singleton]
    (repeat' split) <;> simp_all)

theorem sub_def [SubNegZeroMonoid R] {a b : List R} :
    mk a - mk b = mk (.zipWithAll (·.getD 0 - ·.getD 0) a b) := rfl

@[simp]
theorem coeff_sub [SubNegZeroMonoid R] {p q : R[X]} : (p - q).coeff n = p.coeff n - q.coeff n := by
  cases p; cases q; simp [sub_def, List.getElem?_zipWithAll]; split <;> simp_all

instance [SubtractionMonoid R] : SubtractionMonoid R[X] where
  sub_eq_add_neg p q := by ext; simp [sub_eq_add_neg]
  zsmul z := Quot.lift (fun l => mk (l.map (z • ·))) (by
    intro l _ rfl; apply Quot.sound; simp)
  zsmul_zero' p := by
    cases p; rename_i l; change mk (l.map (0 • ·)) = mk []; simp [List.map_const', eq_iff]
  zsmul_succ' n p := by
    cases p; rename_i l; change mk (l.map ((n.succ : ℤ) • ·)) = mk (l.map ((n : ℤ) • ·)) + mk l
    simp_rw [SubNegMonoid.zsmul_succ']; simp [add_def, List.zipWith_map_left]
  zsmul_neg' n p := by
    cases p; rename_i l; change mk (l.map (Int.negSucc n • ·)) = mk ((l.map _).map _)
    simp [-Int.natCast_add, -Nat.cast_add]; rfl
  neg_neg p := by ext; simp
  neg_add_rev p q := by ext; simp
  neg_eq_of_add p q h := by
    simp [CPoly.ext_iff] at h; ext n; simpa using neg_eq_of_add_eq_zero_right (h n)

instance [SubtractionCommMonoid R] : SubtractionCommMonoid R[X] where

instance [AddGroup R] : AddGroup R[X] where
  neg_add_cancel p := by ext; simp

instance [AddCommGroup R] : AddCommGroup R[X] where

instance [AddGroupWithOne R] : AddGroupWithOne R[X] where
  intCast z := mk [z]
  intCast_ofNat n := by simp [natCast_def]
  intCast_negSucc n := by rw [natCast_def]; simp [neg_def]

instance [AddCommGroupWithOne R] : AddCommGroupWithOne R[X] where

theorem intCast_def [AddGroupWithOne R] {z : ℤ} : (z : R[X]) = mk [(z : R)] := rfl

/-! ## Scalar multiplication -/

instance [Zero R] [SMulZeroClass S R] : SMul S R[X] where
  smul c := Quot.lift (fun l => mk (l.map (c • ·))) (by intro a _ rfl; apply Quot.sound; simp)

theorem smul_def [Zero R] [SMulZeroClass S R] {c : S} {l : List R} :
    c • mk l = mk (l.map (c • ·)) := rfl

@[simp]
theorem coeff_smul [Zero R] [SMulZeroClass S R] {c : S} {p : R[X]} :
    (c • p).coeff n = c • p.coeff n := by cases p; simp [smul_def, ← Option.getD_map (β := R)]

instance [Zero R] [SMulZeroClass S R] : SMulZeroClass S R[X] where
  smul_zero c := by ext; simp

instance [Zero R] [SMulZeroClass S R] [FaithfulSMul S R] : FaithfulSMul S R[X] where
  eq_of_smul_eq_smul h := eq_of_smul_eq_smul fun a : R => by
    simpa [smul_def, eq_iff, ← or_and_right, or_iff_left_of_imp Eq.symm] using h (mk [a])

instance [AddZeroClass R] [DistribSMul S R] : DistribSMul S R[X] where
  smul_add c p q := by ext; simp [smul_add]

instance [Monoid S] [AddMonoid R] [DistribMulAction S R] : DistribMulAction S R[X] where
  mul_smul c d p := by ext; simp [mul_smul]
  one_smul p := by ext; simp
  smul_zero := smul_zero
  smul_add := smul_add

instance [Zero S] [Zero R] [SMulWithZero S R] : SMulWithZero S R[X] where
  zero_smul p := by ext; simp

instance [MonoidWithZero S] [Zero R] [MulActionWithZero S R] : MulActionWithZero S R[X] where
  mul_smul c d p := by ext; simp [mul_smul]
  one_smul p := by ext; simp
  smul_zero := smul_zero
  zero_smul := zero_smul S

instance [Semiring S] [AddCommMonoid R] [Module S R] : Module S R[X] where
  add_smul c d p := by ext; simp [add_smul]
  zero_smul := zero_smul S

instance [Zero R] [SMulZeroClass S₁ R] [SMulZeroClass S₂ R] [SMulCommClass S₁ S₂ R] :
    SMulCommClass S₁ S₂ R[X] where
  smul_comm c d p := by ext; simp [smul_comm]

instance [Zero R] [SMul S₁ S₂] [SMulZeroClass S₁ R] [SMulZeroClass S₂ R] [IsScalarTower S₁ S₂ R] :
    IsScalarTower S₁ S₂ R[X] where
  smul_assoc c d p := by ext; simp

instance [Zero R] [SMulZeroClass S R] [SMulZeroClass Sᵐᵒᵖ R] [IsCentralScalar S R] :
    IsCentralScalar S R[X] where
  op_smul_eq_smul c p := by ext; simp

instance [Semiring S] [AddCommMonoid R] [Module S R] [Module.IsTorsionFree S R] :
    Module.IsTorsionFree S R[X] where
  isSMulRegular c h p q := by simp [CPoly.ext_iff]; intro h' n; exact h.isSMulRegular (h' n)

/-! ## Multiplication -/

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
  simp [zero_def, shiftLeft_mk, eq_iff]

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
  one_mul p := by cases p; simp [one_def, mk_mul, smul_def]
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
  cast_injective n m := by simp [natCast_def, CPoly.ext_iff]; intro h; simpa using h 0

instance [AddMonoidWithOne R] [CharP R p] : CharP R[X] p where
  cast_eq_zero_iff n := by
    simp [natCast_def, zero_def, eq_iff, List.eq_replicate_iff, CharP.cast_eq_zero_iff R]

instance [NonUnitalNonAssocSemiring R] [DistribSMul S R] [IsScalarTower S R R] :
    IsScalarTower S R[X] R[X] where
  smul_assoc c p q := by ext; simp [coeff_mul, Finset.smul_sum, smul_mul_assoc]

def toPolynomial [Semiring R] [DecidableEq R] : R[X] → Polynomial R :=
  Quot.lift (fun l => ⟨⟨l.toFinsupp⟩⟩) (by
    intro l _ rfl; simp [List.toFinsupp_concat_eq_toFinsupp_add_single])

@[simp]
theorem coeff_toPolynomial [Semiring R] [DecidableEq R] {p : R[X]} {n : ℕ} :
    p.toPolynomial.coeff n = p.coeff n := by
  cases p; rename_i l; simp [toPolynomial]; simp [mk]

theorem _root_.WithBot.succ_le_iff [Preorder α] [OrderBot α] [SuccOrder α] [NoMaxOrder α]
    (x : WithBot α) (y : α) : x.succ ≤ y ↔ x < y := by
  rw [← WithBot.coe_le_coe, WithBot.succ_eq_succ, Order.succ_le_iff]

-- just for completeness
theorem _root_.WithTop.le_pred_iff [Preorder α] [OrderTop α] [PredOrder α] [NoMinOrder α]
    (x : α) (y : WithTop α) : x ≤ y.pred ↔ x < y := by
  rw [← WithTop.coe_le_coe, WithTop.pred_eq_pred, Order.le_pred_iff]

@[simps]
def equivPolynomial [Semiring R] [DecidableEq R] : R[X] ≃+* Polynomial R where
  toFun := toPolynomial
  invFun P := mk ((List.range P.degree.succ).map P.coeff)
  left_inv p := by
    ext n; simp [Option.getD_eq_iff]; by_cases! h : n < p.toPolynomial.degree.succ <;> simp [h]
    rw [WithBot.succ_le_iff] at h; convert_to _ < (n : WithBot ℕ) at h; rfl
    rw [Polynomial.degree_lt_iff_coeff_zero] at h; symm; simpa using h n
  right_inv P := by
    ext n; simp [Option.getD_eq_iff]; by_cases! h : n < P.degree.succ <;> simp [h]
    rw [WithBot.succ_le_iff] at h; convert_to _ < (n : WithBot ℕ) at h; rfl
    rw [P.degree_lt_iff_coeff_zero] at h; exact (h n le_rfl).symm
  map_mul' p q := by ext; simp [coeff_mul, Polynomial.coeff_mul]
  map_add' p q := by ext; simp

def out [Zero R] [DecidableEq R] : R[X] → List R :=
  Quot.lift (fun l => l.rdropWhile (· = 0)) (by intro l _ rfl; simp)

theorem mk_out [Zero R] [DecidableEq R] (p : R[X]) : mk p.out = p := by
  cases p; rename_i l; simp [out, eq_iff]; simp [mk]
  use (l.rtakeWhile (· = 0)).length; right; symm
  convert ← List.rdropWhile_append_rtakeWhile
  simp [List.eq_replicate_length]; intro b hb
  simpa using l.mem_rtakeWhile_imp hb

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
