import Mathlib.Data.List.ToFinsupp
import Mathlib.Data.Nat.SuccPred
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.List.DropRight

theorem List.zipWithAll_of_le {f : Option α → Option β → γ} (hab : a.length ≤ b.length) :
    zipWithAll f a b = zipWith (fun x y => f (some x) (some y)) a b
      ++ (b.drop (a.length)).map fun y => f none (some y) := by
  induction a generalizing b with
  | nil => simp
  | cons x a ih => induction b with
    | nil => simp at hab
    | cons y b ih => simp_all

theorem List.zipWithAll_of_ge {f : Option α → Option β → γ} (hab : b.length ≤ a.length) :
    zipWithAll f a b = zipWith (fun x y => f (some x) (some y)) a b
      ++ (a.drop (b.length)).map fun x => f (some x) none := by
  induction a generalizing b with
  | nil => simpa using hab
  | cons x a ih => induction b with
    | nil => simp
    | cons y b ih => simp_all

@[simp]
theorem List.zipWithAll_of_eq {f : Option α → Option β → γ} (hab : a.length = b.length) :
    zipWithAll f a b = zipWith (fun x y => f (some x) (some y)) a b := by
  rw [zipWithAll_of_le (Nat.le_of_eq hab)]; simp [hab]

/-- The type of finitely supported functions from `ℕ` to `α`, implemented as `List α` quotiented by
the presence of trailing zeros. -/
def LFinsupp (α) [Zero α] := Quot (fun x y : List α => y = x.concat 0)

namespace LFinsupp

abbrev mk [Zero α] (l : List α) : LFinsupp α := Quot.mk _ l

@[cases_eliminator, elab_as_elim]
theorem casesOn [Zero α] {motive : LFinsupp α → Prop} (f : LFinsupp α)
    (mk : (l : List α) → motive (mk l)) : motive f := f.inductionOn mk

theorem eq_iff [Zero α] {x y : List α} : mk x = mk y ↔
    ∃ n, x = y ++ List.replicate n 0 ∨ y = x ++ List.replicate n 0 := by
  unfold LFinsupp; rw [Quot.eq]; constructor
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

instance [Zero α] : FunLike (LFinsupp α) Nat α where
  coe f n := f.liftOn (fun l => l.getD n 0) (by
    intro a _ rfl; simp [List.getElem?_append, List.getElem?_singleton]; split_ifs
    · rfl
    · rw [List.getElem?_eq_none]; rfl; omega
    · rw [List.getElem?_eq_none]; omega)
  coe_injective f g := by
    cases f; cases g; rename_i l l'; simp [eq_iff]; intro h; simp [funext_iff, mk] at h
    rcases Nat.le_total l.length l'.length with (h' | h')
    · use l'.length - l.length; right; apply List.ext_getElem?; intro i; specialize h i
      rw [Quot.liftOn_mk, Quot.liftOn_mk] at h
      simp [getElem?_def, h', List.getElem_append] at ⊢ h; split_ifs at ⊢ h <;> simp_all
    · use l.length - l'.length; left; apply List.ext_getElem?; intro i; specialize h i
      rw [Quot.liftOn_mk, Quot.liftOn_mk] at h
      simp [getElem?_def, h', List.getElem_append] at ⊢ h; split_ifs at ⊢ h <;> simp_all

@[ext]
theorem ext [Zero α] (f g : LFinsupp α) : (∀ n, f n = g n) → f = g := DFunLike.ext f g

@[simp]
theorem coe_mk [Zero α] {l : List α} : mk l = fun n => l.getD n 0 := rfl

instance [Zero α] : Zero (LFinsupp α) := ⟨mk []⟩

theorem zero_def [Zero α] : (0 : LFinsupp α) = mk [] := rfl

@[simp]
theorem coe_zero [Zero α] : ⇑(0 : LFinsupp α) = 0 := rfl

theorem zero_apply [Zero α] (n : ℕ) : (0 : LFinsupp α) n = 0 := rfl

@[inline_if_reduce]
def single [Zero α] (n : ℕ) (a : α) := go [a] n where
  @[inline] go (l : List α) : ℕ → LFinsupp α
  | 0 => mk l
  | n + 1 => go (0 :: l) n

theorem single_def [Zero α] {a : α} : single n a = mk (List.replicate n 0 ++ [a]) := by
  unfold single; generalize [a] = l
  induction n generalizing l <;> simp_all [single.go, List.replicate_succ']

theorem single_apply [Zero α] {a : α} : single n a m = if m = n then a else 0 := by
  rcases m.lt_trichotomy n with (h | rfl | h)
  · simp [single_def, List.getElem?_append_left, h, Nat.ne_of_lt h]
  · simp [single_def]
  · simp [single_def, List.getElem?_append_right, Nat.le_of_lt h, Nat.sub_ne_zero_of_lt h,
      Nat.ne_of_gt h]

@[simp]
theorem single_apply_same [Zero α] {a : α} : single n a n = a := by simp [single_apply]

@[simp]
theorem single_apply_of_ne [Zero α] {a : α} (h : m ≠ n) : single n a m = 0 := by
  simp [single_apply, h]

@[simp]
theorem single_apply_of_ne' [Zero α] {a : α} (h : n ≠ m) : single n a m = 0 := by simp [h.symm]

@[simp]
theorem single_zero [Zero α] (n : Nat) : single n (0 : α) = 0 := by ext; simp [single_apply]

@[simp]
theorem single_inj [Zero α] (n : Nat) (a b : α) : single n a = single n b ↔ a = b := by
  constructor
  · intro h; simp [LFinsupp.ext_iff] at h; simpa using h n
  · apply congrArg

instance [Zero α] : Inhabited (LFinsupp α) := ⟨0⟩

@[simp]
theorem default_eq_zero [Zero α] : (default : LFinsupp α) = 0 := rfl

instance [Zero α] [Nontrivial α] : Nontrivial (LFinsupp α) where
  exists_pair_ne := by have ⟨x, y, h⟩ := exists_pair_ne α; use single 0 x, single 0 y; simpa

instance [Zero α] [Subsingleton α] : Unique (LFinsupp α) where
  uniq p := by ext; apply Subsingleton.elim

instance [Zero α] [DecidableEq α] : DecidableEq (LFinsupp α) :=
  fun p q => Quot.recOnSubsingleton₂ p q decRel where
  decRel : (l l' : List α) → Decidable (mk l = mk l')
  | [], l => decidable_of_iff (∀ x ∈ l, x = 0) (by
    simp [eq_iff, List.eq_replicate_iff]; constructor
    · intro h; use l.length; right; trivial
    · rintro ⟨n, ⟨rfl, rfl⟩ | ⟨rfl, h⟩⟩; simp; exact h)
  | l, [] => decidable_of_iff (∀ x ∈ l, x = 0) (by
    simp [eq_iff, List.eq_replicate_iff]; constructor
    · intro h; use l.length; left; trivial
    · rintro ⟨n, ⟨rfl, h⟩ | ⟨rfl, rfl⟩⟩; exact h; simp)
  | a :: l, b :: l' => match decEq a b with
    | isFalse nab => isFalse (by simp [LFinsupp.ext_iff]; use 0; simpa)
    | isTrue hab => match decRel l l' with
      | isFalse h => isFalse (by simpa [eq_iff, hab] using h)
      | isTrue h => isTrue (by simpa [eq_iff, hab] using h)

instance [AddZeroClass α] : Add (LFinsupp α) where
  add := Quot.lift₂ (fun a b => mk <| .zipWithAll (fun x y => x.getD 0 + y.getD 0) a b) (by
    intro a b _ rfl; ext
    simp [List.getElem?_zipWithAll, List.getElem?_append, List.getElem?_singleton]
    (repeat' split) <;> simp_all) (by
    intro a _ b rfl; ext
    simp [List.getElem?_zipWithAll, List.getElem?_append, List.getElem?_singleton]
    (repeat' split) <;> simp_all)

theorem add_apply [AddZeroClass α] (f g : LFinsupp α) (n : ℕ) : (f + g) n = f n + g n := by
  cases f; cases g; change Option.getD _ 0 = _; simp [List.getElem?_zipWithAll]; split <;> simp_all

@[simp]
theorem coe_add [AddZeroClass α] {f g : LFinsupp α} : ⇑(f + g) = f + g := funext (add_apply f g)

@[simp]
theorem single_add [AddZeroClass α] {a b : α} : single n (a + b) = single n a + single n b := by
  ext; simp [single_apply, ite_add_ite]

instance [AddZeroClass α] : AddZeroClass (LFinsupp α) where
  zero_add f := by ext; simp
  add_zero f := by ext; simp

instance [AddZeroClass α] [IsLeftCancelAdd α] : IsLeftCancelAdd (LFinsupp α) where
  add_left_cancel {f g h} := by simp [LFinsupp.ext_iff]

instance [AddZeroClass α] [IsRightCancelAdd α] : IsRightCancelAdd (LFinsupp α) where
  add_right_cancel {f g h} := by simp [LFinsupp.ext_iff]

instance [AddZeroClass α] [IsCancelAdd α] : IsCancelAdd (LFinsupp α) where

instance [AddMonoid M] : NSMul (LFinsupp M) where
  nsmul n := Quot.lift (fun l => mk (l.map (n • ·))) (by intro a _ rfl; apply Quot.sound; simp)

theorem nsmul_apply [AddMonoid M] (n : ℕ) (f : LFinsupp M) (m : ℕ) :
    (n • f) m = n • f m := by
  cases f; change Option.getD _ _ = _; simp; unfold Option.map; split <;> simp_all

@[simp]
theorem coe_nsmul [AddMonoid M] {n : ℕ} {f : LFinsupp M} : ⇑(n • f) = n • f :=
  funext (nsmul_apply n f)

instance [AddMonoid M] : AddMonoid (LFinsupp M) where
  add_assoc f g h := by ext; simp [add_assoc]
  nsmul_zero f := by ext; simp
  nsmul_succ n f := by ext; simp [succ_nsmul]

instance [AddMonoid M] [IsAddTorsionFree M] : IsAddTorsionFree (LFinsupp M) where
  nsmul_right_injective n hn f g := by simp [LFinsupp.ext_iff, nsmul_right_inj hn]

instance [AddCommMonoid M] : AddCommMonoid (LFinsupp M) where
  add_comm f g := by ext; simp [add_comm]

instance [NegZeroClass G] : NegZeroClass (LFinsupp G) where
  neg := Quot.lift (fun l => mk (l.map (-·))) (by intro a _ rfl; apply Quot.sound; simp)
  neg_zero := rfl

theorem neg_apply [NegZeroClass G] (f : LFinsupp G) (n : ℕ) : (-f) n = -f n := by
  cases f; change Option.getD _ _ = _; simp; unfold Option.map; split <;> simp_all

@[simp]
theorem coe_neg [NegZeroClass G] (f : LFinsupp G) : ⇑(-f) = -f := funext f.neg_apply

@[simp]
theorem single_neg [NegZeroClass G] {a : G} : single n (-a) = -single n a := by
  ext; simp [single_apply, neg_ite]

instance [SubNegZeroMonoid G] : Sub (LFinsupp G) where
  sub := Quot.lift₂ (fun a b => mk <| .zipWithAll (fun x y => x.getD 0 - y.getD 0) a b) (by
    intro a b _ rfl; ext
    simp [List.getElem?_zipWithAll, List.getElem?_append, List.getElem?_singleton]
    (repeat' split) <;> simp_all) (by
    intro a _ b rfl; ext
    simp [List.getElem?_zipWithAll, List.getElem?_append, List.getElem?_singleton]
    (repeat' split) <;> simp_all)

theorem sub_apply [SubNegZeroMonoid G] (f g : LFinsupp G) (n : ℕ) : (f - g) n = f n - g n := by
  cases f; cases g; change Option.getD _ 0 = _; simp [List.getElem?_zipWithAll]; split <;> simp_all

@[simp]
theorem coe_sub [SubNegZeroMonoid G] {f g : LFinsupp G} : ⇑(f - g) = f - g := funext (sub_apply f g)

@[simp]
theorem single_sub [SubNegZeroMonoid G] {a b : G} : single n (a - b) = single n a - single n b := by
  ext; simp [single_apply, ite_sub_ite]

instance [SubtractionMonoid G] : ZSMul (LFinsupp G) where
  zsmul z := Quot.lift (fun l => mk (l.map (z • ·))) (by intro a _ rfl; apply Quot.sound; simp)

theorem zsmul_apply [SubtractionMonoid G] (z : ℤ) (f : LFinsupp G) (n : ℕ) :
    (z • f) n = z • f n := by
  cases f; change Option.getD _ _ = _; simp; unfold Option.map; split <;> simp_all

@[simp]
theorem coe_zsmul [SubtractionMonoid G] {z : ℤ} {f : LFinsupp G} : ⇑(z • f) = z • f :=
  funext (zsmul_apply z f)

instance [SubtractionMonoid G] : SubtractionMonoid (LFinsupp G) where
  sub_eq_add_neg f g := by ext; simp [sub_eq_add_neg]
  zsmul_zero' f := by ext; simp
  zsmul_succ' n f := by ext; rw [zsmul_apply, SubNegMonoid.zsmul_succ']; simp
  zsmul_neg' n f := by ext; rw [zsmul_apply, SubNegMonoid.zsmul_neg']; simp
  neg_neg f := by ext; simp
  neg_add_rev f g := by ext; simp
  neg_eq_of_add f g h := by
    simp [LFinsupp.ext_iff] at h; ext n; simpa using neg_eq_of_add_eq_zero_right (h n)

instance [SubtractionCommMonoid G] : SubtractionCommMonoid (LFinsupp G) where

instance [AddGroup G] : AddGroup (LFinsupp G) where
  neg_add_cancel g := by ext; simp

instance [AddCommGroup G] : AddCommGroup (LFinsupp G) where

instance [Zero M] [SMulZeroClass R M] : SMulZeroClass R (LFinsupp M) where
  smul c := Quot.lift (fun l => mk (l.map (c • ·))) (by intro a _ rfl; apply Quot.sound; simp)
  smul_zero c := rfl

theorem smul_apply [Zero M] [SMulZeroClass R M] (c : R) (f : LFinsupp M) (n : ℕ) :
    (c • f) n = c • f n := by
  cases f; change Option.getD _ _ = _; simp; unfold Option.map; split <;> simp_all

@[simp]
theorem coe_smul [Zero M] [SMulZeroClass R M] {c : R} {f : LFinsupp M} : ⇑(c • f) = c • f :=
  funext (smul_apply c f)

@[simp]
theorem smul_single [Zero M] [SMulZeroClass R M] {c : R} {a : M} :
    c • single n a = single n (c • a) := by ext; simp [single_apply]

instance [Zero R] [Zero M] [SMulWithZero R M] : SMulWithZero R (LFinsupp M) where
  zero_smul f := by ext; simp

instance [AddZeroClass M] [DistribSMul R M] : DistribSMul R (LFinsupp M) where
  smul_add c f g := by ext; simp [smul_add]

instance [Zero M] [SMulZeroClass R M] [SMulZeroClass S M] [SMul R S] [IsScalarTower R S M] :
    IsScalarTower R S (LFinsupp M) where
  smul_assoc r s f := by ext; simp

instance [Zero M] [SMulZeroClass R M] [SMulZeroClass S M] [SMulCommClass R S M] :
    SMulCommClass R S (LFinsupp M) where
  smul_comm r s f := by ext; simp [smul_comm]

instance [Zero M] [SMulZeroClass R M] [SMulZeroClass Rᵐᵒᵖ M] [IsCentralScalar R M] :
    IsCentralScalar R (LFinsupp M) where
  op_smul_eq_smul c f := by ext; simp

instance [Zero M] [SMulZeroClass R M] [FaithfulSMul R M] : FaithfulSMul R (LFinsupp M) where
  eq_of_smul_eq_smul h := eq_of_smul_eq_smul fun a : M => by simpa using h (single 0 a)

instance [Monoid R] [AddMonoid M] [DistribMulAction R M] : DistribMulAction R (LFinsupp M) where
  mul_smul c d f := by ext; simp [mul_smul]
  one_smul f := by ext; simp
  smul_zero := smul_zero
  smul_add := smul_add

instance [Semiring R] [AddCommMonoid M] [Module R M] : Module R (LFinsupp M) where
  add_smul c d f := by ext; simp [add_smul]
  zero_smul f := by ext; simp

instance [Semiring R] [AddCommMonoid M] [Module R M] [Module.IsTorsionFree R M] :
    Module.IsTorsionFree R (LFinsupp M) where
  isSMulRegular c h f g := by simp [LFinsupp.ext_iff, h]

def toFinsupp [Zero α] [DecidablePred fun x : α => x ≠ 0] : LFinsupp α → ℕ →₀ α :=
    Quot.lift (fun l => l.toFinsupp) (by
      intro l _ rfl; ext n; change mk l n = mk (l.concat 0) n; rw [mk, Quot.sound]; rfl)

@[simp]
theorem coe_toFinsupp [Zero α] [DecidablePred fun x : α => x ≠ 0] (f : LFinsupp α) :
    ⇑f.toFinsupp = ⇑f := by cases f; simp [toFinsupp, List.coe_toFinsupp]

theorem toFinsupp_apply [Zero α] [DecidablePred fun x : α => x ≠ 0] (f : LFinsupp α) (n : ℕ) :
    f.toFinsupp n = f n := by simp

theorem _root_.WithBot.succ_le_iff [Preorder α] [OrderBot α] [SuccOrder α] [NoMaxOrder α]
    (x : WithBot α) (y : α) : x.succ ≤ y ↔ x < y := by
  rw [← WithBot.coe_le_coe, WithBot.succ_eq_succ, Order.succ_le_iff]

-- just for completeness
theorem _root_.WithTop.le_pred_iff [Preorder α] [OrderTop α] [PredOrder α] [NoMinOrder α]
    (x : α) (y : WithTop α) : x ≤ y.pred ↔ x < y := by
  rw [← WithTop.coe_le_coe, WithTop.pred_eq_pred, Order.le_pred_iff]

def equivFinsupp (α) [Zero α] [DecidablePred fun x : α => x ≠ 0] : LFinsupp α ≃ (ℕ →₀ α) where
  toFun := toFinsupp
  invFun f := mk (List.ofFn fun n : Fin f.support.max.succ => f n)
  left_inv f := by
    ext n; simp [Option.getD_eq_iff, Decidable.or_iff_not_imp_left, imp_and, WithBot.succ_le_iff]
    convert_to _ < (n : WithBot ℕ) → _; rfl; intro h; symm; simpa using Finset.notMem_of_max_lt_coe h
  right_inv f := by
    ext n; simp [Option.getD_eq_iff, Decidable.or_iff_not_imp_left, imp_and, WithBot.succ_le_iff]
    convert_to _ < (n : WithBot ℕ) → _; rfl; intro h; symm; simpa using Finset.notMem_of_max_lt_coe h

@[simp]
theorem coe_equivFinsupp_apply [Zero α] [DecidablePred fun x : α => x ≠ 0] (f : LFinsupp α) :
    ⇑(equivFinsupp α f) = f := by simp [equivFinsupp]

@[simp]
theorem coe_equivFinsupp_symm_apply [Zero α] [DecidablePred fun x : α => x ≠ 0] (f : ℕ →₀ α) :
    ⇑((equivFinsupp α).symm f) = f := by
  rw [← (equivFinsupp α).apply_symm_apply f, Equiv.symm_apply_apply, coe_equivFinsupp_apply]

def addEquivFinsupp (α) [AddZeroClass α] [DecidablePred fun x : α => x ≠ 0] :
    LFinsupp α ≃+ (ℕ →₀ α) where
  toEquiv := equivFinsupp α
  map_add' f g := by ext; simp

@[simp]
theorem coe_addEquivFinsupp_apply [AddZeroClass α] [DecidablePred fun x : α => x ≠ 0]
    (f : LFinsupp α) : ⇑(addEquivFinsupp α f) = f := by simp [addEquivFinsupp]

@[simp]
theorem coe_addEquivFinsupp_symm_apply [AddZeroClass α] [DecidablePred fun x : α => x ≠ 0]
    (f : ℕ →₀ α) : ⇑((addEquivFinsupp α).symm f) = f := by simp [addEquivFinsupp]

def linearEquivFinsupp (R) [Semiring R] [DecidablePred fun x : R => x ≠ 0] :
    LFinsupp R ≃ₗ[R] (ℕ →₀ R) where
  toAddEquiv := addEquivFinsupp R
  map_smul' c f := by ext; simp

@[simp]
theorem coe_linearEquivFinsupp_apply [Semiring R] [DecidablePred fun x : R => x ≠ 0]
    (f : LFinsupp R) : ⇑(linearEquivFinsupp R f) = f := by simp [linearEquivFinsupp]

@[simp]
theorem coe_linearEquivFinsupp_symm_apply [Semiring R] [DecidablePred fun x : R => x ≠ 0]
    (f : ℕ →₀ R) : ⇑((linearEquivFinsupp R).symm f) = f := by simp [linearEquivFinsupp]

/-- Obtain a canonical representation by dropping trailing zeros. -/
def out [Zero α] [DecidablePred fun x : α => x = 0] : LFinsupp α → List α :=
  Quot.lift (fun l => l.rdropWhile (· = 0)) (by intro l _ rfl; simp)

theorem mk_out [Zero α] [DecidablePred fun x : α => x = 0] (f : LFinsupp α) : mk f.out = f := by
  cases f; rename_i l; simp [out, eq_iff]
  use (l.rtakeWhile (· = 0)).length; right; symm
  convert ← List.rdropWhile_append_rtakeWhile
  simp [List.eq_replicate_length]; intro b hb
  simpa using l.mem_rtakeWhile_imp hb

/-- Remove trailing zeros from the internal representation. Propositionally it has no
effect (see `trim_eq`), but may improve performance in algorithms. -/
def trim [Zero α] [DecidablePred fun x : α => x = 0] (f : LFinsupp α) : LFinsupp α := mk f.out

@[simp]
theorem trim_eq [Zero α] [DecidablePred fun x : α => x = 0] (f : LFinsupp α) : f.trim = f :=
  f.mk_out

instance [Zero α] [DecidablePred fun x : α => x = 0] [Repr α] : Repr (LFinsupp α) where
  reprPrec f prec := Repr.addAppParen f!"LFinsupp.mk {repr f.out}" prec
