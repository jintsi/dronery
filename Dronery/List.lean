import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Basic
import Mathlib.Algebra.Group.Basic

namespace List

/-- Lists the numbers from `n-1` to `0`, in decreasing order. -/
def revRange : (n : Nat) → List Nat
| 0   => []
| n+1 => n :: revRange n

@[simp]
theorem revRange_zero : revRange 0 = [] := rfl

@[simp]
theorem revRange_succ : revRange n.succ = n :: revRange n := rfl

theorem revRange_def : revRange n = (range n).reverse := by
  induction n with simp [range_succ, *]

/-- Tail-recursive version of `List.revRange`. -/
def revRangeTR (n : Nat) : List Nat :=
  go n 0 []
where @[inline] go : Nat → Nat → List Nat → List Nat
| 0,   _, acc => acc
| n+1, i, acc => go n (i+1) (i :: acc)

@[csimp] theorem revRange_eq_revRangeTR : revRange = revRangeTR := by
  suffices ∀ n i, revRangeTR.go n i (revRange i) = revRange (i + n) by
    ext1 n; rw [revRangeTR, ← n.zero_add, ← this, n.zero_add, revRange]
  intro n i; induction n generalizing i with
  | zero => rfl
  | succ n ih => rw [revRangeTR.go, n.add_comm, ← i.add_assoc, ← ih, revRange]

/-- Lists all elements of `Fin n`, in decreasing order. -/
def revFinRange (n : Nat) : List (Fin n) := ofFn Fin.rev

theorem revFinRange_def : revFinRange n = (finRange n).reverse :=
  ext_get (by simp [revFinRange]) fun i h h' => by simp [revFinRange, Fin.rev]; omega

/-- Returns the list `[stop+(len-1)*step, ..., stop+step, stop]`, with length `len` and decreasing
by `step` at each element. -/
def revRange' (stop len : Nat) (step := 1) : List Nat := go len stop [] where
  @[inline] go : Nat → Nat → List Nat → List Nat
  | 0,   _, acc => acc
  | l+1, s, acc => go l (s + step) (s :: acc)

theorem revRange'_def {stop len step : Nat} :
    revRange' stop len step = (range' stop len step).reverse := by
  suffices ∀ l i, revRange'.go step l (stop + step * i) (range' stop i step).reverse
    = (range' stop (i + l) step).reverse by rw [← len.zero_add, ← this]; simp; rfl
  intro l i; induction l generalizing i with
  | zero => rfl
  | succ l ih => rw [revRange'.go, l.add_comm, ← i.add_assoc, ← ih, Nat.mul_add_one, Nat.add_assoc,
    range'_concat]; simp

/-- An better version of Mathlib's `foldlIdxM` (really, use this one). The indexes can optionally
begin at some `start` (by default 0). -/
@[inline]
def foldlIdxM' [Monad m] (f : ℕ → β → α → m β) (init : β) (l : List α) (start := 0) : m β :=
  Prod.snd <$> l.foldlM (fun (n, acc) a => Prod.mk n.succ <$> f n acc a) (start, init)

@[simp]
theorem foldlIdxM'_nil [Monad m] [LawfulApplicative m] {f : ℕ → β → α → m β} :
    [].foldlIdxM' f i s = pure i := by unfold foldlIdxM'; simp

@[simp]
theorem foldlIdxM'_cons [Monad m] [LawfulMonad m] {f : ℕ → β → α → m β} :
    (a :: l).foldlIdxM' f i s = f s i a >>= (l.foldlIdxM' f · (s + 1)) := by
  unfold foldlIdxM'; simp

/-- Can't make it `@[csimp]` because it requires `LawfulMonad`. -/
theorem foldlIdxM_eq_foldlIdxM' [Monad m] [LawfulMonad m] {f : ℕ → β → α → m β} {init : β}
    {l : List α} : l.foldlIdxM f init = l.foldlIdxM' f init := by
  unfold foldlIdxM; generalize 0 = start
  induction l generalizing start init with
  | nil => simp
  | cons a l ih =>
    simp [← ih]; clear ih; generalize f start init a = x
    induction l generalizing start x with
    | nil => simp
    | cons a' l ih => simp; rw [ih, bind_assoc]; simp [← ih]

theorem foldlIdxM'_eq_foldlM_zipIdx [Monad m] [LawfulMonad m] {f : ℕ → β → α → m β} {l : List α} :
    l.foldlIdxM' f i s = (l.zipIdx s).foldlM (fun b ai => f ai.snd b ai.fst) i := by
  induction l generalizing s i with simp_all

/-- An better version of Mathlib's `foldrIdxM` (really, use this one). The indexes can optionally
begin at some `start` (by default 0). -/
@[inline]
def foldrIdxM' [Monad m] (f : ℕ → α → β → m β) (init : β) (l : List α) (start := 0) : m β :=
  Prod.snd <$> l.foldrM (fun a (n, acc) => Prod.mk n.pred <$> f n.pred a acc) (start + l.length, init)

@[simp]
theorem foldrIdxM'_nil [Monad m] [LawfulApplicative m] {f : ℕ → α → β → m β} :
    [].foldrIdxM' f i s = pure i := by unfold foldrIdxM'; simp

@[simp]
theorem foldrIdxM'_cons [Monad m] [LawfulMonad m] {f : ℕ → α → β → m β} :
    (a :: l).foldrIdxM' f i s = l.foldrIdxM' f i (s + 1) >>= f s a := by
  unfold foldrIdxM'
  suffices (a :: l).foldrM _ _ = l.foldrM _ _ >>= fun x : ℕ × β => Prod.mk s <$> f s a x.snd by
    convert congrArg (Prod.snd <$> ·) this; simp; rfl
  simp; induction l generalizing s a with
  | nil => simp
  | cons a' l ih =>
    rw [foldrM_cons, length_cons, ← s.add_assoc, s.add_right_comm, ih]; symm
    rw [foldrM_cons, ih]; simp

/-- Can't make it `@[csimp]` because it requires `LawfulMonad`. -/
theorem foldrIdxM_eq_foldrIdxM' [Monad m] [LawfulMonad m] {f : ℕ → α → β → m β} {init : β}
    {l : List α} : foldrIdxM f init l = foldrIdxM' f init l := by
  unfold foldrIdxM; generalize 0 = start; induction l generalizing start with simp_all

theorem foldrIdxM'_eq_foldrM_zipIdx [Monad m] [LawfulMonad m] {f : ℕ → α → β → m β} {l : List α} :
    l.foldrIdxM' f i s = (l.zipIdx s).foldrM (fun ai b => f ai.snd ai.fst b) i := by
  induction l generalizing s with simp_all

/-- Applies a monadic function that returns an `Option` to each element of a list along with the
index at which that element is found, collecting the non-`none` values. -/
@[inline]
def filterMapIdxM [Monad m] (f : ℕ → α → m (Option β)) (l : List α) : m (List β) :=
  reverse <$> l.foldlIdxM' (fun i bs a => (fun o => o.toList ++ bs) <$> f i a) []

@[simp]
theorem filterMapIdxM_eq_filterMapM_zipIdx [Monad m] [LawfulMonad m] {f : ℕ → α → m (Option β)}
    {l : List α} : l.filterMapIdxM f = l.zipIdx.filterMapM fun ai => f ai.snd ai.fst := by
  simp [filterMapIdxM, filterMapM]; generalize [] = acc, 0 = s
  induction l generalizing acc s with
  | nil => simp [filterMapM.loop]
  | cons a l ih => simp [ih, filterMapM.loop]; apply bind_congr; rintro (_ | _) <;> simp

@[simp]
theorem _root_.Option.reverse_toList (o : Option α) : o.toList.reverse = o.toList := by
  cases o <;> simp

/-- Applies a function that returns an `Option` to each element of a list along with the index at
which that element is found, collecting the non-`none` values. -/
@[inline]
def filterMapIdx (f : ℕ → α → Option β) (l : List α) : List β :=
  reverse <| l.foldlIdx (fun i bs a => (f i a).toList ++ bs) []

@[simp]
theorem filterMapIdx_eq_filterMap_zipIdx {f : ℕ → α → Option β} {l : List α} :
    l.filterMapIdx f = l.zipIdx.filterMap fun ai => f ai.snd ai.fst := by
  simp [filterMapIdx, foldlIdx_eq_foldl_zipIdx, filterMap_eq_flatMap_toList, ← flatMap_id,
    reverse_flatMap, flatMap_map]

/-- Computes the sum of `f` applied to elements of the list. Note that it does a left fold,
as opposed to regular `List.sum` which does a right fold. -/
@[specialize]
def sumOn [Add β] [Zero β] (f : α → β) := List.foldl (fun acc a => acc + f a) 0

theorem sumOn_def [Add β] [Zero β] {f : α → β} {l : List α} :
    l.sumOn f = (l.map f).foldl (· + ·) 0 := foldl_map.symm

@[simp]
theorem sumOn_eq_sum_map [AddMonoid β] {f : α → β} {l : List α} : l.sumOn f = (l.map f).sum := by
  rw [sumOn_def]; symm; exact sum_eq_foldl

theorem sumOn_id [AddMonoid α] {l : List α} : l.sumOn id = l.sum := by simp

/-- Bitwise OR (`|||`) of all elements of `l` (assumes `0` is the identity). -/
abbrev lany [OrOp α] [Zero α] (l : List α) := l.foldl (· ||| ·) 0

/-- Bitwise AND (`&&&`) of all elements of `l` (assumes `~~~0` is the identity). -/
abbrev lall [AndOp α] [Zero α] [Complement α] (l : List α) := l.foldl (· &&& ·) (~~~0)

/-- Bitwise XOR (`^^^`) of all elements of `l` (assumes `0` is the identity). -/
abbrev xor [XorOp α] [Zero α] (l : List α) := l.foldl (· ^^^ ·) 0
