import Mathlib.Algebra.Group.Basic
import Mathlib.Data.List.Basic

namespace List

@[elab_as_elim]
theorem revInduction {motive : List α → Prop} (l : List α) (nil : motive [])
    (concat : ∀ l a, motive l → motive (l ++ [a])) : motive l := by
  rw [← l.reverse_reverse]; generalize l.reverse = l; induction l with
  | nil => exact nil
  | cons a l ih => simpa using concat l.reverse a ih

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

/-- Unsafe implementation of `attachFin` making use of the fact that `Nat` and `Fin n` have the
same memory layout, and thus so do `List Nat` and `List (Fin n)`. -/
@[inline]
unsafe def attachFinImpl (l : List ℕ) {n : ℕ} (_ : ∀ a ∈ l, a < n) : List (Fin n) :=
  unsafeCast l

/-- Turns a list of numbers, all smaller than `n`, into a list of `Fin n`s.
`O(1)` (a no-op, in fact). -/
@[implemented_by attachFinImpl]
def attachFin (l : List ℕ) {n : ℕ} (h : ∀ a ∈ l, a < n) : List (Fin n) := l.pmap Fin.mk h

/-! ## Operations with acces to indices
(why are there so many of these) -/

/-- Monadic variant of `foldlFinIdx`. -/
@[inline]
def foldlFinIdxM [Monad m] (l : List α) (f : (i : ℕ) → β → α → i < l.length → m β) (init : β) :=
  go l init 0 rfl where
  @[specialize] go : (as : List α) → (acc : β) → (i : ℕ) → as.length + i = l.length → m β
  | [], acc, _, _ => pure acc
  | a :: as, acc, i, h => f i acc a (by grind) >>= fun b => go as b i.succ (by grind)

@[simp]
theorem foldlFinIdxM_nil [Monad m] {f : (i : ℕ) → β → α → i < 0 → m β} {init : β} :
    [].foldlFinIdxM f init = pure init := rfl

@[simp]
theorem foldlFinIdxM_cons [Monad m] {a : α} {l : List α}
    {f : (i : ℕ) → β → α → i < l.length + 1 → m β} {init : β} :
    (a :: l).foldlFinIdxM f init = f 0 init a (by simp) >>= fun b =>
      l.foldlFinIdxM (fun i acc a h => f i.succ acc a (by simpa)) b := by
  let rec go (l' : List α) (n : ℕ) (h : l'.length + n = l.length) (b : β) :
    foldlFinIdxM.go (a :: l) f l' b n.succ (by simpa [← Nat.add_assoc]) =
      foldlFinIdxM.go l (fun i acc a h => f i.succ acc a (by simpa)) l' b n h := by
    induction l' generalizing n b with simp [foldlFinIdxM.go]
    | cons a' l' ih => apply bind_congr; apply ih
  unfold foldlFinIdxM; rw [foldlFinIdxM.go]; apply bind_congr; apply go

theorem foldlFinIdxM_append [Monad m] [LawfulMonad m] {xs ys : List α}
    {f : (i : ℕ) → β → α → i < (xs ++ ys).length → m β} {init : β} : (xs ++ ys).foldlFinIdxM f init
    = xs.foldlFinIdxM (fun i acc a h => f i acc a (by simp; lia)) init >>= fun b =>
      ys.foldlFinIdxM (fun i acc a h => f (xs.length + i) acc a (by simpa)) b := by
  induction xs generalizing init with
  | nil => simp; rfl
  | cons a xs ih => simp; apply bind_congr; intro b; rw [ih]; congr! 7; lia

@[simp]
theorem foldlFinIdxM_concat [Monad m] [LawfulMonad m] {l : List α} {a : α}
    {f : (i : ℕ) → β → α → i < (l ++ [a]).length → m β} {init : β} : (l ++ [a]).foldlFinIdxM f init
    = l.foldlFinIdxM (fun i acc a h => f i acc a (by simp; lia)) init >>= fun b =>
      f l.length b a (by simp) := by simp [foldlFinIdxM_append]

/-- An better version of Mathlib's `foldlIdxM` (really, use this one). -/
@[inline]
def foldlIdxM' [Monad m] (f : ℕ → β → α → m β) (init : β) (l : List α) : m β :=
  l.foldlFinIdxM (fun i acc a _ => f i acc a) init

@[simp]
theorem foldlIdxM'_nil [Monad m] {f : ℕ → β → α → m β} : [].foldlIdxM' f i = pure i := rfl

@[simp]
theorem foldlIdxM'_cons [Monad m] {f : ℕ → β → α → m β} :
    (a :: l).foldlIdxM' f i = f 0 i a >>= l.foldlIdxM' (fun i => f i.succ) := foldlFinIdxM_cons

/-- Can't make it `@[csimp]` because it requires `LawfulMonad`. -/
theorem foldlIdxM_eq_foldlIdxM' [Monad m] [LawfulMonad m] {f : ℕ → β → α → m β} {init : β}
    {l : List α} : l.foldlIdxM f init = l.foldlIdxM' f init := by
  change foldlIdx _ _ _ = foldlIdxM' (fun i => f (i + 0)) _ _; generalize 0 = s
  induction l generalizing init s with
  | nil => simp
  | cons a l ih =>
    simp [Nat.add_assoc, ← ih]; clear ih; generalize f s init a = x
    induction l generalizing s x with
    | nil => simp
    | cons a' l ih => simp; rw [ih, bind_assoc]; simp [← ih]; lia

theorem foldlIdxM'_eq_foldlM_zipIdx [Monad m] [LawfulMonad m] {f : ℕ → β → α → m β} {l : List α} :
    l.foldlIdxM' f i = l.zipIdx.foldlM (fun b ai => f ai.snd b ai.fst) i := by
  induction l generalizing i f with simp_all [zipIdx_eq_map_add (i := 1), foldlM_map, Nat.add_comm]

/-- Fold a list from left to right as with `foldl`, but the combining function also receives each
element's index alongside a proof that the index is valid. -/
@[inline]
def foldlFinIdx (l : List α) (f : (i : ℕ) → β → α → i < l.length → β) (init : β) : β :=
  Id.run (l.foldlFinIdxM (fun i acc a h => pure (f i acc a h)) init)

@[simp]
theorem foldlFinIdx_nil {f : (i : ℕ) → β → α → i < 0 → β} {i : β} : [].foldlFinIdx f i = i := rfl

@[simp]
theorem foldlFinIdx_cons {a : α} {l : List α} {f : (i : ℕ) → β → α → i < l.length + 1 → β}
    {init : β} : (a :: l).foldlFinIdx f init =
      l.foldlFinIdx (fun i acc a h => f i.succ acc a (by simpa)) (f 0 init a (by simp)) :=
  foldlFinIdxM_cons

@[simp]
theorem foldlFinIdx_concat {l : List α} {a : α} {f : (i : ℕ) → β → α → i < (l ++ [a]).length → β}
    {init : β} : (l ++ [a]).foldlFinIdx f init
    = f l.length (l.foldlFinIdx (fun i acc a h => f i acc a (by simp; lia)) init) a (by simp) :=
  foldlFinIdxM_concat

theorem foldlIdx_eq_foldlIdxM' {l : List α} {f : ℕ → β → α → β} {init : β} :
    l.foldlIdx f init = Id.run (l.foldlIdxM' (fun i acc a => pure (f i acc a)) init) := by
  change _ = Id.run (foldlIdxM' (fun i acc a => pure (f (i + 0) acc a)) init l); generalize 0 = s
  induction l generalizing init s with simp_all <;> lia

theorem foldlIdx_map {f : α₁ → α₂} {l : List α₁} {g : ℕ → β → α₂ → β} {init : β} :
    (l.map f).foldlIdx g init = l.foldlIdx (fun i acc a => g i acc (f a)) init := by
  induction l generalizing g init with simp_all [foldlIdx_start (s := 1)]

/-- Monadic variant of `foldrFinIdx`. -/
@[inline]
def foldrFinIdxM [Monad m] (l : List α) (f : (i : ℕ) → α → β → i < l.length → m β) (init : β) :=
  go l.reverse init l.length length_reverse l.length.le_refl where
  @[specialize] go : (as : List α) → (acc : β) → (i : ℕ) → as.length = i → i ≤ l.length → m β
  | [], acc, 0, _, _ => pure acc
  | a :: as, acc, i + 1, h', h => f i a acc h >>= fun b => go as b i (by simpa using h') (by lia)

@[simp]
theorem foldrFinIdxM_nil [Monad m] {f : (i : ℕ) → α → β → i < 0 → m β} {init : β} :
    [].foldrFinIdxM f init = pure init := rfl

@[simp]
theorem foldrFinIdxM_concat [Monad m] {l : List α} {a : α}
    {f : (i : ℕ) → α → β → i < (l ++ [a]).length → m β} {init : β} :
    (l ++ [a]).foldrFinIdxM f init = f l.length a init (by simp) >>= fun b =>
      l.foldrFinIdxM (fun i a acc h => f i a acc (by simp; lia)) b := by
  let rec go (l' : List α) (h : l'.length ≤ l.length) (b : β) :
    foldrFinIdxM.go (l ++ [a]) f l'.reverse b l'.length length_reverse (by simp; lia) =
      foldrFinIdxM.go l (fun i a acc h => f i a acc (by simp; lia))
        l'.reverse b l'.length length_reverse h := by
    induction l' using revInduction generalizing b with simp [foldrFinIdxM.go]
    | concat l a ih => apply bind_congr; apply ih
  simp [foldrFinIdxM, foldrFinIdxM.go]; apply bind_congr; apply go

theorem foldrFinIdxM_append [Monad m] [LawfulMonad m] {xs ys : List α}
    {f : (i : ℕ) → α → β → i < (xs ++ ys).length → m β} {init : β} : (xs ++ ys).foldrFinIdxM f init
    = ys.foldrFinIdxM (fun i a acc h => f (xs.length + i) a acc (by simp; lia)) init >>= fun b =>
      xs.foldrFinIdxM (fun i a acc h => f i a acc (by simp; lia)) b := by
  induction ys using revInduction generalizing init with
  | nil => simp; eta_expand; rw! [append_nil]; rfl
  | concat l a ih => eta_expand; rw! [← append_assoc]; simp; apply bind_congr; apply ih

@[simp]
theorem foldrFinIdxM_cons [Monad m] [LawfulMonad m] {a : α} {l : List α}
    {f : (i : ℕ) → α → β → i < l.length + 1 → m β} {init : β} : (a :: l).foldrFinIdxM f init =
    l.foldrFinIdxM (fun i a acc h => f i.succ a acc (by simpa)) init >>= fun b =>
    f 0 a b (by simp) := by
    eta_expand; rw! (castMode := .all) [← singleton_append, foldrFinIdxM_append]; simp [Nat.add_comm]
    apply bind_congr; intro b; rw! (castMode := .all) [← nil_append [a], foldrFinIdxM_concat]; simp

/-- A better version of Mathlib's `foldrIdxM` (really, use this one). -/
@[inline]
def foldrIdxM' [Monad m] (f : ℕ → α → β → m β) (init : β) (l : List α) : m β :=
  l.foldrFinIdxM (fun i a acc _ => f i a acc) init

@[simp]
theorem foldrIdxM'_nil [Monad m] {f : ℕ → α → β → m β} : [].foldrIdxM' f i = pure i := rfl

@[simp]
theorem foldrIdxM'_cons [Monad m] [LawfulMonad m] {f : ℕ → α → β → m β} {init : β} :
    (a :: l).foldrIdxM' f init = l.foldrIdxM' (fun i => f i.succ) init >>= fun b => f 0 a b :=
  foldrFinIdxM_cons

/-- Can't make it `@[csimp]` because it requires `LawfulMonad`. -/
theorem foldrIdxM_eq_foldrIdxM' [Monad m] [LawfulMonad m] {f : ℕ → α → β → m β} {init : β}
    {l : List α} : foldrIdxM f init l = foldrIdxM' f init l := by
  change foldrIdx _ _ _ = foldrIdxM' (fun i => f (i + 0)) _ _; generalize 0 = s
  induction l generalizing s with
  | nil => simp
  | cons a l ih => simp [Nat.add_assoc, ← ih]; simp [Nat.add_comm]

theorem foldrIdxM'_eq_foldrM_zipIdx [Monad m] [LawfulMonad m] {f : ℕ → α → β → m β} {l : List α} :
    l.foldrIdxM' f i = l.zipIdx.foldrM (fun ai b => f ai.snd ai.fst b) i := by
  induction l generalizing i f with simp_all [zipIdx_eq_map_add (i := 1), foldrM_map, Nat.add_comm]

theorem foldrIdx_eq_foldrIdxM' {f : ℕ → α → β → β} :
    foldrIdx f i l = Id.run (foldrIdxM' (fun i acc a => pure (f i acc a)) i l) := by
  change _ = Id.run (foldrIdxM' (fun i acc a => pure (f (i + 0) acc a)) i l); generalize 0 = s
  induction l generalizing i s with simp_all <;> lia

/-- Fold a list from right to left as with `foldr`, but the combining function also receives each
element's index alongside a proof that the index is valid. -/
@[inline]
def foldrFinIdx (l : List α) (f : (i : ℕ) → α → β → i < l.length → β) (init : β) : β :=
  Id.run (l.foldrFinIdxM (fun i acc a h => pure (f i acc a h)) init)

@[simp]
theorem foldrFinIdx_nil {f : (i : ℕ) → α → β → i < 0 → β} {i : β} : [].foldrFinIdx f i = i := rfl

@[simp]
theorem foldrFinIdx_cons {a : α} {l : List α} {f : (i : ℕ) → α → β → i < l.length + 1 → β}
    {init : β} : (a :: l).foldrFinIdx f init
    = f 0 a (l.foldrFinIdx (fun i a acc h => f i.succ a acc (by lia)) init) (by simp) :=
  foldrFinIdxM_cons

@[simp]
theorem foldrFinIdx_concat {l : List α} {a : α} {f : (i : ℕ) → α → β → i < (l ++ [a]).length → β}
    {init : β} : (l ++ [a]).foldrFinIdx f init =
      l.foldrFinIdx (fun i a acc h => f i a acc (by simp; lia)) (f l.length a init (by simp)) :=
  foldrFinIdxM_concat

/-- Applies a monadic function that returns an `Option` to each element of a list along with the
index at which that element is found, collecting the non-`none` values. -/
@[inline]
def filterMapIdxM [Monad m] (f : ℕ → α → m (Option β)) (l : List α) : m (List β) :=
  reverse <$> l.foldlIdxM' (fun i bs a => (fun o => o.toList ++ bs) <$> f i a) []

@[simp]
theorem filterMapIdxM_eq_filterMapM_zipIdx [Monad m] [LawfulMonad m] {f : ℕ → α → m (Option β)}
    {l : List α} : l.filterMapIdxM f = l.zipIdx.filterMapM fun ai => f ai.snd ai.fst := by
  change _ <$> foldlIdxM' (fun i bs a => _ <$> f (i + 0) a) _ _ = filterMapM.loop _ _ _
  generalize [] = acc, 0 = s; induction l generalizing acc s with
  | nil => simp [filterMapM.loop]
  | cons a l ih => simp [Nat.add_assoc, ih, filterMapM.loop]; apply bind_congr; rintro (_ | _)
      <;> simp [Nat.add_comm]

@[simp]
theorem _root_.Option.reverse_toList (o : Option α) : o.toList.reverse = o.toList :=
  o.casesOn rfl fun _ => rfl

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
