import Dronery.List

namespace Array

/-- Construct an array of numbers from `n-1` to `0` in decreasing order. -/
def revRange (n : Nat) : Array Nat := ofFn (n := n) fun i => i.rev

theorem revRange_def : revRange n = (range n).reverse := by
  ext <;> simp [revRange]; omega

@[simp]
theorem toList_revRange : (revRange n).toList = List.revRange n := by
  simp [revRange_def, List.revRange_def]

/-- Construct an array of all elements of `Fin n` in decreasing order. -/
def revFinRange (n : Nat) : Array (Fin n) := ofFn Fin.rev

theorem revFinRange_def : revFinRange n = (Array.finRange n).reverse := by
  ext <;> simp [revFinRange]; omega

@[simp]
theorem toList_revFinRange : (revFinRange n).toList = List.revFinRange n := by
  simp [revFinRange]; rfl

/-- Construct an array of numbers of size `len`, decreasing by `step` at each element and ending
at `stop`, that is, `#[stop+(len-1)*step, ..., stop+step, stop]`. -/
def revRange' (stop len : Nat) (step := 1) : Array Nat :=
  ofFn (n := len) fun i => stop + step * (len - 1) - step * i

theorem revRange'_def {stop len step} :
    revRange' stop len step = (range' stop len step).reverse := by
  ext i h <;> simp [revRange']; simp [revRange'] at h
  rw [Nat.add_sub_assoc, ← Nat.mul_sub]; apply Nat.mul_le_mul_left; omega

@[simp]
theorem toList_revRange' {stop len step} :
    (revRange' stop len step).toList = List.revRange' stop len step := by
  simp [revRange'_def, List.revRange'_def]

/-- Fold an array from left to right as with `foldlM`, but the combining function also receives
each element's index as a parameter. Monadic variant of `foldlIdx`. -/
@[inline]
def foldlIdxM [Monad m] (f : ℕ → β → α → m β) (init : β) (as : Array α) : m β :=
  Prod.snd <$> as.foldlM (fun (n, acc) a => Prod.mk n.succ <$> f n acc a) (0, init)

@[simp]
theorem _root_.List.foldlIdxM_toArray [Monad m] (f : ℕ → β → α → m β) (init : β) (l : List α) :
    l.toArray.foldlIdxM f init = l.foldlIdxM' f init := by unfold foldlIdxM List.foldlIdxM'; simp

theorem foldlIdxM_eq_foldlM_zipIdx [Monad m] [LawfulMonad m] {f : ℕ → β → α → m β} {as : Array α} :
    as.foldlIdxM f i = as.zipIdx.foldlM (fun b ai => f ai.snd b ai.fst) i := by
  cases as; simp; apply List.foldlIdxM'_eq_foldlM_zipIdx

/-- Fold an array from right to left as with `foldrM`, but the combining function also receives
each element's index as a parameter. Monadic variant of `foldrIdx`. -/
@[inline]
def foldrIdxM [Monad m] (f : ℕ → α → β → m β) (init : β) (as : Array α) : m β :=
  Prod.snd <$> as.foldrM (fun a (n, acc) => Prod.mk n.pred <$> f n.pred a acc) (as.size, init)

@[simp]
theorem _root_.List.foldrIdxM_toArray [Monad m] (f : ℕ → α → β → m β) (init : β) (l : List α) :
    l.toArray.foldrIdxM f init = l.foldrIdxM' f init := by unfold foldrIdxM List.foldrIdxM'; simp

theorem foldrIdxM_eq_foldrM_zipIdx [Monad m] [LawfulMonad m] {f : ℕ → α → β → m β} {as : Array α} :
    as.foldrIdxM f i = as.zipIdx.foldrM (fun ai b => f ai.snd ai.fst b) i := by
  cases as; simp; apply List.foldrIdxM'_eq_foldrM_zipIdx

/-- Fold an array from left to right as with `foldl`, but the combining function also receives
each element's index as a parameter. -/
@[inline]
def foldlIdx (f : ℕ → β → α → β) (init : β) (as : Array α) : β :=
  Id.run <| foldlIdxM (fun n b a => pure (f n b a)) init as

@[simp]
theorem _root_.List.foldlIdx_toArray {l : List α} : l.toArray.foldlIdx f i = l.foldlIdx f i := by
  unfold foldlIdx; simp; generalize 0 = s; induction l generalizing i s with simp_all

theorem foldlIdx_eq_foldl_zipIdx {as : Array α} :
    as.foldlIdx f i = as.zipIdx.foldl (fun b ai => f ai.snd b ai.fst) i := by
  cases as; simp; apply List.foldlIdx_eq_foldl_zipIdx

/-- Fold an array from right to left as with `foldr`, but the combining function also receives
each element's index as a parameter. -/
@[inline]
def foldrIdx (f : ℕ → α → β → β) (init : β) (as : Array α) : β :=
  Id.run <| foldrIdxM (fun n a b => pure (f n a b)) init as

@[simp]
theorem _root_.List.foldrIdx_toArray {l : List α} : l.toArray.foldrIdx f i = l.foldrIdx f i := by
  unfold foldrIdx; simp; generalize 0 = s; induction l generalizing i s with simp_all

theorem foldrIdx_eq_foldr_zipIdx {as : Array α} :
    as.foldrIdx f i = as.zipIdx.foldr (fun ai b => f ai.snd ai.fst b) i := by
  cases as; simp; apply List.foldrIdx_eq_foldr_zipIdx

/-- Applies a monadic function that returns an `Option` to each element of an array along with the
index at which that element is found, collecting the non-`none` values. -/
@[inline]
def filterMapIdxM [Monad m] (f : ℕ → α → m (Option β)) (as : Array α) : m (Array β) :=
  as.foldlIdxM (init := #[]) fun i bs a => (fun
    | some b => bs.push b
    | none   => bs) <$> f i a

@[simp]
theorem filterMapIdxM_eq_filterMapM_zipIdx [Monad m] [LawfulMonad m] {f : ℕ → α → m (Option β)}
    {as : Array α} : as.filterMapIdxM f = as.zipIdx.filterMapM fun ai => f ai.snd ai.fst := by
  rw [filterMapIdxM, foldlIdxM_eq_foldlM_zipIdx, filterMapM]; simp [← bind_pure_comp]
  congr!; split <;> rfl

/-- Applies a function that returns an `Option` to each element of an array along with the index at
which that element is found, collecting the non-`none` values. -/
@[inline]
def filterMapIdx (f : ℕ → α → Option β) (as : Array α) : Array β :=
  as.foldlIdx (init := #[]) fun i bs a => match f i a with
    | some b => bs.push b
    | none   => bs

@[simp]
theorem filterMapIdx_eq_filterMap_zipIdx {f : ℕ → α → Option β} {as : Array α} :
    as.filterMapIdx f = as.zipIdx.filterMap fun ai => f ai.snd ai.fst := by
  rw [filterMap, ← filterMapIdxM_eq_filterMapM_zipIdx (f := fun i a => pure (f i a)),
    filterMapIdxM, filterMapIdx, foldlIdx]; simp_rw [map_pure]

/-- Computes the sum of `f` applied to elements of the array. Note that it does a left fold,
as opposed to `Array.sum` which does a right fold. -/
abbrev sumOn [Add β] [Zero β] (f : α → β) := Array.foldl (fun acc a => acc + f a) 0

theorem sumOn_def [Add β] [Zero β] {f : α → β} {as : Array α} :
    as.sumOn f = (as.map f).foldl (· + ·) 0 := foldl_map.symm

@[simp]
theorem sumOn_eq_sum_map [AddMonoid β] {f : α → β} {as : Array α} : as.sumOn f = (as.map f).sum := by
  rw [sumOn_def]; symm; exact sum_eq_foldl

theorem sumOn_id [AddMonoid α] {as : Array α} : as.sumOn id = as.sum := by simp

/-- Bitwise OR (`|||`) of all elements of `as` (assumes `0` is the identity). -/
abbrev lany [OrOp α] [Zero α] (as : Array α) := as.foldl (· ||| ·) 0

/-- Bitwise AND (`&&&`) of all elements of `as` (assumes `~~~0` is the identity). -/
abbrev lall [AndOp α] [Zero α] [Complement α] (as : Array α) := as.foldl (· &&& ·) (~~~0)

/-- Bitwise XOR (`^^^`) of all elements of `as` (assumes `0` is the identity). -/
abbrev xor [XorOp α] [Zero α] (as : Array α) := as.foldl (· ^^^ ·) 0
