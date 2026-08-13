import Dronery.List

namespace Array

@[elab_as_elim]
theorem pushInduction {motive : Array α → Prop} (as : Array α) (empty : motive #[])
    (push : ∀ as a, motive as → motive (as.push a)) : motive as := by
  rcases as with ⟨l⟩; induction l using List.revInduction with
  | nil => exact empty
  | concat l a ih => simpa using push ⟨l⟩ a ih

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

/-! ## Random lemmas -/

@[simp]
theorem idxOf_toList [BEq α] {as : Array α} {a : α} : as.toList.idxOf a = as.idxOf a :=
  as.rec fun _ => List.idxOf_toArray.symm

@[simp]
theorem getElem_idxOf [BEq α] [LawfulBEq α] {as : Array α} {a : α} (h : as.idxOf a < as.size) :
    as[as.idxOf a] = a := by cases as; simp

/-- Unsafe implementation of `attachFin` making use of the fact that `Nat` and `Fin n` have the
same memory layout, and thus so do `Array Nat` and `Array (Fin n)`. -/
@[inline]
unsafe def attachFinImpl (xs : Array ℕ) {n : ℕ} (_ : ∀ a ∈ xs, a < n) : Array (Fin n) :=
  unsafeCast xs

/-- Turns a list of numbers, all smaller than `n`, into a list of `Fin n`s.
`O(1)` (a no-op, in fact). -/
@[implemented_by attachFinImpl]
def attachFin (xs : Array ℕ) {n : ℕ} (h : ∀ a ∈ xs, a < n) : Array (Fin n) := xs.pmap Fin.mk h

/-! ## Operations with acces to indices
(why are there so many of these) -/

/-- See comment at `forIn'Unsafe`.
The in-bounds proof is supplied by `lcProof`, paralleling `mapFinIdxMUnsafe`. -/
@[inline]
unsafe def foldlFinIdxMUnsafe [Monad m] (as : Array α) (f : (i : ℕ) → β → α → i < as.size → m β)
    (init : β) : m β :=
  let rec @[specialize] fold (i : USize) (stop : USize) (b : β) : m β := do
    if i == stop then pure b
    else fold (i+1) stop (← f i.toNat b (as.uget i lcProof) lcProof)
  fold 0 (.ofNat as.size) init

/-- Fold an array from left to right as with `foldlM`, but the combining function also receives
each element's index as a parameter alongside a proof that the index is in bounds.
Monadic variant of `foldlFinIdxM`. -/
-- Screw reference implementations, just defer to `List`.
@[implemented_by foldlFinIdxMUnsafe]
def foldlFinIdxM [Monad m] (as : Array α) (f : (i : ℕ) → β → α → i < as.size → m β) (init : β) :=
  as.toList.foldlFinIdxM f init

@[simp]
theorem _root_.List.foldlFinIdxM_toArray [Monad m] {l : List α}
    {f : (i : ℕ) → β → α → i < l.length → m β} {init : β} :
    l.toArray.foldlFinIdxM f init = l.foldlFinIdxM f init := rfl

@[simp]
theorem foldlFinIdxM_empty [Monad m] {f : (i : ℕ) → β → α → i < 0 → m β} {init : β} :
    #[].foldlFinIdxM f init = pure init := rfl

@[simp]
theorem foldlFinIdxM_push [Monad m] [LawfulMonad m] {as : Array α} {a : α}
    {f : (i : ℕ) → β → α → i < (as.push a).size → m β} {init : β} : (as.push a).foldlFinIdxM f init
    = as.foldlFinIdxM (fun i acc a h => f i acc a (by simp; lia)) init >>= fun b =>
      f as.size b a (by simp) := by
  cases as; eta_expand; simp [push]; rw! [List.concat_eq_append]; simp; rfl

/-- See comment at `forIn'Unsafe`.
The in-bounds proof is supplied by `lcProof`, paralleling `mapFinIdxMUnsafe`. -/
@[inline]
unsafe def foldrFinIdxMUnsafe [Monad m] (as : Array α) (f : (i : ℕ) → α → β → i < as.size → m β)
    (init : β) : m β :=
  let rec @[specialize] fold (i : USize) (stop : USize) (b : β) : m β := do
    if i == stop then pure b
    else fold (i-1) stop (← f (i-1).toNat (as.uget (i-1) lcProof) b lcProof)
  fold (.ofNat as.size) 0 init

/-- Fold an array from right to left as with `foldrM`, but the combining function also receives
each element's index as a parameter alongside a proof that the index is in bounds.
Monadic variant of `foldrFinIdxM`. -/
-- Screw reference implementations, just defer to `List`.
@[implemented_by foldrFinIdxMUnsafe]
def foldrFinIdxM [Monad m] (as : Array α) (f : (i : ℕ) → α → β → i < as.size → m β) (init : β) :=
  as.toList.foldrFinIdxM f init

@[simp]
theorem _root_.List.foldrFinIdxM_toArray [Monad m] {l : List α}
    {f : (i : ℕ) → α → β → i < l.length → m β} {init : β} :
    l.toArray.foldrFinIdxM f init = l.foldrFinIdxM f init := rfl

@[simp]
theorem foldrFinIdxM_empty [Monad m] {f : (i : ℕ) → α → β → i < 0 → m β} {init : β} :
    #[].foldrFinIdxM f init = pure init := rfl

@[simp]
theorem foldrFinIdxM_push [Monad m] {as : Array α} {a : α}
    {f : (i : ℕ) → α → β → i < (as.push a).size → m β} {init : β} :
    (as.push a).foldrFinIdxM f init = f as.size a init (by simp) >>= fun b =>
      as.foldrFinIdxM (fun i a acc h => f i a acc (by simp; lia)) b := by
  cases as; eta_expand; simp [push]; rw! [List.concat_eq_append]; simp; rfl

/-- Fold an array from left to right as with `foldlM`, but the combining function also receives
each element's index as a parameter. Monadic variant of `foldlIdx`. -/
@[inline]
def foldlIdxM [Monad m] (f : ℕ → β → α → m β) (init : β) (as : Array α) : m β :=
  as.foldlFinIdxM (fun i acc a _ => f i acc a) init

@[simp]
theorem _root_.List.foldlIdxM_toArray [Monad m] {f : ℕ → β → α → m β} {init : β} {l : List α} :
    l.toArray.foldlIdxM f init = l.foldlIdxM' f init := rfl

@[simp]
theorem foldlIdxM_empty [Monad m] {f : ℕ → β → α → m β} {init : β} :
    #[].foldlIdxM f init = pure init := rfl

@[simp]
theorem foldlIdxM_push [Monad m] [LawfulMonad m] {f : ℕ → β → α → m β} {init : β} {as : Array α}
    {a : α} : (as.push a).foldlIdxM f init = as.foldlIdxM f init >>= fun b => f as.size b a :=
  foldlFinIdxM_push

theorem foldlIdxM_eq_foldlM_zipIdx [Monad m] [LawfulMonad m] {f : ℕ → β → α → m β} {init : β}
    {as : Array α} : as.foldlIdxM f init = as.zipIdx.foldlM (fun b ai => f ai.snd b ai.fst) init := by
  cases as; simp; apply List.foldlIdxM'_eq_foldlM_zipIdx

/-- Fold an array from right to left as with `foldrM`, but the combining function also receives
each element's index as a parameter. Monadic variant of `foldrIdx`. -/
@[inline]
def foldrIdxM [Monad m] (f : ℕ → α → β → m β) (init : β) (as : Array α) : m β :=
  as.foldrFinIdxM (fun i a acc _ => f i a acc) init

@[simp]
theorem _root_.List.foldrIdxM_toArray [Monad m] {f : ℕ → α → β → m β} {init : β} {l : List α} :
    l.toArray.foldrIdxM f init = l.foldrIdxM' f init := rfl

@[simp]
theorem foldrIdxM_empty [Monad m] {f : ℕ → α → β → m β} {init : β} :
    #[].foldrIdxM f init = pure init := rfl

@[simp]
theorem foldrIdxM_push [Monad m] {f : ℕ → α → β → m β} {init : β} {as : Array α} {a : α} :
    (as.push a).foldrIdxM f init = f as.size a init >>= fun b => as.foldrIdxM f b :=
  foldrFinIdxM_push

theorem foldrIdxM_eq_foldrM_zipIdx [Monad m] [LawfulMonad m] {f : ℕ → α → β → m β} {as : Array α} :
    as.foldrIdxM f i = as.zipIdx.foldrM (fun ai b => f ai.snd ai.fst b) i := by
  cases as; simp; apply List.foldrIdxM'_eq_foldrM_zipIdx

/-- Fold an array from left to right as with `foldl`, but the combining function also receives
each element's index as a parameter alongside a proof that the index is in bounds. -/
@[inline]
def foldlFinIdx (as : Array α) (f : (i : ℕ) → β → α → i < as.size → β) (init : β) : β :=
  Id.run <| as.foldlFinIdxM (fun i acc a h => pure (f i acc a h)) init

@[simp]
theorem _root_.List.foldlFinIdx_toArray {l : List α} {f : (i : ℕ) → β → α → i < l.length → β}
    {init : β} : l.toArray.foldlFinIdx f init = l.foldlFinIdx f init := rfl

@[simp]
theorem foldlFinIdx_empty {f : (i : ℕ) → β → α → i < 0 → β} {init : β} :
    #[].foldlFinIdx f init = init := rfl

@[simp]
theorem foldlFinIdx_push {as : Array α} {a : α} {f : (i : ℕ) → β → α → i < (as.push a).size → β}
    {init : β} : (as.push a).foldlFinIdx f init =
      f as.size (as.foldlFinIdx (fun i acc a h => f i acc a (by simp; lia)) init) a (by simp) :=
  foldlFinIdxM_push

/-- Fold an array from right to left as with `foldr`, but the combining function also receives
each element's index as a parameter alongside a proof that the index is in bounds. -/
@[inline]
def foldrFinIdx (as : Array α) (f : (i : ℕ) → α → β → i < as.size → β) (init : β) : β :=
  Id.run <| as.foldrFinIdxM (fun i a acc h => pure (f i a acc h)) init

@[simp]
theorem _root_.List.foldrFinIdx_toArray {l : List α} {f : (i : ℕ) → α → β → i < l.length → β}
    {init : β} : l.toArray.foldrFinIdx f init = l.foldrFinIdx f init := rfl

@[simp]
theorem foldrFinIdx_empty {f : (i : ℕ) → α → β → i < 0 → β} {init : β} :
    #[].foldrFinIdx f init = init := rfl

@[simp]
theorem foldrFinIdx_push {as : Array α} {a : α} {f : (i : ℕ) → α → β → i < (as.push a).size → β}
    {init : β} : (as.push a).foldrFinIdx f init =
      as.foldrFinIdx (fun i a acc h => f i a acc (by simp; lia)) (f as.size a init (by simp)) :=
  foldrFinIdxM_push

/-- Fold an array from left to right as with `foldl`, but the combining function also receives
each element's index as a parameter. -/
@[inline]
def foldlIdx (f : ℕ → β → α → β) (init : β) (as : Array α) : β :=
  Id.run <| as.foldlIdxM (fun i acc a => pure (f i acc a)) init

@[simp]
theorem _root_.List.foldlIdx_toArray {f : ℕ → β → α → β} {init : β} {l : List α} :
    l.toArray.foldlIdx f init = l.foldlIdx f init := List.foldlIdx_eq_foldlIdxM'.symm

@[simp]
theorem foldlIdx_empty {f : ℕ → β → α → β} {init : β} : #[].foldlIdx f init = init := rfl

@[simp]
theorem foldlIdx_push {f : ℕ → β → α → β} {init : β} {as : Array α} {a : α} :
    (as.push a).foldlIdx f init = f as.size (as.foldlIdx f init) a := foldlIdxM_push

theorem foldlIdx_map {f : α₁ → α₂} {as : Array α₁} {g : ℕ → β → α₂ → β} {init : β} :
    (as.map f).foldlIdx g init = as.foldlIdx (fun i acc a => g i acc (f a)) init := by
  cases as; simpa using List.foldlIdx_map

theorem foldlIdx_eq_foldl_zipIdx {f : ℕ → β → α → β} {init : β} {as : Array α} :
    as.foldlIdx f init = as.zipIdx.foldl (fun b ai => f ai.snd b ai.fst) init := by
  cases as; simp; apply List.foldlIdx_eq_foldl_zipIdx

/-- Fold an array from right to left as with `foldr`, but the combining function also receives
each element's index as a parameter. -/
@[inline]
def foldrIdx (f : ℕ → α → β → β) (init : β) (as : Array α) : β :=
  Id.run <| foldrIdxM (fun n a b => pure (f n a b)) init as

@[simp]
theorem _root_.List.foldrIdx_toArray {f : ℕ → α → β → β} {init : β} {l : List α} :
    l.toArray.foldrIdx f init = l.foldrIdx f init := List.foldrIdx_eq_foldrIdxM'.symm

@[simp]
theorem foldrIdx_empty {f : ℕ → α → β → β} {init : β} : #[].foldrIdx f init = init := rfl

@[simp]
theorem foldrIdx_push {f : ℕ → α → β → β} {init : β} {as : Array α} {a : α} :
    (as.push a).foldrIdx f init = as.foldrIdx f (f as.size a init) := foldrIdxM_push

theorem foldrIdx_eq_foldr_zipIdx {f : ℕ → α → β → β} {init : β} {as : Array α} :
    as.foldrIdx f init = as.zipIdx.foldr (fun ai b => f ai.snd ai.fst b) init := by
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
