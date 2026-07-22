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
where go : Nat → Nat → List Nat → List Nat
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
  go : Nat → Nat → List Nat → List Nat
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

/-- Computes the sum of `f` applied to elements of the  list. -/
abbrev sumOn [Add β] [Zero β] (f : α → β) (l : List α) := (l.map f).sum

/-- Bitwise OR (`|||`) of all elements of `l` (assumes `0` is the identity). -/
abbrev lany [OrOp α] [Zero α] (l : List α) := l.foldl (· ||| ·) 0

/-- Bitwise AND (`&&&`) of all elements of `l` (assumes `~~~0` is the identity). -/
abbrev lall [AndOp α] [Zero α] [Complement α] (l : List α) := l.foldl (· &&& ·) (~~~0)

/-- Bitwise XOR (`^^^`) of all elements of `l` (assumes `0` is the identity). -/
abbrev xor [XorOp α] [Zero α] (l : List α) := l.foldl (· ^^^ ·) 0
