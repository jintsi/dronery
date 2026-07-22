namespace Array

/-- Construct an array of numbers from `n-1` to `0` in decreasing order. -/
def revRange (n : Nat) : Array Nat := ofFn (n := n) fun i => i.rev

theorem revRange_def : revRange n = (range n).reverse := by
  ext <;> simp [revRange]; omega

/-- Construct an array of all elements of `Fin n` in decreasing order. -/
def revFinRange (n : Nat) : Array (Fin n) := ofFn Fin.rev

theorem revFinRange_def : revFinRange n = (Array.finRange n).reverse := by
  ext <;> simp [revFinRange]; omega

/-- Construct an array of numbers of size `len`, decreasing by `step` at each element and ending
at `stop`, that is, `#[stop+(len-1)*step, ..., stop+step, stop]`. -/
def revRange' (stop len : Nat) (step := 1) : Array Nat :=
  ofFn (n := len) fun i => stop + step * (len - 1) - step * i

theorem revRange'_def {stop len step} :
    revRange' stop len step = (range' stop len step).reverse := by
  ext i h <;> simp [revRange']; simp [revRange'] at h
  rw [Nat.add_sub_assoc, ← Nat.mul_sub]; apply Nat.mul_le_mul_left; omega

/-- Computes the sum of `f` applied to elements of the array. -/
abbrev sumOn [Add β] [Zero β] (f : α → β) (as : Array α) := (as.map f).sum

/-- Bitwise OR (`|||`) of all elements of `as` (assumes `0` is the identity). -/
abbrev lany [OrOp α] [Zero α] (as : Array α) := as.foldl (· ||| ·) 0

/-- Bitwise AND (`&&&`) of all elements of `as` (assumes `~~~0` is the identity). -/
abbrev lall [AndOp α] [Zero α] [Complement α] (as : Array α) := as.foldl (· &&& ·) (~~~0)

/-- Bitwise XOR (`^^^`) of all elements of `as` (assumes `0` is the identity). -/
abbrev xor [XorOp α] [Zero α] (as : Array α) := as.foldl (· ^^^ ·) 0
