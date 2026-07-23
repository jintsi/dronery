import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Data.Nat.Factorial.SuperFactorial
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Fintype.Lattice
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

namespace Nat

def chooseImpl (n k : ℕ) :=
  if n < k then 0 else
  if k = 0 then 1 else
  if k = 1 then n else
  chooseImpl n (k / 2) * chooseImpl (n - k / 2) (k - k / 2) / chooseImpl k (k / 2)
termination_by k

@[csimp] theorem choose_eq_chooseImpl : choose = chooseImpl := by
  ext n k; induction k using Nat.strong_induction_on generalizing n
  rename_i k ih; unfold chooseImpl; split_ifs
  · rwa [choose_eq_zero_of_lt]
  · subst k; simp
  · subst k; simp
  rw [← ih, ← ih, ← ih] <;> try omega
  apply Nat.eq_div_of_mul_eq_left (choose_ne_zero (k.div_le_self 2))
  exact choose_mul (k.div_le_self 2)

def multichooseImpl (n k : ℕ) := choose (n + k - 1) k

@[csimp] theorem multichoose_eq_multichooseImpl : @multichoose = @multichooseImpl :=
  funext₂ multichoose_eq

def centralBinomImpl (n : ℕ) := choose (2 * n) n

@[csimp] theorem centralBinom_eq_centralBinomImpl : @centralBinom = @centralBinomImpl := rfl

def catalanImpl (n : ℕ) := centralBinom n / (n + 1)

@[csimp] theorem catalan_eq_catalanImpl : @catalan = @catalanImpl :=
  funext catalan_eq_centralBinom_div

theorem _root_.numDerangements_ne_zero (h : n ≠ 1) : numDerangements n ≠ 0 := by
  induction n using twoStepInduction with
  | zero => simp
  | one => simp at h
  | more => unfold numDerangements; grind

def _root_.numDerangementsImpl (n : ℕ) :=
  n.fold (fun i _ d => if Odd i then (i + 1) * d + 1 else (i + 1) * d - 1) 1

@[csimp]
theorem numDerangements_eq_numDerangementsImpl : @numDerangements = @numDerangementsImpl := by
  ext n; unfold numDerangementsImpl; induction n with
  | zero => simp
  | succ n ih =>
    rw [fold_succ, ← ih, ← Int.ofNat_inj, numDerangements_succ]; split <;> rename_i h
    · simp [h]
    simp at h; rw [Int.ofNat_sub, h.neg_one_pow]; simp
    simp [one_le_iff_ne_zero]; apply numDerangements_ne_zero; contrapose h; simp [h]

def superFactorialImpl (n : ℕ) := (n.fold (fun i _ (f, s) => ((i + 2) * f, f * s)) (1, 1)).2

@[csimp] theorem superFactorial_eq_superFactorialImpl : @superFactorial = @superFactorialImpl := by
  ext n; unfold superFactorialImpl; suffices ((n + 1)!, sf n) = _ from congrArg Prod.snd this
  induction n with
  | zero => simp
  | succ n ih => simp [← ih, factorial_succ, superFactorial_succ]

open Finset Fintype

open Fin in
theorem _root_.Fin.card_fun_surjective :
    #{f : Fin n → Fin k | f.Surjective} = k ! * stirlingSecond n k := by
  induction n generalizing k with
  | zero => cases k <;> simp [Function.Surjective]
  | succ n ih =>
    rcases k with (_ | k)
    · simp
    rw [stirlingSecond, mul_add, mul_left_comm, ← ih, factorial_succ, mul_assoc, ← ih, ← mul_add]
    calc #{f : Fin n.succ → Fin k.succ | f.Surjective}
    _ = #{(f, a) : (Fin n → Fin k.succ) × Fin k.succ | ∀ i, a = i ∨ ∃ x, f x = i} := by
      apply card_equiv (Fin.succFunEquiv _ _); intro f; simp
      apply forall_congr'; simp [Fin.exists_iff_castSucc, natAdd, last, castSucc]
    _ = ∑ a, #{(f, a') : (Fin n → Fin k.succ) × Fin k.succ | a' = a ∧ ∀ i, a = i ∨ ∃ x, f x = i} := by
      convert card_eq_sum_card_fiberwise (f := Prod.snd) ?_ using 3; swap; infer_instance; swap; simp
      rename_i a _; ext ⟨f, a'⟩; simp [and_comm]; rintro rfl; rfl
    _ = ∑ a, #{f : Fin n → Fin k.succ | ∀ i, a = i ∨ ∃ x, f x = i} := by
      congr! with a; apply card_nbij' Prod.fst (·, a) <;> simp [Set.MapsTo, Set.LeftInvOn]
    _ = ∑ a, #{f : Fin n → Fin k.succ | f.Surjective ∨
        ∃ (h : ∀ x, f x ≠ a), (fun x => ⟨f x, h x⟩ : Fin n → {i // i ≠ a}).Surjective} := by
      congr! with a _ f; simp [Function.Surjective]; constructor
      · intro h; by_cases! hx : ∃ x, f x = a
        · left; intro i; convert h i; rw [or_iff_right_of_imp]; rintro rfl; exact hx
        · right; use hx; intro i hi; exact (h i).resolve_left (Ne.symm hi)
      · rintro (h | ⟨h, h'⟩)
        · intro i; right; exact h i
        · convert h'; grind
    _ = ∑ a, (#{f : Fin n → Fin k.succ | f.Surjective} + #{f : Fin n → Fin k.succ |
        ∃ (h : ∀ x, f x ≠ a), (fun x => ⟨f x, h x⟩ : Fin n → {i // i ≠ a}).Surjective}) := by
      congr! with a; rw [← card_union_of_disjoint, filter_or]
      simp [disjoint_right]; simp [Function.Surjective]; intro f h _; use a
    _ = ∑ a, (#{f : Fin n → Fin k.succ | f.Surjective} + #{f : Fin n → Fin k | f.Surjective}) := by
      congr! with a; symm; apply card_nbij (a.succAbove ∘ ·)
      · simp [Set.MapsTo]; simp [Function.Surjective]; intro f h i hi
        have ⟨b, hb⟩ := exists_succAbove_eq hi; apply (h b).imp; simp +contextual [hb]
      · exact Fin.succAbove_right_injective.comp_left.injOn
      · simp [Set.SurjOn, Set.subset_def]; intro f h hf
        apply forall_imp fun x => exists_succAbove_eq at h; choose g hg using h; use g; and_intros
        swap; exact funext hg
        simp [Function.Surjective] at hf; intro i; specialize hf (a.succAbove i) (a.succAbove_ne i)
        exact hf.imp fun x hx => a.succAbove_right_injective ((hg x).trans hx)
    _ = (k + 1) * (#{f : Fin n → Fin k.succ | f.Surjective} + #{f : Fin n → Fin k | f.Surjective}) := by
      simp

theorem factorial_mul_stirlingSecond_eq_sum :
    (k ! * stirlingSecond n k) = ∑ i ∈ range (k + 1), (-1 : ℤ) ^ (k - i) * choose k i * i ^ n := by
  trans (#(univ.inf fun (a : Fin k) => (piFinset fun (_ : Fin n) => {a}ᶜ)ᶜ) : ℤ)
  · rw [← cast_mul, ← Fin.card_fun_surjective]; congr; ext f
    simp; simp [Function.Surjective, mem_inf]
  rw [inclusion_exclusion_card_inf_compl, sum_powerset, Finset.card_fin, ← sum_flip]
  congr! with i hi; simp at hi
  trans ∑ s ∈ powersetCard (k - i) (univ (α := Fin k)), (-1) ^ #s * (k - #s) ^ n; swap
  · rw [sum_powersetCard (f := fun s => _ ^ s * (k - s : ℤ) ^ n)]; simp [hi]; ring
  congr! 2 with s hs; trans (#(piFinset fun _ : Fin n => sᶜ) : ℤ)
  · congr; ext f; simp [mem_inf]; grind
  · simp_all [card_compl]

/-- The number of surjections from `Fin n` (or any other `n`-element type) to `Fin k`
(or any other `k`-element type), equal to `k ! * stirlingSecond n k` -/
def surjpow (n k : ℕ) := if n < k then 0 else (go (k + 1) 1 0).toNat where
  @[inline] go : (i : ℕ) → (nkCi : ℤ) → (acc : ℤ) → ℤ
  | 0, _, acc => acc
  | i+1, nkCi, acc => go i (-nkCi * i / (k - i + 1)) (acc + nkCi * i ^ n)

theorem surjpow_def : surjpow n k = k ! * stirlingSecond n k := by
  unfold surjpow; split
  · rw [stirlingSecond_eq_zero_of_lt ‹_›, mul_zero]
  suffices ∀ i ≤ k, ∀ acc, surjpow.go n k (i + 1) ((-1) ^ (k - i) * choose k i) acc =
      acc + ∑ j ∈ range (i + 1), (-1 : ℤ) ^ (k - j) * choose k j * j ^ n by
    convert Int.toNat_natCast _; rw [cast_mul, factorial_mul_stirlingSecond_eq_sum]
    convert this k le_rfl 0 <;> simp
  intro i hi acc; induction i generalizing acc with unfold surjpow.go
  | zero => unfold surjpow.go; simp
  | succ i ih =>
    rw [sum_range_succ, add_left_comm, ← add_comm (acc + _)]; convert ih (le_of_succ_le hi) _
    rw [cast_add_one, ← sub_sub, sub_add_cancel, ← neg_mul, ← neg_one_mul, ← Int.pow_succ',
      ← Nat.sub_add_comm hi, succ_sub_succ]
    apply Int.ediv_eq_of_eq_mul_left (by simpa [sub_eq_zero] using ne_of_gt hi)
    rw [mul_assoc, ← cast_add_one, ← cast_mul, choose_succ_right_eq, cast_mul, mul_assoc,
      cast_sub (le_of_succ_le hi)]

theorem Fintype.card_fun_surjective [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] :
    #{f : α → β | f.Surjective} = surjpow (card α) (card β) := by
  rw [surjpow_def, ← Fin.card_fun_surjective]
  apply Finset.card_equiv ((equivFin α).arrowCongr (equivFin β)); simp; intro f
  apply (equivFin β).forall_congr; simp [(equivFin α).exists_congr_left]

def stirlingSecondImpl (n k : ℕ) := surjpow n k / k !

@[csimp]
theorem stirlingSecond_eq_stirlingSecondImpl : stirlingSecond = stirlingSecondImpl := by
  ext n k; rw [stirlingSecondImpl, surjpow_def, mul_div_cancel_left₀ _ (k.factorial_ne_zero)]

/-- to be proven later -/
theorem stirlingFirst_eq_sum (hk : k ≠ 0) : stirlingFirst n k =
    ∑ i ∈ range (n - k + 1), ((-1) ^ (n - k - i) * choose (n + i - 1) (k - 1) *
      choose (2 * n - k) (n + i) * stirlingSecond (n - k + i) i : ℤ) := by sorry

def stirlingFirstImpl (n k : ℕ) :=
  if k = 0 then n.stirlingFirst k else if n < k then 0 else
    (go (n - k + 1) (choose (2 * n - k - 1) (k - 1)) 0).toNat where
  @[inline] go : (i : ℕ) → (nBinoms : ℤ) → (acc : ℤ) → ℤ
  | 0, _, acc => acc
  | i+1, nBinoms, acc => go i (-nBinoms * (n + i - k) * (n + i) / ((n + i - 1) * (n - k + 1 - i)))
    (acc + nBinoms * stirlingSecond (n - k + i) i)

@[csimp]
theorem stirlingFirst_eq_stirlingFirstImpl : stirlingFirst = stirlingFirstImpl := by
  ext n k; unfold stirlingFirstImpl; split_ifs
  · rfl
  · exact stirlingFirst_eq_zero_of_lt ‹_›
  rename_i hk hn; simp at hn; suffices ∀ i ≤ n - k, ∀ acc, stirlingFirstImpl.go n k (i + 1)
      ((-1) ^ (n - k - i) * choose (n + i - 1) (k - 1) * choose (2 * n - k) (n + i)) acc
      = acc + ∑ j ∈ range (i + 1), ((-1) ^ (n - k - j) * choose (n + j - 1) (k - 1) *
        choose (2 * n - k) (n + j) * stirlingSecond (n - k + j) j : ℤ) by
    symm; convert Int.toNat_natCast _; rw [stirlingFirst_eq_sum hk]
    convert this (n - k) le_rfl 0 <;> simp [two_mul, Nat.add_sub_assoc hn]
  intro i hi acc; induction i generalizing acc with unfold stirlingFirstImpl.go
  | zero => unfold stirlingFirstImpl.go; simp
  | succ i ih =>
    rw [sum_range_succ, acc.add_left_comm, ← add_comm (acc + _)]; convert ih (le_of_succ_le hi) _
    rw [← neg_mul, ← neg_mul, ← neg_one_mul, ← Int.pow_succ', ← Nat.sub_add_comm hi, succ_sub_succ,
      cast_add_one, ← add_assoc, ← add_assoc, Nat.add_sub_cancel,
      add_sub_cancel_right, Int.add_sub_add_right]; apply Int.ediv_eq_of_eq_mul_left
    · rw [mul_ne_zero_iff]; omega
    have := choose_mul_succ_eq (n + i - 1) (k - 1)
    rw [Nat.sub_add_cancel (by omega), Nat.sub_sub_right _ (by omega)] at this
    have this' := choose_succ_right_eq (2 * n - k) (n + i)
    rw [two_mul, sub_add_eq, (n + n).sub_right_comm, Nat.add_sub_cancel,← two_mul] at this'
    simp [mul_assoc]; rw [← mul_assoc, mul_mul_mul_comm, ← cast_add, ← cast_add_one,
      ← cast_sub (by omega), sub_sub, ← cast_add, ← cast_sub (by omega)]; norm_cast; grind
