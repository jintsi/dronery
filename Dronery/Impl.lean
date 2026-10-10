import Dronery.List
import Batteries.Tactic.OpenPrivate
import Mathlib.Data.List.Fold
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Data.Nat.Factorial.SuperFactorial
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Fintype.Lattice
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! # The efficiency paranoia file -/

/-! ## `List` -/

namespace List

variable {as : List α} {bs : List β}

/-- A variant of `List.foldr` that performs better when the list is unshared. -/
@[inline] def foldr' (f : α → β → β) (init : β) (l : List α) := l.reverse.foldl (flip f) init

@[simp]
theorem foldr'_eq_foldr {f : α → β → β} : foldr' f b l = foldr f b l :=
  foldr_eq_foldl_reverse.symm

/-- `l.mapRev f` is `(l.map f).reverse`, faster than `l.map f`. -/
@[inline] def mapRev (f : α → β) (l : List α) : List β :=
  l.foldl (init := []) fun bs a => f a :: bs

@[simp]
theorem mapRev_eq {f : α → β} : mapRev f l = (map f l).reverse := by simp [mapRev]

/-- `l.filterRev p` is `(l.filter p).reverse`, faster than `l.filter p`. -/
@[inline] def filterRev (p : α → Bool) (l : List α) : List α :=
  l.foldl (init := []) fun acc a => bif p a then a :: acc else acc

@[simp]
theorem filterRev_eq {p : α → Bool} : filterRev p l = (l.filter p).reverse := by
  simp [filterRev]; induction l using revInduction with
  | nil => rfl
  | concat l a ih => simp [ih, filter_singleton]; split <;> rfl

/-- `l.filterMapRev f` is `(l.filterMap f).reverse`, faster than `l.filterMap f`. -/
@[inline] def filterMapRev (f : α → Option β) (l : List α) : List β :=
  l.foldl (init := []) fun bs a => match f a with | none => bs | some b => b :: bs

@[simp]
theorem filterMapRev_eq {f : α → Option β} : filterMapRev f l = (filterMap f l).reverse := by
  simp [filterMapRev]; induction l using revInduction with
  | nil => rfl
  | concat l a ih => simp [ih, filterMap_cons]; split <;> simp_all

/-- `l.flatMapRev f` is `(l.flatMap f).reverse`, faster than `l.flatMap f`. -/
@[inline] def flatMapRev (f : α → List β) (l : List α) : List β :=
  l.foldl (init := []) fun acc a => (f a).reverseAux acc

@[simp]
theorem flatMapRev_eq {f : α → List β} : flatMapRev f l = (l.flatMap f).reverse := by
  simp [flatMapRev, flatten_reverse, flatMap_def, Function.comp_def]

/-- `l.flattenRev` is `l.flatten.reverse`, faster than `l.flatten`. -/
@[inline] def flattenRev (l : List (List α)) := l.flatMapRev id

@[simp]
theorem flattenRev_eq : @flattenRev α l = l.flatten.reverse := by simp [flattenRev]

/-- `l.partitionRev p` is `l.reverse.partition p`, faster than `l.partition p`. -/
@[inline] def partitionRev (p : α → Bool) (l : List α) : List α × List α :=
  l.foldl (init := ([], [])) fun (ys, ns) a => bif p a then (a::ys, ns) else (ys, a::ns)

@[simp]
theorem partitionRev_eq {l : List α} :
    l.partitionRev p = ((l.filter p).reverse, (l.filter (not ∘ p)).reverse) := by
  simp [partitionRev]; induction l using revInduction with
  | nil => rfl
  | concat l a ih => simp [ih, filter_singleton, ← Bool.not_eq_true]; split <;> rfl

@[inline] def erasePImpl (p : α → Bool) (l : List α) : List α := go l [] where
  @[specialize] go : List α → List α → List α
  | [],     _ => l
  | a::l, acc => bif p a then acc.reverseAux l else go l (a::acc)

open private erasePTR.go from Init.Data.List.Impl in
@[csimp] theorem eraseP_eq_erasePImpl : @erasePTR = @erasePImpl := by
  funext α p l; unfold erasePTR erasePImpl
  suffices ∀ as acc, erasePTR.go p l as acc.reverse.toArray = erasePImpl.go p l as acc by
    simpa using this l []
  intro as acc; induction as generalizing acc with
  | nil => rfl
  | cons a as ih => simp [erasePTR.go, erasePImpl.go, ← ih]

@[inline] def eraseImpl [BEq α] (l : List α) (a : α) := l.eraseP (· == a)

@[csimp] theorem erase_eq_eraseImpl : @eraseTR = @eraseImpl := by
  funext α _ l a; rw [← erase_eq_eraseTR, erase_eq_eraseP']; rfl

/-- `l.eraseP? p` is `some (l.erase p)` is `l` contains some element for which `p` returns `true`,
`none` otherwise. -/
@[inline] def eraseP? (p : α → Bool) (l : List α) : Option (List α) := go l [] where
  @[specialize] go : List α → List α → Option (List α)
  | [],     _ => none
  | a::l, acc => bif p a then some (acc.reverseAux l) else go l (a::acc)

theorem eraseP?_eq_ite {l : List α} :
    eraseP? p l = if ∃ a ∈ l, p a then some (l.eraseP p) else none := by
  rw [eraseP?, eraseP_eq_erasePTR, eraseP_eq_erasePImpl, erasePImpl]
  generalize [] = acc; fun_induction erasePImpl.go with
  | case1 acc => rfl
  | case2 a l acc h => simp [eraseP?.go, h]
  | case3 a l acc h ih => simpa [eraseP?.go, h]

def bagInterRev [BEq α] (l₁ l₂ : List α) : List α := go l₁ l₂ [] where
  go : List α → List α → List α → List α
  | [], _, acc => acc
  | _, [], acc => acc
  | a::l₁, l₂, acc => match l₂.eraseP? (· == a) with
    | none => go l₁ l₂ acc
    | some l => go l₁ l (a :: acc)

@[simp]
theorem bagInterRev_eq [DecidableEq α] {l₁ l₂ : List α} :
    l₁.bagInterRev l₂ = (l₁.bagInter l₂).reverse := by
  rw [bagInterRev, ← append_nil (reverse _)]; generalize [] = acc
  fun_induction bagInterRev.go with
  | case1 l acc => rfl
  | case2 l acc h => simp
  | case3 a l₁ l₂ acc h₁ h₂ ih => rw [ih, cons_bagInter_of_notMem]; simpa [eraseP?_eq_ite] using h₂
  | case4 a l₁ l₂ acc h l hl ih =>
    simp [eraseP?_eq_ite, ← erase_eq_eraseP'] at hl
    rw [ih, cons_bagInter_of_mem l₁ hl.1]; simp [hl.2]

@[inline] def pwFilterRev (R : α → α → Prop) [DecidableRel R] : List α → List α :=
  foldl (init := []) fun acc x => if ∀ y ∈ acc, R x y then x :: acc else acc

@[simp]
theorem pwFilterRev_eq [DecidableRel R] {l : List α} : l.pwFilterRev R = l.reverse.pwFilter R := by
  simp [pwFilterRev, pwFilter]

@[csimp] theorem rotateLeft_eq_rotate : @rotateLeft = @rotate := by
  funext α l (n : ℕ); simp [rotateLeft, rotate]; match l with
  | [] => simp
  | [a] => simp [Nat.mod_one]
  | a :: b :: _ => simp

def Nat.antidiagonalImpl (n : ℕ) : List (ℕ × ℕ) := ofFn fun (i : Fin (n + 1)) => (i, n - i)

@[csimp] theorem Nat.antidiagonal_eq_antidiagonalImpl : @antidiagonal = @antidiagonalImpl := by
  funext n; simp [antidiagonal, antidiagonalImpl, -ofFn_succ, ofFn_eq_pmap]

end List

/-! ## `Multiset` -/

namespace Multiset

/-- Compiles to a no-op by lifting `List.attachWith`. -/
@[inline] def attachWith (s : Multiset α) (P : α → Prop) (H : ∀ a ∈ s, P a) : Multiset {x // P x} :=
  Quotient.pliftOn s (fun l h => ofList (l.attachWith P (by simpa [h] using H))) fun l l' h h' p =>
    Quot.sound (p.pmap _)

/-- `Multiset.attach` that compiles to a no-op by lifting `List.attach`. -/
@[inline] def attachImpl (s : Multiset α) : Multiset {x // x ∈ s} := s.attachWith (· ∈ s) fun _ => id

@[csimp] theorem attach_eq_attachImpl : @attach = @attachImpl := by
  funext α s; rcases s with ⟨l⟩; rfl

@[inline] def foldlImpl {β : Type v} (f : β → α → β) [RightCommutative f]
    (b : β) (s : Multiset α) : β :=
  Quotient.liftOn s (List.foldl f b) fun _ _ p => p.foldl_eq b

@[csimp] theorem foldl_eq_foldlImpl : @foldl = @foldlImpl := by rfl

@[inline] def foldrImpl {β : Type v} (f : α → β → β) [LeftCommutative f] := foldl (fun x y => f y x)

@[csimp] theorem foldr_eq_foldrImpl : @foldr = @foldrImpl := by funext; apply foldr_swap

@[inline] def foldImpl (op : α → α → α) [Std.Commutative op] [Std.Associative op] := foldl op

@[csimp] theorem fold_eq_foldImpl : @fold = @foldImpl := by
  funext; apply fold_eq_foldl

@[inline] def fold' (op : α → α → α) [Std.Commutative op] [Std.Associative op]
    (s : Multiset α) (H : s ≠ 0) : α :=
  Quotient.pliftOn s (fun l h => l.tail.foldl op (l.head (by simpa [h] using H))) fun l l' h h' p => by
    generalize_proofs hl hl'; clear h h'; induction p with
    | nil => simp
    | @cons a l₁ l₂ p ih => simp; apply p.foldl_eq
    | swap a a' l => simp [Std.Commutative.comm]
    | @trans l₁ l₂ l₃ p p' ih ih' =>
      have : l₂ ≠ [] := fun h => by simp_all
      exact (ih hl this).trans (ih' this hl')

@[simp]
theorem fold'_cons {op : α → α → α} [Std.Commutative op] [Std.Associative op] :
    fold' op (a ::ₘ s) cons_ne_zero = fold op a s := by
  rw [fold_eq_foldl]; rcases s with ⟨l⟩; rfl

/-- `Multiset.add` that uses `List.reverseAux` instead of `List.append`. -/
@[inline] def addImpl (s t : Multiset α) : Multiset α :=
  Quotient.liftOn₂ s t (fun l₁ l₂ => ofList (l₂.reverseAux l₁)) fun s s' t t' p p' => by
    simp; apply List.Perm.append; simp; assumption; assumption

@[csimp] theorem add_eq_addImpl : @Multiset.add = @addImpl := by
  funext α s t; rcases s with ⟨s⟩; rcases t with ⟨t⟩
  simp [Multiset.add, addImpl]; rw [← List.perm_reverse]; simp [List.Perm.append]

def subImpl [DecidableEq α] (s t : Multiset α) : Multiset α :=
  Quotient.liftOn₂ s t (fun l₁ l₂ => ofList (l₂.foldl List.erase l₁)) fun s s' t t' p p' => by
    simpa [← List.diff_eq_foldl] using p.diff p'

@[csimp] theorem sub_eq_subImpl : @Multiset.sub = @subImpl := by
  funext α _ s t; unfold Multiset.sub subImpl; congr; funext l₁ l₂; rw [List.diff_eq_foldl]

def interImpl [DecidableEq α] (s t : Multiset α) : Multiset α :=
  Quotient.liftOn₂ s t (fun l l' => l.bagInterRev l') fun s s' t t' p p' => by simp [p.bagInter p']

@[csimp] theorem inter_eq_interImpl : @inter = @interImpl := by
  funext α _ s t; simp [inter, interImpl]

@[inline] def mapImpl {β : Type v} (f : α → β) (s : Multiset α) : Multiset β :=
  Quotient.liftOn s (fun l => ofList (l.mapRev f)) fun l l' p => by simp; apply p.map

@[csimp] theorem map_eq_mapImpl : @map = @mapImpl := by funext; simp [map, mapImpl]

@[inline] def filterImpl (p : α → Prop) [DecidablePred p] (s : Multiset α) : Multiset α :=
  Quotient.liftOn s (fun l => ofList (l.filterRev fun a => p a)) fun l l' p => by
    simp; apply p.filter

@[csimp] theorem filter_eq_filterImpl : @filter = @filterImpl := by ext; simp [filter, filterImpl]

@[inline] def filterMapImpl {β : Type v} (f : α → Option β) (s : Multiset α) : Multiset β :=
  Quotient.liftOn s (fun l => ofList (l.filterMapRev f)) fun l l' p => by simp; apply p.filterMap

@[csimp] theorem filterMap_eq_filterMapImpl : @filterMap = @filterMapImpl := by
  funext; simp [filterMap, filterMapImpl]

@[to_additive (attr := inline)] def prodImpl [CommMonoid M] : Multiset M → M := fold (· * ·) 1

@[to_additive (attr := csimp)] theorem prod_eq_prodImpl : @prod = @prodImpl := rfl

@[to_additive (attr := inline)] def prodOn [CommMonoid M] (s : Multiset α) (f : α → M) : M :=
  haveI : RightCommutative (· * f ·) := by constructor; intros; apply mul_right_comm
  foldl (· * f ·) 1 s

@[to_additive (attr := simp)]
theorem prodOn_eq_prod_map [CommMonoid M] {f : α → M} : prodOn s f = (s.map f).prod := by
  rw [prodOn, foldl_swap]; induction s using Multiset.induction with
  | empty => rfl
  | cons a s ih => simp [ih, mul_comm]

@[inline] def bindImpl {β : Type v} : Multiset α → (α → Multiset β) → Multiset β := sumOn

@[csimp] theorem bind_eq_bindImpl : @bind = @bindImpl := by funext; simp [bindImpl]; rfl

def productImpl {β : Type v} (s : Multiset α) (t : Multiset β) := s.bind fun a => t.map (Prod.mk a)

@[csimp] theorem product_eq_productImpl : @product = @productImpl := rfl

@[specialize] def sigmaImpl {α : Type*} {σ : α → Type*} (s : Multiset α)
    (t : (a : α) → Multiset (σ a)) := s.bind fun a => (t a).map (Sigma.mk a)

@[csimp] theorem sigma_eq_sigmaImpl : @Multiset.sigma = @sigmaImpl := rfl

@[inline] def disjSumImpl (s : Multiset α) (t : Multiset β) := s.map Sum.inl + t.map Sum.inr

@[csimp] theorem disjSum_eq_disjSumImpl : @disjSum = @disjSumImpl := rfl

def powersetImplAux (l : List α) : Multiset (Multiset α) :=
  l.foldl (init := {0}) fun s a => s.bind fun t => {t, a ::ₘ t}

theorem powersetImplAux_eq {l : List α} : powersetImplAux l = (ofList l).powerset := by
  unfold powersetImplAux; induction l using List.revInduction with
  | nil => rfl
  | concat l a ih =>
    simp [-powerset_coe', ← coe_add, add_comm (ofList l), -cons_coe] at ⊢ ih; rw [ih]

def powersetImpl (s : Multiset α) : Multiset (Multiset α) :=
  Quotient.liftOn s powersetImplAux fun l l' p => by
    simp only [powersetImplAux_eq]; congr 1; exact Quot.sound p

@[csimp] theorem powerset_eq_powersetImpl : @powerset = @powersetImpl := by
  symm; funext α s; rcases s with ⟨l⟩; exact powersetImplAux_eq

def antidiagonalImplAux (l : List α) : Multiset (Multiset α × Multiset α) :=
  l.foldl (init := {(0, 0)}) fun s a => s.bind fun (s, t) => {(s, a::ₘt), (a::ₘs, t)}

theorem antidiagonalImplAux_eq {l : List α} : antidiagonalImplAux l = (ofList l).antidiagonal := by
  unfold antidiagonalImplAux; simp [-antidiagonal_coe']; induction l using List.revInduction with
  | nil => rfl
  | concat l a ih =>
    simp [ih, -antidiagonal_coe', ← coe_add, add_comm (ofList l), -cons_coe]; rfl

def antidiagonalImpl (s : Multiset α) :=
  Quotient.liftOn s antidiagonalImplAux fun l l' p => by
    simp only [antidiagonalImplAux_eq]; congr 1; simpa

@[csimp] theorem antidiagonal_eq_antidiagonalImpl : @antidiagonal = @antidiagonalImpl := by
  symm; funext α s; rcases s with ⟨l⟩; exact antidiagonalImplAux_eq

def powersetCardImplAux : ℕ → List α → Multiset α → Multiset (Multiset α) → Multiset (Multiset α)
| 0,   _,    s, acc => s ::ₘ acc
| _+1, [],   _, acc => acc
| n+1, a::l, s, acc => powersetCardImplAux (n + 1) l s (powersetCardImplAux n l (a ::ₘ s) acc)

theorem powersetCardImplAux_eq {acc : Multiset (Multiset α)} :
    powersetCardImplAux n l s acc = map (s + ·) (powersetCard n l) + acc := by
  fun_induction powersetCardImplAux with
  | case1 l s acc => simp
  | case2 n s acc => simp [powersetCard_zero_right]
  | case3 n a l s acc ih₂ ih₁ => rw [ih₁, ih₂]; simp [← cons_coe, add_assoc]

def powersetCardImpl (n : ℕ) (s : Multiset α) : Multiset (Multiset α) :=
  Quotient.liftOn s (fun l => powersetCardImplAux n l 0 0) fun l l' p => by
    simp [powersetCardImplAux_eq]; congr 1; simpa

@[csimp] theorem powersetCard_eq_powersetCardImpl : @powersetCard = @powersetCardImpl := by
  funext α n s; rcases s with ⟨l⟩; simp [powersetCardImpl, powersetCardImplAux_eq]

@[inline] def dedupImpl [DecidableEq α] (s : Multiset α) : Multiset α :=
  Quotient.liftOn s (fun l => ofList (l.pwFilterRev (· ≠ ·))) fun l l' p => by
    simp; apply List.Perm.dedup; simpa

@[csimp] theorem dedup_eq_dedupImpl : @dedup = @dedupImpl := by
  funext α _ s; simp [dedup, dedupImpl]; congr; funext l
  apply Quot.sound; apply List.Perm.dedup; simp

@[inline] def ndunionImpl [DecidableEq α] (s t : Multiset α) : Multiset α :=
  Quotient.liftOn₂ s t (fun l₁ l₂ => ofList <| l₁.foldl (flip List.insert) l₂) fun s s' t t' p p' => by
    unfold flip; simp [← List.foldr_reverse, ← List.union_def]; apply List.Perm.union <;> simpa

@[csimp] theorem ndunion_eq_ndunionImpl : @ndunion = @ndunionImpl := by
  funext α _ s t; simp [ndunion, ndunionImpl]; congr; funext l₁ l₂; unfold flip
  simp [← List.foldr_reverse, ← List.union_def]; apply List.Perm.union_right; simp

def Nat.antidiagonalImpl (n : ℕ) := ofList (List.Nat.antidiagonal n)

@[csimp] theorem Nat.antidiagonal_eq_antidiagonalImpl : @antidiagonal = @antidiagonalImpl := rfl

end Multiset

/-! ## `Finset` -/

namespace Finset

@[inline] def attachWith (s : Finset α) (P : α → Prop) (H : ∀ a ∈ s, P a) : Finset {x // P x} where
  val := s.val.attachWith P H
  nodup := by
    rcases s with ⟨⟨l⟩, hl⟩; change (Multiset.ofList _).Nodup; simp at hl; apply hl.pmap; simp

@[simp] theorem mem_attachWith : x ∈ attachWith s P H ↔ x.val ∈ s := by
  rcases s with ⟨⟨l⟩⟩; apply l.mem_attachWith

@[inline] def attachImpl (s : Finset α) : Finset s := s.attachWith _ fun _ => id

@[csimp] theorem attach_eq_attachImpl : @attach = @attachImpl := by ext; simp [attachImpl]

@[inline] def attachFinImpl (s : Finset ℕ) {n} (h : ∀ m ∈ s, m < n) : Finset (Fin n) where
  val := Quotient.pliftOn s.val (fun l hl => l.attachFin fun a ha => by
      simp [← mem_val, hl] at h; exact h a ha)
    fun l l' h h' p => by simp [List.attachFin]; apply List.Perm.pmap; exact p
  nodup := by
    rcases s with ⟨⟨l⟩, hl⟩; simp at ⊢ hl; change (Multiset.ofList _).Nodup
    simp [List.attachFin]; apply hl.pmap; simp

@[csimp] theorem attachFin_eq_attachFinImpl : @attachFin = @attachFinImpl := by
  funext s n f; rcases s with ⟨⟨l⟩, _⟩; rfl

@[inline] def foldr (f : α → β → β) [LeftCommutative f] (b : β) (s : Finset α) := s.val.foldr f b

@[simp]
theorem foldr_empty [LeftCommutative f] : foldr f b ∅ = b := rfl

@[simp]
theorem foldr_cons [LeftCommutative f] (h : a ∉ s) :
    foldr f b (cons a s h) = f a (foldr f b s) := by simp [foldr]

@[simp]
theorem foldr_insert [DecidableEq α] {s : Finset α} [LeftCommutative f] (h : a ∉ s) :
    foldr f b (insert a s) = f a (foldr f b s) := by rw [← cons_eq_insert a s h, foldr_cons]

@[inline] def foldImpl {α β : Type*} (op : β → β → β) [Std.Commutative op] [Std.Associative op]
    (b : β) (f : α → β) (s : Finset α) : β :=
  haveI : LeftCommutative (fun a b => op (f a) b) := ⟨by intros; apply LeftCommutative.left_comm⟩
  s.foldr (fun a b => op (f a) b) b

@[csimp] theorem fold_eq_foldImpl : @fold = @foldImpl := by
  funext α β op _ _ b f s; unfold foldImpl; induction s using cons_induction with
  | empty => rfl
  | cons a s h ih => simp [ih]

/-- `fold' op f s` folds `op` over the `f`-image of `s` using one of its elements as a starting
point, given a proof of non-emptiness. -/
@[inline] def fold' (op : β → β → β) [Std.Commutative op] [Std.Associative op] (f : α → β)
    (s : Finset α) (H : s.Nonempty) : β :=
  Quotient.pliftOn s.val (fun l h => l.tail.foldl (op · <| f ·) (f (l.head (by
    contrapose H; simp_all; rwa [← val_eq_zero])))) fun l l' hl hl' p => by
    generalize_proofs h h'; clear hl hl'; induction p with
    | nil => rfl
    | cons a p ih => apply p.foldl_eq'; intros; apply RightCommutative.right_comm
    | swap a a' l => dsimp; congr 1; apply Std.Commutative.comm
    | @trans l₁ l₂ l₃ p p' ih ih' =>
      have : l₂ ≠ [] := by contrapose h; simp_all
      exact (ih h this).trans (ih' this h')

@[simp]
theorem fold'_singleton {op : β → β → β} [Std.Commutative op] [Std.Associative op] (f : α → β) :
    fold' op f {a} (singleton_nonempty a) = f a := rfl

@[simp]
theorem fold'_cons {op : β → β → β} [Std.Commutative op] [Std.Associative op]
    (H : s.Nonempty) (f : α → β) :
    fold' op f (cons a s h) (cons_nonempty h) = op (f a) (fold' op f s H) := by
  rcases H.exists_cons_eq with ⟨⟨⟨l⟩, hl⟩, b, hb, rfl⟩
  change List.foldl _ _ _ = op _ (List.foldl _ _ _); simp; clear * -
  induction l using List.revInduction with
  | nil => rfl
  | concat l x ih => simp [ih]; apply Std.Associative.assoc

@[simp]
theorem fold'_insert [DecidableEq α] {op : β → β → β} [Std.Commutative op] [Std.Associative op]
    (h : a ∉ s) (H : s.Nonempty) (f : α → β) :
    fold' op f (insert a s) (insert_nonempty a s) = op (f a) (fold' op f s H) := by
    rw! [← cons_eq_insert a s h, fold'_cons]; rfl

@[to_dual (attr := inline)]
def supImpl [SemilatticeSup β] [OrderBot β] (s : Finset α) (f : α → β) :=
  s.fold (· ⊔ · : β → β → β) ⊥ f

@[to_dual (attr := csimp)] theorem sup_eq_supImpl : @sup = @supImpl := rfl

@[to_dual (attr := inline)]
def sup'Impl [SemilatticeSup β] (s : Finset α) (H : s.Nonempty) (f : α → β) :=
  s.fold' (· ⊔ · : β → β → β) f H

@[to_dual (attr := csimp)] theorem sup'_eq_sup'Impl : @sup' = @sup'Impl := by
  funext β α _ s H f; unfold sup'Impl; induction H using Nonempty.cons_induction with
  | singleton => simp
  | cons a s h H ih => simp [H, ih]

@[inline] def disjUnionImpl (s t : Finset α) (h : Disjoint s t) : Finset α where
  val := s.val + t.val
  nodup := Multiset.nodup_add.2 ⟨s.nodup, t.nodup, disjoint_val.2 h⟩

@[csimp] theorem disjUnion_eq_disjUnionImpl : @disjUnion = @disjUnionImpl := rfl

@[instance_reducible] def instInterImpl [DecidableEq α] : Inter (Finset α) where
  inter s t := ⟨t.val.ndinter s.val, t.nodup.ndinter s.val⟩

@[csimp] theorem inter_eq_interImpl : @instInter = @instInterImpl := by
  unfold instInter instInterImpl; congr! 6; rw [← inter_val_nd, ← inter_val_nd, inter_comm]

@[inline] def mapOn (s : Finset α) (f : α → β) (h : Set.InjOn f s) : Finset β where
  val := s.val.map f
  nodup := s.nodup.map_on h

@[simp] theorem mem_mapOn : b ∈ mapOn s f h ↔ ∃ a ∈ s, f a = b := by simp [mapOn]

@[inline] def mapImpl (f : α ↪ β) (s : Finset α) : Finset β := s.mapOn f f.injective.injOn

@[csimp] theorem map_eq_mapImpl : @map = @mapImpl := by ext; simp [mapImpl]

@[inline] def filterMapImpl (f : α → Option β) (s : Finset α)
    (f_inj : ∀ a a' : α, ∀ b ∈ f a, b ∈ f a' → a = a') : Finset β where
  val := s.val.filterMap f
  nodup := s.nodup.filterMap f f_inj

@[csimp] theorem filterMap_eq_filterMapImpl : @filterMap = @filterMapImpl := rfl

@[inline] def subtypeImpl (p : α → Prop) [DecidablePred p] (s : Finset α) : Finset {x // p x} :=
  (s.filter p).attachWith p (by simp)

end Finset

/-! ## `Nat` -/

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

/-
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
-/
