import Mathlib.Data.Fintype.Card

/-! # The `scan` and `scan'` combinators

The main difference between the unprimed `scan` and primed `scan'` combinators is that
the former emit the seed value `init` first (meaning they emit one more value than the underlying
iterator), while the latter are _marginally_ faster and simpler to reason about. -/

namespace Std

/-- The internal state of the `IterM.scan'` iterator. -/
@[unbox]
structure Iterators.Types.Scan' (α : Type w) {β γ : Type w} (m : Type w → Type w')
    (n : Type w → Type w'') (lift : ⦃α : Type w⦄ → m α → n α) (f : γ → β → PostconditionT n γ) where
  inner : IterM (α := α) m β
  last : γ

/-- The internal state of the `IterM.scan` iterator. -/
@[unbox]
structure Iterators.Types.Scan (α : Type w) {β γ : Type w} (m : Type w → Type w')
    (n : Type w → Type w'') (lift : ⦃α : Type w⦄ → m α → n α) (f : γ → β → PostconditionT n γ) where
  inner : IterM (α := α) m β
  last : γ
  emittedInit : Bool

variable {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}

open Iterators Types

/-- *Note: This is a very general combinator that requires an advanced understanding of monads,
dependent types and termination proofs. The variants `scan'` and `scanM'` are easier to use and
sufficient for most use cases.*

If `it` is an iterator, then `it.scanWithPostcondition' f init` is another iterator that folds a
monadic function `f` over `it` starting with `init` and emits the partial results. As opposed to
unprimed `it.scanWithPostcondition f init`, it does not emit `init` itself.

`f` is expected to return `PostconditionT n _`. The base iterator `it` being monadic in
`m`, `n` can be different from `m`, but `it.scanWithPostcondition' f` expects a `MonadLiftT m n`
instance. The `PostconditionT` transformer allows the caller to intrinsically prove properties about
`f`'s return value in the monad `n`, enabling termination proofs depending on the specific behavior
of `f`.

**Marble diagram (without monadic effects):**
```text
it                           ---a --b -c --⊥
it.scanWithPostcondition'    ---a'--b'-c'--⊥
```
(given that `f init a = pure a'`, `f a' b = pure b'`, and `f b' c = pure c'`)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

For certain mapping functions `f`, the resulting iterator will be finite (or productive) even
though no `Finite` (or `Productive`) instance is provided. For example, if `f` is an `ExceptT`
monad and will always fail, then `it.scanWithPostcondition'` will be finite even if `it` isn't.

In such situations, the missing instances can be proved manually if the postcondition bundled in
the `PostconditionT n` monad is strong enough. In the given example, a suitable postcondition might
be `fun _ => False`.

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f`.
-/
@[always_inline, inline]
def IterM.scanWithPostcondition' [Iterator α m β] [Monad n] [MonadLiftT m n]
    (f : γ → β → PostconditionT n γ) (init : γ) (it : IterM (α := α) m β) :
    IterM (α := Scan' α m n (fun _ => liftM) f) n γ := ⟨⟨it, init⟩⟩

/-- If `it` is an iterator, then `it.scanM' f init` is another iterator that folds a monadic
function `f` over `it` starting with `init` and emits the partial results. As opposed to
unprimed `it.scanM f init`, it does not emit `init` itself.

The base iterator `it` being monadic in `m`, `f` can return values in any monad `n` for which a
`MonadLiftT m n` instance is available.

If `f` is pure, then the simpler variant `it.scan'` can be used instead.

**Marble diagram (without monadic effects):**
```text
it           ---a --b -c --⊥
it.scanM'    ---a'--b'-c'--⊥
```
(given that `f init a = pure a'`, `f a' b = pure b'`, and `f b' c = pure c'`)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

For certain mapping functions `f`, the resulting iterator will be finite (or productive) even
though no `Finite` (or `Productive`) instance is provided. For example, if `f` is an `ExceptT`
monad and will always fail, then `it.scanM'` will be finite even if `it` isn't. In such cases, the
termination proof needs to be done manually.

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f`.
-/
@[always_inline, inline]
def IterM.scanM' [Iterator α m β] [Monad n] [MonadAttach n] [MonadLiftT m n]
    (f : γ → β → n γ) (init : γ) (it : IterM (α := α) m β) :=
  it.scanWithPostcondition' (fun c b => .attachLift (f c b)) init

/-- If `it` is an iterator, then `it.scan' f init` is another iterator that folds a function `f`
over `it` starting with `init` and emits the partial results. As opposed to unprimed
`it.scan f init`, it does not emit `init` itself.

In situations where `f` is monadic, use `it.scanM'` instead.

**Marble diagram:**
```text
it          ---a --b -c --⊥
it.scan'    ---a'--b'-c'--⊥
```
(given that `f init a = a'`, `f a' b = b'`, and `f b' c = c'`)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f`.
-/
@[always_inline, inline]
def IterM.scan' [Iterator α m β] [Monad m] (f : γ → β → γ) (init : γ) (it : IterM (α := α) m β) :=
    it.scanWithPostcondition' (n := m) (fun c b => pure (f c b)) init

/-- *Note: This is a very general combinator that requires an advanced understanding of monads,
dependent types and termination proofs. The variants `scan` and `scanM` are easier to use and
sufficient for most use cases.*

If `it` is an iterator, then `it.scanWithPostcondition f init` is another iterator that folds a
monadic function `f` over `it` and emits the partial results, beginning with `init`.

`f` is expected to return `PostconditionT n _`. The base iterator `it` being monadic in
`m`, `n` can be different from `m`, but `it.scanWithPostcondition f` expects a `MonadLiftT m n`
instance. The `PostconditionT` transformer allows the caller to intrinsically prove properties about
`f`'s return value in the monad `n`, enabling termination proofs depending on the specific behavior
of `f`.

**Marble diagram (without monadic effects):**
```text
it                              ---a --b -c --⊥
it.scanWithPostcondition    init---a'--b'-c'--⊥
```
(given that `f init a = pure a'`, `f a' b = pure b'`, and `f b' c = pure c'`)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

For certain mapping functions `f`, the resulting iterator will be finite (or productive) even
though no `Finite` (or `Productive`) instance is provided. For example, if `f` is an `ExceptT`
monad and will always fail, then `it.scanWithPostcondition` will be finite even if `it` isn't.

In such situations, the missing instances can be proved manually if the postcondition bundled in
the `PostconditionT n` monad is strong enough. In the given example, a suitable postcondition might
be `fun _ => False`.

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f`.
-/
@[always_inline, inline]
def IterM.scanWithPostcondition [Iterator α m β] [Monad n] [MonadLiftT m n]
    (f : γ → β → PostconditionT n γ) (init : γ) (it : IterM (α := α) m β) :
    IterM (α := Scan α m n (fun _ => liftM) f) n γ := ⟨⟨it, init, false⟩⟩

/-- If `it` is an iterator, then `it.scanM f init` is another iterator that folds a monadic
function `f` over `it` and emits the partial results, beginning with `init`.

The base iterator `it` being monadic in `m`, `f` can return values in any monad `n` for which a
`MonadLiftT m n` instance is available.

If `f` is pure, then the simpler variant `it.scan` can be used instead.

**Marble diagram (without monadic effects):**
```text
it              ---a --b -c --⊥
it.scanM    init---a'--b'-c'--⊥
```
(given that `f init a = pure a'`, `f a' b = pure b'`, and `f b' c = pure c'`)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

For certain mapping functions `f`, the resulting iterator will be finite (or productive) even
though no `Finite` (or `Productive`) instance is provided. For example, if `f` is an `ExceptT`
monad and will always fail, then `it.scanM` will be finite even if `it` isn't. In such cases, the
termination proof needs to be done manually.

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f`.
-/
@[always_inline, inline]
def IterM.scanM [Iterator α m β] [Monad n] [MonadAttach n] [MonadLiftT m n]
    (f : γ → β → n γ) (init : γ) (it : IterM (α := α) m β) :=
  it.scanWithPostcondition (fun c b => .attachLift (f c b)) init

/-- If `it` is an iterator, then `it.scan f init` is another iterator that folds a function `f`
over `it` and emits the partial results, beginning with `init`.

In situations where `f` is monadic, use `it.scanM` instead.

**Marble diagram:**
```text
it             ---a --b -c --⊥
it.scan    init---a'--b'-c'--⊥
```
(given that `f init a = a'`, `f a' b = b'`, and `f b' c = c'`)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f`.
-/
@[always_inline, inline]
def IterM.scan [Iterator α m β] [Monad m] (f : γ → β → γ) (init : γ) (it : IterM (α := α) m β) :=
    it.scanWithPostcondition (n := m) (fun c b => pure (f c b)) init

variable {lift : ⦃α : Type w⦄ → m α → n α} {f : γ → β → PostconditionT n γ}

/-- Convert a `Scan'`-based iterator to a `Scan`-based iterator. This is mostly reserved for
advanced use cases, as well as representing intermediate states of `Scan`-based iterators. -/
def IterM.toScan : IterM (α := Scan' α m n lift f) n γ → IterM (α := Scan α m n lift f) n γ
| ⟨⟨it, last⟩⟩ => ⟨⟨it, last, true⟩⟩

namespace Iterators.Types

inductive Scan'.PlausibleStep [Iterator α m β] (it : IterM (α := Scan' α m n lift f) n γ) :
    IterStep (IterM (α := Scan' α m n lift f) n γ) γ → Prop where
  | yield : ∀ {it' out out'}, it.internalState.inner.IsPlausibleStep (.yield it' out) →
      (f it.internalState.last out).Property out' → PlausibleStep it (.yield ⟨⟨it', out'⟩⟩ out')
  | skip : ∀ {it'}, it.internalState.inner.IsPlausibleStep (.skip it') →
      PlausibleStep it (.skip ⟨⟨it', it.internalState.last⟩⟩)
  | done : it.internalState.inner.IsPlausibleStep .done → PlausibleStep it .done

instance Scan'.instIterator [Iterator α m β] [Monad n] : Iterator (Scan' α m n lift f) n γ where
  IsPlausibleStep := Scan'.PlausibleStep
  step it :=
    letI : MonadLift m n := ⟨lift (α := _)⟩
    do match (← it.internalState.inner.step).inflate with
    | .yield _ out h =>
      let ⟨_, h'⟩ ← (f it.internalState.last out).operation
      pure (.deflate (.yield _ _ (.yield h h')))
    | .skip _ h => pure (.deflate (.skip _ (.skip h)))
    | .done h => pure (.deflate (.done (.done h)))

private def Scan'.finitenessRelation [Iterator α m β] [Finite α m] [Monad n] :
    FinitenessRelation (Scan' α m n lift f) n where
  Rel := InvImage WellFoundedRelation.rel (fun it => it.internalState.inner.finitelyManySteps)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation h := by
    rcases h with ⟨_, hs, h⟩; cases h <;> cases hs
    case yield h _ => exact IterM.TerminationMeasures.Finite.rel_of_yield h
    case skip h => exact IterM.TerminationMeasures.Finite.rel_of_skip h

instance Scan'.instFinite [Iterator α m β] [Finite α m] [Monad n] : Finite (Scan' α m n lift f) n :=
  .of_finitenessRelation finitenessRelation

private def Scan'.productivenessRelation [Iterator α m β] [Productive α m] [Monad n] :
    ProductivenessRelation (Scan' α m n lift f) n where
  Rel := InvImage WellFoundedRelation.rel (fun it => it.internalState.inner.finitelyManySkips)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation h := by cases h; exact IterM.TerminationMeasures.Productive.rel_of_skip ‹_›

instance Scan'.instProductive [Iterator α m β] [Productive α m] [Monad n] :
    Productive (Scan' α m n lift f) n := .of_productivenessRelation productivenessRelation

instance Scan'.instIteratorLoop {o : Type x → Type x'} [Iterator α m β] [Monad n] [Monad o] :
    IteratorLoop (Scan' α m n lift f) n o := .defaultImplementation

inductive Scan.PlausibleStep [Iterator α m β] (it : IterM (α := Scan α m n lift f) n γ) :
    IterStep (IterM (α := Scan α m n lift f) n γ) γ → Prop where
  | first : it.internalState.emittedInit = false →
      PlausibleStep it (.yield {it with internalState.emittedInit := true} it.internalState.last)
  | yield : ∀ {it' out out'}, it.internalState.emittedInit →
      it.internalState.inner.IsPlausibleStep (.yield it' out) →
      (f it.internalState.last out).Property out' →
      PlausibleStep it (.yield ⟨⟨it', out', true⟩⟩ out')
  | skip : ∀ {it'}, it.internalState.emittedInit →
      it.internalState.inner.IsPlausibleStep (.skip it') →
      PlausibleStep it (.skip ⟨⟨it', it.internalState.last, true⟩⟩)
  | done : it.internalState.emittedInit → it.internalState.inner.IsPlausibleStep .done →
      PlausibleStep it .done

instance Scan.instIterator [Iterator α m β] [Monad n] : Iterator (Scan α m n lift f) n γ where
  IsPlausibleStep := Scan.PlausibleStep
  step it := match hi : it.internalState.emittedInit with
  | false => pure (.deflate (.yield _ _ (.first hi)))
  | true =>
    letI : MonadLift m n := ⟨lift (α := _)⟩
    do match (← it.internalState.inner.step).inflate with
    | .yield _ out h =>
      let ⟨_, h'⟩ ← (f it.internalState.last out).operation
      pure (.deflate (.yield _ _ (.yield hi h h')))
    | .skip _ h => pure (.deflate (.skip _ (.skip hi h)))
    | .done h => pure (.deflate (.done (.done hi h)))

private def Scan.finitenessRelation [Iterator α m β] [Finite α m] [Monad n] :
    FinitenessRelation (Scan α m n lift f) n where
  Rel := InvImage
    (Prod.Lex WellFoundedRelation.rel (· > ·))
    (fun it => (it.internalState.inner.finitelyManySteps, it.internalState.emittedInit))
  wf := InvImage.wf _ (WellFoundedRelation.wf.prod_lex wellFounded_gt)
  subrelation h := by
    rcases h with ⟨_, hs, h⟩; cases h <;> cases hs
    case first hi => apply Prod.Lex.right; simp [hi]
    case yield h _ =>
      exact Prod.Lex.left _ _ (IterM.TerminationMeasures.Finite.rel_of_yield h)
    case skip h =>
      exact Prod.Lex.left _ _ (IterM.TerminationMeasures.Finite.rel_of_skip h)

instance Scan.instFinite [Iterator α m β] [Finite α m] [Monad n] : Finite (Scan α m n lift f) n :=
  .of_finitenessRelation finitenessRelation

private def Scan.productivenessRelation [Iterator α m β] [Productive α m] [Monad n] :
    ProductivenessRelation (Scan α m n lift f) n where
  Rel := InvImage WellFoundedRelation.rel (fun it => it.internalState.inner.finitelyManySkips)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation h := by cases h; exact IterM.TerminationMeasures.Productive.rel_of_skip ‹_›

instance Scan.instProductive [Iterator α m β] [Productive α m] [Monad n] :
    Productive (Scan α m n lift f) n := .of_productivenessRelation productivenessRelation

/-- TODO: this one could be optimized to use `scan'` internally. -/
instance Scan.instIteratorLoop {o : Type x → Type x'} [Iterator α m β] [Monad n] [Monad o] :
    IteratorLoop (Scan α m n lift f) n o := .defaultImplementation

end Iterators.Types

/-- *Note: This is a very general combinator that requires an advanced understanding of monads,
dependent types and termination proofs. The variants `scan'` and `scanM'` are easier to use and
sufficient for most use cases.*

If `it` is an iterator, then `it.scanWithPostcondition' f init` is another iterator that folds a
monadic function `f` over `it` starting with `init` and emits the partial results. As opposed to
unprimed `it.scanWithPostcondition f init`, it does not emit `init` itself.

`f` is expected to return `PostconditionT m _`, where `m` is an arbitrary monad. The
`PostconditionT` transformer allows the caller to intrinsically prove properties about `f`'s return
value in the monad `m`, enabling termination proofs depending on the specific behavior of `f`.

**Marble diagram (without monadic effects):**
```text
it                           ---a --b -c --⊥
it.scanWithPostcondition'    ---a'--b'-c'--⊥
```
(given that `f init a = pure a'`, `f a' b = pure b'`, and `f b' c = pure c'`)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

For certain mapping functions `f`, the resulting iterator will be finite (or productive) even
though no `Finite` (or `Productive`) instance is provided. For example, if `f` is an `ExceptT`
monad and will always fail, then `it.scanWithPostcondition'` will be finite even if `it` isn't.

In such situations, the missing instances can be proved manually if the postcondition bundled in
the `PostconditionT n` monad is strong enough. In the given example, a suitable postcondition might
be `fun _ => False`.

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f`.
-/
def Iter.scanWithPostcondition' [Iterator α Id β] [Monad m] (f : γ → β → PostconditionT m γ)
    (init : γ) (it : Iter (α := α) β) := it.toIterM.scanWithPostcondition' f init

/-- If `it` is an iterator, then `it.scanM' f init` is another iterator that folds a monadic
function `f` over `it` starting with `init` and emits the partial results. As opposed to
unprimed `it.scanM f init`, it does not emit `init` itself.

If `f` is pure, then the simpler variant `it.scan'` can be used instead.

**Marble diagram (without monadic effects):**
```text
it           ---a --b -c --⊥
it.scanM'    ---a'--b'-c'--⊥
```
(given that `f init a = pure a'`, `f a' b = pure b'`, and `f b' c = pure c'`)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

For certain mapping functions `f`, the resulting iterator will be finite (or productive) even
though no `Finite` (or `Productive`) instance is provided. For example, if `f` is an `ExceptT`
monad and will always fail, then `it.scanM'` will be finite even if `it` isn't. In such cases, the
termination proof needs to be done manually.

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f`.
-/
@[always_inline, inline]
def Iter.scanM' [Iterator α Id β] [Monad m] [MonadAttach m] (f : γ → β → m γ) (init : γ)
    (it : Iter (α := α) β) := it.toIterM.scanM' f init

/-- If `it` is an iterator, then `it.scan' f init` is another iterator that folds a function `f`
over `it` starting with `init` and emits the partial results. As opposed to unprimed
`it.scan f init`, it does not emit `init` itself.

In situations where `f` is monadic, use `it.scanM'` instead.

**Marble diagram:**
```text
it          ---a --b -c --⊥
it.scan'    ---a'--b'-c'--⊥
```
(given that `f init a = a'`, `f a' b = b'`, and `f b' c = c'`)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f`.
-/
@[always_inline, inline]
def Iter.scan' [Iterator α Id β] (f : γ → β → γ) (init : γ) (it : Iter (α := α) β) :=
  (it.toIterM.scan' f init).toIter

/-- *Note: This is a very general combinator that requires an advanced understanding of monads,
dependent types and termination proofs. The variants `scan` and `scanM` are easier to use and
sufficient for most use cases.*

If `it` is an iterator, then `it.scanWithPostcondition f init` is another iterator that folds a
monadic function `f` over `it` and emits the partial results, beginning with `init`.

`f` is expected to return `PostconditionT m _`, where `m` is an arbitrary monad. The
`PostconditionT` transformer allows the caller to intrinsically prove properties about `f`'s return
value in the monad `m`, enabling termination proofs depending on the specific behavior of `f`.

**Marble diagram (without monadic effects):**
```text
it                              ---a --b -c --⊥
it.scanWithPostcondition    init---a'--b'-c'--⊥
```
(given that `f init a = pure a'`, `f a' b = pure b'`, and `f b' c = pure c'`)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

For certain mapping functions `f`, the resulting iterator will be finite (or productive) even
though no `Finite` (or `Productive`) instance is provided. For example, if `f` is an `ExceptT`
monad and will always fail, then `it.scanWithPostcondition` will be finite even if `it` isn't.

In such situations, the missing instances can be proved manually if the postcondition bundled in
the `PostconditionT n` monad is strong enough. In the given example, a suitable postcondition might
be `fun _ => False`.

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f`.
-/
def Iter.scanWithPostcondition [Iterator α Id β] [Monad m] (f : γ → β → PostconditionT m γ)
    (init : γ) (it : Iter (α := α) β) := it.toIterM.scanWithPostcondition f init

/-- If `it` is an iterator, then `it.scanM f init` is another iterator that folds a monadic
function `f` over `it` and emits the partial results, beginning with `init`.

If `f` is pure, then the simpler variant `it.scan` can be used instead.

**Marble diagram (without monadic effects):**
```text
it              ---a --b -c --⊥
it.scanM    init---a'--b'-c'--⊥
```
(given that `f init a = pure a'`, `f a' b = pure b'`, and `f b' c = pure c'`)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

For certain mapping functions `f`, the resulting iterator will be finite (or productive) even
though no `Finite` (or `Productive`) instance is provided. For example, if `f` is an `ExceptT`
monad and will always fail, then `it.scanM` will be finite even if `it` isn't. In such cases, the
termination proof needs to be done manually.

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f`.
-/
@[always_inline, inline]
def Iter.scanM [Iterator α Id β] [Monad m] [MonadAttach m] (f : γ → β → m γ) (init : γ)
    (it : Iter (α := α) β) := it.toIterM.scanM f init

/-- If `it` is an iterator, then `it.scan f init` is another iterator that folds a function `f`
over `it` and emits the partial results, beginning with `init`.

In situations where `f` is monadic, use `it.scanM` instead.

**Marble diagram:**
```text
it             ---a --b -c --⊥
it.scan    init---a'--b'-c'--⊥
```
(given that `f init a = a'`, `f a' b = b'`, and `f b' c = c'`)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f`.
-/
@[always_inline, inline]
def Iter.scan [Iterator α Id β] (f : γ → β → γ) (init : γ) (it : Iter (α := α) β) :=
  (it.toIterM.scan f init).toIter

/-- Convert a `Scan'`-based iterator to a `Scan`-based iterator. This is mostly reserved for
advanced use cases, as well as representing intermediate states of `Scan`-based iterators. -/
def Iter.toScan : Iter (α := Scan' α m n lift f) γ → Iter (α := Scan α m n lift f) γ
| ⟨⟨it, last⟩⟩ => ⟨⟨it, last, true⟩⟩
