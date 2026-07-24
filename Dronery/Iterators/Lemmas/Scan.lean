import Dronery.Iterators.Scan
import Batteries.Data.Array.Scan

open Std Iterators

variable {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}

namespace Std.IterM

variable [Iterator α m β] {it : IterM (α := α) m β} {init : γ}

theorem step_scanWithPostcondition {f : γ → β → PostconditionT n γ} [Monad n] [MonadLiftT m n] :
    (it.scanWithPostcondition f init).step = (do
      match (← it.step).inflate with
      | .yield it' out h => do
        let out' ← (f init out).operation
        pure (.deflate (.yield (it'.scanWithPostcondition f out') out' (.yield h out'.2)))
      | .skip it' h => pure (.deflate (.skip (it'.scanWithPostcondition f init) (.skip h)))
      | .done h => pure (.deflate (.done (.done h)))) := by
  apply bind_congr; intro step; match step.inflate with
  | .yield it' out h => rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem step_scanM {f : γ → β → n γ} [Monad n] [MonadAttach n] [MonadLiftT m n] :
    (it.scanM f init).step = (do
      match (← it.step).inflate with
      | .yield it' out h => do
        let out' ← MonadAttach.attach (f init out)
        pure (.deflate (.yield (it'.scanM f out') out' (.yield h out'.2)))
      | .skip it' h => pure (.deflate (.skip (it'.scanM f init) (.skip h)))
      | .done h => pure (.deflate (.done (.done h)))) := by
  apply bind_congr; intro step; match step.inflate with
  | .yield it' out h => rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem step_scan [Monad m] [LawfulMonad m] :
    (it.scan f init).step = (do
      match (← it.step).inflate with
      | .yield it' out h => do
        letI out' := f init out
        pure (.deflate (.yield (it'.scan f out') out' (.yield h rfl)))
      | .skip it' h => pure (.deflate (.skip (it'.scan f init) (.skip h)))
      | .done h => pure (.deflate (.done (.done h)))) := by
  apply bind_congr; intro step; match step.inflate with
  | .yield it' out h => simp; rfl
  | .skip it' h => rfl
  | .done h => rfl

@[simp]
theorem toList_scan [Finite α m] [Monad m] [LawfulMonad m] :
    (it.scan f init).toList = (fun l => (l.scanl f init).tail) <$> it.toList := by
  induction it using IterM.inductSteps generalizing init
  rename_i it ihy ihs
  rw [toList_eq_match_step, toList_eq_match_step]
  simp only [bind_pure_comp, map_bind]
  rw [step_scan]
  simp only [bind_assoc, map_eq_pure_bind]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp; rw [ihy ‹_›, Functor.map_map]; apply map_congr
    intro l; rw [← List.cons_head_tail (List.scanl_ne_nil)]; simp
  · simp; exact ihs ‹_›
  · simp

@[simp]
theorem toListRev_scan [Finite α m] [Monad m] [LawfulMonad m] :
    (it.scan f init).toListRev = (fun l => (l.scanr (flip f) init).dropLast) <$> it.toListRev := by
  simp [toListRev_eq]

@[simp]
theorem toArray_scan [Finite α m] [Monad m] [LawfulMonad m] :
    (it.scan f init).toArray = (fun bs => (bs.scanl f init).drop 1) <$> it.toArray := by
  simp [← toArray_toList, -List.size_toArray, ← List.toArray_scanl]; congr
  funext l; simp; apply List.take_length.symm.trans; simp

end IterM

namespace Iter

variable [Iterator α Id β] {it : Iter (α := α) β} {init : γ}

theorem step_scanWithPostcondition {f : γ → β → PostconditionT m γ} [Monad m] [LawfulMonad m] :
    (it.scanWithPostcondition f init).step =
      match it.step with
      | .yield it' out h => do
        let out' ← (f init out).operation
        pure (.deflate (.yield (it'.scanWithPostcondition f out') out' (.yield h out'.2)))
      | .skip it' h => pure (.deflate (.skip (it'.scanWithPostcondition f init) (.skip h)))
      | .done h => pure (.deflate (.done (.done h))) := by
  simp only [scanWithPostcondition, IterM.step_scanWithPostcondition, step]
  simp only [liftM, monadLift, pure_bind]
  match it.toIterM.step.inflate with
  | .yield it' out h => rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem step_scanM {f : γ → β → m γ} [Monad m] [MonadAttach m] [LawfulMonad m] :
    (it.scanM f init).step =
      match it.step with
      | .yield it' out h => do
        let out' ← MonadAttach.attach (f init out)
        pure (.deflate (.yield (it'.scanM f out') out' (.yield h out'.2)))
      | .skip it' h => pure (.deflate (.skip (it'.scanM f init) (.skip h)))
      | .done h => pure (.deflate (.done (.done h))) := by
  simp only [scanM, IterM.step_scanM, step]
  simp only [liftM, monadLift, pure_bind]
  match it.toIterM.step.inflate with
  | .yield it' out h => rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem step_scan : (it.scan f init).step =
      match it.step with
      | .yield it' out h =>
        letI out' := f init out
        .yield (it'.scan f out') out' (.yield h rfl)
      | .skip it' h => .skip (it'.scan f init) (.skip h)
      | .done h => .done (.done h) := by
  apply Subtype.ext
  simp only [scan, step, toIterM_toIter, IterM.step_scan, Id.run_bind]
  match it.toIterM.step.inflate with
  | .yield it' out h => simp
  | .skip it' h => simp
  | .done h => simp

@[simp]
theorem toList_scanWithPostcondition {f : γ → β → PostconditionT m γ} [Finite α Id] [Monad m]
    [LawfulMonad m] : (it.scanWithPostcondition f init).toList =
    List.tail <$> it.toList.scanlM (fun c b => (f c b).run) init := by
  induction it using Iter.inductSteps generalizing init
  rename_i it ihy ihs
  rw [IterM.toList_eq_match_step, toList_eq_match_step]
  simp only [bind_pure_comp]
  rw [step_scanWithPostcondition]
  cases it.step using PlausibleIterStep.casesOn
  · simp; rw [PostconditionT.run]; simp
    apply bind_congr; intro out'
    rw [ihy ‹_›]; simp
    rename_i it' _ _; generalize it'.toList = l
    induction l <;> simp
  · simp; exact ihs ‹_›
  · simp

@[simp]
theorem toList_scanM {f : γ → β → m γ} [Finite α Id] [Monad m] [MonadAttach m] [LawfulMonad m]
    [WeaklyLawfulMonadAttach m] :
    (it.scanM f init).toList = List.tail <$> it.toList.scanlM f init := by
  change (it.scanWithPostcondition _ init).toList = _
  simp

@[simp]
theorem toList_scan [Finite α Id] : (it.scan f init).toList = (it.toList.scanl f init).tail := by
  rw [scan, IterM.toList_toIter, IterM.toList_scan]; rfl

@[simp]
theorem toListRev_scanWithPostcondition {f : γ → β → PostconditionT m γ} [Finite α Id] [Monad m]
    [LawfulMonad m] : (it.scanWithPostcondition f init).toListRev =
    List.dropLast <$> it.toListRev.scanrM (fun b c => (f c b).run) init := by
  simp [IterM.toListRev_eq, toListRev_eq]; rfl

@[simp]
theorem toListRev_scanM {f : γ → β → m γ} [Finite α Id] [Monad m] [MonadAttach m] [LawfulMonad m]
    [WeaklyLawfulMonadAttach m] :
    (it.scanM f init).toListRev = List.dropLast <$> it.toListRev.scanrM (flip f) init := by
  simp [IterM.toListRev_eq, toListRev_eq]

@[simp]
theorem toListRev_scan [Finite α Id] : (it.scan f init).toListRev =
    (it.toListRev.scanr (flip f) init).dropLast := by
  simp [toListRev_eq]

@[simp]
theorem toArray_scanWithPostconition {f : γ → β → PostconditionT m γ} [Finite α Id] [Monad m]
    [LawfulMonad m] : (it.scanWithPostcondition f init).toArray =
    (fun xs => Array.drop xs 1) <$> it.toArray.scanlM (fun c b => (f c b).run) init := by
  rw [← toArray_toList, ← List.toArray_scanlM]
  simp [← IterM.toArray_toList]; apply map_congr
  intro l; congr; apply l.tail.take_length.symm.trans; simp

@[simp]
theorem toArray_scanM {f : γ → β → m γ} [Finite α Id] [Monad m] [MonadAttach m] [LawfulMonad m]
    [WeaklyLawfulMonadAttach m] :
    (it.scanM f init).toArray = (fun xs => Array.drop xs 1) <$> it.toArray.scanlM f init := by
  change (it.scanWithPostcondition _ init).toArray = _
  simp

@[simp]
theorem toArray_scan [Finite α Id] : (it.scan f init).toArray =
    (it.toArray.scanl f init).drop 1 := by
  rw [← toArray_toList, ← toArray_toList, ← List.toArray_scanl]; simp
  apply List.take_length.symm.trans; simp
