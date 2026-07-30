import Dronery.Iterators.Scan
import Batteries.Data.Array.Scan

open Std Iterators

variable {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}

namespace Std.IterM

variable [Iterator α m β] {it : IterM (α := α) m β} {init : γ}

theorem step_scanWithPostcondition' {f : γ → β → PostconditionT n γ} [Monad n] [MonadLiftT m n] :
    (it.scanWithPostcondition' f init).step = (do
      match (← it.step).inflate with
      | .yield it' out h => do
        let out' ← (f init out).operation
        pure (.deflate (.yield (it'.scanWithPostcondition' f out') out' (.yield h out'.2)))
      | .skip it' h => pure (.deflate (.skip (it'.scanWithPostcondition' f init) (.skip h)))
      | .done h => pure (.deflate (.done (.done h)))) := by
  apply bind_congr; intro step; match step.inflate with
  | .yield it' out h => rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem step_scanM' {f : γ → β → n γ} [Monad n] [MonadAttach n] [MonadLiftT m n] :
    (it.scanM' f init).step = (do
      match (← it.step).inflate with
      | .yield it' out h => do
        let out' ← MonadAttach.attach (f init out)
        pure (.deflate (.yield (it'.scanM' f out') out' (.yield h out'.2)))
      | .skip it' h => pure (.deflate (.skip (it'.scanM' f init) (.skip h)))
      | .done h => pure (.deflate (.done (.done h)))) := by
  apply bind_congr; intro step; match step.inflate with
  | .yield it' out h => rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem step_scan' [Monad m] [LawfulMonad m] :
    (it.scan' f init).step = (do
      match (← it.step).inflate with
      | .yield it' out h => do
        letI out' := f init out
        pure (.deflate (.yield (it'.scan' f out') out' (.yield h rfl)))
      | .skip it' h => pure (.deflate (.skip (it'.scan' f init) (.skip h)))
      | .done h => pure (.deflate (.done (.done h)))) := by
  apply bind_congr; intro step; match step.inflate with
  | .yield it' out h => simp; rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem step_scanWithPostcondition {f : γ → β → PostconditionT n γ} [Monad n] [MonadLiftT m n] :
    (it.scanWithPostcondition f init).step =
    pure (.deflate (.yield (it.scanWithPostcondition' f init).toScan init (.first rfl))) := rfl

theorem step_scanM {f : γ → β → n γ} [Monad n] [MonadAttach n] [MonadLiftT m n] :
    (it.scanM f init).step =
    pure (.deflate (.yield (it.scanM' f init).toScan init (.first rfl))) := rfl

theorem step_scan [Monad m] : (it.scan f init).step =
    pure (.deflate (.yield (it.scan' f init).toScan init (.first rfl))) := rfl

open Iterators.Types in
@[simp]
theorem step_toScan {lift : ⦃α : Type w⦄ → m α → n α} {f : γ → β → PostconditionT n γ}
    {it : IterM (α := Scan' α m n lift f) n γ} [Monad n] [LawfulMonad n] :
    it.toScan.step = (fun s => match s.inflate with
      | .yield ⟨⟨it', out⟩⟩ out' h => .deflate (.yield ⟨⟨it', out, true⟩⟩ out' (by
        cases h; exact .yield rfl ‹_› ‹_›))
      | .skip ⟨⟨it', last⟩⟩ h => .deflate (.skip ⟨⟨it', last, true⟩⟩ (by
        cases h; exact .skip rfl ‹_›))
      | .done h => .deflate (.done (by cases h; exact .done rfl ‹_›))) <$> it.step := by
  unfold step Iterator.step Scan'.instIterator Scan.instIterator
  simp only [toScan, bind_pure_comp, map_bind]
  apply bind_congr; intro step; match step.inflate with
  | .yield it' out h => simp
  | .skip it' h => simp
  | .done h => simp

@[simp]
theorem toList_scan' [Finite α m] [Monad m] [LawfulMonad m] :
    (it.scan' f init).toList = (fun l => (l.scanl f init).tail) <$> it.toList := by
  induction it using IterM.inductSteps generalizing init
  rename_i it ihy ihs
  rw [toList_eq_match_step, toList_eq_match_step]
  simp only [bind_pure_comp, map_bind]
  rw [step_scan']
  simp only [bind_assoc, map_eq_pure_bind]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp; rw [ihy ‹_›, Functor.map_map]; apply map_congr
    intro l; rw [← List.cons_head_tail (List.scanl_ne_nil)]; simp
  · simp; exact ihs ‹_›
  · simp

open Iterators.Types in
@[simp]
theorem toList_toScan {lift : ⦃α : Type w⦄ → m α → n α} {f : γ → β → PostconditionT n γ}
    {it : IterM (α := Scan' α m n lift f) n γ} [Finite α m] [Monad n] [LawfulMonad n] :
    it.toScan.toList = it.toList := by
  induction it using IterM.inductSteps
  rename_i it ihy ihs
  rw [toList_eq_match_step, toList_eq_match_step]; simp
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp; exact ihy ‹_›
  · simp; exact ihs ‹_›
  · simp

@[simp]
theorem toList_scan [Finite α m] [Monad m] [LawfulMonad m] :
    (it.scan f init).toList = List.scanl f init <$> it.toList := by
  rw [toList_eq_match_step]; simp [step_scan]
  congr; funext l; cases l <;> simp

@[simp]
theorem toListRev_scan' [Finite α m] [Monad m] [LawfulMonad m] :
    (it.scan' f init).toListRev = (fun l => (l.scanr (flip f) init).dropLast) <$> it.toListRev := by
  simp [toListRev_eq]

@[simp]
theorem toListRev_scan [Finite α m] [Monad m] [LawfulMonad m] :
    (it.scan f init).toListRev = List.scanr (flip f) init <$> it.toListRev := by
  simp [toListRev_eq]

@[simp]
theorem toArray_scan' [Finite α m] [Monad m] [LawfulMonad m] :
    (it.scan' f init).toArray = (fun bs => (bs.scanl f init).drop 1) <$> it.toArray := by
  simp [← toArray_toList, -List.size_toArray, ← List.toArray_scanl]; congr
  funext l; simp

@[simp]
theorem toArray_scan [Finite α m] [Monad m] [LawfulMonad m] :
    (it.scan f init).toArray = Array.scanl f init <$> it.toArray := by
  simp [← toArray_toList, List.toArray_scanl]

end IterM

namespace Iter

variable [Iterator α Id β] {it : Iter (α := α) β} {init : γ}

theorem step_scanWithPostcondition' {f : γ → β → PostconditionT m γ} [Monad m] [LawfulMonad m] :
    (it.scanWithPostcondition' f init).step =
      match it.step with
      | .yield it' out h => do
        let out' ← (f init out).operation
        pure (.deflate (.yield (it'.scanWithPostcondition' f out') out' (.yield h out'.2)))
      | .skip it' h => pure (.deflate (.skip (it'.scanWithPostcondition' f init) (.skip h)))
      | .done h => pure (.deflate (.done (.done h))) := by
  simp only [scanWithPostcondition', IterM.step_scanWithPostcondition', step]
  simp only [liftM, monadLift, pure_bind]
  match it.toIterM.step.inflate with
  | .yield it' out h => rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem step_scanM' {f : γ → β → m γ} [Monad m] [MonadAttach m] [LawfulMonad m] :
    (it.scanM' f init).step =
      match it.step with
      | .yield it' out h => do
        let out' ← MonadAttach.attach (f init out)
        pure (.deflate (.yield (it'.scanM' f out') out' (.yield h out'.2)))
      | .skip it' h => pure (.deflate (.skip (it'.scanM' f init) (.skip h)))
      | .done h => pure (.deflate (.done (.done h))) := by
  simp only [scanM', IterM.step_scanM', step]
  simp only [liftM, monadLift, pure_bind]
  match it.toIterM.step.inflate with
  | .yield it' out h => rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem step_scan' : (it.scan' f init).step =
    match it.step with
    | .yield it' out h =>
      letI out' := f init out
      .yield (it'.scan' f out') out' (.yield h rfl)
    | .skip it' h => .skip (it'.scan' f init) (.skip h)
    | .done h => .done (.done h) := by
  apply Subtype.ext
  simp only [scan', step, toIterM_toIter, IterM.step_scan', Id.run_bind]
  match it.toIterM.step.inflate with
  | .yield it' out h => simp
  | .skip it' h => simp
  | .done h => simp

theorem step_scanWithPostcondition {f : γ → β → PostconditionT m γ} [Monad m] :
    (it.scanWithPostcondition f init).step =
    pure (.deflate (.yield (it.scanWithPostcondition' f init).toScan init (.first rfl))) := rfl

theorem step_scanM {f : γ → β → m γ} [Monad m] [MonadAttach m] : (it.scanM f init).step =
    pure (.deflate (.yield (it.scanM' f init).toScan init (.first rfl))) := rfl

theorem step_scan : (it.scan f init).step =
    .yield (it.scan' f init).toScan init (.first rfl) := by
  simp only [scan, step, toIterM_toIter, IterM.step_scan, Id.run_pure, Shrink.inflate_deflate]
  rfl

@[simp]
theorem step_toScan : (it.scan' f init).toScan.step =
    match it.step with
    | .yield it' out h =>
      letI out' := f init out
      .yield (it'.scan' f out').toScan out' (.yield rfl h rfl)
    | .skip it' h => .skip (it'.scan' f init).toScan (.skip rfl h)
    | .done h => .done (.done rfl h) := by
  unfold step scan' IterM.scan' IterM.scanWithPostcondition' toScan
  conv => lhs; unfold IterM.step Iterator.step Types.Scan.instIterator
  simp; split <;> simp_all

@[simp]
theorem toList_scanWithPostcondition' {f : γ → β → PostconditionT m γ} [Finite α Id] [Monad m]
    [LawfulMonad m] : (it.scanWithPostcondition' f init).toList =
    List.tail <$> it.toList.scanlM (fun c b => (f c b).run) init := by
  induction it using Iter.inductSteps generalizing init
  rename_i it ihy ihs
  rw [IterM.toList_eq_match_step, toList_eq_match_step]
  simp only [bind_pure_comp]
  rw [step_scanWithPostcondition']
  cases it.step using PlausibleIterStep.casesOn
  · simp; rw [PostconditionT.run]; simp
    apply bind_congr; intro out'
    rw [ihy ‹_›]; simp
    rename_i it' _ _; generalize it'.toList = l
    induction l <;> simp
  · simp; exact ihs ‹_›
  · simp

@[simp]
theorem toList_scanM' {f : γ → β → m γ} [Finite α Id] [Monad m] [MonadAttach m] [LawfulMonad m]
    [WeaklyLawfulMonadAttach m] :
    (it.scanM' f init).toList = List.tail <$> it.toList.scanlM f init := by
  change (it.scanWithPostcondition' _ init).toList = _
  simp

@[simp]
theorem toList_scan' [Finite α Id] : (it.scan' f init).toList = (it.toList.scanl f init).tail := by
  rw [scan', IterM.toList_toIter, IterM.toList_scan']; rfl

@[simp]
theorem toList_scanWithPostcondition {f : γ → β → PostconditionT m γ} [Finite α Id] [Monad m]
    [LawfulMonad m] : (it.scanWithPostcondition f init).toList =
    it.toList.scanlM (fun c b => (f c b).run) init := by
  induction it using Iter.inductSteps
  rename_i it ihy ihs
  rw [IterM.toList_eq_match_step]
  simp [step_scanWithPostcondition]
  generalize it.toList = l; cases l <;> simp

@[simp]
theorem toList_scanM {f : γ → β → m γ} [Finite α Id] [Monad m] [MonadAttach m] [LawfulMonad m]
    [WeaklyLawfulMonadAttach m] : (it.scanM f init).toList = it.toList.scanlM f init := by
  change (it.scanWithPostcondition _ init).toList = _
  simp

@[simp]
theorem toList_scan [Finite α Id] : (it.scan f init).toList = it.toList.scanl f init := by
  rw [scan, IterM.toList_toIter, IterM.toList_scan]; rfl

@[simp]
theorem toListRev_scanWithPostcondition' {f : γ → β → PostconditionT m γ} [Finite α Id] [Monad m]
    [LawfulMonad m] : (it.scanWithPostcondition' f init).toListRev =
    List.dropLast <$> it.toListRev.scanrM (fun b c => (f c b).run) init := by
  simp [IterM.toListRev_eq, toListRev_eq]; rfl

@[simp]
theorem toListRev_scanM' {f : γ → β → m γ} [Finite α Id] [Monad m] [MonadAttach m] [LawfulMonad m]
    [WeaklyLawfulMonadAttach m] :
    (it.scanM' f init).toListRev = List.dropLast <$> it.toListRev.scanrM (flip f) init := by
  simp [IterM.toListRev_eq, toListRev_eq]

@[simp]
theorem toListRev_scan' [Finite α Id] : (it.scan' f init).toListRev =
    (it.toListRev.scanr (flip f) init).dropLast := by
  simp [toListRev_eq]

@[simp]
theorem toListRev_scanWithPostcondition {f : γ → β → PostconditionT m γ} [Finite α Id] [Monad m]
    [LawfulMonad m] : (it.scanWithPostcondition f init).toListRev =
    it.toListRev.scanrM (fun b c => (f c b).run) init := by
  simp [IterM.toListRev_eq, toListRev_eq]; rfl

@[simp]
theorem toListRev_scanM {f : γ → β → m γ} [Finite α Id] [Monad m] [MonadAttach m] [LawfulMonad m]
    [WeaklyLawfulMonadAttach m] : (it.scanM f init).toListRev = it.toListRev.scanrM (flip f) init := by
  simp [IterM.toListRev_eq, toListRev_eq]

@[simp]
theorem toListRev_scan [Finite α Id] :
    (it.scan f init).toListRev = it.toListRev.scanr (flip f) init := by
  simp [toListRev_eq]

@[simp]
theorem toArray_scanWithPostconition' {f : γ → β → PostconditionT m γ} [Finite α Id] [Monad m]
    [LawfulMonad m] : (it.scanWithPostcondition' f init).toArray =
    (fun xs => Array.drop xs 1) <$> it.toArray.scanlM (fun c b => (f c b).run) init := by
  rw [← toArray_toList, ← List.toArray_scanlM]
  simp [← IterM.toArray_toList]; apply map_congr
  intro l; congr; nth_rw 1 [← l.tail.take_length]; simp

@[simp]
theorem toArray_scanM' {f : γ → β → m γ} [Finite α Id] [Monad m] [MonadAttach m] [LawfulMonad m]
    [WeaklyLawfulMonadAttach m] :
    (it.scanM' f init).toArray = (fun xs => Array.drop xs 1) <$> it.toArray.scanlM f init := by
  change (it.scanWithPostcondition' _ init).toArray = _
  simp

@[simp]
theorem toArray_scan' [Finite α Id] : (it.scan' f init).toArray =
    (it.toArray.scanl f init).drop 1 := by
  rw [← toArray_toList, ← toArray_toList, ← List.toArray_scanl]; simp

@[simp]
theorem toArray_scanWithPostconition {f : γ → β → PostconditionT m γ} [Finite α Id] [Monad m]
    [LawfulMonad m] : (it.scanWithPostcondition f init).toArray =
    it.toArray.scanlM (fun c b => (f c b).run) init := by
  rw [← toArray_toList, ← List.toArray_scanlM]
  simp [← IterM.toArray_toList]

@[simp]
theorem toArray_scanM {f : γ → β → m γ} [Finite α Id] [Monad m] [MonadAttach m] [LawfulMonad m]
    [WeaklyLawfulMonadAttach m] :
    (it.scanM f init).toArray = it.toArray.scanlM f init := by
  change (it.scanWithPostcondition _ init).toArray = _
  simp

@[simp]
theorem toArray_scan [Finite α Id] :
    (it.scan f init).toArray = (it.toArray.scanl f init) := by
  rw [← toArray_toList, ← toArray_toList, ← List.toArray_scanl, toList_scan]
