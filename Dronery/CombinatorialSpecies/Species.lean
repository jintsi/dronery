import Mathlib.Data.Multiset.Antidiagonal
import Mathlib.Data.Finset.Powerset
import Mathlib.Control.EquivFunctor
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.NatAntidiagonal

attribute [local implicit_reducible] Function.Injective

@[simps]
def Finset.equivMapEquiv (e : α ≃ β) (s : Finset α) : s ≃ s.map e.toEmbedding where
  toFun x := ⟨e x, by simp⟩
  invFun b := ⟨e.symm b, by simpa using b.prop⟩
  left_inv x := by simp
  right_inv b := by simp

theorem Finset.equivOfEq_eq_cast {s t : Finset α} (h : s = t) :
  equivOfEq h = Equiv.cast (by congr!) := by cases h; simp

@[simp]
theorem EquivFunctor.map_cast_heq [EquivFunctor f] (h : α = β) (x : f α) :
    map (Equiv.cast h) x ≍ x := by cases h; simp

/-- This could've been called `Finset.antidiagonal`, but that's already taken. -/
def Finset.binPartitions (s : Finset α) : Finset (Finset α × Finset α) where
  val := s.val.antidiagonal.pmap (fun x (h : x.1.Nodup ∧ x.2.Nodup) => (⟨x.1, h.1⟩, ⟨x.2, h.2⟩)) (by
    simp; intro a b h; and_intros <;>
      refine Multiset.nodup_of_le ?_ s.nodup <;> simp [← h])
  nodup := by
    apply Multiset.Nodup.pmap; · simp +contextual
    apply Multiset.Nodup.of_map; rw [Multiset.antidiagonal_map_fst]; simpa using s.nodup

@[simp]
theorem Finset.mem_binPartitions (s : Finset α) :
    x ∈ s.binPartitions ↔ ∃ (h : Disjoint x.1 x.2), x.1.disjUnion x.2 h = s := by
  rcases x with ⟨a, b⟩; simp +contextual [binPartitions, ← val_inj, ← disjoint_val,
    Multiset.disjoint_of_nodup_add, s.nodup]

@[simp]
theorem Finset.binPartitions_eq_map [DecidableEq α] (s : Finset α) :
    s.binPartitions = s.powerset.map (by use fun t => (t, s \ t); unfold Function.Injective; simp) := by
  ext x; rcases x with ⟨a, b⟩; simp; constructor
  · rintro ⟨h, rfl⟩; simp [Finset.union_sdiff_cancel_left h]
  · rintro ⟨h, rfl⟩; simpa [Finset.disjoint_sdiff]

namespace CombinatorialSpecies

open EquivFunctor

class Species (F : Type u → Type v) extends EquivFunctor F where
  mapFintype (α) [Fintype α] : Fintype (F α)

instance [Species F] [Fintype α] : Fintype (F α) := Species.mapFintype α

def card (F) [Species F] (n : ℕ) := Fintype.card (F (Fin n))

@[simp]
theorem card_eq_card [Species F] [Fintype α] :
    Fintype.card (F α) = card F (Fintype.card α) :=
  Fintype.card_congr (mapEquiv F (Fintype.equivFin α))

abbrev Add (F : Type u → Type v) (G : Type u → Type w) (α : Type u) := F α ⊕ G α

instance [Species F] [Species G] : Species (Add F G) where
  map e := Sum.map (map e) (map e)
  map_refl' α := by simp
  map_trans' e e' := by simp [map_trans']
  mapFintype α := inferInstance

@[simp]
theorem card_add [Species F] [Species G] : card (Add F G) n = card F n + card G n :=
  Fintype.card_sum

@[ext]
structure Mul (F : Type u → Type v) (G : Type u → Type w) (α : Type u) where
  left : Finset α
  right : Finset α
  disj : Disjoint left right
  complete : ∀ a, a ∈ left ∨ a ∈ right
  fst : F left
  snd : G right

instance [Species F] [Species G] : Species (Mul F G) where
  map e s := ⟨s.left.map e, s.right.map e, by simpa using s.disj,
    by simp; intro; apply s.complete,
    map (s.left.equivMapEquiv e) s.fst, map (s.right.equivMapEquiv e) s.snd⟩
  map_refl' α := by
    funext ⟨l, r, _, _, f, g⟩; simp; ext
    · simp
    · simp
    · simp; convert! map_cast_heq _ f; swap; simp
      congr; ext; rw [Finset.equivMapEquiv_apply_coe, ← Finset.equivOfEq_eq_cast]
      · rfl
      · simp
    · simp; convert! map_cast_heq _ g; swap; simp
      congr; ext; rw [Finset.equivMapEquiv_apply_coe, ← Finset.equivOfEq_eq_cast]
      · rfl
      · simp
  map_trans' e e' := by
    funext ⟨l, r, _, _, f, g⟩; ext1 <;> simp [Finset.map_map]
    · apply HEq.trans; symm; apply map_cast_heq
      pick_goal 3; apply heq_of_eq; swap
      · simp [Finset.map_map]
      · simp_rw [← Function.comp_apply (f := map _)]
        apply congrFun; rw [← map_trans']; trans; · symm; apply map_trans'
        congr 1; ext; simp
        rw (transparency := .default) [Equiv.trans_apply, ← Finset.equivOfEq_eq_cast]; rfl
        simp [Finset.map_map]
    · apply HEq.trans; symm; apply map_cast_heq
      pick_goal 3; apply heq_of_eq; swap
      · simp [Finset.map_map]
      · simp_rw [← Function.comp_apply (f := map _)]
        apply congrFun; rw [← map_trans']; trans; · symm; apply map_trans'
        congr 1; ext; simp
        rw (transparency := .default) [Equiv.trans_apply, ← Finset.equivOfEq_eq_cast]; rfl
        simp [Finset.map_map]
  mapFintype α := {
    elems := (Finset.univ : Finset α).binPartitions.attach.disjiUnion (fun ⟨(l, r), h⟩ =>
      (Finset.univ : Finset (F l × G r)).map (by
        use fun (f, g) => ⟨l, r, (by simp at h; exact h.fst),
          (by simp_all [Finset.eq_univ_iff_forall]), f, g⟩
        rintro ⟨f, g⟩ ⟨f', g'⟩; simp)) (by
      rintro ⟨⟨l, r⟩, h⟩ - ⟨⟨l', r'⟩, h'⟩ - hne; simp [Function.onFun, Finset.disjoint_iff_ne]
      intro _ f g rfl _ f' g' rfl; rw [Mul.ext_iff]; simp_all)
    complete x := by
      rw (transparency := .default) [Finset.mem_disjiUnion]
      simp [Finset.eq_univ_iff_forall, Mul.ext_iff]; exact ⟨x.disj, x.complete⟩}

set_option linter.auxLemma false in
theorem card_mul [Species F] [Species G] :
    card (Mul F G) n = ∑ p ∈ Finset.antidiagonal n, n.choose p.1 * card F p.1 * card G p.2 := by
  change Finset.card (Finset.disjiUnion _ _ ?_) = _; swap
  · unfold Set.PairwiseDisjoint; apply instSpeciesMul._proof_12
  rw [Finset.card_disjiUnion, Finset.sum_congr rfl]; swap
  · intros; rw [Finset.card_map, Finset.card_univ, Fintype.card_prod,
      card_eq_card, card_eq_card, Fintype.card_coe, Fintype.card_coe]
  rw [Finset.univ.binPartitions.sum_attach fun x => card F x.1.card * card G x.2.card]
  simp [Finset.binPartitions_eq_map, Finset.card_univ_sdiff, -Finset.powerset_univ]
  rw [Finset.univ.sum_powerset_apply_card fun m => _ * card G _]; simp [← mul_assoc]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

abbrev Prod (F : Type u → Type v) (G : Type u → Type w) (α : Type u) := F α × G α

instance [Species F] [Species G] : Species (Prod F G) where
  map e := Prod.map (map e) (map e)
  map_refl' α := by simp
  map_trans' e e' := by simp [map_trans', Prod.map_comp_map]
  mapFintype α := inferInstance

@[simp]
theorem card_prod [Species F] [Species G] : card (Prod F G) n = card F n * card G n :=
  Fintype.card_prod _ _
