import Dronery.Permutation
import Mathlib.Logic.Embedding.Basic

namespace Dronery

open Permutation

/-- `Finperm n` is the type of permutations on `Fin n`. -/
def Finperm (n : ℕ) : Type := {p // size p = n}

namespace Finperm

@[simp]
theorem size_val {p : Finperm n} : p.val.size = n := p.property

def mk (p : Permutation) (h : p.size = n) : Finperm n := ⟨p, h⟩

@[simp]
theorem val_mk {p} {h : p.size = n} : (mk p h).val = p := rfl

@[cases_eliminator, elab_as_elim]
theorem casesOn {motive : Finperm n → Prop} (p : Finperm n)
    (mk : ∀ p, (h : p.size = n) → motive (mk p h)) : motive p := Subtype.casesOn p mk

def mk' (as : Array ℕ) (h : as.Perm (Array.range n)) : Finperm n :=
  mk ⟨as, by simpa [h.size_eq]⟩ (by simp [size, h.size_eq])

@[simp]
theorem mk'_eq {n as h} : @mk' n as h = mk ⟨as, by simpa [h.size_eq]⟩ (by simp [size, h.size_eq]) := rfl

instance : FunLike (Finperm n) (Fin n) (Fin n) where
  coe p := p.val.applyFin size_val
  coe_injective p₁ p₂ h := by
    apply Subtype.ext; rw [← Permutation.applyFin_inj]; exact h

@[simp]
theorem coe_mk {p : Permutation} {h : p.size = n} : mk p h = p.applyFin h := rfl

@[simp]
theorem applyFin_val {p : Finperm n} :
    p.val.applyFin p.property = p := rfl

@[ext]
theorem ext {p q : Finperm n} (H : ∀ i, p i = q i) : p = q := DFunLike.ext p q H

/-- The identity permutation. -/
instance : One (Finperm n) where
  one := mk' (Array.range n) Array.Perm.rfl

theorem one_apply (i : Fin n) : (1 : Finperm n) i = i := Fin.ext (Array.getElem_range (by simp))

@[simp]
theorem coe_one : ⇑(1 : Finperm n) = id := funext one_apply

/-- The inverse permutation to `p`. `O(n)`. -/
instance : Inv (Finperm n) where
  inv p := mk p.val.inverse (by simp)

@[simp]
theorem inv_mk {p : Permutation} {h : p.size = n} : (mk p h)⁻¹ = mk p.inverse (by simpa) := rfl

@[simp]
theorem apply_inv_apply (p : Finperm n) (i : Fin n) : p (p⁻¹ i) = i := by cases p; simp

@[simp]
theorem inv_apply_apply (p : Finperm n) (i : Fin n) : p⁻¹ (p i) = i := by cases p; simp

@[simp]
theorem inv_inv (p : Finperm n) : p⁻¹⁻¹ = p := by cases p; simp

/-- Find the preimage of a single element without constructing the whole inverse permutation. -/
def idxOf (p : Finperm n) (i : Fin n) : Fin n where
  val := p.val.val.idxOf i.val
  isLt := by
    nth_rw 3 [← p.size_val]; rw [Array.idxOf_lt_size_iff, mem_val_iff, size_val]; simp

@[simp]
theorem idxOf_eq_inv {p : Finperm n} : idxOf p = p⁻¹ := by
  ext i; symm; apply getElem_inverseAux; simp

theorem injective (p : Finperm n) : (⇑p).Injective := by
  intro i j h; simpa using congrArg ⇑p⁻¹ h

@[simp]
theorem inj {p : Finperm n} {i j : Fin n} : p i = p j ↔ i = j := p.injective.eq_iff

instance : Mul (Finperm n) where
  mul p q := mk' ((q.val.val.attachFin (by simp [mem_val_iff])).map (Fin.val ∘ p)) (by
    simp [Array.perm_iff_toList_perm, Array.attachFin]; rw [List.perm_ext_iff_of_nodup]
    · intro a; simp; constructor
      · simp; intro _ _ rfl; simp
      · intro h; use p⁻¹ ⟨a, h⟩; simp [mem_val_iff]
    · apply List.Nodup.map fun i j => by simp [← Fin.ext_iff]
      apply List.Nodup.pmap (by simp); exact q.val.nodup
    · exact List.nodup_range)

theorem mul_apply (p q : Finperm n) (i : Fin n) : (p * q) i = p (q i) := by
  change mk _ _ _ = _; simp [applyFin, Array.attachFin]; rfl

@[simp]
theorem coe_mul (p q : Finperm n) : ⇑(p * q) = p ∘ q := funext (mul_apply p q)

/-- TODO: cycle decomposition-based exponentiation -/
instance : Group (Finperm n) where
  mul_assoc p q r := by ext; simp
  one_mul p := by ext; simp
  mul_one p := by ext; simp
  inv_mul_cancel p := by ext; simp
