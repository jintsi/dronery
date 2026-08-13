import Dronery.Array
import Mathlib.Data.List.Nodup

namespace Dronery

/-- A `Permutation` is a permutation of `Array.range n` for some `n`. It's the type underlying both
`Finperm` and `Natperm`. -/
@[implicit_reducible]
def Permutation := {as // Array.Perm as (Array.range as.size)}

namespace Permutation

abbrev size (p : Permutation) := p.val.size

theorem mem_val_iff {p : Permutation} : n ∈ p.val ↔ n < p.size := by simp [p.property.mem_iff]

theorem nodup {p : Permutation} : p.val.toList.Nodup := by
  rw [List.Nodup, p.property.pairwise_iff Ne.symm, Array.toList_range]; apply List.nodup_range

/-- A `Permutation` as an endofunction (a permutation, in fact) on `Fin n` for some `n`. -/
def applyFin (p : Permutation) (h : p.size = n) (i : Fin n) : Fin n :=
  ⟨p.val[i]'(h ▸ i.isLt), h ▸ mem_val_iff.mp (by simp)⟩

theorem coe_applyFin {i : Fin n} : (applyFin p h i : Nat) = p.val[i]'(h ▸ i.isLt) := rfl

theorem applyFin_inj {p₁ p₂ : Permutation} {h₁ : p₁.size = n} {h₂ : p₂.size = n} :
    p₁.applyFin h₁ = p₂.applyFin h₂ ↔ p₁ = p₂ := by
  constructor; case mpr => intro rfl; rfl
  intro h; simp [funext_iff, Fin.ext_iff, coe_applyFin] at h
  apply Subtype.ext; ext i hi; simp [h₁, h₂]
  unfold size at h₁; rw [h₁] at hi; exact h ⟨i, hi⟩

/-- A `Permutation` as an endofunction (a permutation, in fact) on `ℕ` that's a natural extension
of the one on `Fin p.size`. -/
def applyNat (p : Permutation) (n : Nat) : Nat := if h : n < p.size then p.applyFin rfl ⟨n, h⟩ else n

theorem applyNat_inj {p₁ p₂ : Permutation} (h : p₁.size = p₂.size) : p₁.applyNat = p₂.applyNat ↔ p₁ = p₂ := by
  constructor; case mpr => apply congrArg
  intro h; simp [funext_iff, applyNat, coe_applyFin] at h
  apply Subtype.ext; ext i hi₁ hi₂; simp_all
  simpa [hi₁, hi₂] using h i

/-- Compute the inverse of a permutation. It is later shown to be a valid permutation and that it
is in fact the inverse. -/
def inverseAux (p : Permutation) : Vector Nat p.size :=
  p.val.attach.foldlIdx (fun i acc pi => acc.set pi.val i (mem_val_iff.mp pi.property)) 0

-- TODO: combine these two into one with `Array.foldlIdx_induction`
theorem inverseAux_eq_fold {p : Permutation} : p.inverseAux = p.val.attach.foldl (fun acc pi =>
    acc.set pi.val (p.val.idxOf pi.val) (mem_val_iff.mp pi.property)) 0 := by
  unfold inverseAux; generalize_proofs h; have ha := p.nodup; generalize p.val = as at h ha
  induction as using Array.pushInduction with
  | empty => simp
  | push as a ih =>
    simp [Array.foldlIdx_map, Array.foldl_map']
    simp [List.nodup_append'] at ha; rw [ih _ ha.1]; congr 2
    · funext v pi; congr 1; rw [Array.push_eq_append, Array.idxOf_append, ite_eq_left pi.property]
    · simp
    · rw [Array.push_eq_append, Array.idxOf_append, ite_eq_right ha.2]; simp

theorem getElem_inverseAux_getElem {p : Permutation} : ∀ i, (hi : i < p.size) →
    p.inverseAux[p.val[i]]'(mem_val_iff.mp (by simp)) = i := by
  suffices H : ∀ i : Fin p.size, i < p.val.attach.size →
      p.inverseAux[p.val[i]]'(mem_val_iff.mp (by simp)) = i from fun i hi => H ⟨i, hi⟩ (by simpa)
  rw [inverseAux_eq_fold]; apply p.val.attach.foldl_induction (motive := fun n (v : Vector ℕ _) =>
    ∀ i : Fin p.size, i < n → v[p.val[i]]'(mem_val_iff.mp (by simp)) = i)
  · simp
  · intro n v ih i h; simp [Nat.lt_add_one_iff_lt_or_eq] at h; rcases h with (h | h)
    · rw [Vector.getElem_set_ne]; exact ih i h
      simp [← Array.getElem_toList, p.nodup]; lia
    · simp [h]; rw [← p.val.idxOf_toList, ← Array.getElem_toList]; apply p.nodup.idxOf_getElem

theorem getElem_inverseAux {p : Permutation} {i : ℕ} (hi : i < p.size) :
    p.inverseAux[i] = p.val.idxOf i := by
  rw! [← p.getElem_inverseAux_getElem (p.val.idxOf i), Array.getElem_idxOf]; rfl
  simpa [Array.idxOf_lt_size_iff, mem_val_iff]

/-- The inverse permutation to `p`. `O(p.size)`. -/
def inverse (p : Permutation) : Permutation where
  val := p.inverseAux.toArray
  property := by
    rw [Array.perm_iff_toList_perm, List.perm_ext_iff_of_nodup]
    · intro a; simp [Vector.mem_iff_getElem]; constructor
      · simp; intro i h rfl; simpa [getElem_inverseAux, Array.idxOf_lt_size_iff, mem_val_iff]
      · intro h; constructor; constructor; apply getElem_inverseAux_getElem _ h
    · simp [List.nodup_iff_eq_of_getElem_eq, getElem_inverseAux, ← Array.idxOf_toList]
      intro i j hi hj; rw [List.idxOf_inj (by simpa [mem_val_iff])]; exact id
    · simp [List.nodup_range]

@[simp]
theorem size_inverse {p : Permutation} : p.inverse.size = p.size := by simp [size, inverse]

@[simp]
theorem applyFin_inverse_applyFin {p : Permutation} {h : p.size = n} {i : Fin n} :
    p.inverse.applyFin (p.size_inverse.trans h) (p.applyFin h i) = i := by
  ext; apply getElem_inverseAux_getElem

@[simp]
theorem applyFin_applyFin_inverse {p : Permutation} {h : p.size = n} {i : Fin n} :
    p.applyFin h (p.inverse.applyFin (p.size_inverse.trans h) i) = i := by
  ext; simp [applyFin, inverse, getElem_inverseAux]

@[simp]
theorem applyNat_inverse_applyNat {p : Permutation} {i : ℕ} :
    p.inverse.applyNat (p.applyNat i) = i := by
  unfold applyNat; split <;> simp [*]; apply getElem_inverseAux_getElem

@[simp]
theorem applyNat_applyNat_inverse {p : Permutation} {i : ℕ} :
    p.applyNat (p.inverse.applyNat i) = i := by
  unfold applyNat; simp; split; case isFalse => rfl
  rw [dite_eq_left (by rw! [← p.size_inverse]; apply Fin.isLt)]
  simp [applyFin, inverse, getElem_inverseAux]

@[simp]
theorem inverse_inverse {p : Permutation} : p.inverse.inverse = p := by
  rw [← applyNat_inj (by simp)]; funext i
  rw [← p.inverse.applyNat_inverse_applyNat (i := p.applyNat i), p.applyNat_inverse_applyNat]
