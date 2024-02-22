import Mathlib.Algebra.Ring.Basic

/-
Basic tactics:
* apply
* aesop
* ext
* rfl
* unfold
* have
* simp only
-/

variable {R : Type*} [Ring R]

theorem add_assoc₁ : ∀ a b c : R, a + (b + c) = (a + b) + c := by
  -- let a, b, c be elements of the ring R
  intros a b c
  rw [add_assoc a b c]

-- We now tag this theorem with @[simp], which teaches it to the simplifier
@[simp]
theorem add_assoc₂ : ∀ a b c : R, a + (b + c) = (a + b) + c := by
  intros a b c
  -- swap the goal from a + (b + c) = (a + b) + c
  symm
  -- this is now exactly associativity of the underlying additive group
  exact add_assoc a b c

-- Note that the proof below would not work if we hadn't labelled add_assoc₂ with simp
theorem add_assoc₃ : ∀ a b c : R, a + (b + c) = (a + b) + c := by
  simp

/-
We show that the underlying additive group of a ring is necessarily abelian if the
multiplication distributes over addition
-/
theorem add_comm' {R : Type*} [Ring R] (a b : R) : a + b = b + a := by
  have key₁ : (a + b) * (1 + 1) = a + (a + b) + b := by
    simp_rw [right_distrib, left_distrib, mul_one, add_assoc]
  have key₂ : (a + b) * (1 + 1) = a + (b + a) + b := by
    simp_rw [left_distrib, right_distrib, mul_one, add_assoc]
  rw [key₁] at key₂
  apply AddGroup.toAddCancelMonoid.proof_6 (a + b) b
  apply AddGroup.toAddCancelMonoid.proof_1 a
  have key₃ : a + (a + b) + b = a + (a + b + b) := by simp
  rw [← key₃]
  have key₄ : a + (b + a) + b = a + (b + a + b) := by simp
  rw [← key₄]
  exact key₂
