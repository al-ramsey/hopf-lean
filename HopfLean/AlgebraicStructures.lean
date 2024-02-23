class Group₁ (G : Type u) where
  -- there is a binary product `G × G → G` (curried to `G → G → G`)
  mul : G → G → G
  -- there is an element `e`
  e : G
  -- `e` is a left identity
  e_mul : ∀ x : G, mul e x = x
  -- `e` is a right identity
  mul_e : ∀ x : G, mul x e = x
  -- every element has a left inverse
  left_inv : ∀ x : G, ∃ y : G, mul y x = e
  -- every element has a right inverse
  right_inv : ∀ x : G, ∃ y : G, mul x y = e
  -- the binary product is associative
  mul_assoc : ∀ x y z : G, mul x (mul y z) = mul (mul x y) z

namespace Group₁
-- let G be a group
variable {G : Type u} [Group₁ G]

-- the identity of a group is unique
theorem e_unique (e₁ e₂ : G) (e₁_mul : ∀ x : G, mul e₁ x = x) (mul_e₂ : ∀ x : G, mul x e₂ = x) :
    e₁ = e₂ := by
  calc
    e₁ = mul e₁ e₂ := by rw [mul_e₂ e₁]
    _  = e₂ := e₁_mul e₂

-- the left and right inverses of an element coincide
theorem left_inv_eq_right_inv (x a b : G) (a_right_inv : mul x a = e) (b_left_inv : mul b x = e) :
    a = b := by
  calc
    a = mul e a := by rw [e_mul a]
    _ = mul (mul b x) a := by rw [b_left_inv]
    _ = mul b (mul x a) := by rw [mul_assoc]
    _ = mul b e := by rw [a_right_inv]
    _ = b := mul_e b

end Group₁

class Monoid (M : Type u) where
  mul : M → M → M
  e : M
  e_mul : ∀ x : M, mul e x = x
  mul_e : ∀ x : M, mul x e = x
  mul_assoc : ∀ x y z : M, mul x (mul y z) = mul (mul x y) z

namespace Monoid
variable {M : Type u} [Monoid M]

-- the identity of a monoid is unique (note that the proof is exactly the same as for groups)
theorem e_unique (e₁ e₂ : M) (e₁_mul : ∀ x : M, mul e₁ x = x) (mul_e₂ : ∀ x : M, mul x e₂ = x) :
    e₁ = e₂ := by
  calc
    e₁ = mul e₁ e₂ := by rw [mul_e₂ e₁]
    _ = e₂ := e₁_mul e₂

-- the left and right inverses of an element coincide (the same proof as for groups, again)
theorem left_inv_eq_right_inv (x a b : M) (a_right_inv : mul x a = e) (b_left_inv : mul b x = e) :
    a = b := by
  calc
    a = mul e a := by rw [e_mul a]
    _ = mul (mul b x) a := by rw [b_left_inv]
    _ = mul b (mul x a) := by rw [mul_assoc]
    _ = mul b e := by rw [a_right_inv]
    _ = b := mul_e b

end Monoid

class Group₂ (G : Type u) extends Monoid G where
  left_inv : ∀ x : G, ∃ y : G, mul y x = e
  right_inv : ∀ x : G, ∃ y : G, mul x y = e

namespace Group₂
variable (G : Type u) [Group₂ G]

open Monoid

/-
We have already proven the lemmas below for monoids, so we know they must be true for groups.
We can therefore just give Lean the name of the corresponding lemma for monoids as the proof.
-/

-- the identity of a group is unique
theorem e_unique' (e₁ e₂ : G) (e₁_mul : ∀ x : G, mul e₁ x = x) (mul_e₂ : ∀ x : G, mul x e₂ = x) :
    e₁ = e₂ := e_unique _ _ e₁_mul mul_e₂

-- the left and right inverses of an element coincide
theorem left_inv_eq_right_inv' (x a b : G) (a_right_inv : mul x a = e) (b_left_inv : mul b x = e) :
    a = b := left_inv_eq_right_inv _ _ _ a_right_inv b_left_inv

end Group₂
