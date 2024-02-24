import HopfLean.Bialgebra

/-!
# Hopf algebras

In this file we define `HopfAlgebra`, and provide instances for:

* Commutative semirings: `CommSemiring.toHopfAlgebra`

## References

* <https://en.wikipedia.org/wiki/Hopf_algebra>
-/

suppress_compilation

universe u v

/-- A Hopf algebra over a commutative (semi)ring `R` is a bialgebra over `R`
equipped with a linear map `S` (the antipode of the Hopf algebra) satisfying the
antipode axioms. -/
class HopfAlgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] extends
    Bialgebra R A where
  /-- The antipode of the Hopf algebra -/
  S : A →ₗ[R] A
  /-- The antipode axioms for a Hopf algebra -/
  mSid : (LinearMap.mul' R A) ∘ₗ (S.rTensor A) ∘ₗ comul =
    (Algebra.linearMap R A) ∘ₗ counit
  midS : (LinearMap.mul' R A) ∘ₗ (S.lTensor A) ∘ₗ comul =
    (Algebra.linearMap R A) ∘ₗ counit

namespace HopfAlgebra
variable {R : Type u} {A : Type v}
variable [CommSemiring R] [Semiring A] [H : HopfAlgebra R A]

@[simp]
theorem mSid_apply (a : A) : LinearMap.mul' R A (S.rTensor A (H.comul a)) =
    Algebra.linearMap R A (H.counit a) :=
  LinearMap.congr_fun mSid a

@[simp]
theorem midS_apply (a : A) : LinearMap.mul' R A (S.lTensor A (H.comul a)) =
    Algebra.linearMap R A (H.counit a) :=
  LinearMap.congr_fun midS a

end HopfAlgebra

section CommSemiring
variable (R : Type u) [CommSemiring R]

open HopfAlgebra

namespace CommSemiring

/-- Every commutative (semi)ring is a Hopf algebra over itself -/
noncomputable
instance toHopfAlgebra : HopfAlgebra R R where
  S := .id
  mSid := by ext; simp
  midS := by ext; simp

@[simp]
theorem S_apply (r : R) : S (R := R) r = r := rfl

end CommSemiring
