import Mathlib.RingTheory.TensorProduct

open scoped TensorProduct

open LinearMap

class Coalgebra (R : Type u) (A : Type v) [CommRing R] [AddCommGroup A] [Module R A] where
  comul : A →ₗ[R] A ⊗[R] A
  counit : A →ₗ[R] R
  coassoc : ∀ a : A, (TensorProduct.assoc R A A A) ((TensorProduct.map comul id) (comul a)) = ((TensorProduct.map id comul) (comul a))
  counit_id : ∀ a : A, (TensorProduct.lid R A) ((TensorProduct.map counit id) (comul a)) = a
  id_counit : ∀ a : A, (TensorProduct.rid R A) ((TensorProduct.map id counit) (comul a)) = a

noncomputable
def Finsupp.Coalgebra (R : Type u) (S : Type v) [CommRing R] : Coalgebra R (S →₀ R) where
  comul := Finsupp.total S ((S →₀ R) ⊗[R] (S →₀ R)) R (fun s ↦ Finsupp.single s 1 ⊗ₜ Finsupp.single s 1)
  counit := Finsupp.total S R R (fun _ ↦ 1)
  coassoc := by
    intros b; rw [Finsupp.total_apply R b]
    rw [map_finsupp_sum (TensorProduct.map (Finsupp.total S ((S →₀ R) ⊗[R] (S →₀ R)) R fun s => (fun₀ | s => 1) ⊗ₜ[R] fun₀ | s => 1) LinearMap.id) b (fun i a => a • (fun₀ | i => 1) ⊗ₜ[R] fun₀ | i => 1)]; simp
    rw [map_finsupp_sum (TensorProduct.map LinearMap.id (Finsupp.total S ((S →₀ R) ⊗[R] (S →₀ R)) R fun s => (fun₀ | s => 1) ⊗ₜ[R] fun₀ | s => 1)) b (fun i a => a • (fun₀ | i => 1) ⊗ₜ[R] fun₀ | i => 1)]; simp
    exact map_finsupp_sum (TensorProduct.assoc R (S →₀ R) (S →₀ R) (S →₀ R)) b fun a b => b • ((fun₀ | a => 1) ⊗ₜ[R] fun₀ | a => 1) ⊗ₜ[R] fun₀ | a => 1
  counit_id := by
    intros b; rw [Finsupp.total_apply R b]
    rw [map_finsupp_sum (TensorProduct.map (Finsupp.total S R R fun _ => 1) LinearMap.id) b (fun i a ↦ a • ((fun₀ | i => 1) ⊗ₜ[R] fun₀ | i => 1))]; simp
    rw [map_finsupp_sum (TensorProduct.lid R (S →₀ R)) b (fun i a ↦ a • 1 ⊗ₜ[R] fun₀ | i => 1)]; simp
  id_counit := by
    intros b; rw [Finsupp.total_apply R b]
    rw [map_finsupp_sum (TensorProduct.map LinearMap.id (Finsupp.total S R R fun _ => 1)) b (fun i a ↦ a • ((fun₀ | i => 1) ⊗ₜ[R] fun₀ | i => 1))]; simp
    rw [map_finsupp_sum (TensorProduct.rid R (S →₀ R)) b (fun i a ↦ a • (fun₀ | i => 1) ⊗ₜ[R] 1)]; simp

noncomputable
def Finsupp'.Coalgebra (R : Type u) (S : Type v) [CommRing R] : Coalgebra R (S →₀ R) where
  comul := Finsupp.total S ((S →₀ R) ⊗[R] (S →₀ R)) R (fun s ↦ Finsupp.single s 1 ⊗ₜ Finsupp.single s 1)
  counit := Finsupp.total S R R (fun _ ↦ 1)
  coassoc := by
    intro b
    apply Finsupp.induction_linear b <;> aesop
  counit_id := by
    intro b
    apply Finsupp.induction_linear b <;> aesop
  id_counit := by
    intro b
    apply Finsupp.induction_linear b <;> aesop
