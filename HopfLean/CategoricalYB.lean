import Mathlib.CategoryTheory.Monoidal.Braided

namespace CategoryTheory

open Category

open MonoidalCategory

open BraidedCategory

theorem cat_yang_baxter {C : Type u} [Category.{v, u}    C] [MonoidalCategory C]
    [self : BraidedCategory C] :
    ∀ X Y Z : C, (α_ X Y Z).hom ≫ (((𝟙 X) ⊗ (β_ Y Z).hom) ≫ ((α_ X Z Y).inv ≫
    (((β_ X Z).hom ⊗ (𝟙 Y)) ≫ ((α_ Z X Y).hom ≫ ((𝟙 Z) ⊗ (β_ X Y).hom))))) =
    ((β_ X Y).hom ⊗ (𝟙 Z)) ≫ ((α_ Y X Z).hom ≫ (((𝟙 Y) ⊗ (β_ X Z).hom) ≫
    ((α_ Y Z X).inv ≫ (((β_ Y Z).hom ⊗ (𝟙 X)) ≫ (α_ Z Y X).hom)))) := by
  intros X Y Z
  have key : ∀ X Y Z : C, (α_ X Y Z).hom ≫ (((𝟙 X) ⊗ (β_ Y Z).hom) ≫
      ((α_ X Z Y).inv ≫ (((β_ X Z).hom ⊗ (𝟙 Y)) ≫ (α_ Z X Y).hom))) =
      (β_ (X ⊗ Y) Z).hom := by
    intros X Y Z
    have this₁ : ((α_ X Y Z).inv ≫ (β_ (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv) ≫
        (α_ Z X Y).hom = ((𝟙 X) ⊗ (β_ Y Z).hom) ≫ ((α_ X Z Y).inv ≫
        (((β_ X Z).hom ⊗ (𝟙 Y)) ≫ (α_ Z X Y).hom)) := by
      rw [eq_whisker (hexagon_reverse X Y Z) (α_ Z X Y).hom]; simp
    simp only [assoc, Iso.inv_hom_id, comp_id] at this₁
    have this₂ : (α_ X Y Z).hom ≫ (((α_ X Y Z).inv ≫ (β_ (X ⊗ Y) Z).hom ≫
        (α_ Z X Y).inv) ≫ (α_ Z X Y).hom) = (α_ X Y Z).hom ≫
        (((𝟙 X) ⊗ (β_ Y Z).hom) ≫ ((α_ X Z Y).inv ≫ (((β_ X Z).hom ⊗ (𝟙 Y)) ≫
        (α_ Z X Y).hom))) := by
      rw [← whisker_eq (α_ X Y Z).hom this₁]; simp
    simp only [assoc, Iso.inv_hom_id, comp_id, Iso.hom_inv_id_assoc] at this₂
    rw [this₂]
  have aux : (α_ X Y Z).hom ≫ (𝟙 X ⊗ (β_ Y Z).hom) ≫ (α_ X Z Y).inv ≫
      ((β_ X Z).hom ⊗ 𝟙 Y) ≫ (α_ Z X Y).hom ≫ (𝟙 Z ⊗ (β_ X Y).hom) =
      ((α_ X Y Z).hom ≫ (𝟙 X ⊗ (β_ Y Z).hom) ≫ (α_ X Z Y).inv ≫
      ((β_ X Z).hom ⊗ 𝟙 Y) ≫ (α_ Z X Y).hom) ≫ (𝟙 Z ⊗ (β_ X Y).hom) := by
    simp
  rw [aux, key X Y Z, key Y X Z, braiding_naturality (β_ X Y).hom (𝟙 Z)]

end CategoryTheory
