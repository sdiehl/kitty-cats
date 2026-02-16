import KittyCats.Morphism

open Category

-- Mac Lane, Ch VII
class MonoidalCategory (C : Type u) [Category C] where
  tensorObj : C → C → C
  tensorHom : {a b c d : C} → Hom a b → Hom c d → Hom (tensorObj a c) (tensorObj b d)
  tensorUnit : C
  associator : (a b c : C) → Iso (tensorObj (tensorObj a b) c) (tensorObj a (tensorObj b c))
  leftUnitor : (a : C) → Iso (tensorObj tensorUnit a) a
  rightUnitor : (a : C) → Iso (tensorObj a tensorUnit) a
  tensor_id : {a b : C} →
    tensorHom (Category.id (a := a)) (Category.id (a := b)) = Category.id
  tensor_comp : {a₁ b₁ c₁ a₂ b₂ c₂ : C} →
    (f₁ : Hom a₁ b₁) → (f₂ : Hom b₁ c₁) →
    (g₁ : Hom a₂ b₂) → (g₂ : Hom b₂ c₂) →
    tensorHom (f₁ ≫ f₂) (g₁ ≫ g₂) = tensorHom f₁ g₁ ≫ tensorHom f₂ g₂
  pentagon : (a b c d : C) →
    tensorHom (associator a b c).hom Category.id ≫
      (associator a (tensorObj b c) d).hom ≫
      tensorHom Category.id (associator b c d).hom =
    (associator (tensorObj a b) c d).hom ≫ (associator a b (tensorObj c d)).hom
  triangle : (a b : C) →
    (associator a tensorUnit b).hom ≫ tensorHom Category.id (leftUnitor b).hom =
    tensorHom (rightUnitor a).hom Category.id

-- $\mathrm{id} \otimes \mathrm{id} = \mathrm{id}$
attribute [simp] MonoidalCategory.tensor_id

namespace MonoidalCategory
scoped infixl:70 " ⊗ " => MonoidalCategory.tensorObj
end MonoidalCategory

open MonoidalCategory

-- Mac Lane, Ch XI
class BraidedCategory (C : Type u) [Category C] [MonoidalCategory C] where
  braiding : (a b : C) → Iso (a ⊗ b) (b ⊗ a)
  hexagon_fwd : (a b c : C) →
    (associator a b c).hom ≫ (braiding a (b ⊗ c)).hom ≫ (associator b c a).hom =
    tensorHom (braiding a b).hom Category.id ≫
      (associator b a c).hom ≫
      tensorHom Category.id (braiding a c).hom
  hexagon_bwd : (a b c : C) →
    (associator a b c).inv ≫ (braiding (a ⊗ b) c).hom ≫ (associator c a b).inv =
    tensorHom Category.id (braiding b c).hom ≫
      (associator a c b).inv ≫
      tensorHom (braiding a c).hom Category.id

-- Mac Lane, Ch XI
class SymmetricCategory (C : Type u) [Category C] [MonoidalCategory C]
    extends BraidedCategory C where
  symmetry : (a b : C) → (braiding a b).hom ≫ (braiding b a).hom = Category.id
