import KittyCats.Morphism

namespace KittyCats

open Category

-- Mac Lane, Ch VII
class MonoidalCategory (C : Type u) [Category C] where
  tensorObj : C → C → C
  tensorHom : {a b c d : C} → Hom a b → Hom c d → Hom (tensorObj a c) (tensorObj b d)
  tensorUnit : C
  associator : (a b c : C) → Iso (tensorObj (tensorObj a b) c) (tensorObj a (tensorObj b c))
  leftUnitor : (a : C) → Iso (tensorObj tensorUnit a) a
  rightUnitor : (a : C) → Iso (tensorObj a tensorUnit) a
  tensor_id : {a b : C} → tensorHom (Category.id (a := a)) (Category.id (a := b)) = Category.id
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

namespace MonoidalCategory

scoped infixl:70 " ⊗ " => MonoidalCategory.tensorObj

end MonoidalCategory

-- Mac Lane, Ch XI
class BraidedCategory (C : Type u) [Category C] [MonoidalCategory C] where
  braiding : (a b : C) → Iso (MonoidalCategory.tensorObj a b) (MonoidalCategory.tensorObj b a)
  hexagon_fwd : (a b c : C) →
    (MonoidalCategory.associator a b c).hom ≫
      (braiding a (MonoidalCategory.tensorObj b c)).hom ≫
      (MonoidalCategory.associator b c a).hom =
    MonoidalCategory.tensorHom (braiding a b).hom Category.id ≫
      (MonoidalCategory.associator b a c).hom ≫
      MonoidalCategory.tensorHom Category.id (braiding a c).hom
  hexagon_bwd : (a b c : C) →
    (MonoidalCategory.associator a b c).inv ≫
      (braiding (MonoidalCategory.tensorObj a b) c).hom ≫
      (MonoidalCategory.associator c a b).inv =
    MonoidalCategory.tensorHom Category.id (braiding b c).hom ≫
      (MonoidalCategory.associator a c b).inv ≫
      MonoidalCategory.tensorHom (braiding a c).hom Category.id

-- Mac Lane, Ch XI
class SymmetricCategory (C : Type u) [Category C] [MonoidalCategory C]
    extends BraidedCategory C where
  symmetry : (a b : C) → (braiding a b).hom ≫ (braiding b a).hom = Category.id

end KittyCats
