import KittyCats.Category

namespace KittyCats

open Category

-- Awodey, Ch 1
structure Iso {C : Type u} [Category C] (a b : C) where
  hom : Hom a b
  inv : Hom b a
  hom_inv : hom ≫ inv = Category.id
  inv_hom : inv ≫ hom = Category.id

-- Awodey, Ch 2
structure Mono {C : Type u} [Category C] {a b : C} (f : Hom a b) : Prop where
  cancel_right : ∀ {c : C} (g h : Hom c a), g ≫ f = h ≫ f → g = h

-- Awodey, Ch 2
structure Epi {C : Type u} [Category C] {a b : C} (f : Hom a b) : Prop where
  cancel_left : ∀ {c : C} (g h : Hom b c), f ≫ g = f ≫ h → g = h

-- Awodey, Ch 2
structure SplitMono {C : Type u} [Category C] {a b : C} (f : Hom a b) where
  leftInv : Hom b a
  left_inv_comp : f ≫ leftInv = Category.id

-- Awodey, Ch 2
structure SplitEpi {C : Type u} [Category C] {a b : C} (f : Hom a b) where
  rightInv : Hom b a
  comp_right_inv : rightInv ≫ f = Category.id

-- Awodey, Ch 4
class Groupoid (Obj : Type u) [Category Obj] where
  inv : {a b : Obj} → Hom a b → Hom b a
  comp_inv : {a b : Obj} → (f : Hom a b) → f ≫ inv f = Category.id
  inv_comp : {a b : Obj} → (f : Hom a b) → inv f ≫ f = Category.id

namespace Groupoid

def toIso {C : Type u} [Category C] [Groupoid C] {a b : C} (f : Hom a b) : Iso a b where
  hom := f
  inv := Groupoid.inv f
  hom_inv := Groupoid.comp_inv f
  inv_hom := Groupoid.inv_comp f

end Groupoid

end KittyCats
