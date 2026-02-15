import KittyCats.Category

open Category

section
variable {C : Type u} [Category C]

-- Awodey, Ch 1
structure Iso (a b : C) where
  hom : Hom a b
  inv : Hom b a
  hom_inv : hom ≫ inv = Category.id
  inv_hom : inv ≫ hom = Category.id

-- round-trip in either direction is identity
attribute [simp] Iso.hom_inv Iso.inv_hom

-- Awodey, Ch 2
structure Mono {a b : C} (f : Hom a b) : Prop where
  cancel_right : ∀ {c : C} (g h : Hom c a), g ≫ f = h ≫ f → g = h

-- Awodey, Ch 2
structure Epi {a b : C} (f : Hom a b) : Prop where
  cancel_left : ∀ {c : C} (g h : Hom b c), f ≫ g = f ≫ h → g = h

-- Awodey, Ch 2
structure SplitMono {a b : C} (f : Hom a b) where
  leftInv : Hom b a
  left_inv_comp : f ≫ leftInv = Category.id

-- Awodey, Ch 2
structure SplitEpi {a b : C} (f : Hom a b) where
  rightInv : Hom b a
  comp_right_inv : rightInv ≫ f = Category.id

end

-- Awodey, Ch 4
class Groupoid (Obj : Type u) [Category Obj] where
  inv : {a b : Obj} → Hom a b → Hom b a
  comp_inv : {a b : Obj} → (f : Hom a b) → f ≫ inv f = Category.id
  inv_comp : {a b : Obj} → (f : Hom a b) → inv f ≫ f = Category.id

namespace Groupoid

variable {C : Type u} [Category C] [Groupoid C]

def toIso {a b : C} (f : Hom a b) : Iso a b where
  hom := f
  inv := Groupoid.inv f
  hom_inv := Groupoid.comp_inv f
  inv_hom := Groupoid.inv_comp f

end Groupoid
