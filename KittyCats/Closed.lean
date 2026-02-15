import KittyCats.Cartesian

open Category

-- Awodey, Ch 6
class HasExponentials (C : Type u) [Category C] [HasProducts C] where
  exp : C → C → C
  curry : {a b c : C} → Hom (HasProducts.prod c a) b → Hom c (exp a b)
  uncurry : {a b c : C} → Hom c (exp a b) → Hom (HasProducts.prod c a) b
  curry_uncurry : {a b c : C} → (g : Hom c (exp a b)) → curry (uncurry g) = g
  uncurry_curry : {a b c : C} → (f : Hom (HasProducts.prod c a) b) → uncurry (curry f) = f

-- curry and uncurry witness the exponential adjunction
attribute [simp] HasExponentials.curry_uncurry HasExponentials.uncurry_curry

namespace HasExponentials

variable {C : Type u} [Category C] [HasProducts C] [HasExponentials C]
open HasProducts

def eval {a b : C} : Hom (prod (exp a b) a) b :=
  uncurry Category.id

def const {a b : C} : Hom b (exp a b) :=
  curry (fst (a := b) (b := a))

end HasExponentials

-- Awodey, Ch 6
class CCC (C : Type u) [Category C] extends Cartesian C, HasExponentials C
