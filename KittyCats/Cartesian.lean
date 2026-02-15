import KittyCats.Limits

namespace KittyCats

open Category

-- Awodey, Ch 5
class Cartesian (C : Type u) [Category C] extends HasTerminal C, HasProducts C

-- Awodey, Ch 5
class Cocartesian (C : Type u) [Category C] extends HasInitial C, HasCoproducts C

namespace Cartesian

variable {C : Type u} [Category C] [Cartesian C]

def diag {a : C} : Hom a (HasProducts.prod a a) :=
  HasProducts.pair Category.id Category.id

def prodMap {a b c d : C} (f : Hom a c) (g : Hom b d) :
    Hom (HasProducts.prod a b) (HasProducts.prod c d) :=
  HasProducts.pair (HasProducts.fst ≫ f) (HasProducts.snd ≫ g)

end Cartesian

namespace Cocartesian

variable {C : Type u} [Category C] [Cocartesian C]

def codiag {a : C} : Hom (HasCoproducts.coprod a a) a :=
  HasCoproducts.copair Category.id Category.id

def coprodMap {a b c d : C} (f : Hom a c) (g : Hom b d) :
    Hom (HasCoproducts.coprod a b) (HasCoproducts.coprod c d) :=
  HasCoproducts.copair (f ≫ HasCoproducts.inl) (g ≫ HasCoproducts.inr)

end Cocartesian

end KittyCats
