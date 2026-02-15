import KittyCats.Limits

open Category

-- Awodey, Ch 5
class Cartesian (C : Type u) [Category C] extends HasTerminal C, HasProducts C

-- Awodey, Ch 5
class Cocartesian (C : Type u) [Category C] extends HasInitial C, HasCoproducts C

namespace Cartesian

variable {C : Type u} [Category C] [Cartesian C]
open HasProducts

def diag {a : C} : Hom a (prod a a) :=
  pair Category.id Category.id

def prodMap {a b c d : C} (f : Hom a c) (g : Hom b d) : Hom (prod a b) (prod c d) :=
  pair (fst ≫ f) (snd ≫ g)

end Cartesian

namespace Cocartesian

variable {C : Type u} [Category C] [Cocartesian C]
open HasCoproducts

def codiag {a : C} : Hom (coprod a a) a :=
  copair Category.id Category.id

def coprodMap {a b c d : C} (f : Hom a c) (g : Hom b d) :
    Hom (coprod a b) (coprod c d) :=
  copair (f ≫ inl) (g ≫ inr)

end Cocartesian
