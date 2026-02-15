import KittyCats.Category

namespace KittyCats

open Category

-- Awodey, Ch 1.2
structure Functor (C : Type u₁) (D : Type u₂) [Category C] [Category D] where
  obj : C → D
  map : {a b : C} → Hom a b → Hom (obj a) (obj b)
  map_id : (a : C) → map (Category.id (a := a)) = Category.id
  map_comp : {a b c : C} → (f : Hom a b) → (g : Hom b c) →
    map (f ≫ g) = map f ≫ map g

namespace Functor

def identity (C : Type u₁) [Category C] : KittyCats.Functor C C where
  obj a := a
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

def compose {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category C] [Category D] [Category E]
    (F : KittyCats.Functor C D) (G : KittyCats.Functor D E) : KittyCats.Functor C E where
  obj a := G.obj (F.obj a)
  map f := G.map (F.map f)
  map_id a := by rw [F.map_id, G.map_id]
  map_comp f g := by rw [F.map_comp, G.map_comp]

end Functor

abbrev Endofunctor (C : Type u₁) [Category C] := KittyCats.Functor C C

end KittyCats
