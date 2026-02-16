import KittyCats.Category

open Category

universe u₁ u₂ u₃

-- Awodey, Ch 1.2
structure CFunctor (C : Type u₁) (D : Type u₂) [Category C] [Category D] where
  obj : C → D
  map : {a b : C} → Hom a b → Hom (obj a) (obj b)
  map_id : (a : C) → map (Category.id (a := a)) = Category.id
  map_comp : {a b c : C} → (f : Hom a b) → (g : Hom b c) →
    map (f ≫ g) = map f ≫ map g

-- $F(\mathrm{id}) = \mathrm{id}$ and $F(f \circ g) = F(f) \circ F(g)$
attribute [simp] CFunctor.map_id CFunctor.map_comp

namespace CFunctor

def identity (C : Type u₁) [Category C] : CFunctor C C where
  obj a := a
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

def compose {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category C] [Category D] [Category E]
    (F : CFunctor C D) (G : CFunctor D E) : CFunctor C E where
  obj a := G.obj (F.obj a)
  map f := G.map (F.map f)
  map_id a := by simp
  map_comp f g := by simp

end CFunctor

abbrev Endofunctor (C : Type u₁) [Category C] := CFunctor C C
