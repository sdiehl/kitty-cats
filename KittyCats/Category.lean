namespace KittyCats

universe u v

-- Awodey, Ch 1
class Category (Obj : Type u) where
  Hom : Obj → Obj → Type v
  id : {a : Obj} → Hom a a
  comp : {a b c : Obj} → Hom a b → Hom b c → Hom a c
  id_comp : {a b : Obj} → (f : Hom a b) → comp id f = f
  comp_id : {a b : Obj} → (f : Hom a b) → comp f id = f
  assoc : {a b c d : Obj} → (f : Hom a b) → (g : Hom b c) → (h : Hom c d) →
    comp (comp f g) h = comp f (comp g h)

namespace Category

scoped infixr:80 " ≫ " => Category.comp

end Category

-- Awodey, Ch 3
structure Op (α : Type u) where
  unop : α

namespace Op

def op (a : α) : Op α := ⟨a⟩

instance [inst : Category Obj] : Category (Op Obj) where
  Hom a b := inst.Hom b.unop a.unop
  id := inst.id
  comp f g := inst.comp g f
  id_comp f := inst.comp_id f
  comp_id f := inst.id_comp f
  assoc f g h := (inst.assoc h g f).symm

end Op

end KittyCats
