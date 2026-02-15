import KittyCats.Functor

namespace KittyCats

open Category

-- Awodey, Ch 7
structure NatTrans {C : Type u₁} {D : Type u₂} [Category C] [Category D]
    (F G : KittyCats.Functor C D) where
  app : (a : C) → Hom (F.obj a) (G.obj a)
  naturality : {a b : C} → (f : Hom a b) →
    F.map f ≫ app b = app a ≫ G.map f

namespace NatTrans

def ident {C : Type u₁} {D : Type u₂} [Category C] [Category D]
    (F : KittyCats.Functor C D) : NatTrans F F where
  app _ := Category.id
  naturality f := by rw [Category.id_comp, Category.comp_id]

def vcomp {C : Type u₁} {D : Type u₂} [Category C] [Category D]
    {F G H : KittyCats.Functor C D}
    (α : NatTrans F G) (β : NatTrans G H) : NatTrans F H where
  app a := α.app a ≫ β.app a
  naturality f := by
    simp only [← Category.assoc]
    rw [α.naturality]
    simp only [Category.assoc]
    rw [β.naturality]

end NatTrans

-- Awodey, Ch 7
structure NatIso {C : Type u₁} {D : Type u₂} [Category C] [Category D]
    (F G : KittyCats.Functor C D) where
  fwd : NatTrans F G
  bwd : NatTrans G F
  fwd_bwd : ∀ (a : C), fwd.app a ≫ bwd.app a = Category.id
  bwd_fwd : ∀ (a : C), bwd.app a ≫ fwd.app a = Category.id

end KittyCats
