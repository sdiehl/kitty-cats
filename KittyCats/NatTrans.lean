import KittyCats.Functor

open Category

variable {C : Type u₁} {D : Type u₂} [Category C] [Category D]

-- Awodey, Ch 7
@[ext]
structure NatTrans (F G : CFunctor C D) where
  app : (a : C) → Hom (F.obj a) (G.obj a)
  naturality : {a b : C} → (f : Hom a b) →
    F.map f ≫ app b = app a ≫ G.map f

namespace NatTrans

def ident (F : CFunctor C D) : NatTrans F F where
  app _ := Category.id
  naturality _ := by simp

def vcomp {F G H : CFunctor C D}
    (α : NatTrans F G) (β : NatTrans G H) : NatTrans F H where
  app a := α.app a ≫ β.app a
  naturality f := by
    simp only [← assoc]
    rw [α.naturality]
    simp only [assoc]
    rw [β.naturality]

end NatTrans

-- Awodey, Ch 7
structure NatIso (F G : CFunctor C D) where
  fwd : NatTrans F G
  bwd : NatTrans G F
  fwd_bwd : ∀ (a : C), fwd.app a ≫ bwd.app a = Category.id
  bwd_fwd : ∀ (a : C), bwd.app a ≫ fwd.app a = Category.id

-- $\alpha_a \circ \beta_a = \mathrm{id}$ and $\beta_a \circ \alpha_a = \mathrm{id}$
attribute [simp] NatIso.fwd_bwd NatIso.bwd_fwd
