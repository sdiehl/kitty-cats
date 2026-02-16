import KittyCats.NatTrans

open Category

-- Awodey, Ch 9
structure Adjunction {C : Type u₁} {D : Type u₂} [Category C] [Category D]
    (F : CFunctor D C) (G : CFunctor C D) where
  unit : NatTrans (CFunctor.identity D) (CFunctor.compose F G)
  counit : NatTrans (CFunctor.compose G F) (CFunctor.identity C)
  -- triangle identities (zig-zag)
  left_triangle : ∀ (a : D),
    F.map (unit.app a) ≫ counit.app (F.obj a) = Category.id
  right_triangle : ∀ (b : C),
    unit.app (G.obj b) ≫ G.map (counit.app b) = Category.id

attribute [simp] Adjunction.left_triangle Adjunction.right_triangle
