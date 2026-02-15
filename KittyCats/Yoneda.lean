import KittyCats.NatTrans
import KittyCats.Instances

open Category

-- Awodey, Ch 8

-- A presheaf on C is a contravariant functor from C to Type, i.e., a functor
-- from Cᵒᵖ to Type. The category of presheaves is the ambient universe in
-- which the Yoneda lemma lives.
abbrev Presheaf (C : Type u) [Category.{u,v} C] := CFunctor (Op C) (Type v)

-- Awodey, Def 8.1
-- The Yoneda embedding sends each object a to the representable presheaf
-- Hom(-, a). A morphism f in Cᵒᵖ (i.e., a morphism in C going the other way)
-- acts by precomposition.
def yoneda (C : Type u) [inst : Category.{u,v} C] (a : C) : Presheaf C where
  obj b := Hom b.unop a
  map f g := f ≫ g
  map_id _ := funext fun g => id_comp g
  map_comp f₁ f₂ := funext fun g => by
    dsimp [Category.comp]
    exact @assoc C inst _ _ _ _ f₂ f₁ g

-- Awodey, Lemma 8.2 (forward direction)
-- Given a natural transformation α : y(a) ⟹ F, evaluate the component at a
-- on the identity morphism to obtain an element of F(a). This is the
-- "evaluation at id" map that extracts the element determining α.
def yonedaFwd {C : Type u} [inst : Category.{u,v} C]
    {a : C} {F : Presheaf C}
    (α : NatTrans (yoneda C a) F) : F.obj (Op.op a) :=
  α.app (Op.op a) Category.id

-- Awodey, Lemma 8.2 (backward direction)
-- Given an element x : F(a), build a natural transformation y(a) ⟹ F whose
-- component at b sends f : Hom(b, a) to F(f)(x). Naturality follows from
-- functoriality of F.
def yonedaBwd {C : Type u} [inst : Category.{u,v} C]
    {a : C} {F : Presheaf C}
    (x : F.obj (Op.op a)) : NatTrans (yoneda C a) F where
  app b f := F.map f x
  naturality {b c} f := by
    -- Pointwise, the goal reduces to F.map(g ≫ f)(x) = F.map(f)(F.map(g)(x))
    -- which is functoriality of F (map_comp) applied to x.
    funext g
    dsimp [Category.comp]
    exact congrFun (F.map_comp g f) x

-- Awodey, Thm 8.3 (Yoneda lemma, first round-trip)
-- Evaluating at id the transformation built from x recovers x.
-- This is immediate from F.map_id: F(id)(x) = x.
theorem yoneda_fwd_bwd {C : Type u} [inst : Category.{u,v} C]
    {a : C} {F : Presheaf C} (x : F.obj (Op.op a)) :
    yonedaFwd (yonedaBwd x) = x :=
  congrFun (F.map_id (Op.op a)) x

-- Awodey, Thm 8.3 (Yoneda lemma, second round-trip)
-- Rebuilding a transformation from its value at id recovers the original.
-- The key step uses naturality of α: for f : Hom(b, a) viewed as a morphism
-- Op.op a → b in Cᵒᵖ, naturality gives α_b(f ≫ id) = F(f)(α_a(id)), and
-- comp_id reduces the left side to α_b(f).
theorem yoneda_bwd_fwd {C : Type u} [inst : Category.{u,v} C]
    {a : C} {F : Presheaf C} (α : NatTrans (yoneda C a) F) :
    yonedaBwd (yonedaFwd α) = α := by
  ext b
  funext f
  simp only [yonedaFwd, yonedaBwd]
  have nat := congrFun (α.naturality (a := Op.op a) (b := b) f) Category.id
  simp [yoneda, Category.comp] at nat
  exact nat.symm

-- Awodey, Cor 8.4
-- The Yoneda embedding on morphisms: a morphism f : a → b in C induces a
-- natural transformation y(a) ⟹ y(b) whose component at c sends
-- g : Hom(c, a) to g ≫ f : Hom(c, b). This is postcomposition by f.
def yonedaMap {C : Type u} [inst : Category.{u,v} C]
    {a b : C} (f : Hom a b) : NatTrans (yoneda C a) (yoneda C b) where
  app c g := g ≫ f
  naturality {c d} h := by
    funext g
    simp [yoneda, Category.comp, assoc]

-- Awodey, Cor 8.4 (fully faithful, forward)
-- Extracting the morphism from the embedding recovers the original: the
-- component at a evaluated on id gives f back, since id ≫ f = f.
theorem yoneda_map_eval {C : Type u} [inst : Category.{u,v} C]
    {a b : C} (f : Hom a b) :
    (yonedaMap f).app (Op.op a) Category.id = f := by
  simp [yonedaMap]

-- Awodey, Cor 8.4 (fully faithful, backward)
-- Re-embedding the extracted morphism recovers the transformation. This is the
-- Yoneda lemma specialized to the representable presheaf y(b): naturality of α
-- at f forces each component to be determined by α_a(id).
theorem yoneda_eval_map {C : Type u} [inst : Category.{u,v} C]
    {a b : C} (α : NatTrans (yoneda C a) (yoneda C b)) :
    yonedaMap (α.app (Op.op a) Category.id) = α := by
  ext c
  funext f
  simp [yonedaMap]
  have nat := congrFun (α.naturality (a := Op.op a) (b := c) f) Category.id
  simp [yoneda, Category.comp] at nat
  exact nat.symm
