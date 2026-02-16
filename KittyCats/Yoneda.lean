import KittyCats.NatTrans
import KittyCats.Instances

open Category

-- Awodey, Ch 8

-- A presheaf on C is a functor C^op -> Type.
abbrev Presheaf (C : Type u) [Category.{u,v} C] := CFunctor (Op C) (Type v)

-- Awodey, Def 8.1
-- The Yoneda embedding: $a \mapsto \mathrm{Hom}(-, a)$.
def yoneda (C : Type u) [inst : Category.{u,v} C] (a : C) : Presheaf C where
  obj b := Hom b.unop a
  map f g := f ≫ g
  map_id _ := funext fun g => id_comp g
  map_comp f₁ f₂ := funext fun g => by
    dsimp [Category.comp]
    exact @assoc C inst _ _ _ _ f₂ f₁ g

-- Awodey, Lemma 8.2 (forward direction)
-- $\alpha \mapsto \alpha_a(\mathrm{id}_a)$.
def yonedaFwd {C : Type u} [inst : Category.{u,v} C]
    {a : C} {F : Presheaf C}
    (α : NatTrans (yoneda C a) F) : F.obj (Op.op a) :=
  α.app (Op.op a) Category.id

-- Awodey, Lemma 8.2 (backward direction)
-- $x \mapsto (\alpha_b(f) = F(f)(x))$.
def yonedaBwd {C : Type u} [inst : Category.{u,v} C]
    {a : C} {F : Presheaf C}
    (x : F.obj (Op.op a)) : NatTrans (yoneda C a) F where
  app b f := F.map f x
  naturality {b c} f := by
    -- $F(g \circ f)(x) = F(f)(F(g)(x))$ by functoriality.
    funext g
    dsimp [Category.comp]
    exact congrFun (F.map_comp g f) x

-- Awodey, Thm 8.3 (Yoneda lemma, first round-trip)
-- $F(\mathrm{id})(x) = x$ by functoriality.
theorem yoneda_fwd_bwd {C : Type u} [inst : Category.{u,v} C]
    {a : C} {F : Presheaf C} (x : F.obj (Op.op a)) :
    yonedaFwd (yonedaBwd x) = x :=
  congrFun (F.map_id (Op.op a)) x

-- Awodey, Thm 8.3 (Yoneda lemma, second round-trip)
-- Naturality gives $\alpha_b(f) = F(f)(\alpha_a(\mathrm{id}))$.
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
-- $y(f)_c(g) = g \circ f$ (postcomposition).
def yonedaMap {C : Type u} [inst : Category.{u,v} C]
    {a b : C} (f : Hom a b) : NatTrans (yoneda C a) (yoneda C b) where
  app c g := g ≫ f
  naturality {c d} h := by
    funext g
    simp [yoneda, Category.comp, assoc]

-- Awodey, Cor 8.4 (fully faithful, forward)
-- $y(f)_a(\mathrm{id}) = f$.
theorem yoneda_map_eval {C : Type u} [inst : Category.{u,v} C]
    {a b : C} (f : Hom a b) :
    (yonedaMap f).app (Op.op a) Category.id = f := by
  simp [yonedaMap]

-- Awodey, Cor 8.4 (fully faithful, backward)
-- $y(\alpha_a(\mathrm{id})) = \alpha$ by naturality.
theorem yoneda_eval_map {C : Type u} [inst : Category.{u,v} C]
    {a b : C} (α : NatTrans (yoneda C a) (yoneda C b)) :
    let f := α.app (Op.op a) Category.id
    yonedaMap f = α := by
  ext c
  funext f
  simp [yonedaMap]
  have nat := congrFun (α.naturality (a := Op.op a) (b := c) f) Category.id
  simp [yoneda, Category.comp] at nat
  exact nat.symm
