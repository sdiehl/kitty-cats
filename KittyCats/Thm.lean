import KittyCats.Closed
import KittyCats.Morphism

open Category HasProducts HasExponentials

variable {C : Type u} [Category C]

-- Awodey, Prop 5.4
-- Pairing is natural: precomposing into a product distributes over the components.
-- That is, h followed by <f, g> is the same as <h then f, h then g>.
theorem pair_comp [HasProducts C] {a b c d : C}
    (f : Hom d a) (g : Hom d b) (h : Hom c d) :
    h ≫ pair f g = pair (h ≫ f) (h ≫ g) :=
  HasProducts.pair_unique (h ≫ f) (h ≫ g) (h ≫ pair f g)
    (by simp [assoc]) (by simp [assoc])

-- Awodey, Ch 5 (corollary of product UMP)
-- The diagonal followed by a product map is just pairing.
-- Duplicating and then applying f and g to each copy is the same as pairing f and g directly.
theorem diag_prodMap [Cartesian C] {a b c : C} (f : Hom a b) (g : Hom a c) :
    Cartesian.diag ≫ Cartesian.prodMap f g = pair f g := by
  unfold Cartesian.diag Cartesian.prodMap
  rw [pair_comp]
  simp [← assoc]

-- Awodey, Prop 6.1
-- Currying the evaluation map yields the identity on the exponential object.
-- This is the counit equation of the curry/eval adjunction: curry(eval) = id.
theorem curry_eval [HasProducts C] [HasExponentials C] {a b : C} :
    curry (eval (a := a) (b := b)) = Category.id := by
  unfold eval
  simp

-- Awodey, Prop 2.2
-- Every isomorphism is a monomorphism: if two morphisms agree after composing
-- with an iso, they were already equal. The key step is postcomposing both sides
-- of the hypothesis with the inverse, which cancels the iso.
theorem iso_mono {a b : C} (i : Iso a b) : Mono i.hom where
  cancel_right g h hyp := by
    -- postcompose both sides with the inverse to cancel
    have : (g ≫ i.hom) ≫ i.inv = (h ≫ i.hom) ≫ i.inv := by rw [hyp]
    simp [assoc] at this
    exact this

-- Awodey, Prop 2.2
-- Every isomorphism is an epimorphism: if two morphisms agree after precomposing
-- with an iso, they were already equal. Dual to the mono case, we precompose
-- with the inverse to cancel.
theorem iso_epi {a b : C} (i : Iso a b) : Epi i.hom where
  cancel_left g h hyp := by
    -- precompose both sides with the inverse to cancel
    have : i.inv ≫ (i.hom ≫ g) = i.inv ≫ (i.hom ≫ h) := by rw [hyp]
    simp [← assoc] at this
    exact this

-- Awodey, Def 2.9
-- An object is terminal if every object has exactly one morphism into it.
structure IsTerminal (t : C) where
  to : {a : C} → Hom a t
  unique : {a : C} → (f : Hom a t) → f = to

-- Awodey, Prop 2.10
-- Any two terminal objects are isomorphic. The morphisms are the unique maps
-- guaranteed by terminality. The round-trips are identity because both the
-- round-trip and the identity are maps into a terminal object, and there can
-- be only one such map.
def terminal_unique {t₁ t₂ : C} (ht₁ : IsTerminal t₁) (ht₂ : IsTerminal t₂) :
    Iso t₁ t₂ where
  hom := ht₂.to
  inv := ht₁.to
  hom_inv :=
    let roundtrip := ht₂.to ≫ ht₁.to
    (ht₁.unique roundtrip).trans (ht₁.unique Category.id).symm
  inv_hom :=
    let roundtrip := ht₁.to ≫ ht₂.to
    (ht₂.unique roundtrip).trans (ht₂.unique Category.id).symm
