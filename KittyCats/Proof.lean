import KittyCats.Closed

open Category HasProducts HasExponentials

variable {C : Type u} [Category C]

-- Pairing is natural: precomposing into a product distributes over the components.
-- That is, h followed by <f, g> is the same as <h then f, h then g>.
theorem pair_comp [HasProducts C] {a b c d : C}
    (f : Hom d a) (g : Hom d b) (h : Hom c d) :
    h ≫ pair f g = pair (h ≫ f) (h ≫ g) :=
  HasProducts.pair_unique (h ≫ f) (h ≫ g) (h ≫ pair f g)
    (by simp [assoc]) (by simp [assoc])

-- The diagonal followed by a product map is just pairing.
-- Duplicating and then applying f and g to each copy is the same as pairing f and g directly.
theorem diag_prodMap [Cartesian C] {a b c : C} (f : Hom a b) (g : Hom a c) :
    Cartesian.diag ≫ Cartesian.prodMap f g = pair f g := by
  unfold Cartesian.diag Cartesian.prodMap
  rw [pair_comp]
  simp [← assoc]

-- Currying the evaluation map yields the identity on the exponential object.
-- This is the counit equation of the curry/eval adjunction: curry(eval) = id.
theorem curry_eval [HasProducts C] [HasExponentials C] {a b : C} :
    curry (eval (a := a) (b := b)) = Category.id := by
  unfold eval
  simp
