import KittyCats.Closed
import KittyCats.Morphism

open Category HasProducts HasExponentials

variable {C : Type u} [Category C]

-- Awodey, Prop 5.4
-- $h \circ \langle f, g \rangle = \langle h \circ f, h \circ g \rangle$.
theorem pair_comp [HasProducts C] {a b c d : C}
    (f : Hom d a) (g : Hom d b) (h : Hom c d) :
    h ≫ pair f g = pair (h ≫ f) (h ≫ g) :=
  HasProducts.pair_unique (h ≫ f) (h ≫ g) (h ≫ pair f g)
    (by simp [assoc]) (by simp [assoc])

-- Awodey, Ch 5
-- $\Delta \circ (f \times g) = \langle f, g \rangle$.
theorem diag_prodMap [Cartesian C] {a b c : C} (f : Hom a b) (g : Hom a c) :
    Cartesian.diag ≫ Cartesian.prodMap f g = pair f g := by
  unfold Cartesian.diag Cartesian.prodMap
  rw [pair_comp]
  simp [← assoc]

-- Awodey, Prop 6.1
-- $\mathrm{curry}(\mathrm{eval}) = \mathrm{id}$.
theorem curry_eval [HasProducts C] [HasExponentials C] {a b : C} :
    curry (eval (a := a) (b := b)) = Category.id := by
  unfold eval
  simp

-- Awodey, Prop 2.2
-- Every iso is mono: $g \circ f = h \circ f \implies g = h$.
theorem iso_mono {a b : C} (i : Iso a b) : Mono i.hom where
  cancel_right g h hyp := by
    -- postcompose with $f^{-1}$
    have : (g ≫ i.hom) ≫ i.inv = (h ≫ i.hom) ≫ i.inv := by rw [hyp]
    simp [assoc] at this
    exact this

-- Awodey, Prop 2.2
-- Every iso is epi: $f \circ g = f \circ h \implies g = h$.
theorem iso_epi {a b : C} (i : Iso a b) : Epi i.hom where
  cancel_left g h hyp := by
    -- precompose with $f^{-1}$
    have : i.inv ≫ (i.hom ≫ g) = i.inv ≫ (i.hom ≫ h) := by rw [hyp]
    simp [← assoc] at this
    exact this

-- Awodey, Def 2.9
-- Terminal: $\forall a, \exists! f : a \to t$.
structure IsTerminal (t : C) where
  to : {a : C} → Hom a t
  unique : {a : C} → (f : Hom a t) → f = to

-- Awodey, Prop 2.10
-- Terminal objects are unique up to isomorphism: $t_1 \cong t_2$.
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
