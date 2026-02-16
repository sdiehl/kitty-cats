import KittyCats.Category

open Category

-- Awodey, Ch 2
class HasTerminal (C : Type u) [Category C] where
  terminal : C
  toTerminal : {a : C} → Hom a terminal
  toTerminal_unique : {a : C} → (f : Hom a terminal) → f = toTerminal

-- Awodey, Ch 2
class HasInitial (C : Type u) [Category C] where
  initial : C
  fromInitial : {a : C} → Hom initial a
  fromInitial_unique : {a : C} → (f : Hom initial a) → f = fromInitial

-- Awodey, Ch 5
class HasProducts (C : Type u) [Category C] where
  prod : C → C → C
  fst : {a b : C} → Hom (prod a b) a
  snd : {a b : C} → Hom (prod a b) b
  pair : {a b c : C} → Hom c a → Hom c b → Hom c (prod a b)
  pair_fst : {a b c : C} → (f : Hom c a) → (g : Hom c b) → pair f g ≫ fst = f
  pair_snd : {a b c : C} → (f : Hom c a) → (g : Hom c b) → pair f g ≫ snd = g
  pair_unique : {a b c : C} → (f : Hom c a) → (g : Hom c b) → (h : Hom c (prod a b)) →
    h ≫ fst = f → h ≫ snd = g → h = pair f g

-- $\langle f, g \rangle \circ \pi_i = f$ or $g$
attribute [simp] HasProducts.pair_fst HasProducts.pair_snd

-- Awodey, Ch 5
class HasCoproducts (C : Type u) [Category C] where
  coprod : C → C → C
  inl : {a b : C} → Hom a (coprod a b)
  inr : {a b : C} → Hom b (coprod a b)
  copair : {a b c : C} → Hom a c → Hom b c → Hom (coprod a b) c
  copair_inl : {a b c : C} → (f : Hom a c) → (g : Hom b c) → inl ≫ copair f g = f
  copair_inr : {a b c : C} → (f : Hom a c) → (g : Hom b c) → inr ≫ copair f g = g
  copair_unique : {a b c : C} → (f : Hom a c) → (g : Hom b c) → (h : Hom (coprod a b) c) →
    inl ≫ h = f → inr ≫ h = g → h = copair f g

-- $\iota_i \circ [f, g] = f$ or $g$
attribute [simp] HasCoproducts.copair_inl HasCoproducts.copair_inr
