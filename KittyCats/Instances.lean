import KittyCats.Closed
import KittyCats.Product

open Category

instance : Category (Type u) where
  Hom a b := a → b
  id := fun x => x
  comp f g := g ∘ f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

instance : HasTerminal (Type u) where
  terminal := PUnit
  toTerminal := fun _ => PUnit.unit
  toTerminal_unique _ := funext fun _ => rfl

instance : HasInitial (Type u) where
  initial := PEmpty
  fromInitial := PEmpty.elim
  fromInitial_unique _ := funext fun e => PEmpty.elim e

instance : HasProducts (Type u) where
  prod := Prod
  fst := Prod.fst
  snd := Prod.snd
  pair f g := fun x => (f x, g x)
  pair_fst _ _ := rfl
  pair_snd _ _ := rfl
  pair_unique _ _ _ hf hg := funext fun x => Prod.ext (congrFun hf x) (congrFun hg x)

instance : HasCoproducts (Type u) where
  coprod := Sum
  inl := Sum.inl
  inr := Sum.inr
  copair := Sum.elim
  copair_inl _ _ := rfl
  copair_inr _ _ := rfl
  copair_unique _ _ _ hf hg := funext fun
    | .inl a => congrFun hf a
    | .inr b => congrFun hg b

instance : HasExponentials (Type u) where
  exp a b := a → b
  curry f c a := f (c, a)
  uncurry g p := g p.1 p.2
  curry_uncurry _ := rfl
  uncurry_curry _ := funext fun ⟨_, _⟩ => rfl

instance : Cartesian (Type u) where

instance : CCC (Type u) where
