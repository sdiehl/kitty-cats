import KittyCats.Morphism
import KittyCats.Limits

open Category

-- Awodey, Ch 3
-- Duality: reverse all morphisms.

variable {C : Type u} [Category C]

-- Awodey, Prop 2.3
-- Terminal in $\mathcal{C}$ is initial in $\mathcal{C}^{\mathrm{op}}$.
instance [ht : HasTerminal C] : HasInitial (Op C) where
  initial := Op.op ht.terminal
  fromInitial := ht.toTerminal
  fromInitial_unique f := ht.toTerminal_unique f

-- Awodey, Prop 2.3
-- Initial in $\mathcal{C}$ is terminal in $\mathcal{C}^{\mathrm{op}}$.
instance [hi : HasInitial C] : HasTerminal (Op C) where
  terminal := Op.op hi.initial
  toTerminal := hi.fromInitial
  toTerminal_unique f := hi.fromInitial_unique f

-- Awodey, Prop 5.1
-- Products in $\mathcal{C}$ are coproducts in $\mathcal{C}^{\mathrm{op}}$.
instance [hp : HasProducts C] : HasCoproducts (Op C) where
  coprod a b := Op.op (hp.prod a.unop b.unop)
  inl := hp.fst
  inr := hp.snd
  copair f g := hp.pair f g
  copair_inl f g := hp.pair_fst f g
  copair_inr f g := hp.pair_snd f g
  copair_unique f g h hinl hinr := hp.pair_unique f g h hinl hinr

-- Awodey, Prop 5.1
-- Coproducts in $\mathcal{C}$ are products in $\mathcal{C}^{\mathrm{op}}$.
instance [hc : HasCoproducts C] : HasProducts (Op C) where
  prod a b := Op.op (hc.coprod a.unop b.unop)
  fst := hc.inl
  snd := hc.inr
  pair f g := hc.copair f g
  pair_fst f g := hc.copair_inl f g
  pair_snd f g := hc.copair_inr f g
  pair_unique f g h hfst hsnd := hc.copair_unique f g h hfst hsnd

-- Awodey, Prop 2.2
-- Mono in $\mathcal{C}$ is epi in $\mathcal{C}^{\mathrm{op}}$.
def Mono.toOpEpi {a b : C} {f : Hom a b} (m : Mono f) :
    @Epi (Op C) _ (Op.op b) (Op.op a) f where
  cancel_left g h hyp := m.cancel_right g h hyp

-- Awodey, Prop 2.2
-- Epi in $\mathcal{C}$ is mono in $\mathcal{C}^{\mathrm{op}}$.
def Epi.toOpMono {a b : C} {f : Hom a b} (e : Epi f) :
    @Mono (Op C) _ (Op.op b) (Op.op a) f where
  cancel_right g h hyp := e.cancel_left g h hyp
