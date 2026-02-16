import KittyCats.NatTrans

open Category

-- Awodey, Ch 7.5
-- Equivalence: $F \circ G \cong \mathrm{Id}$ and $G \circ F \cong \mathrm{Id}$.
structure CEquiv (C : Type u₁) (D : Type u₂) [Category C] [Category D] where
  fwd : CFunctor C D
  bwd : CFunctor D C
  unit : NatIso (CFunctor.identity C) (CFunctor.compose fwd bwd)
  counit : NatIso (CFunctor.compose bwd fwd) (CFunctor.identity D)

-- Awodey, Ch 3
-- $\mathcal{C}^{\mathrm{op}\,\mathrm{op}} \simeq \mathcal{C}$.
def opInvolution (C : Type u) [Category C] : CEquiv C (Op (Op C)) where
  fwd := {
    obj := fun a => Op.op (Op.op a)
    map := fun f => f
    map_id := fun _ => rfl
    map_comp := fun _ _ => rfl
  }
  bwd := {
    obj := fun a => a.unop.unop
    map := fun f => f
    map_id := fun _ => rfl
    map_comp := fun _ _ => rfl
  }
  unit := {
    fwd := {
      app := fun _ => Category.id
      naturality := fun _ => by simp [CFunctor.identity, CFunctor.compose]
    }
    bwd := {
      app := fun _ => Category.id
      naturality := fun _ => by simp [CFunctor.identity, CFunctor.compose]
    }
    fwd_bwd := fun _ => by simp
    bwd_fwd := fun _ => by simp
  }
  counit := {
    fwd := {
      app := fun _ => Category.id
      naturality := fun _ => by simp [CFunctor.identity, CFunctor.compose]
    }
    bwd := {
      app := fun _ => Category.id
      naturality := fun _ => by simp [CFunctor.identity, CFunctor.compose]
    }
    fwd_bwd := fun _ => by simp
    bwd_fwd := fun _ => by simp
  }
