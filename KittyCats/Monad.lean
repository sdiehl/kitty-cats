import KittyCats.Monoidal
import KittyCats.NatTrans

open Category MonoidalCategory

-- Mac Lane, Ch VI.1
-- A monad on C is an endofunctor T with unit η and multiplication μ
-- satisfying associativity and unit laws.
structure CMonad (C : Type u) [Category C] where
  T : Endofunctor C
  η : NatTrans (CFunctor.identity C) T
  μ : NatTrans (CFunctor.compose T T) T
  mul_assoc : ∀ (a : C), T.map (μ.app a) ≫ μ.app a = μ.app (T.obj a) ≫ μ.app a
  left_unit : ∀ (a : C), T.map (η.app a) ≫ μ.app a = Category.id
  right_unit : ∀ (a : C), η.app (T.obj a) ≫ μ.app a = Category.id

-- Mac Lane, Ch VI.5
-- The Kleisli category of a monad. A morphism a → b is a morphism
-- a → T(b) in C. Composition: f then g is f followed by T(g) then μ.
structure Kleisli (C : Type u) [Category C] (M : CMonad C) where
  obj : C

section KleisliSection

variable {C : Type u} [Category C] (M : CMonad C)

theorem kleisli_assoc_lemma {b c d : C}
    (g : Hom b (M.T.obj c)) (h : Hom c (M.T.obj d)) :
    M.T.map g ≫ M.μ.app c ≫ M.T.map h ≫ M.μ.app d =
    M.T.map (g ≫ M.T.map h ≫ M.μ.app d) ≫ M.μ.app d := by
  have nat_μ := M.μ.naturality h
  simp only [CFunctor.compose] at nat_μ
  rw [M.T.map_comp, M.T.map_comp (M.T.map h),
      assoc, assoc, ← assoc (M.μ.app c),
      nat_μ.symm, assoc (M.T.map (M.T.map h)),
      ← M.mul_assoc]

instance : Category (Kleisli C M) where
  Hom a b := Hom a.obj (M.T.obj b.obj)
  id := M.η.app _
  comp f g := f ≫ M.T.map g ≫ M.μ.app _
  id_comp f := by
    have nat := M.η.naturality f
    simp [CFunctor.identity] at nat
    rw [← assoc, nat.symm, assoc, M.right_unit, comp_id]
  comp_id f := by
    rw [M.left_unit, comp_id]
  assoc f g h := by
    rw [assoc, assoc]
    congr 1
    exact kleisli_assoc_lemma M g h

end KleisliSection

-- Mac Lane, Ch VII
-- A monoid object in a monoidal category.
structure MonoidObj (C : Type u) [Category C] [MonoidalCategory C] where
  carrier : C
  mul : Hom (carrier ⊗ carrier) carrier
  unit : Hom tensorUnit carrier
  mul_assoc :
    tensorHom mul Category.id ≫ mul =
    (associator carrier carrier carrier).hom ≫ tensorHom Category.id mul ≫ mul
  left_unit : tensorHom unit Category.id ≫ mul = (leftUnitor carrier).hom
  right_unit : tensorHom Category.id unit ≫ mul = (rightUnitor carrier).hom

-- The endofunctor category: morphisms are natural transformations.
instance endoCat (C : Type u) [Category C] : Category (Endofunctor C) where
  Hom F G := NatTrans F G
  id := NatTrans.ident _
  comp α β := NatTrans.vcomp α β
  id_comp α := by ext a; simp [NatTrans.vcomp, NatTrans.ident]
  comp_id α := by ext a; simp [NatTrans.vcomp, NatTrans.ident]
  assoc α β γ := by ext a; simp [NatTrans.vcomp, assoc]

-- Round-trip proof for identity-component NatTrans pairs.
local macro "endo_roundtrip" : tactic =>
  `(tactic| (show NatTrans.vcomp _ _ = NatTrans.ident _
             ext a
             simp [NatTrans.vcomp, NatTrans.ident]))

-- Horizontal composition (Godement product) of natural transformations.
def endoTensorHom {C : Type u} [Category C] {F F' G G' : Endofunctor C}
    (α : NatTrans F F') (β : NatTrans G G') :
    NatTrans (CFunctor.compose F G) (CFunctor.compose F' G') where
  app a := G.map (α.app a) ≫ β.app (F'.obj a)
  naturality f := by
    simp [CFunctor.compose]
    rw [← assoc, ← G.map_comp, α.naturality,
        G.map_comp, assoc, β.naturality, ← assoc]

-- Strict coherence isomorphisms for the endofunctor category.
-- All components are identity because functor composition is
-- strictly associative and unital on objects and morphisms.

def endoAssociator {C : Type u} [Category C] (F G H : Endofunctor C) :
    @Iso _ (endoCat C) (CFunctor.compose (CFunctor.compose F G) H)
                       (CFunctor.compose F (CFunctor.compose G H)) :=
  { hom := { app := fun _ => Category.id
             naturality := fun _ => by simp [CFunctor.compose] }
    inv := { app := fun _ => Category.id
             naturality := fun _ => by simp [CFunctor.compose] }
    hom_inv := by endo_roundtrip
    inv_hom := by endo_roundtrip }

def endoLeftUnitor {C : Type u} [Category C] (F : Endofunctor C) :
    @Iso _ (endoCat C) (CFunctor.compose (CFunctor.identity C) F) F :=
  { hom := { app := fun _ => Category.id
             naturality := fun _ => by simp [CFunctor.compose, CFunctor.identity] }
    inv := { app := fun _ => Category.id
             naturality := fun _ => by simp [CFunctor.compose, CFunctor.identity] }
    hom_inv := by endo_roundtrip
    inv_hom := by endo_roundtrip }

def endoRightUnitor {C : Type u} [Category C] (F : Endofunctor C) :
    @Iso _ (endoCat C) (CFunctor.compose F (CFunctor.identity C)) F :=
  { hom := { app := fun _ => Category.id
             naturality := fun _ => by simp [CFunctor.compose, CFunctor.identity] }
    inv := { app := fun _ => Category.id
             naturality := fun _ => by simp [CFunctor.compose, CFunctor.identity] }
    hom_inv := by endo_roundtrip
    inv_hom := by endo_roundtrip }

-- Unfold the endofunctor monoidal structure to NatTrans components.
local macro "endo_simp" : tactic =>
  `(tactic| simp [endoTensorHom, endoAssociator, endoLeftUnitor, endoRightUnitor,
                   NatTrans.vcomp, NatTrans.ident, CFunctor.compose, CFunctor.identity])

-- The endofunctor category is monoidal under composition.
instance endoMonoidal (C : Type u) [Category C] :
    @MonoidalCategory _ (endoCat C) where
  tensorObj F G := CFunctor.compose F G
  tensorHom α β := endoTensorHom α β
  tensorUnit := CFunctor.identity C
  associator := endoAssociator
  leftUnitor := endoLeftUnitor
  rightUnitor := endoRightUnitor
  tensor_id {F G} := by
    show endoTensorHom (NatTrans.ident F) (NatTrans.ident G) = NatTrans.ident _
    ext a
    simp [endoTensorHom, NatTrans.ident]
  tensor_comp {_ _ F₃ G₁ _ _} f₁ f₂ g₁ g₂ := by
    show endoTensorHom (NatTrans.vcomp f₁ f₂) (NatTrans.vcomp g₁ g₂) =
         NatTrans.vcomp (endoTensorHom f₁ g₁) (endoTensorHom f₂ g₂)
    ext a
    simp only [endoTensorHom, NatTrans.vcomp, CFunctor.compose]
    rw [G₁.map_comp, assoc,
        ← assoc (G₁.map (f₂.app a)) (g₁.app (F₃.obj a)) (g₂.app (F₃.obj a)),
        g₁.naturality (f₂.app a),
        assoc, ← assoc (G₁.map (f₁.app a))]
  pentagon F G H K := by
    show NatTrans.vcomp
          (endoTensorHom (endoAssociator F G H).hom (NatTrans.ident K))
          (NatTrans.vcomp (endoAssociator F (CFunctor.compose G H) K).hom
            (endoTensorHom (NatTrans.ident F) (endoAssociator G H K).hom)) =
         NatTrans.vcomp (endoAssociator (CFunctor.compose F G) H K).hom
           (endoAssociator F G (CFunctor.compose H K)).hom
    ext a
    endo_simp
  triangle F G := by
    show NatTrans.vcomp (endoAssociator F (CFunctor.identity C) G).hom
          (endoTensorHom (NatTrans.ident F) (endoLeftUnitor G).hom) =
         endoTensorHom (endoRightUnitor F).hom (NatTrans.ident G)
    ext a
    endo_simp

-- A monad is just a monoid in the category of endofunctors, what's the problem?
def monadIsMonoidObj {C : Type u} [Category C] (M : CMonad C) :
    @MonoidObj _ (endoCat C) (endoMonoidal C) where
  carrier := M.T
  mul := M.μ
  unit := M.η
  mul_assoc := by
    show NatTrans.vcomp (endoTensorHom M.μ (NatTrans.ident M.T)) M.μ =
         NatTrans.vcomp (endoAssociator M.T M.T M.T).hom
           (NatTrans.vcomp (endoTensorHom (NatTrans.ident M.T) M.μ) M.μ)
    ext a; endo_simp
    exact M.mul_assoc a
  left_unit := by
    show NatTrans.vcomp (endoTensorHom M.η (NatTrans.ident M.T)) M.μ =
         (endoLeftUnitor M.T).hom
    ext a; endo_simp
    exact M.left_unit a
  right_unit := by
    show NatTrans.vcomp (endoTensorHom (NatTrans.ident M.T) M.η) M.μ =
         (endoRightUnitor M.T).hom
    ext a; endo_simp
    exact M.right_unit a
