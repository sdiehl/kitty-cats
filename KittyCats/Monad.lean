import KittyCats.Monoidal
import KittyCats.NatTrans

open Category MonoidalCategory

-- Mac Lane, Ch VI.1
-- A monad on a category C is an endofunctor T equipped with natural
-- transformations η (unit) and μ (multiplication) satisfying associativity
-- and unit laws. Named CMonad to avoid collision with Lean's built-in Monad.
structure CMonad (C : Type u) [Category C] where
  T : Endofunctor C
  η : NatTrans (CFunctor.identity C) T
  μ : NatTrans (CFunctor.compose T T) T
  mul_assoc : ∀ (a : C), T.map (μ.app a) ≫ μ.app a = μ.app (T.obj a) ≫ μ.app a
  left_unit : ∀ (a : C), T.map (η.app a) ≫ μ.app a = Category.id
  right_unit : ∀ (a : C), η.app (T.obj a) ≫ μ.app a = Category.id

-- Mac Lane, Ch VI.5
-- The Kleisli category of a monad. Objects are the same as C, but a morphism
-- a → b is a morphism a → T(b) in C. Composition threads through the monad:
-- f then g is f followed by T(g) followed by μ (flatten).
structure Kleisli (C : Type u) [Category C] (M : CMonad C) where
  obj : C

variable {C : Type u} [Category C] (M : CMonad C)

-- Kleisli associativity uses naturality of μ and the monad associativity law.
theorem kleisli_assoc_lemma {b c d : C}
    (g : Hom b (M.T.obj c)) (h : Hom c (M.T.obj d)) :
    M.T.map g ≫ M.μ.app c ≫ M.T.map h ≫ M.μ.app d =
    M.T.map (g ≫ M.T.map h ≫ M.μ.app d) ≫ M.μ.app d := by
  have nat_μ := M.μ.naturality h
  simp only [CFunctor.compose] at nat_μ
  rw [M.T.map_comp, M.T.map_comp (M.T.map h), assoc, assoc,
      ← assoc (M.μ.app c), nat_μ.symm, assoc (M.T.map (M.T.map h)),
      ← M.mul_assoc]

instance : Category (Kleisli C M) where
  Hom a b := Hom a.obj (M.T.obj b.obj)
  id := M.η.app _
  comp f g := f ≫ M.T.map g ≫ M.μ.app _
  id_comp f := by
    have nat := M.η.naturality f
    simp [CFunctor.identity] at nat
    rw [← assoc, nat.symm, assoc, M.right_unit, comp_id]
  comp_id f := by rw [M.left_unit, comp_id]
  assoc f g h := by rw [assoc, assoc]; congr 1; exact kleisli_assoc_lemma M g h

-- Mac Lane, Ch VII
-- A monoid object in a monoidal category: an object M with multiplication
-- M ⊗ M → M and unit I → M satisfying associativity and unit laws.
structure MonoidObj (C : Type u) [Category C] [MonoidalCategory C] where
  carrier : C
  mul : Hom (carrier ⊗ carrier) carrier
  unit : Hom tensorUnit carrier
  mul_assoc : tensorHom mul Category.id ≫ mul =
    (associator carrier carrier carrier).hom ≫ tensorHom Category.id mul ≫ mul
  left_unit : tensorHom unit Category.id ≫ mul = (leftUnitor carrier).hom
  right_unit : tensorHom Category.id unit ≫ mul = (rightUnitor carrier).hom

-- The category of endofunctors on C: objects are endofunctors,
-- morphisms are natural transformations, composition is vertical composition.
instance endoCat (C : Type u) [Category C] : Category (Endofunctor C) where
  Hom F G := NatTrans F G
  id := NatTrans.ident _
  comp α β := NatTrans.vcomp α β
  id_comp α := by ext a; simp [NatTrans.vcomp, NatTrans.ident]
  comp_id α := by ext a; simp [NatTrans.vcomp, NatTrans.ident]
  assoc α β γ := by ext a; simp [NatTrans.vcomp, assoc]

-- Horizontal composition (Godement product) of natural transformations.
-- Given α : F ⟹ F' and β : G ⟹ G', the composite F ∘ G ⟹ F' ∘ G'
-- has component G(α_a) ≫ β(F'(a)).
def endoTensorHom {C : Type u} [Category C] {F F' G G' : Endofunctor C}
    (α : NatTrans F F') (β : NatTrans G G') :
    NatTrans (CFunctor.compose F G) (CFunctor.compose F' G') where
  app a := G.map (α.app a) ≫ β.app (F'.obj a)
  naturality {a b} f := by
    simp [CFunctor.compose]
    rw [← assoc, ← G.map_comp, α.naturality, G.map_comp, assoc, β.naturality, ← assoc]

-- Strict associator, left unitor, right unitor for the endofunctor category.
-- All components are the identity because functor composition is strictly
-- associative and unital on objects and morphisms.

def endoAssociator {C : Type u} [Category C] (F G H : Endofunctor C) :
    @Iso (Endofunctor C) (endoCat C)
      (CFunctor.compose (CFunctor.compose F G) H)
      (CFunctor.compose F (CFunctor.compose G H)) where
  hom := { app := fun _ => Category.id, naturality := fun _ => by simp [CFunctor.compose] }
  inv := { app := fun _ => Category.id, naturality := fun _ => by simp [CFunctor.compose] }
  hom_inv := by show NatTrans.vcomp _ _ = NatTrans.ident _; ext a; simp [NatTrans.vcomp, NatTrans.ident]
  inv_hom := by show NatTrans.vcomp _ _ = NatTrans.ident _; ext a; simp [NatTrans.vcomp, NatTrans.ident]

def endoLeftUnitor {C : Type u} [Category C] (F : Endofunctor C) :
    @Iso (Endofunctor C) (endoCat C) (CFunctor.compose (CFunctor.identity C) F) F where
  hom := { app := fun _ => Category.id, naturality := fun _ => by simp [CFunctor.compose, CFunctor.identity] }
  inv := { app := fun _ => Category.id, naturality := fun _ => by simp [CFunctor.compose, CFunctor.identity] }
  hom_inv := by show NatTrans.vcomp _ _ = NatTrans.ident _; ext a; simp [NatTrans.vcomp, NatTrans.ident]
  inv_hom := by show NatTrans.vcomp _ _ = NatTrans.ident _; ext a; simp [NatTrans.vcomp, NatTrans.ident]

def endoRightUnitor {C : Type u} [Category C] (F : Endofunctor C) :
    @Iso (Endofunctor C) (endoCat C) (CFunctor.compose F (CFunctor.identity C)) F where
  hom := { app := fun _ => Category.id, naturality := fun _ => by simp [CFunctor.compose, CFunctor.identity] }
  inv := { app := fun _ => Category.id, naturality := fun _ => by simp [CFunctor.compose, CFunctor.identity] }
  hom_inv := by show NatTrans.vcomp _ _ = NatTrans.ident _; ext a; simp [NatTrans.vcomp, NatTrans.ident]
  inv_hom := by show NatTrans.vcomp _ _ = NatTrans.ident _; ext a; simp [NatTrans.vcomp, NatTrans.ident]

-- The endofunctor category is monoidal with composition as the tensor
-- product and the identity functor as the unit. The coherence isomorphisms
-- are all strict (identity natural transformations) because functor
-- composition is strictly associative and unital.
instance endoMonoidal (C : Type u) [Category C] :
    @MonoidalCategory (Endofunctor C) (endoCat C) where
  tensorObj F G := CFunctor.compose F G
  tensorHom α β := endoTensorHom α β
  tensorUnit := CFunctor.identity C
  associator := endoAssociator
  leftUnitor := endoLeftUnitor
  rightUnitor := endoRightUnitor
  tensor_id {F G} := by
    show endoTensorHom (NatTrans.ident F) (NatTrans.ident G) = NatTrans.ident _
    ext a; simp [endoTensorHom, NatTrans.ident]
  tensor_comp {F₁ F₂ F₃ G₁ G₂ G₃} f₁ f₂ g₁ g₂ := by
    show endoTensorHom (NatTrans.vcomp f₁ f₂) (NatTrans.vcomp g₁ g₂) =
         NatTrans.vcomp (endoTensorHom f₁ g₁) (endoTensorHom f₂ g₂)
    ext a; simp only [endoTensorHom, NatTrans.vcomp, CFunctor.compose]
    rw [G₁.map_comp, assoc,
        ← assoc (G₁.map (f₂.app a)) (g₁.app (F₃.obj a)) (g₂.app (F₃.obj a)),
        g₁.naturality (f₂.app a), assoc, ← assoc (G₁.map (f₁.app a))]
  pentagon F G H K := by
    show NatTrans.vcomp (endoTensorHom (endoAssociator F G H).hom (NatTrans.ident K))
          (NatTrans.vcomp (endoAssociator F (CFunctor.compose G H) K).hom
            (endoTensorHom (NatTrans.ident F) (endoAssociator G H K).hom)) =
         NatTrans.vcomp (endoAssociator (CFunctor.compose F G) H K).hom
           (endoAssociator F G (CFunctor.compose H K)).hom
    ext a; simp [endoTensorHom, endoAssociator, NatTrans.vcomp, NatTrans.ident, CFunctor.compose]
  triangle F G := by
    show NatTrans.vcomp (endoAssociator F (CFunctor.identity C) G).hom
          (endoTensorHom (NatTrans.ident F) (endoLeftUnitor G).hom) =
         endoTensorHom (endoRightUnitor F).hom (NatTrans.ident G)
    ext a; simp [endoTensorHom, endoAssociator, endoLeftUnitor, endoRightUnitor,
                 NatTrans.vcomp, NatTrans.ident, CFunctor.compose, CFunctor.identity]

-- A monad is just a monoid in the category of endofunctors, what's the problem? ;-)
def monadIsMonoidObj {C : Type u} [Category C] (M : CMonad C) :
    @MonoidObj (Endofunctor C) (endoCat C) (endoMonoidal C) where
  carrier := M.T
  mul := M.μ
  unit := M.η
  mul_assoc := by
    show NatTrans.vcomp (endoTensorHom M.μ (NatTrans.ident M.T)) M.μ =
         NatTrans.vcomp (endoAssociator M.T M.T M.T).hom
           (NatTrans.vcomp (endoTensorHom (NatTrans.ident M.T) M.μ) M.μ)
    ext a; simp [endoTensorHom, endoAssociator, NatTrans.vcomp, NatTrans.ident, CFunctor.compose]
    exact M.mul_assoc a
  left_unit := by
    show NatTrans.vcomp (endoTensorHom M.η (NatTrans.ident M.T)) M.μ =
         (endoLeftUnitor M.T).hom
    ext a; simp [endoTensorHom, endoLeftUnitor, NatTrans.vcomp, NatTrans.ident,
                 CFunctor.compose, CFunctor.identity]
    exact M.left_unit a
  right_unit := by
    show NatTrans.vcomp (endoTensorHom (NatTrans.ident M.T) M.η) M.μ =
         (endoRightUnitor M.T).hom
    ext a; simp [endoTensorHom, endoRightUnitor, NatTrans.vcomp, NatTrans.ident,
                 CFunctor.compose, CFunctor.identity]
    exact M.right_unit a
