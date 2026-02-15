# KittyCats

A Lean 4 formalization of undergraduate category theory built from first principles with no Mathlib.

- [Category](KittyCats/Category.lean) - categories, composition, identity, and the opposite category
- [Functor](KittyCats/Functor.lean) - functors, identity functor, functor composition
- [NatTrans](KittyCats/NatTrans.lean) - natural transformations, vertical composition, natural isomorphisms
- [Morphism](KittyCats/Morphism.lean) - isomorphisms, monomorphisms, epimorphisms, split monos/epis, groupoids
- [Product](KittyCats/Product.lean) - the product of two categories
- [Limits](KittyCats/Limits.lean) - terminal and initial objects, categorical products, coproducts
- [Cartesian](KittyCats/Cartesian.lean) - cartesian and cocartesian categories, diagonal, product maps
- [Monoidal](KittyCats/Monoidal.lean) - monoidal, braided, and symmetric monoidal categories
- [Closed](KittyCats/Closed.lean) - exponential objects, cartesian closed categories
- [Adjunction](KittyCats/Adjunction.lean) - adjunctions via unit/counit with triangle identities
- [Dual](KittyCats/Dual.lean) - the duality principle: terminal/initial, product/coproduct, mono/epi via Op
- [Equiv](KittyCats/Equiv.lean) - equivalence of categories, the Op involution
- [Yoneda](KittyCats/Yoneda.lean) - presheaves, the Yoneda lemma, fully faithful embedding
- [Instances](KittyCats/Instances.lean) - the category of types as a cartesian closed category
- [Thm](KittyCats/Thm.lean) - naturality of pairing, diagonal absorption, and the curry/eval adjunction

## Refs

- Steve Awodey, _Category Theory_ (2nd edition, Oxford Logic Guides, 2010).
- Saunders Mac Lane, _Categories for the Working Mathematician_ (2nd edition, Springer GTM, 1998).

## License

MIT
