import KittyCats.Category

open Category

-- Awodey, Ch 1
instance instProductCategory {C : Type u₁} {D : Type u₂}
    [instC : Category C] [instD : Category D] : Category (C × D) where
  Hom p q := instC.Hom p.1 q.1 × instD.Hom p.2 q.2
  id := (instC.id, instD.id)
  comp f g := (instC.comp f.1 g.1, instD.comp f.2 g.2)
  id_comp f := Prod.ext (instC.id_comp f.1) (instD.id_comp f.2)
  comp_id f := Prod.ext (instC.comp_id f.1) (instD.comp_id f.2)
  assoc f g h := Prod.ext (instC.assoc f.1 g.1 h.1) (instD.assoc f.2 g.2 h.2)
