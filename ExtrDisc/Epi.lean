import ExtrDisc.Basic
import Mathlib.Topology.Category.CompHaus.EffectiveEpi

import Profinite.Epi

open CategoryTheory Limits




-- namespace Test

-- variable {α : Type} [Fintype α] {C D : Type u} [Category C] [Category D]
--   {B : C} {X : α → C}
--   (π : (a : α) → (X a ⟶ B)) (F : C ⥤ D)
--   [Full F] [Faithful F]

-- -- Hmm…
-- -- variable (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b)

-- #check fun (a : α) => F.map (π a)

-- variable (a : α)

-- #check F.obj (X a)

-- -- def π₂ : (a : α) → ((X a).compHaus ⟶ B.compHaus) :=
-- --   fun a => (ExtrDisc.toCompHaus.map (π a))

-- lemma EffectiveEpiFamily_of_fully_faithful
--     (h : EffectiveEpiFamily (fun a => F.obj (X a)) (fun a => F.map (π a))) :
--     EffectiveEpiFamily X π :=
--   ⟨⟨{
--     desc := (fun {W} e he => by
--       apply Full.preimage (F := F)
--       refine EffectiveEpiFamily.desc (fun a => F.obj (X a)) (fun a => F.map (π a)) ?_ ?_
--       · exact (fun a => F.map (e a))
--       · intro Z a₁ a₂ (g₁ : Z ⟶ F.obj (X a₁)) (g₂ : Z ⟶ F.obj (X a₂))
--           (hg : g₁ ≫ F.map (π a₁) = g₂ ≫ F.map (π a₂))

--         -- wanted to use `he` but `(Z : D)` might not be of the form `F.obj Z'`,
--         -- so this doesn't work :(
--         sorry
--     )
--     fac := (fun {W} e he a => by
--       sorry
--       )
--     uniq := sorry }⟩⟩

-- end Test

namespace ExtrDisc

universe u

variable {α : Type} [Fintype α] (X : α → ExtrDisc.{u})

variable {α : Type} [Fintype α] {B : ExtrDisc.{u}}
  {X : α → ExtrDisc.{u}} (π : (a : α) → (X a ⟶ B))
  (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b)

-- For mathlib?
/-- Construct a term of `Profinite` from a type endowed with the structure of a
compact, Hausdorff and totally disconnected topological space.
-/
def of (X : Type _) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ExtremallyDisconnected X] : ExtrDisc :=
  ⟨⟨⟨X, inferInstance⟩⟩⟩

-- -- For mathlib?
instance {π : ι → Type _} [∀ i, TopologicalSpace (π i)] [∀ i, ExtremallyDisconnected (π i)] :
    ExtremallyDisconnected (Σi, π i) := by
  sorry
--   refine ⟨fun s hs₁ hs₂ ⟨a, hs₃⟩  => ?_⟩
--   simp at hs₃

--   obtain rfl | h := s.eq_empty_or_nonempty
--   · sorry -- exact Set.subsingleton_empty
--   · obtain ⟨a, t, ht, rfl⟩ := Sigma.isConnected_iff.1 ⟨h, hs⟩
--     exact ht.isPreconnected.subsingleton.image _

section FiniteCoproducts

variable {α : Type} [Fintype α] (X : α → ExtrDisc.{u})

/--
The coproduct of a finite family of objects in `ExtrDisc`, constructed as the disjoint
union with its usual topology.
-/
def finiteCoproduct : ExtrDisc := ExtrDisc.of <| Σ (a : α), X a

/--
The inclusion of one of the factors into the explicit finite coproduct.
-/
def finiteCoproduct.ι (a : α) : X a ⟶ finiteCoproduct X where
  toFun := fun x => ⟨a,x⟩
  continuous_toFun := continuous_sigmaMk (σ := fun a => X a)

/--
To construct a morphism from the explicit finite coproduct, it suffices to
specify a morphism from each of its factors.
This is essentially the universal property of the coproduct.
-/
def finiteCoproduct.desc {B : ExtrDisc.{u}} (e : (a : α) → (X a ⟶ B)) :
    finiteCoproduct X ⟶ B where
  toFun := fun ⟨a,x⟩ => e a x
  continuous_toFun := by
    apply continuous_sigma
    intro a ; exact (e a).continuous

@[reassoc (attr := simp)]
lemma finiteCoproduct.ι_desc {B : ExtrDisc.{u}} (e : (a : α) → (X a ⟶ B)) (a : α) :
  finiteCoproduct.ι X a ≫ finiteCoproduct.desc X e = e a := rfl

lemma finiteCoproduct.hom_ext {B : ExtrDisc.{u}} (f g : finiteCoproduct X ⟶ B)
    (h : ∀ a : α, finiteCoproduct.ι X a ≫ f = finiteCoproduct.ι X a ≫ g) : f = g := by
  ext ⟨a,x⟩
  specialize h a
  apply_fun (fun q => q x) at h
  exact h

/--
The coproduct cocone associated to the explicit finite coproduct.
-/
@[simps]
def finiteCoproduct.cocone : Limits.Cocone (Discrete.functor X) where
  pt := finiteCoproduct X
  ι := Discrete.natTrans fun ⟨a⟩ => finiteCoproduct.ι X a

/--
The explicit finite coproduct cocone is a colimit cocone.
-/
@[simps]
def finiteCoproduct.isColimit : Limits.IsColimit (finiteCoproduct.cocone X) where
  desc := fun s => finiteCoproduct.desc _ fun a => s.ι.app ⟨a⟩
  fac := fun s ⟨a⟩ => finiteCoproduct.ι_desc _ _ _
  uniq := fun s m hm => finiteCoproduct.hom_ext _ _ _ fun a => by
    specialize hm ⟨a⟩
    ext t
    apply_fun (fun q => q t) at hm
    exact hm

end FiniteCoproducts


-- /-
-- pick any open subset

-- -/
-- #check Full

lemma epi_iff_surjective {X Y : ExtrDisc.{u}} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective f :=
  sorry

namespace EffectiveEpiFamily

#check ExtrDisc.toCompHaus
#check profiniteToCompHaus
#check ExtrDisc.toProfinite

/- Lifting the diagram `π` to `CompHaus`. -/
def π₂ : (a : α) → ((X a).compHaus ⟶ B.compHaus) :=
  fun a => (ExtrDisc.toCompHaus.map (π a))

#check CompHaus.EffectiveEpiFamily.ι (π₂ π) surj

#check (CompHaus.EffectiveEpiFamily.struct (π₂ π) surj).desc

#check Quotient.lift


noncomputable
def struct : EffectiveEpiFamilyStruct X π where
  desc := fun {W} e h => ExtrDisc.toCompHaus.preimage <|
    by
      dsimp
      have f₁ := CompHaus.EffectiveEpiFamily.ι (π₂ π) surj
      have f₂ : CompHaus.EffectiveEpiFamily.QB π ⟶ W.compHaus := {
    toFun := Quotient.lift (fun ⟨a,x⟩ => e a x) <| by
      sorry
      -- rintro ⟨a,x⟩ ⟨b,y⟩ ⟨Z,z,fst,snd,hh,hx,hy⟩
      -- dsimp at *
      -- rw [← hx, ← hy]
      -- specialize h _ _ fst ?_ ?_
      -- · ext z
      --   apply ιFun_injective
      --   apply_fun (fun q => q z) at hh
      --   exact hh
      -- apply_fun (fun q => q z) at h
      -- exact h
    continuous_toFun := by
      apply Continuous.quotient_lift
      apply continuous_sigma
      intro a
      exact (e a).continuous }
      exact f₁.inv ≫ f₂
  fac := sorry
  uniq := sorry

end EffectiveEpiFamily

theorem effectiveEpiFamily_of_jointly_surjective
    {α : Type} [Fintype α] {B : ExtrDisc.{u}}
    (X : α → ExtrDisc.{u}) (π : (a : α) → (X a ⟶ B))
    (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b) :
    EffectiveEpiFamily X π := -- by
  -- apply Test.EffectiveEpiFamily_of_fully_faithful π ExtrDisc.toCompHaus
  -- simp
  -- apply CompHaus.effectiveEpiFamily_of_jointly_surjective
  -- assumption

  ⟨⟨ExtrDisc.EffectiveEpiFamily.struct π surj⟩⟩ -- TODO: add `surj`


open List in
theorem effectiveEpiFamily_tfae {α : Type} [Fintype α] {B : ExtrDisc.{u}}
    (X : α → ExtrDisc.{u})
    (π : (a : α) → (X a ⟶ B)) :
    TFAE [
      EffectiveEpiFamily X π,
      Epi (Limits.Sigma.desc π),
      ∀ (b : B), ∃ (a : α) (x : X a), π a x = b
    ] := by
  tfae_have 1 → 2
  · intro ; infer_instance
  tfae_have 2 → 3
  · intro e
    rw [epi_iff_surjective] at e
    let i : ∐ X ≅ finiteCoproduct X :=
      (colimit.isColimit _).coconePointUniqueUpToIso (finiteCoproduct.isColimit _)
    intro b
    obtain ⟨t,rfl⟩ := e b
    let q := i.hom t
    refine ⟨q.1,q.2,?_⟩
    have : t = i.inv (i.hom t) := show t = (i.hom ≫ i.inv) t by simp only [i.hom_inv_id] ; rfl
    rw [this]
    show _ = (i.inv ≫ Sigma.desc π) (i.hom t)
    suffices i.inv ≫ Sigma.desc π = finiteCoproduct.desc X π by
      rw [this] ; rfl
    rw [Iso.inv_comp_eq]
    apply colimit.hom_ext
    rintro ⟨a⟩
    simp only [Discrete.functor_obj, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app,
      colimit.comp_coconePointUniqueUpToIso_hom_assoc]
    ext ; rfl
  tfae_have 3 → 1
  · apply effectiveEpiFamily_of_jointly_surjective
  tfae_finish

end ExtrDisc
