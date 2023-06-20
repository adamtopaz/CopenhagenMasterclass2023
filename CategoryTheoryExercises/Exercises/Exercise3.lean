import Mathlib.CategoryTheory.Equivalence
set_option autoImplicit false

open CategoryTheory

universe u v

variable {C : Type u} [Category C]
variable {D : Type v} [Category D]

lemma equiv_reflects_mono {X Y : C} (f : X ⟶ Y) (e : C ≌ D)
  (hef : Mono (e.functor.map f)) : Mono f := by
-- Hint: when `e : C ≌ D`, `e.functor.map_injective` says
--   `∀ f g, e.functor.map f = e.functor.map g → f = g`
-- Hint: use `cancel_mono`.
have h := e.functor.map_injective (X := X) (Y := Y)
cases' hef with hef
constructor
intros W φ ψ h
specialize @hef (e.functor.obj W) (e.functor.map φ) (e.functor.map ψ)
sorry
done

lemma equiv_preserves_mono {X Y : C} (f : X ⟶ Y) [Mono f] (e : C ≌ D) :
  Mono (e.functor.map f) :=
-- Hint: if `w : f = g`, to obtain `F.map f = F.map G`,
--   you can use `have w' := congr_arg (λ k, F.map k) w`.
sorry

/-!
There are some further hints in
`hints/category_theory/exercise3/`
-/

